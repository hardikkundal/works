use std::{borrow::Cow, fmt, fmt::Write, ops::Deref};

use jslt_macro::expect_inner;
use pest::iterators::Pairs;
use serde_json::Value;
use serde_json::json;   // ← add this


use crate::{
  context::{Context, builtins::boolean_cast},
  error::{JsltError, Result},
  format,
  parser::{FromPairs, Rule},
  transform::{
    Transform,
    expr::{ExprTransformer, ForTransformer},
  },
};

#[derive(Debug)]
pub struct PairTransformer(ExprTransformer, ExprTransformer);

impl FromPairs for PairTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let mut inner = expect_inner!(pairs, Rule::Pair)?;

    let key = ExprTransformer::from_pairs(&mut inner)?;
    let value = ExprTransformer::from_pairs(&mut inner)?;

    Ok(PairTransformer(key, value))
  }
}

impl format::Display for PairTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let PairTransformer(key, value) = self;

    format::Display::fmt(key, f)?;
    f.write_str(": ")?;
    format::Display::fmt(value, f)
  }
}

#[derive(Debug, Default)]
pub struct ObjectTransformer {
  inner: Vec<ObjectTransformerInner>,
}

impl FromPairs for ObjectTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let pairs = expect_inner!(pairs, Rule::Object)?;

    let mut builder = ObjectTransformer::default();

    for pair in pairs {
      match pair.as_rule() {
        Rule::Pair => {
          builder
            .inner
            .push(ObjectTransformerInner::Pair(PairTransformer::from_pairs(
              &mut Pairs::single(pair),
            )?));
        }
        Rule::ObjectFor => {
          let mut inner_pairs = pair.into_inner();

          builder.inner.push(ObjectTransformerInner::For(
            ObjectForTransformer::from_pairs(&mut inner_pairs)?,
          ));
        }
        Rule::ObjectSpread => {
          let mut pairs = pair.into_inner();

          builder
            .inner
            .push(ObjectTransformerInner::Spread(ExprTransformer::from_pairs(
              &mut pairs,
            )?))
        }
        _ => unimplemented!("for Pair: {pair:#?}"),
      }
    }

    Ok(builder)
  }
}

impl Transform for ObjectTransformer {
  fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
    let mut items = serde_json::Map::new();

    for inner in &self.inner {
      match inner {
    // ────────────────────────────────────── ordinary  "key : value"  pair
    ObjectTransformerInner::Pair(PairTransformer(key_expr, val_expr)) => {
        // create ONE owned JsltContext we can mutate
        let mut pair_ctx = context.clone();
        println!("🔰 [Pair]  cloned vars (start) = {:#?}", pair_ctx.variables);

        // ─ key  (may contain `let …`)
        let key_val = key_expr.transform_value(
            Context::Borrowed(pair_ctx.to_mut()),   // same mutable ctx
            input,
        )?;
        println!("🔰 [Pair]  after key  vars     = {:#?}", pair_ctx.variables);

        let key_str = key_val.as_str().ok_or_else(|| JsltError::RuntimeError(
            format!("key must be string but got {key_val}")
        ))?;
        println!("🔰 [Pair]  key = {}", key_str);

        // ─ value (reads the variable we just defined)
        let val_val = val_expr.transform_value(
            Context::Borrowed(pair_ctx.to_mut()),   // same mutable ctx
            input,
        )?;
        println!("🔰 [Pair]  after value vars     = {:#?}", pair_ctx.variables);
        println!("🔰 [Pair]  val = {:?}", val_val);

        items.insert(key_str.to_owned(), val_val);
    }

    // ───────────────────────────────────────────────  for ( … )  pair
    ObjectTransformerInner::For(ObjectForTransformer {
        source,
        output,
        condition,
    }) => {
        let PairTransformer(key_expr, val_expr) = output.deref();

        // evaluate collection we’re iterating
        let src_val = source.transform_value(Context::Borrowed(&context), input)?;

        let iter: Box<dyn Iterator<Item = Cow<Value>>> = if src_val.is_object() {
            println!("🔁 [For]  iterating object: {:?}", src_val);
            Box::new(src_val.as_object().unwrap().iter().map(|(k,v)| {
                Cow::Owned(json!({ "key": k, "value": v }))
            }))
        } else if src_val.is_array() {
            println!("🔁 [For]  iterating array: {:?}", src_val);
            Box::new(src_val.as_array().unwrap().iter().map(Cow::Borrowed))
        } else {
            return Err(JsltError::RuntimeError(format!(
                "Can iterate only arrays or objects (got {src_val})"
            )));
        };

        for elem in iter {
           // ONE owned context per element  (not a Cow!)
          let mut pair_ctx_owned = (*context).clone();
          println!("🔰 [ForPair] cloned vars (start) = {:#?}", pair_ctx_owned.variables);

          // key
          let key_val = key_expr.transform_value(
              Context::Borrowed(&mut pair_ctx_owned),   // borrow the SAME ctx
              &elem,
          )?;
          println!("🔰 [ForPair] after key  vars = {:#?}", pair_ctx_owned.variables);

          let key_str = key_val.as_str().ok_or_else(|| JsltError::RuntimeError(
              format!("key must be string but got {key_val}")
          ))?;

          // value
          let val_val = val_expr.transform_value(
              Context::Borrowed(&mut pair_ctx_owned),   // SAME ctx again
              &elem,
          )?;
          println!("🔰 [ForPair] after value vars = {:#?}", pair_ctx_owned.variables);
          println!("🔰 [ForPair] val = {:?}", val_val);

          items.insert(key_str.to_owned(), val_val);

        }
    }



        ObjectTransformerInner::Spread(expr) => {
          let source = input.as_object().ok_or_else(|| {
            JsltError::RuntimeError(format!("object spread expected and object but got {input}"))
          })?;

          for key in source.keys() {
            if items.contains_key(key) {
              continue;
            }

            items.insert(
              key.clone(),
              expr.transform_value(Context::Borrowed(&context), &source[key])?,
            );
          }
        }
      }
    }

    Ok(Value::Object(items))
  }
}

impl format::Display for ObjectTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    if self.inner.is_empty() {
      f.write_str("{}")
    } else {
      f.write_str("{\n")?;

      let last_item_index = self.inner.len() - 1;
      let mut slot = None;
      let mut state = Default::default();

      let mut writer = format::PadAdapter::wrap(f, &mut slot, &mut state);

      for (index, item) in self.inner.iter().enumerate() {
        format::Display::fmt(item, &mut writer)?;

        if index != last_item_index {
          writer.write_str(",\n")?;
        } else {
          writer.write_str("\n")?;
        }
      }

      f.write_str("}")?;

      Ok(())
    }
  }
}

#[derive(Debug)]
pub enum ObjectTransformerInner {
  Pair(PairTransformer),
  For(ObjectForTransformer),
  Spread(ExprTransformer),
}

impl format::Display for ObjectTransformerInner {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    match self {
      ObjectTransformerInner::Pair(pair) => format::Display::fmt(pair, f),
      ObjectTransformerInner::For(object_for) => format::Display::fmt(object_for, f),
      ObjectTransformerInner::Spread(expr) => {
        f.write_str("*: ")?;

        format::Display::fmt(expr, f)
      }
    }
  }
}

pub type ObjectForTransformer = ForTransformer<PairTransformer>;