use std::{borrow::Cow, fmt, fmt::Write, ops::Deref};

use jslt_macro::expect_inner;
use pest::iterators::Pairs;
use serde_json::Value;

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
use crate::trace;


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
    trace!("▶ ObjectTransformer::transform_value; input = {:?}", input);
    let mut items = serde_json::Map::new();

    for inner in &self.inner {
      trace!("  ObjectTransformer inner variant = {:?}", inner);
      match inner {
        ObjectTransformerInner::Pair(PairTransformer(key, value)) => {
          let mut loop_ctx = context.clone();
          trace!("    ▶ Object Pair; evaluating key");
          let key = key.transform_value(Context::Borrowed(&mut loop_ctx), input)?;
           trace!("    key = {:?}", key);

          let key = key.as_str().ok_or_else(|| {
            JsltError::RuntimeError(format!(
              "expression outout for key should be a string but got {key}"
            ))
          })?;
          trace!("    ▶ Object Pair; evaluating value for key `{}`", key);
          let val = value.transform_value(Context::Borrowed(&mut loop_ctx), input)?;
          trace!("    value = {:?}", val);

          items.insert(
            key.to_owned(),
            value.transform_value(Context::Borrowed(&mut loop_ctx), input)?,
          );
        }
        ObjectTransformerInner::For(ObjectForTransformer {
          source,
          output,
          condition,
        }) => {
          let PairTransformer(key, value) = output.deref();
          trace!("    ▶ ObjectFor; evaluating source");
          let source = source.transform_value(Context::Borrowed(&context), input)?;
          trace!("    source produced = {:?}", source);

          let input_iter: Box<dyn Iterator<Item = Cow<Value>>> = if source.is_object() {
            Box::new(
              source
                .as_object()
                .expect("Should be object")
                .into_iter()
                .map(|(key, value)| Cow::Owned(serde_json::json!({ "key": key, "value": value }))),
            )
          } else {
            Box::new(
              source
                .as_array()
                .expect("Should be array")
                .iter()
                .map(Cow::Borrowed),
            )
          };

          for input in input_iter {
            let mut loop_ctx=context.clone();
            trace!("      For item = {:?}", input);
            if let Some(condition) = condition {
              trace!("        ▶ ObjectFor condition");
              let cond_val = condition.transform_value(Context::Borrowed(&mut loop_ctx), &input)?;
              trace!("        condition → {:?}", cond_val);
              if !boolean_cast(&condition.transform_value(Context::Borrowed(&mut loop_ctx), &input)?) {
                trace!("        condition false; skipping");
                continue;
              }
            }

            let key = key.transform_value(Context::Borrowed(&mut loop_ctx), &input)?;
            //  trace!("        key =);

            let key = key.as_str().ok_or_else(|| {
              JsltError::RuntimeError(format!(
                "expression outout for key should be a string but got {key}"
              ))
            })?;

            items.insert(
              key.to_owned(),
              value.transform_value(Context::Borrowed(&mut loop_ctx), &input)?,
            );
          }
        }
        ObjectTransformerInner::Spread(expr) => {
          let source = input.as_object().ok_or_else(|| {
            JsltError::RuntimeError(format!("object spread expected and object but got {input}"))
          })?;

          for key in source.keys() {
            trace!("      considering spread key = {}", key);
            if items.contains_key(key) {
              trace!("      already has key; skipping");
              continue;
            }
            trace!("      ▶ spreading key `{}`", key);
            let v = expr.transform_value(Context::Borrowed(&context), &source[key])?;
            trace!("      spread value = {:?}", v);

            items.insert(
              key.clone(),
              expr.transform_value(Context::Borrowed(&context), &source[key])?,
            );
          }
        }
      }
    }
    trace!("◀ ObjectTransformer::transform_value ⇒ {:?}", items);

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
