use std::{fmt, fmt::Write as _, sync::Arc};



use jslt_macro::expect_inner;
use pest::iterators::{Pair, Pairs};
use serde_json::Value;

use crate::{
  context::{Context, DynamicFunction, JsltFunction, builtins},
  error::{JsltError, Result},
  format,
  parser::{FromPairs, Rule},
  transform::{
    Transform,
    value::{ValueTransformer, accessor::AccessorTransformer},
  },
};
// change 1
use crate::trace;
use crate::Cow;


#[derive(Debug)]
pub enum ExprTransformer {
  Value(ValueTransformer),
  IfStatement(IfStatementTransformer),
  OperatorExpr(OperatorExprTransformer),
  FunctionDef(FunctionDefTransformer),
  FunctionCall(FunctionCallTransformer),
  VariableDef(VariableDefTransformer),
}
// change 2
impl Transform for ExprTransformer {
  fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
    trace!("▶ ExprTransformer::transform_value; variant = {:?}", self);
    let result=match self {
      ExprTransformer::Value(value) => value.transform_value(context, input),
      ExprTransformer::IfStatement(ifstmt) => ifstmt.transform_value(context, input),
      ExprTransformer::FunctionCall(fcall) => fcall.transform_value(context, input),
      ExprTransformer::FunctionDef(fdef) => fdef.transform_value(context, input),
      ExprTransformer::OperatorExpr(oper_expr) => oper_expr.transform_value(context, input),
      ExprTransformer::VariableDef(variable_def) => variable_def.transform_value(context, input),
    }?;
    trace!("◀ ExprTransformer::transform_value; {:?} => {:?}", self, result);
    Ok(result)
  }
}
// change 1
impl FromPairs for ExprTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    trace!("▶ ExprTransformer::from_pairs; next = {:?}", pairs.peek().map(|p| p.as_rule()));
    if let Some(pair) = pairs.peek() {
      let rule=pair.as_rule();


      trace!("  branch = {:?}", rule);
      return match rule {
        Rule::IfStatement => {
          IfStatementTransformer::from_pairs(pairs).map(ExprTransformer::IfStatement)
        }
        Rule::FunctionCall => {
          FunctionCallTransformer::from_pairs(pairs).map(ExprTransformer::FunctionCall)
        }
        Rule::FunctionDef => {
          FunctionDefTransformer::from_pairs(pairs).map(ExprTransformer::FunctionDef)
        }
        Rule::OperatorExpr => {
          OperatorExprTransformer::from_pairs(pairs).map(ExprTransformer::OperatorExpr)
        }
        Rule::VariableDef => {
          VariableDefTransformer::from_pairs(pairs).map(ExprTransformer::VariableDef)
        }
        _ => ValueTransformer::from_pairs(pairs).map(ExprTransformer::Value),
      };
    }

    Err(JsltError::UnexpectedEnd)
  }
}

impl format::Display for ExprTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    match self {
      ExprTransformer::Value(val) => format::Display::fmt(val, f),
      ExprTransformer::IfStatement(ifstmt) => format::Display::fmt(ifstmt, f),
      ExprTransformer::FunctionCall(fcall) => format::Display::fmt(fcall, f),
      ExprTransformer::FunctionDef(fdef) => format::Display::fmt(fdef, f),
      ExprTransformer::OperatorExpr(oper_expr) => format::Display::fmt(oper_expr, f),
      ExprTransformer::VariableDef(variable_def) => format::Display::fmt(variable_def, f),
    }
  }
}

#[derive(Debug)]
pub enum OperatorTransformer {
  Add,
  Sub,
  Div,
  Mul,
  And,
  Or,
  Gt,
  Gte,
  Lt,
  Lte,
  Equal,
  NotEqual,
}

impl fmt::Display for OperatorTransformer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      OperatorTransformer::Add => f.write_char('+'),
      OperatorTransformer::Sub => f.write_char('-'),
      OperatorTransformer::Div => f.write_char('/'),
      OperatorTransformer::Mul => f.write_char('*'),
      OperatorTransformer::And => f.write_str("and"),
      OperatorTransformer::Or => f.write_str("or"),
      OperatorTransformer::Gt => f.write_str(">"),
      OperatorTransformer::Gte => f.write_str(">="),
      OperatorTransformer::Lt => f.write_str("<"),
      OperatorTransformer::Lte => f.write_str("<="),
      OperatorTransformer::Equal => f.write_str("=="),
      OperatorTransformer::NotEqual => f.write_str("!="),
    }
  }
}

#[derive(Debug)]
pub struct OperatorExprTransformer {
  lhs: Box<ExprTransformer>,
  operator: OperatorTransformer,
  rhs: Box<ExprTransformer>,
}

macro_rules! impl_operator_parse {
  ($ident:ident, $op:ident) => {
    if let Some((index, _)) = $ident
      .iter()
      .enumerate()
      .find(|(_, pair)| matches!(pair.as_rule(), Rule::$op))
    {
      let mut right = $ident.split_off(index).split_off(1);

      let lhs = if $ident.len() == 1 {
        Box::new(ExprTransformer::from_pairs(&mut Pairs::single(
          $ident.pop().expect("Should have at least one value"),
        ))?)
      } else {
        Box::new(ExprTransformer::OperatorExpr(
          OperatorExprTransformer::from_inner_vec($ident)?,
        ))
      };

      let rhs = if right.len() == 1 {
        Box::new(ExprTransformer::from_pairs(&mut Pairs::single(
          right.pop().expect("Should have at least one value"),
        ))?)
      } else {
        Box::new(ExprTransformer::OperatorExpr(
          OperatorExprTransformer::from_inner_vec(right)?,
        ))
      };

      return Ok(OperatorExprTransformer {
        lhs,
        rhs,
        operator: OperatorTransformer::$op,
      });
    }
  };
}

impl OperatorExprTransformer {
  pub fn from_inner_vec(mut pairs: Vec<Pair<Rule>>) -> Result<Self> {
    impl_operator_parse!(pairs, And);
    impl_operator_parse!(pairs, Or);
    impl_operator_parse!(pairs, Gt);
    impl_operator_parse!(pairs, Gte);
    impl_operator_parse!(pairs, Lt);
    impl_operator_parse!(pairs, Lte);
    impl_operator_parse!(pairs, Equal);
    impl_operator_parse!(pairs, NotEqual);
    impl_operator_parse!(pairs, Add);
    impl_operator_parse!(pairs, Sub);
    impl_operator_parse!(pairs, Mul);
    impl_operator_parse!(pairs, Div);

    Err(JsltError::InvalidInput(format!(
      "Could not evaluate the expession {pairs:#?}",
    )))
  }
}

impl FromPairs for OperatorExprTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let pairs = expect_inner!(pairs, Rule::OperatorExpr)?;

    Self::from_inner_vec(pairs.collect())
  }
}
// change
impl Transform for OperatorExprTransformer {
  fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
    trace!("▶ OperatorExpr {:?} on {:?}", self.operator, input);
    let left = self
      .lhs
      .transform_value(Context::Borrowed(&context), input)?;
    let right = self.rhs.transform_value(context, input)?;

    let result=match self.operator {
      OperatorTransformer::Add => match (&left, &right) {
        (Value::Array(left), Value::Array(right)) => Ok(Value::Array(
          left.clone().into_iter().chain(right.clone()).collect(),
        )),
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Number(
            (left.as_u64().expect("Should be u64") + right.as_u64().expect("Should be u64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Number(
            (left.as_i64().expect("Should be i64") + right.as_i64().expect("Should be i64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(
          (left.as_f64().expect("Should be f64") + right.as_f64().expect("Should be f64")).into(),
        ),
        (Value::String(left), Value::String(right)) => Ok(Value::String(format!("{left}{right}"))),
        (Value::Object(left), Value::Object(right)) => Ok(Value::Object(
          left
            .into_iter()
            .chain(right)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
        )),
        _ => Err(JsltError::InvalidInput(format!(
          "Add (\"+\") operator invalid input (got \"{left} + {right}\")"
        ))),
      },
      OperatorTransformer::Sub => match (&left, &right) {
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Number(
            (left.as_u64().expect("Should be u64") - right.as_u64().expect("Should be u64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Number(
            (left.as_i64().expect("Should be i64") - right.as_i64().expect("Should be i64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(
          (left.as_f64().expect("Should be f64") - right.as_f64().expect("Should be f64")).into(),
        ),
        _ => Err(JsltError::InvalidInput(format!(
          "Sub (\"-\") operator must be 2 numbers (got \"{left} - {right}\")"
        ))),
      },
      OperatorTransformer::Mul => match (&left, &right) {
        (Value::String(left), Value::Number(right)) if right.is_u64() => Ok(Value::String(
          std::iter::from_fn(|| Some(left.clone()))
            .take(right.as_u64().expect("Should be u64") as usize)
            .collect(),
        )),
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Number(
            (left.as_u64().expect("Should be u64") * right.as_u64().expect("Should be u64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Number(
            (left.as_i64().expect("Should be i64") * right.as_i64().expect("Should be i64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(
          (left.as_f64().expect("Should be f64") * right.as_f64().expect("Should be f64")).into(),
        ),
        _ => Err(JsltError::InvalidInput(format!(
          "Mul (\"*\") operator must be 2 numbers (got \"{left} * {right}\")"
        ))),
      },
      OperatorTransformer::Div => match (&left, &right) {
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Number(
            (left.as_u64().expect("Should be u64") / right.as_u64().expect("Should be u64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Number(
            (left.as_i64().expect("Should be i64") / right.as_i64().expect("Should be i64")).into(),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(
          (left.as_f64().expect("Should be f64") / right.as_f64().expect("Should be f64")).into(),
        ),
        _ => Err(JsltError::InvalidInput(format!(
          "Div (\"/\") operator must be 2 numbers (got \"{left} / {right}\")"
        ))),
      },
      OperatorTransformer::And => match (&left, &right) {
        (Value::Bool(true), Value::Bool(true)) => Ok(Value::Bool(true)),
        (Value::Bool(_) | Value::Null, Value::Bool(_) | Value::Null) => Ok(Value::Bool(false)),
        _ => Err(JsltError::InvalidInput(format!(
          "And (\"and\") operator must be 2 booleans (got \"{left} and {right}\")"
        ))),
      },
      OperatorTransformer::Or => match (&left, &right) {
        (Value::Bool(_) | Value::Null, Value::Bool(true))
        | (Value::Bool(true), Value::Bool(_) | Value::Null) => Ok(Value::Bool(true)),
        (Value::Bool(_) | Value::Null, Value::Bool(_) | Value::Null) => Ok(Value::Bool(false)),
        _ => Err(JsltError::InvalidInput(format!(
          "Or (\"/\") operator must be 2 booleans (got \"{left} or {right}\")"
        ))),
      },
      OperatorTransformer::Gt => match (&left, &right) {
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Bool(
            left.as_u64().expect("Should be u64") > right.as_u64().expect("Should be u64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Bool(
            left.as_i64().expect("Should be i64") > right.as_i64().expect("Should be i64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(Value::Bool(
          left.as_f64().expect("Should be f64") > right.as_f64().expect("Should be f64"),
        )),
        (Value::String(left), Value::String(right)) => Ok(Value::Bool(left > right)),
        _ => Err(JsltError::InvalidInput(format!(
          "GreaterThan (\">\") operator must be 2 numbers or strings (got \"{left} > {right}\")"
        ))),
      },
      OperatorTransformer::Gte => match (&left, &right) {
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Bool(
            left.as_u64().expect("Should be u64") >= right.as_u64().expect("Should be u64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Bool(
            left.as_i64().expect("Should be i64") >= right.as_i64().expect("Should be i64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(Value::Bool(
          left.as_f64().expect("Should be f64") >= right.as_f64().expect("Should be f64"),
        )),
        (Value::String(left), Value::String(right)) => Ok(Value::Bool(left >= right)),
        _ => Err(JsltError::InvalidInput(format!(
          "GreaterThan (\">\") operator must be 2 numbers or strings (got \"{left} > {right}\")"
        ))),
      },
      OperatorTransformer::Lt => match (&left, &right) {
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Bool(
            left.as_u64().expect("Should be u64") < right.as_u64().expect("Should be u64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Bool(
            left.as_i64().expect("Should be i64") < right.as_i64().expect("Should be i64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(Value::Bool(
          left.as_f64().expect("Should be f64") < right.as_f64().expect("Should be f64"),
        )),
        (Value::String(left), Value::String(right)) => Ok(Value::Bool(left < right)),
        _ => Err(JsltError::InvalidInput(format!(
          "LessThanEquals (\"<=\") operator must be 2 numbers or strings (got \"{left} < {right}\")"
        ))),
      },
      OperatorTransformer::Lte => match (&left, &right) {
        (Value::Number(left), Value::Number(right)) if left.is_u64() && right.is_u64() => {
          Ok(Value::Bool(
            left.as_u64().expect("Should be u64") <= right.as_u64().expect("Should be u64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) if left.is_i64() && right.is_i64() => {
          Ok(Value::Bool(
            left.as_i64().expect("Should be i64") <= right.as_i64().expect("Should be i64"),
          ))
        }
        (Value::Number(left), Value::Number(right)) => Ok(Value::Bool(
          left.as_f64().expect("Should be f64") <= right.as_f64().expect("Should be f64"),
        )),
        (Value::String(left), Value::String(right)) => Ok(Value::Bool(left <= right)),
        _ => Err(JsltError::InvalidInput(format!(
          "LessThanEquals (\"<=\") operator must be 2 numbers or strings (got \"{left} < {right}\")"
        ))),
      },
      OperatorTransformer::Equal => Ok(Value::Bool(left == right)),
      OperatorTransformer::NotEqual => Ok(Value::Bool(left != right)),
    }?;
    trace!("◀ OperatorExpr {:?} => {:?}", self.operator, result);
    Ok(result)
  }
}

impl format::Display for OperatorExprTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let OperatorExprTransformer { lhs, operator, rhs } = self;

    format::Display::fmt(lhs.as_ref(), f)?;

    write!(f, " {operator} ")?;

    format::Display::fmt(rhs.as_ref(), f)
  }
}

#[derive(Debug)]
pub struct ForTransformer<B> {
  pub(super) source: Box<ExprTransformer>,

  pub(super) condition: Option<ExprTransformer>,

  pub(super) output: Box<B>,
}
// change
impl<B> FromPairs for ForTransformer<B>
where
  B: FromPairs,
{
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    trace!("▶ ForTransformer::from_pairs; pairs = {:?}", pairs.peek());
    let source = ExprTransformer::from_pairs(pairs)?;

    let output = B::from_pairs(pairs)?;

    let condition = match pairs.peek() {
      Some(pair) if matches!(pair.as_rule(), Rule::IfCondition) => {
        Some(ExprTransformer::from_pairs(&mut pair.into_inner())?)
      }
      _ => None,
    };
    trace!("◀ ForTransformer::from_pairs; source={:?}, has_condition={}", source, condition.is_some());

    Ok(ForTransformer {
      source: Box::new(source),
      condition,
      output: Box::new(output),
    })
  }
}

// MAJOR CHANGE

// impl<B> Transform for ForTransformer<B>
// where
//     B: Transform,
// {
//     fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
//         trace!("▶ ForTransformer::transform_value; input = {:?}", input);

//         // 1️⃣ Evaluate the source expression
//         let src_val = self
//             .source
//             .transform_value(Context::Borrowed(&context), input)?;
//         trace!("  source produced = {:?}", src_val);

//         // 2️⃣ Iterate over the array (empty if not an array)
//         let mut results = Vec::new();
//         for item in src_val.as_array().unwrap_or(&Vec::new()) {
//             trace!("  iteration with item = {:?}", item);

//             // 3️⃣ Optional `if` condition
//             if let Some(cond) = &self.condition {
//                 let cond_val = cond.transform_value(Context::Borrowed(&context), item)?;
//                 trace!("    condition → {:?}", cond_val);
//                 if !builtins::boolean_cast(&cond_val) {
//                     trace!("    condition is false; skipping");
//                     continue;
//                 }
//             }

//             // 4️⃣ Evaluate the loop body
//             let out = self.output.transform_value(context.clone(), item)?;
//             trace!("    body output → {:?}", out);
//             results.push(out);
//         }

//         // 5️⃣ Done
//         trace!("◀ ForTransformer::transform_value ⇒ {:?}", results);
//         Ok(Value::Array(results))
//     }
// }


impl<B> Transform for ForTransformer<B> 

where 

    B: Transform, 

{ 

    fn transform_value(&self, mut context: Context<'_>, input: &Value) -> Result<Value> { 

        trace!("▶ ForTransformer::transform_value; input = {:?}", input); 

 

        // Evaluate the source expression 

        let src_val = self.source.transform_value(Context::Borrowed(&context), input)?; 

        trace!("  source produced = {:?}", src_val); 

 

        let mut results = Vec::new(); 

        for item in src_val.as_array().unwrap_or(&Vec::new()) { 

            trace!("  iteration with item = {:?}", item); 

 

            // Create a NEW SCOPE for each iteration 

            let mut iteration_ctx =  context.to_mut().new_scope(); 

 

            // Optional condition check 

            if let Some(cond) = &self.condition { 

                let cond_val = cond.transform_value(Context::Borrowed(&iteration_ctx), item)?; 

                trace!("    condition → {:?}", cond_val); 

                if !builtins::boolean_cast(&cond_val) { 

                    trace!("    condition is false; skipping"); 

                    continue; 

                } 

            } 

 

            // Evaluate the loop body in the new scope 

            let out = self.output.transform_value(Cow::Owned(iteration_ctx), item)?; 

            trace!("    body output → {:?}", out); 

            results.push(out); 

        } 

 

        trace!("◀ ForTransformer::transform_value ⇒ {:?}", results); 

        Ok(Value::Array(results)) 

    } 

} 


impl<B> format::Display for ForTransformer<B>
where
  B: format::Display,
{
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let ForTransformer {
      source,
      condition,
      output,
    } = self;

    f.write_str("for (")?;
    format::Display::fmt(source.as_ref(), f)?;
    f.write_str(")\n")?;

    let mut slot = None;
    let mut state = Default::default();

    let mut writer = format::PadAdapter::wrap(f, &mut slot, &mut state);
    format::Display::fmt(output.as_ref(), &mut writer)?;

    if let Some(condition) = condition {
      writer.write_str("\n  if (")?;
      format::Display::fmt(condition, &mut writer)?;
      writer.write_char(')')?;
    }

    Ok(())
  }
}





#[derive(Debug)]
pub struct IfStatementTransformer {
  condition: Box<ExprTransformer>,
  value: Box<ExprTransformer>,
  fallback: Option<Box<ExprTransformer>>,
}

impl FromPairs for IfStatementTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let mut pairs = expect_inner!(pairs, Rule::IfStatement)?;

    let mut condition_paris = expect_inner!(pairs, Rule::IfCondition)?;

    let condition = ExprTransformer::from_pairs(&mut condition_paris).map(Box::new)?;

    let value = ExprTransformer::from_pairs(&mut pairs).map(Box::new)?;

    let fallback = (pairs.len() != 0)
      .then(|| ExprTransformer::from_pairs(&mut pairs).map(Box::new))
      .transpose()?;

    Ok(IfStatementTransformer {
      condition,
      value,
      fallback,
    })
  }
}

impl Transform for IfStatementTransformer {
  fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
    if builtins::boolean_cast(
      &self
        .condition
        .transform_value(Context::Borrowed(&context), input)?,
    ) {
      self.value.transform_value(context, input)
    } else {
      self
        .fallback
        .as_ref()
        .map(|fallback| fallback.transform_value(context, input))
        .unwrap_or_else(|| Ok(Value::Null))
    }
  }
}

impl format::Display for IfStatementTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let IfStatementTransformer {
      condition,
      value,
      fallback,
    } = self;

    f.write_str("if (")?;
    format::Display::fmt(condition.as_ref(), f)?;
    f.write_str(")\n")?;

    let mut slot = None;
    let mut state = Default::default();

    let mut writer = format::PadAdapter::wrap(f, &mut slot, &mut state);

    format::Display::fmt(value.as_ref(), &mut writer)?;

    if let Some(fallback) = fallback {
      f.write_str("\nelse\n")?;

      let mut slot = None;
      let mut state = Default::default();

      let mut writer = format::PadAdapter::wrap(f, &mut slot, &mut state);

      format::Display::fmt(fallback.as_ref(), &mut writer)?;
    }

    Ok(())
  }
}

#[derive(Debug)]
pub struct FunctionCallTransformer {
  name: String,
  arguments: Vec<ExprTransformer>,
  accessor: Option<AccessorTransformer>,
}

impl FromPairs for FunctionCallTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let mut pairs = expect_inner!(pairs, Rule::FunctionCall)?;

    let name = pairs
      .next()
      .ok_or(JsltError::UnexpectedEnd)?
      .as_str()
      .to_owned();

    let arguments = pairs
      .next()
      .ok_or(JsltError::UnexpectedEnd)?
      .into_inner()
      .map(|pair| ExprTransformer::from_pairs(&mut Pairs::single(pair)))
      .collect::<Result<_, _>>()?;

    let accessor = pairs
      .next()
      .map(|pair| AccessorTransformer::from_pairs(&mut Pairs::single(pair)))
      .transpose()?;

    Ok(FunctionCallTransformer {
      name,
      arguments,
      accessor,
    })
  }
}

impl Transform for FunctionCallTransformer {
  fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
    trace!("▶ FunctionCall `{}` args = {:?}", self.name, self.arguments);
    let function = context
      .functions
      .get(&self.name)
      .ok_or_else(|| JsltError::RuntimeError(format!("Unknown Functuion: {}", self.name)))?
      .clone();

    let result = function.call(
      Context::Borrowed(&context),
      input,
      &self
        .arguments
        .iter()
        .map(|arg| arg.transform_value(Context::Borrowed(&context), input))
        .collect::<Result<Vec<_>>>()?,
    )?;
    trace!("  `{}` returned = {:?}", self.name, result);

    let finall =match self.accessor.as_ref() {
      Some(accessor) => accessor.transform_value(Context::Borrowed(&context), &result),
      None => Ok(result),
    }?;
    trace!("◀ FunctionCall `{}` final = {:?}", self.name, finall);
    Ok(finall)

  }
}

impl format::Display for FunctionCallTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let FunctionCallTransformer {
      name,
      arguments,
      accessor,
    } = self;

    write!(f, "{name}(")?;

    if !arguments.is_empty() {
      let last_argument_index = arguments.len() - 1;

      for (index, item) in arguments.iter().enumerate() {
        format::Display::fmt(item, f)?;

        if index != last_argument_index {
          f.write_str(", ")?;
        }
      }
    }

    f.write_char(')')?;

    if let Some(accessor) = accessor {
      format::Display::fmt(accessor, f)?;
    }

    Ok(())
  }
}

#[derive(Debug)]
pub struct FunctionDefTransformer {
  name: String,
  arguments: Vec<String>,
  expr: Arc<ExprTransformer>,
  next: Box<ExprTransformer>,
}

impl FromPairs for FunctionDefTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let mut pairs = expect_inner!(pairs, Rule::FunctionDef)?;

    let name = pairs
      .next()
      .ok_or(JsltError::UnexpectedEnd)?
      .as_str()
      .to_owned();

    let mut arguments = Vec::new();

    while pairs
      .peek()
      .map(|pair| matches!(pair.as_rule(), Rule::Ident))
      .unwrap_or(false)
    {
      arguments.push(pairs.next().expect("was peeked").as_str().to_owned());
    }

    let expr = ExprTransformer::from_pairs(&mut pairs).map(Arc::new)?;

    let next = ExprTransformer::from_pairs(&mut pairs).map(Box::new)?;

    Ok(FunctionDefTransformer {
      name,
      arguments,
      expr,
      next,
    })
  }
}

impl Transform for FunctionDefTransformer {
  fn transform_value(&self, mut context: Context<'_>, input: &Value) -> Result<Value> {
    trace!("▶ FunctionDef register `{}`", self.name);
    let function = DynamicFunction {
      name: self.name.clone(),
      arguments: self.arguments.clone(),
      expr: self.expr.clone(),
    };
    trace!("  FunctionDef `{}` registered", self.name);
    context
    .to_mut()
    .functions
    .insert(self.name.clone(), JsltFunction::Dynamic(function));

    let out=self.next.transform_value(context, input)?;
    Ok(out)
  }
}

impl format::Display for FunctionDefTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let FunctionDefTransformer {
      name,
      arguments,
      expr,
      next,
    } = self;

    writeln!(f, "def {name}({})", arguments.join(", "))?;

    let mut slot = None;
    let mut state = Default::default();

    let mut writer = format::PadAdapter::wrap(f, &mut slot, &mut state);
    format::Display::fmt(expr.as_ref(), &mut writer)?;

    f.write_str("\n\n")?;

    format::Display::fmt(next.as_ref(), f)
  }
}

#[derive(Debug)]
pub struct VariableDefTransformer {
  name: String,
  value: Box<ExprTransformer>,
  next: Box<ExprTransformer>,
}

impl FromPairs for VariableDefTransformer {
  fn from_pairs(pairs: &mut Pairs<Rule>) -> Result<Self> {
    let mut pairs = expect_inner!(pairs, Rule::VariableDef)?;

    let name = pairs
      .next()
      .ok_or(JsltError::UnexpectedEnd)?
      .as_str()
      .to_owned();

    let value = ExprTransformer::from_pairs(&mut pairs).map(Box::new)?;
    let next = ExprTransformer::from_pairs(&mut pairs).map(Box::new)?;

    Ok(VariableDefTransformer { name, value, next })
  }
}



// impl Transform for VariableDefTransformer {
//     fn transform_value(&self, context: Context<'_>, input: &Value) -> Result<Value> {
//         // shadow context as mutable so we can call to_mut()
//         let mut context = context;

//         let name = self.name.clone();
//         trace!("▶ VariableDef set `{}`", name);

//         // evaluate the initializer
//         let value = self
//             .value
//             .transform_value(Context::Borrowed(&context), input)?;
//         trace!("  `{}` = {:?}", name, value);

//         // bind into the mutable context
//         context.to_mut().variables.insert(name.clone(), value.clone());

//         // now evaluate the rest of the pipeline
//         let out: Value = self.next.transform_value(context, input)?;
//         trace!("◀ VariableDef `{}` → {:?}", name, out);

//         Ok(out)
//     }
// }



impl Transform for VariableDefTransformer { 

    fn transform_value(&self, mut context: Context<'_>, input: &Value) -> Result<Value> { 

        trace!("▶ VariableDef set `{}`", self.name); 

         

        // Evaluate the value first 

        let value = self.value.transform_value(Context::Borrowed(&context), input)?; 

        trace!("  `{}` = {:?}", self.name, value); 

         

        // Set in LOCAL scope instead of global 

        context.to_mut().set_local(self.name.clone(), value); 

         

        // Transform the next expression with updated context 

        let result = self.next.transform_value(context, input)?; 

        trace!("◀ VariableDef `{}` → {:?}", self.name, result); 

        Ok(result) 

    } 

} 



impl format::Display for VariableDefTransformer {
  fn fmt(&self, f: &mut format::Formatter<'_>) -> fmt::Result {
    let VariableDefTransformer { name, value, next } = self;

    write!(f, "let {name} = ")?;
    format::Display::fmt(value.as_ref(), f)?;
    f.write_str("\n\n")?;

    format::Display::fmt(next.as_ref(), f)
  }
}
