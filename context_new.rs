use std::{borrow::Cow, collections::HashMap, fmt, sync::Arc};

use serde_json::Value;

use crate::{
  error::Result,
  transform::{Transform, expr::ExprTransformer},
};
use crate::trace;
pub(crate) mod builtins;

#[derive(Clone)]
pub enum JsltFunction {
  Static(&'static (dyn Fn(&[Value]) -> Result<Value> + Send + Sync)),
  Dynamic(DynamicFunction),
}

impl JsltFunction {
  pub fn call(&self, context: Context<'_>, input: &Value, arguments: &[Value]) -> Result<Value> {
    trace!("▶ JsltFunction::call; variant = {:?}, args = {:?}", self, arguments);
    let res=match self {
      JsltFunction::Static(function) =>{
        trace!("  invoking Static builtin");
        function(arguments)
      }
        
      JsltFunction::Dynamic(function) => 
      { 
        trace!("  invoking DynamicFunction `{}`", function.name);
        function.call(context, input, arguments)
      }
    }?;
    trace!("◀ JsltFunction::call ⇒ {:?}", res);
    Ok(res)
  }
}

impl fmt::Debug for JsltFunction {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      JsltFunction::Static(_) => fmt.debug_tuple("Static").finish(),
      JsltFunction::Dynamic(function) => fmt.debug_tuple("Dynamic").field(&function).finish(),
    }
  }
}

#[derive(Debug, Clone)]
pub struct DynamicFunction {
  pub name: String,
  pub arguments: Vec<String>,
  pub expr: Arc<ExprTransformer>,
}

impl DynamicFunction {
  pub fn call(
    &self,
    mut context: Context<'_>,
    input: &Value,
    arguments: &[Value],
  ) -> Result<Value> {
    trace!("▶ DynamicFunction::call `{}`; raw args = {:?}", self.name, arguments);

    // change
    let mut new_ctx = context.to_mut().new_scope(); 
    for (name, value) in self.arguments.iter().zip(arguments) { 

        new_ctx.set_local(name.clone(), value.clone()); 

    } 



    // let arguments = self
    //   .arguments
    //   .iter()
    //   .zip(arguments)
    //   .map(|(name, value)| (name.clone(), value.clone()));

    trace!("  binding args = {:?}", arguments);

    // context.to_mut().variables.extend(arguments);

    let result = self.expr.transform_value(Cow::Owned(new_ctx), input)?; 


    trace!("◀ DynamicFunction::call `{}` ⇒ {:?}", self.name, result);
    Ok(result)

  }
}

macro_rules! include_builtin {
  ($functions:ident, $ident:ident, $name:expr) => {
    $functions.insert($name.to_owned(), JsltFunction::Static(&builtins::$ident))
  };
  ($functions:ident, $ident:ident) => {
    include_builtin!($functions, $ident, stringify!($ident))
  };
}

#[derive(Clone, Debug)]
pub struct JsltContext {
  pub functions: HashMap<String, JsltFunction>,
  pub variables: HashMap<String, Value>,

  pub local_variables: HashMap<String, Value>,
}


impl JsltContext { 

    // Add these new methods: 

     

    /// Creates a new context with fresh local variables 

    pub fn new_scope(&self) -> Self { 

        JsltContext { 

            functions: self.functions.clone(), 

            variables: self.variables.clone(), 

            local_variables: HashMap::new(),  // Fresh local scope 

        } 

    } 

 

    /// Sets a variable in the local scope 

    pub fn set_local(&mut self, name: String, value: Value) { 

        self.local_variables.insert(name, value); 

    } 

 

    /// Gets a variable, checking local scope first 

    pub fn get_var(&self, name: &str) -> Option<&Value> { 

        self.local_variables 

            .get(name) 

            .or_else(|| self.variables.get(name)) 

    } 

} 




impl Default for JsltContext {
  fn default() -> Self {
    trace!("▶ JsltContext::default: initializing context");
    let mut functions = HashMap::default();
    let variables = HashMap::default();
    let local_variables = HashMap::default();

    trace!("  before registering builtins: functions={}, variables={}", functions.len(), variables.len());

    include_builtin!(functions, contains);
    include_builtin!(functions, size);
    include_builtin!(functions, error);
    include_builtin!(functions, fallback);
    include_builtin!(functions, min);
    include_builtin!(functions, max);
    include_builtin!(functions, is_number, "is-number");
    include_builtin!(functions, is_integer, "is-integer");
    include_builtin!(functions, is_decimal, "is-decimal");
    include_builtin!(functions, number);
    include_builtin!(functions, round);
    include_builtin!(functions, floor);
    include_builtin!(functions, ceiling);
    include_builtin!(functions, random);
    include_builtin!(functions, sum);
    include_builtin!(functions, r#mod, "mod");
    include_builtin!(functions, hash_int, "hash-int");
    include_builtin!(functions, is_string, "is-string");
    include_builtin!(functions, string);
    include_builtin!(functions, test);
    include_builtin!(functions, capture);
    include_builtin!(functions, split);
    include_builtin!(functions, join);
    include_builtin!(functions, lowercase);
    include_builtin!(functions, uppercase);
    include_builtin!(functions, sha256_hex, "sha256-hex");
    include_builtin!(functions, starts_with, "starts-with");
    include_builtin!(functions, ends_with, "ends-with");
    include_builtin!(functions, from_json, "from-json");
    include_builtin!(functions, to_json, "to-json");
    include_builtin!(functions, replace);
    include_builtin!(functions, trim);
    include_builtin!(functions, uuid);
    include_builtin!(functions, boolean);
    include_builtin!(functions, not);
    include_builtin!(functions, is_boolean, "is-boolean");
    include_builtin!(functions, is_object, "is-object");
    include_builtin!(functions, get_key, "get-key");
    include_builtin!(functions, array);
    include_builtin!(functions, is_array, "is-array");
    include_builtin!(functions, flatten);
    include_builtin!(functions, all);
    include_builtin!(functions, any);
    include_builtin!(functions, zip);
    include_builtin!(functions, zip_with_index, "zip-with-index");
    include_builtin!(functions, index_of, "index-of");
    include_builtin!(functions, now);
    include_builtin!(functions, parse_time, "parse-time");
    include_builtin!(functions, format_time, "format-time");
    include_builtin!(functions, parse_url, "parse-url");
    trace!("  registered builtins: {}", functions.len());

    let ctx=JsltContext {
      functions,
      variables,
      local_variables,
    };
    trace!("◀ JsltContext::default ⇒ {:?}", ctx);
    ctx
  }
}

pub type Context<'s> = Cow<'s, JsltContext>;
