// tests/print_query.rs

use std::{fs, path::Path, panic};
use jslt::Jslt;
use jslt::context::JsltContext;
use serde_json::{Value, Map};
use serde_yaml;

/// One test‐case as it appears in the fixture file
#[derive(serde::Deserialize)]
struct Case {
    query:     String,
    input:     Option<Value>,               // default {}
    output:    Option<Value>,               // expected result
    error:     Option<String>,              // expected error substring
    variables: Option<Map<String, Value>>,  // external vars, if any
}

/// Load all cases from a JSON or YAML fixture file
fn load(path: &Path) -> Vec<Case> {
    let txt = fs::read_to_string(path).unwrap();
    if path.extension().and_then(|e| e.to_str()) == Some("yaml") {
        let root: serde_yaml::Value = serde_yaml::from_str(&txt).unwrap();
        root["tests"]
            .as_sequence().unwrap()
            .iter()
            .map(|n| serde_yaml::from_value(n.clone()).unwrap())
            .collect()
    } else {
        let root: serde_json::Value = serde_json::from_str(&txt).unwrap();
        root["tests"]
            .as_array().unwrap()
            .iter()
            .map(|n| serde_json::from_value(n.clone()).unwrap())
            .collect()
    }
}

/// Catch panics and return either a Value, an Error, a ParseError, or Panic
enum Outcome {
    Value(Value),
    Error(String),
    ParseError(String),
    Panic,
}

#[test]
fn print_query_outputs() {
    let fixtures_dir = Path::new("tests/fixtures");
    assert!(
        fixtures_dir.exists(),
        "Put your query-tests.yaml or query-tests.json in tests/fixtures/"
    );

    // We will look for either of these two files:
    let targets = [ "query-tests.yaml"];
    let mut found_any = false;

    for &target in &targets {
        let path = fixtures_dir.join(target);
        if !path.exists() {
            continue;
        }
        found_any = true;

        let cases = load(&path);
        println!("\n=== {} cases from {} ===", cases.len(), target);

        for (i, case) in cases.into_iter().enumerate() {
            println!("\n--- case [{}] ---", i);
            println!("Query: {}", case.query);

            let input = case.input.unwrap_or_else(|| serde_json::json!({}));
            println!(
                "Input:\n{}",
                serde_json::to_string_pretty(&input).unwrap()
            );

            // build context
            let mut ctx = JsltContext::default();
            if let Some(vars) = case.variables {
                ctx.variables.extend(vars);
            }

            // run inside catch_unwind to never abort on panic
            let outcome = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                match case.query.parse::<Jslt>() {
                    Ok(tpl) => {
                        let actual_input=match &input {
                            Value::String(s)=> serde_json::from_str::<Value>(s)
                            .unwrap_or_else(|_| input.clone()),
                            _=> input.clone(),
                            
                        };
                        match tpl.transform_value(&actual_input) {
                        Ok(v)  => Outcome::Value(v),
                        Err(e) => Outcome::Error(e.to_string()),
                    }
                    },
                    Err(pe) => Outcome::ParseError(pe.to_string()),
                }
            }))
            .unwrap_or(Outcome::Panic);

            // print what happened
            match outcome {
                Outcome::Value(v) => {
                    println!(
                        "Output:\n{}",
                        serde_json::to_string_pretty(&v).unwrap()
                    );
                }
                Outcome::Error(e) => {
                    println!("Error: {}", e);
                }
                Outcome::ParseError(pe) => {
                    println!("Parse error: {}", pe);
                }
                Outcome::Panic => {
                    println!("*** PANIC during evaluation ***");
                }
            }

            // show expected
            if let Some(exp) = case.output {
                println!(
                    "Expected:\n{}",
                    serde_json::to_string_pretty(&exp).unwrap()
                );
            } else if let Some(err_substr) = case.error {
                println!("Expected error containing: {:?}", err_substr);
            }
        }
    }

    assert!(
        found_any,
        "No query-tests.yaml or query-tests.json found under tests/fixtures/"
    );    // and never fail
    assert!(true);
}

