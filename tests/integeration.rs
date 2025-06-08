// tests/integeration.rs

use std::{fs, path::Path, panic};
use jslt::{Jslt};
use jslt::context::JsltContext;
use serde_json::{Value, Map};
use serde_yaml;

/// One test-case as it appears in the fixture files
#[derive(serde::Deserialize)]
struct Case {
    query:     String,
    input:     Option<Value>,              // default {}
    output:    Option<Value>,              // if present, this is the expected
    error:     Option<String>,             // if present, we expect this substring in the error
    variables: Option<Map<String, Value>>, // external vars, if any
}

/// Load all cases from one JSON or YAML fixture file
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

#[test]
fn jslt_print_outputs() {
    let fixtures_dir = Path::new("tests/fixtures");
    assert!(
        fixtures_dir.exists(),
        "Put your *.json / *.yaml files in tests/fixtures/"
    );

    // Only run query-tests.yaml for now:
    let target_file = "query-tests.yaml";

    for entry in fs::read_dir(fixtures_dir).unwrap() {
        let path = entry.unwrap().path();
        if path.file_name().unwrap() != target_file {
            continue;
        }

        let cases = load(&path);
        println!("\n=== Running {} cases from {} ===", cases.len(), target_file);

        for (idx, case) in cases.into_iter().enumerate() {
            println!("\n--- case [{}] ---", idx);
            println!("Query: {}", case.query);

            let input = case.input.unwrap_or_else(|| serde_json::json!({}));
            println!(
                "Input: {}",
                serde_json::to_string_pretty(&input).unwrap()
            );

            // build context
            let mut ctx = JsltContext::default();
            if let Some(vars) = case.variables {
                ctx.variables.extend(vars);
            }

            // parse & run inside catch_unwind
            let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                // parse
                match case.query.parse::<Jslt>() {
                    Ok(tpl) => {
                        // run
                        match tpl.transform_value(&input) {
                            Ok(got) => Output::Value(got),
                            Err(err) => Output::Error(err.to_string()),
                        }
                    }
                    Err(parse_err) => Output::ParseError(parse_err.to_string()),
                }
            }));

            match result {
                Ok(Output::Value(v)) => {
                    println!(
                        "Output: {}",
                        serde_json::to_string_pretty(&v).unwrap()
                    );
                }
                Ok(Output::Error(err)) => {
                    println!("Error: {}", err);
                }
                Ok(Output::ParseError(pe)) => {
                    println!("Parse error: {}", pe);
                }
                Err(_) => {
                    println!("*** PANIC during evaluation ***");
                }
            }

            // print expected, if any
            if let Some(exp) = case.output {
                println!(
                    "Expected: {}",
                    serde_json::to_string_pretty(&exp).unwrap()
                );
            } else if let Some(err_substr) = case.error {
                println!("Expected error containing: {:?}", err_substr);
            }
        }
    }
}

enum Output {
    Value(Value),
    Error(String),
    ParseError(String),
}
