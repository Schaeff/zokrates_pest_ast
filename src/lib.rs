use pest::error::Error;
use pest::iterators::Pairs;
use zokrates_core::absy::*;
use zokrates_core::parser::Position;
use zokrates_core::types::Signature;
use zokrates_field::field::FieldPrime;
use zokrates_pest::parse;
use zokrates_pest::Rule;

struct FieldPrimeProg(Prog<FieldPrime>);

impl<'a> From<Pairs<'a, Rule>> for FieldPrimeProg {
    fn from(pairs: Pairs<'a, Rule>) -> FieldPrimeProg {
        FieldPrimeProg(Prog {
            functions: vec![],
            imports: vec![],
            imported_functions: vec![],
        })
    }
}

fn generate_ast(input: &str) -> Result<Prog<FieldPrime>, Error<Rule>> {
    let parse_tree = parse(input)?;
    Ok(FieldPrimeProg::from(parse_tree).0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_program() {
        assert_eq!(
            generate_ast(&"def main() -> (field): return 1"),
            Ok(Prog {
                functions: vec![Node::new(
                    Position { line: 42, col: 33 },
                    Position { line: 42, col: 33 },
                    Function {
                        id: String::from("main"),
                        /// Arguments of the function
                        arguments: vec![],
                        /// Vector of statements that are executed when running the function
                        statements: vec![],
                        /// function signature
                        signature: Signature::new().inputs(vec![]).outputs(vec![]),
                    }
                )],
                imports: vec![],
                imported_functions: vec![],
            })
        );
    }
}
