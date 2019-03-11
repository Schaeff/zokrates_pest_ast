use from_pest::FromPest;
use pest::error::Error;
use pest::iterators::Pairs;
// use zokrates_core::absy::*;
// use zokrates_core::parser::Position;
// use zokrates_core::types::Signature;
// use zokrates_field::field::FieldPrime;
use zokrates_pest::parse;
use zokrates_pest::Rule;
#[macro_use]
extern crate lazy_static;

mod ast {
    use from_pest::ConversionError;
    use from_pest::FromPest;
    use from_pest::Void;
    use pest::iterators::{Pair, Pairs};
    use pest::prec_climber::{Assoc, Operator, PrecClimber};
    use pest::Span;
    use pest_ast::FromPest;
    use zokrates_pest::Rule;

    lazy_static! {
        static ref PREC_CLIMBER: PrecClimber<Rule> = build_precedence_climber();
    }

    fn build_precedence_climber() -> PrecClimber<Rule> {
        PrecClimber::new(vec![
            Operator::new(Rule::op_inclusive_or, Assoc::Left),
            Operator::new(Rule::op_exclusive_or, Assoc::Left),
            Operator::new(Rule::op_and, Assoc::Left),
            Operator::new(Rule::op_equal, Assoc::Left)
                | Operator::new(Rule::op_not_equal, Assoc::Left),
            Operator::new(Rule::op_lte, Assoc::Left)
                | Operator::new(Rule::op_gte, Assoc::Left)
                | Operator::new(Rule::op_lt, Assoc::Left)
                | Operator::new(Rule::op_gt, Assoc::Left),
            Operator::new(Rule::op_add, Assoc::Left) | Operator::new(Rule::op_sub, Assoc::Left),
            Operator::new(Rule::op_mul, Assoc::Left) | Operator::new(Rule::op_div, Assoc::Left),
            Operator::new(Rule::op_pow, Assoc::Left),
        ])
    }

    // this is only defined when `pair` is an operator
    fn infix_rule<'ast>(lhs: Box<Expression<'ast>>, pair: Pair<'ast, Rule>, rhs: Box<Expression<'ast>>) -> Box<Expression<'ast>> {
    	let (start, _) = lhs.span().split();
    	let (_, end) = rhs.span().split();
    	let span = start.span(&end);
        match pair.as_rule() {
            Rule::op_add => Box::new(Expression::binary(BinaryOperator::Add, lhs, rhs, span)),
            Rule::op_sub => Box::new(Expression::binary(BinaryOperator::Sub, lhs, rhs, span)),
            Rule::op_mul => Box::new(Expression::binary(BinaryOperator::Mul, lhs, rhs, span)),
            Rule::op_div => Box::new(Expression::binary(BinaryOperator::Div, lhs, rhs, span)),
            Rule::op_pow => Box::new(Expression::binary(BinaryOperator::Pow, lhs, rhs, span)),
            Rule::op_equal => Box::new(Expression::binary(BinaryOperator::Eq, lhs, rhs, span)),
            Rule::op_not_equal => Box::new(Expression::binary(BinaryOperator::NotEq, lhs, rhs, span)),
            Rule::op_lte => Box::new(Expression::binary(BinaryOperator::Lte, lhs, rhs, span)),
            Rule::op_lt => Box::new(Expression::binary(BinaryOperator::Lt, lhs, rhs, span)),
            Rule::op_gte => Box::new(Expression::binary(BinaryOperator::Gte, lhs, rhs, span)),
            Rule::op_gt => Box::new(Expression::binary(BinaryOperator::Gt, lhs, rhs, span)),
            Rule::op_inclusive_or => Box::new(Expression::binary(BinaryOperator::Or, lhs, rhs, span)),
            Rule::op_exclusive_or => Box::new(Expression::binary(BinaryOperator::Xor, lhs, rhs, span)),
            _ => unimplemented!(),
        }
    }

    pub fn climb(pair: Pair<Rule>) -> Box<Expression> {
        PREC_CLIMBER.climb(pair.into_inner(), build_factor, infix_rule)
    }

    fn build_factor(pair: Pair<Rule>) -> Box<Expression> {
        match pair.as_rule() {
            Rule::constant => Box::new(Expression::Constant(ConstantExpression {
                value: pair.as_span().as_str().to_string(),
                span: pair.as_span(),
            })),
            Rule::term => build_factor(pair.into_inner().next().unwrap()),
            _ => unimplemented!(),
        }
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::file))]
    pub struct File<'ast> {
        pub imports: Vec<ImportDirective>,
        pub functions: Vec<FunctionDefinition<'ast>>,
        pub eoi: EOI,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::function_definition))]
    pub struct FunctionDefinition<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub returns: Option<Vec<Type>>,
        pub statements: Vec<Statement<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::import_directive))]
    pub struct ImportDirective {}

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::type_name))]
    pub enum Type {
        Field,
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::statement))]
    pub enum Statement<'ast> {
        Return(ReturnStatement<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::return_statement))]
    pub struct ReturnStatement<'ast> {
        pub expressions: ExpressionList<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::expression_list))]
    pub struct ExpressionList<'ast> {
        pub values: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>
    }

    #[derive(Debug, PartialEq)]
    pub enum BinaryOperator {
        Xor,
        Or,
        Add,
        Sub,
        Mul,
        Div,
        Eq,
        NotEq,
        Lt,
        Gt,
        Lte,
        Gte,
        Pow,
    }

    #[derive(Debug, PartialEq)]
    pub enum Expression<'ast> {
        Binary(BinaryExpression<'ast>),
        Identifier(IdentifierExpression<'ast>),
        Constant(ConstantExpression<'ast>),
    }

    #[derive(Debug, PartialEq)]
    pub struct BinaryExpression<'ast> {
    	op: BinaryOperator,
    	left: Box<Expression<'ast>>,
    	right: Box<Expression<'ast>>,
    	span: Span<'ast>
    }

    impl<'ast> Expression<'ast> {
    	pub fn binary(op: BinaryOperator, left: Box<Expression<'ast>>, right: Box<Expression<'ast>>, span: Span<'ast>) -> Self {
    		Expression::Binary(
    			BinaryExpression {
    				op,
    				left,
    				right,
    				span
    			}
    		)
    	}

        pub fn add(left: Expression<'ast>, right: Expression<'ast>, span: Span<'ast>) -> Self {
            Self::binary(BinaryOperator::Add, Box::new(left), Box::new(right), span)
        }

        pub fn mul(left: Expression<'ast>, right: Expression<'ast>, span: Span<'ast>) -> Self {
            Self::binary(BinaryOperator::Mul, Box::new(left), Box::new(right), span)
        }

        pub fn pow(left: Expression<'ast>, right: Expression<'ast>, span: Span<'ast>) -> Self {
            Self::binary(BinaryOperator::Pow, Box::new(left), Box::new(right), span)
        }

        pub fn span(&self) -> Span<'ast> {
        	match self {
        		Expression::Binary(b) => b.span.clone(),
        		Expression::Identifier(i) => i.span.clone(),
        		Expression::Constant(c) => c.span.clone(),
        	}
        }
    }

    impl<'ast> FromPest<'ast> for Expression<'ast> {
        type Rule = Rule;
        type FatalError = Void;

        // we implement AST creation manually here
        // `pest` should yield an `expression` which we can generate AST with based on precedence rules
        fn from_pest(pest: &mut Pairs<'ast, Rule>) -> Result<Self, ConversionError<Void>> {
            // get a clone to "try" to match
            let mut clone = pest.clone();
            // advance by one pair in the clone, if none error out, `pest` is still the original
            let pair = clone.next().ok_or(::from_pest::ConversionError::NoMatch)?;
            // this should be an expression
            if pair.as_rule() == Rule::expression {
                let res = climb(pair);
                // we can replace `pest` with the clone we tried with and got pairs from to create the AST
                *pest = clone;
                Ok(*res)
            } else {
                println!("does this happen");
                Err(ConversionError::NoMatch)
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::constant))]
    pub struct ConstantExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::identifier))]
    pub struct IdentifierExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    fn span_into_str(span: Span) -> String {
        span.as_str().to_string()
	}

    #[derive(Debug, FromPest, PartialEq)]
    #[pest_ast(rule(Rule::EOI))]
    pub struct EOI;
}

struct FieldPrimeProg<'ast>(ast::File<'ast>);

impl<'ast> From<Pairs<'ast, Rule>> for FieldPrimeProg<'ast> {
    fn from(mut pairs: Pairs<'ast, Rule>) -> FieldPrimeProg<'ast> {
        FieldPrimeProg(
            ast::File::from_pest(&mut pairs)
                .map_err(|e| {
                    println!("{:?}", e);
                    e
                })
                .unwrap(),
        )
    }
}

fn generate_ast(input: &str) -> Result<ast::File, Error<Rule>> {
    let parse_tree = parse(input).map_err(|e| {
        println!("{}", e);
        e
    })?;
    Ok(FieldPrimeProg::from(parse_tree).0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::ast::*;
    use pest::Span;

    #[test]
    fn one_plus_one() {
        let source = r#"import "foo"
                def main() -> (field): return 1 + 1
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                functions: vec![FunctionDefinition {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 33, 37).unwrap()
                    },
                    returns: Some(vec![Type::Field]),
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: ExpressionList {
                            values: vec![Expression::add(
                                Expression::Constant(ConstantExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 59, 60).unwrap()
                                }),
                                Expression::Constant(ConstantExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 63, 64).unwrap()
                                }),
                                Span::new(&source, 59, 64).unwrap()
                            )],
                            span: Span::new(&source, 59, 64).unwrap(),
                        },
                        span: Span::new(&source, 52, 64).unwrap(),
                    })],
					span: Span::new(&source, 29, source.len()).unwrap(),
                }],
                imports: vec![ImportDirective {}],
                eoi: EOI {},
                span: Span::new(&source, 0, 65).unwrap()
            })
        );
    }

    #[test]
    fn precedence() {
        let source = r#"import "foo"
                def main() -> (field): return 1 + 2 * 3 ** 4
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                functions: vec![FunctionDefinition {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 33, 37).unwrap()
                    },
                    returns: Some(vec![Type::Field]),
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: ExpressionList {
                            values: vec![Expression::add(
                                Expression::Constant(ConstantExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 59, 60).unwrap()
                                }),
                                Expression::mul(
                                    Expression::Constant(ConstantExpression {
                                        value: String::from("2"),
                                        span: Span::new(&source, 63, 64).unwrap()
                                    }),
                                    Expression::pow(
                                        Expression::Constant(ConstantExpression {
                                            value: String::from("3"),
                                            span: Span::new(&source, 67, 68).unwrap()
                                        }),
                                        Expression::Constant(ConstantExpression {
                                            value: String::from("4"),
                                            span: Span::new(&source, 72, 73).unwrap()
                                        }),
                                        Span::new(&source, 67, 73).unwrap()
                                    ),
                                    Span::new(&source, 63, 73).unwrap()
                                ),
                            Span::new(&source, 59, 73).unwrap())],
                            span: Span::new(&source, 59, 73).unwrap(),
                        },
                        span: Span::new(&source, 52, 73).unwrap(),
                    })],
                    span: Span::new(&source, 29, 74).unwrap(),
                }],
                imports: vec![ImportDirective {}],
                eoi: EOI {},
                span: Span::new(&source, 0, 74).unwrap()
            })
        );
    }
}
