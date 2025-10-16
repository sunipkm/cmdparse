#![doc(hidden)]
//! These macro are intended for testing the implementation in this crate and in the order crates
//! that are part of the `cmdparse` repository. Although these macros are public, they can be
//! changed, removed, renamed at any point for any reason.

#[doc(hidden)]
#[macro_export]
macro_rules! token {
    (--$text:literal) => {
        $crate::tokens::Token::Attribute($crate::tokens::RawLexeme::new($text))
    };
    ($text:literal) => {
        $crate::tokens::Token::Text($crate::tokens::RawLexeme::new($text))
    };
}

pub use token;

#[doc(hidden)]
#[macro_export]
macro_rules! test_parse {
    ($name:ident, $type:ty, $input:literal => Ok($value:expr, $next_token:expr)) => {
        #[test]
        fn $name() {
            let parser = <$type as $crate::Parsable<()>>::Parser::default();
            let stream = $crate::tokens::TokenStream::new($input);
            let (result, remaining) = $crate::Parser::<()>::parse(&parser, stream, ()).unwrap();
            assert_eq!(result, $value);
            assert_eq!(remaining.peek().transpose().unwrap(), $next_token);
        }
    };
    ($name:ident, $type:ty, $input:literal => Error($error:expr)) => {
        #[test]
        fn $name() {
            let parser = <$type as $crate::Parsable<()>>::Parser::default();
            let stream = $crate::tokens::TokenStream::new($input);
            let error = $crate::Parser::<()>::parse(&parser, stream, ()).unwrap_err();
            match error {
                $crate::error::ParseFailure::Error(error) => assert_eq!(error, $error),
                $crate::error::ParseFailure::Unrecognized(unrecognized) => {
                    panic!("expected Error, but found {:?}", unrecognized)
                }
            }
        }
    };
    ($name:ident, $type:ty, $input:literal => Unrecognized($token:expr, $next_token:expr)) => {
        #[test]
        fn $name() {
            let parser = <$type as $crate::Parsable<()>>::Parser::default();
            let stream = $crate::tokens::TokenStream::new($input);
            let error = $crate::Parser::<()>::parse(&parser, stream, ()).unwrap_err();
            match error {
                $crate::error::ParseFailure::Error(error) => {
                    panic!("expected Unrecognized, but found {:?}", error)
                }
                $crate::error::ParseFailure::Unrecognized(unrecognized) => {
                    assert_eq!(unrecognized.token(), $token);
                    assert_eq!(
                        unrecognized.remaining().peek().transpose().unwrap(),
                        $next_token
                    );
                }
            }
        }
    };
}

pub use test_parse;
