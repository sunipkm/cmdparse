use core::fmt;
use core::marker::PhantomData;
use core::num::{IntErrorKind, ParseIntError};
use core::str::FromStr;

use crate::error::{ParseError, UnrecognizedToken};
use crate::tokens::{Token, TokenStream};
use crate::{Parsable, ParseResult, Parser};

macro_rules! no_state_parsable {
    ($type:ty, $parser:ident) => {
        impl<Ctx> Parsable<Ctx> for $type {
            type Parser = $parser<$type>;
        }
    };
}

/// Parser implementation for integral types ([`i8`]..[`i128`], [`isize`], [`u8`]..[`u128`],
/// [`usize`], non-zero variants)
///
/// More specifically, this parser can be used to parse values of any type that implements
/// [`FromStr`] trait with an error type [`ParseIntError`]. This parser consumes exactly one token
/// during parsing and completion and doesn’t yield and suggestions. It also does not recognize any
/// attributes.
///
/// The implementation is similar to [`FromStrParser`] but it provides a special error messages for
/// overflow and underflow errors as well as for parsed zero with types that disallow it.
///
/// # Example
/// ```
/// use kmdparse::parse;
///
/// # fn main() -> Result<(), kmdparse::error::ParseError<'static>> {
/// let value = parse::<_, i32>("15", ());
/// assert_eq!(value, Ok(15));
///
/// let failure = parse::<_, u8>("300", ());
/// assert_eq!(
///     failure.map_err(|err| err.to_string()),
///     Err(r#"cannot parse "300" (too large), expected integer"#.to_string()),
/// );
/// # Ok(())
/// # }
/// ```
#[derive(Clone, Copy)]
pub struct IntegerParser<T> {
    _phantom: PhantomData<T>,
}

impl<T> core::fmt::Debug for IntegerParser<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IntegerParser").finish()
    }
}

impl<T> Default for IntegerParser<T> {
    fn default() -> Self {
        Self {
            _phantom: Default::default(),
        }
    }
}

no_state_parsable!(i8, IntegerParser);
no_state_parsable!(u8, IntegerParser);
no_state_parsable!(i16, IntegerParser);
no_state_parsable!(u16, IntegerParser);
no_state_parsable!(i32, IntegerParser);
no_state_parsable!(u32, IntegerParser);
no_state_parsable!(i64, IntegerParser);
no_state_parsable!(u64, IntegerParser);
no_state_parsable!(i128, IntegerParser);
no_state_parsable!(u128, IntegerParser);
no_state_parsable!(isize, IntegerParser);
no_state_parsable!(usize, IntegerParser);

#[cfg(feature = "std")]
mod std_num_parsers {
    use super::*;
    extern crate std;
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroI8, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroU8, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroI16, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroU16, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroI32, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroU32, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroI64, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroU64, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroI128, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroU128, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroIsize, IntegerParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::num::NonZeroUsize, IntegerParser);
}
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub use std_num_parsers::*;

impl<T, Ctx> Parser<Ctx> for IntegerParser<T>
where
    T: FromStr<Err = ParseIntError>,
{
    type Value = T;

    fn parse<'a>(&self, input: TokenStream<'a>, _ctx: Ctx) -> ParseResult<'a, Self::Value> {
        let (token, remaining) = input
            .take()
            .transpose()?
            .ok_or_else(|| ParseError::token_required().expected("integer"))?;
        match token {
            Token::Text(text) => match text.parse_string().parse() {
                Ok(value) => Ok((value, remaining)),
                Err(error) => {
                    let message = match error.kind() {
                        IntErrorKind::PosOverflow => Some("too large"),
                        IntErrorKind::NegOverflow => Some("too small"),
                        IntErrorKind::Zero => Some("cannot be zero"),
                        _ => None,
                    };
                    Err(ParseError::invalid(token, message)
                        .expected("integer")
                        .into())
                }
            },
            Token::Attribute(_) => Err(UnrecognizedToken::new(token, remaining).into()),
        }
    }
}

/// Generic parser implementation for any type that implements [`FromStr`] trait
///
/// This parser consumes exactly one token and parses it using the target type’s [`FromStr`]
/// implementation for producing the parser's result. Note, that on failure, the error value is
/// discarded. `FromStrParser` does not recognize any attributes and does not yield any completion
/// suggestions.
///
/// Note, that there is no blanket implementation of [`Parsable`] that uses this parser
/// implementation. If you want to use this implementation for any custom type, you must either
/// implement [`Parsable`] for it or specify this parser explicitly when performing parsing or
/// completion.
///
/// The implementation is similar to [`IntegerParser`] with the only difference being more specific
/// error handling by the [`IntegerParser`].
///
/// # Example
///
/// The following example demonstrates how to use `FromStrParser` for custom types that implement
/// [`FromStr`]:
///
/// ```
/// use kmdparse::parsers::FromStrParser;
/// use kmdparse::{parse, Parsable};
/// use std::str::FromStr;
///
/// #[derive(Debug, PartialEq, Eq, Copy, Clone)]
/// enum MyBool {
///     Yes,
///     No,
/// }
///
/// impl FromStr for MyBool {
///     type Err = (); // the error type is discarded by the parser
///
///     fn from_str(s: &str) -> Result<Self, Self::Err> {
///         match s {
///             "yes" => Ok(MyBool::Yes),
///             "no" => Ok(MyBool::No),
///             _ => Err(()),
///         }
///     }
/// }
///
/// impl<Ctx> Parsable<Ctx> for MyBool {
///     type Parser = FromStrParser<Self>;
/// }
///
/// # fn main() {
/// assert_eq!(parse::<_, MyBool>("yes", ()), Ok(MyBool::Yes));
/// assert_eq!(parse::<_, MyBool>("no", ()), Ok(MyBool::No));
/// # }
/// ```
#[derive(Clone, Copy)]
pub struct FromStrParser<T> {
    _phantom: PhantomData<T>,
}

impl<T> fmt::Debug for FromStrParser<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromStrParser").finish()
    }
}

impl<T> Default for FromStrParser<T> {
    fn default() -> Self {
        FromStrParser {
            _phantom: Default::default(),
        }
    }
}

no_state_parsable!(f32, FromStrParser);
no_state_parsable!(f64, FromStrParser);
#[cfg(feature = "std")]
pub mod std_net_parsers {
    //! Standard library network address parsers implementations
    use super::*;
    extern crate std;
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::net::Ipv4Addr, FromStrParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::net::Ipv6Addr, FromStrParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::net::IpAddr, FromStrParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::net::SocketAddrV4, FromStrParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::net::SocketAddrV6, FromStrParser);
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    no_state_parsable!(std::net::SocketAddr, FromStrParser);
}
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub use std_net_parsers::*;

impl<T: FromStr, Ctx> Parser<Ctx> for FromStrParser<T> {
    type Value = T;

    fn parse<'a>(&self, input: TokenStream<'a>, _ctx: Ctx) -> ParseResult<'a, Self::Value> {
        let (token, remaining) = input
            .take()
            .transpose()?
            .ok_or_else(|| ParseError::token_required().expected("real number"))?;
        match token {
            Token::Text(text) => match text.parse_string().parse() {
                Ok(value) => Ok((value, remaining)),
                Err(_) => Err(ParseError::invalid(token, None)
                    .expected("real number")
                    .into()),
            },
            Token::Attribute(_) => Err(UnrecognizedToken::new(token, remaining).into()),
        }
    }
}

#[cfg(feature = "std")]
pub mod std_string_parsers {
    //! Standard library string parsers implementations
    use super::*;
    extern crate std;
    use std::string::String;
    use std::string::ToString;
    ///
    /// This parser consumes exactly one token, does not recognize any attributes, and does not yield
    /// any completion suggestions.
    ///
    /// # Example
    /// ```
    /// use kmdparse::parse;
    ///
    /// # fn main() -> Result<(), kmdparse::error::ParseError<'static>> {
    /// assert_eq!(parse::<_, String>("token", ())?, "token".to_string());
    /// assert_eq!(
    ///     parse::<_, String>("'multiple words'", ())?,
    ///     "multiple words".to_string()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    #[derive(Debug, Default)]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub struct StringParser;

    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    impl<Ctx> Parser<Ctx> for StringParser {
        type Value = String;

        fn parse<'a>(&self, input: TokenStream<'a>, _ctx: Ctx) -> ParseResult<'a, Self::Value> {
            let (token, remaining) = input
                .take()
                .transpose()?
                .ok_or_else(|| ParseError::token_required().expected("string"))?;
            match token {
                Token::Text(text) => Ok((ToString::to_string(&text.parse_string()), remaining)),
                Token::Attribute(_) => Err(UnrecognizedToken::new(token, remaining).into()),
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    impl<Ctx> Parsable<Ctx> for String {
        type Parser = StringParser;
    }
}
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub use std_string_parsers::StringParser;

/// Parser implementation for [`bool`]ean values
///
/// This parser consumes exactly one token and does not recognize any attributes. At allows the
/// following input tokens as only recognized valid input:
///
/// | Parsing result | Recognized tokens       |
/// |----------------|-------------------------|
/// | [`true`]       | `true`, `t`, `yes`, `y` |
/// | [`false`]      | `false`, `f`, `no`, `n` |
///
/// # Example
/// ```
/// use kmdparse::{complete, parse};
/// use std::collections::BTreeSet;
///
/// # fn main() -> Result<(), kmdparse::error::ParseError<'static>> {
/// assert_eq!(parse::<_, bool>("false", ())?, false);
/// assert_eq!(complete::<_, bool>("tr", ()), BTreeSet::from(["ue".into()]));
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Default)]
pub struct BooleanParser;

impl<Ctx> Parser<Ctx> for BooleanParser {
    type Value = bool;

    fn parse<'a>(&self, input: TokenStream<'a>, _ctx: Ctx) -> ParseResult<'a, Self::Value> {
        let (token, remaining) = input
            .take()
            .transpose()?
            .ok_or_else(|| ParseError::token_required().expected("boolean"))?;
        match token {
            Token::Text(text) => match text.parse_string() {
                "true" | "t" | "yes" | "y" => Ok((true, remaining)),
                "false" | "f" | "no" | "n" => Ok((false, remaining)),
                _ => Err(ParseError::invalid(token, None).expected("boolean").into()),
            },
            Token::Attribute(_) => Err(UnrecognizedToken::new(token, remaining).into()),
        }
    }
}

impl<Ctx> Parsable<Ctx> for bool {
    type Parser = BooleanParser;
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::{FromStrParser, IntegerParser};
    use crate::error::{ParseError, ParseFailure};
    use crate::testing::token;
    use crate::tokens::TokenStream;
    use crate::{Parsable, Parser};
    use std::{
        format,
        string::{String, ToString},
    };

    macro_rules! test_parse {
        ($name:ident, $type:ty, $text:literal => Ok($value:expr)) => {
            #[test]
            #[allow(clippy::bool_assert_comparison)]
            fn $name() {
                let parser = <$type as Parsable<()>>::Parser::default();

                let stream = TokenStream::new($text);
                let (result, remaining) = Parser::<()>::parse(&parser, stream, ()).unwrap();
                assert_eq!(result, $value);
                assert!(remaining.peek().is_none());

                let mut input = $text.to_string();
                input.push_str(" abc");
                let stream = TokenStream::new(&input);
                let (result, remaining) = Parser::<()>::parse(&parser, stream, ()).unwrap();
                assert_eq!(result, $value);
                assert_eq!(remaining.peek().unwrap().unwrap(), token!("abc"));
            }
        };
        ($name:ident, $type:ty, $text:literal => Err($err:expr)) => {
            #[test]
            fn $name() {
                let parser = <$type as Parsable<()>>::Parser::default();
                let stream = TokenStream::new($text);
                let failure = Parser::<()>::parse(&parser, stream, ()).unwrap_err();
                match failure {
                    ParseFailure::Error(error) => assert_eq!(error, $err),
                    ParseFailure::Unrecognized(_) => {
                        std::panic!("expected Error, got {:?}", failure)
                    }
                }
            }
        };
    }

    macro_rules! test_unrecognized_attribute {
        ($name:ident, $type:ty) => {
            #[test]
            fn $name() {
                let parser = <$type as Parsable<()>>::Parser::default();
                let stream = TokenStream::new("--unrecognized abc");
                let failure = Parser::<()>::parse(&parser, stream, ()).unwrap_err();
                match failure {
                    ParseFailure::Error(_) => {
                        std::panic!("expected Unrecognized, got {:?}", failure)
                    }
                    ParseFailure::Unrecognized(unrecognized) => {
                        assert_eq!(unrecognized.token(), token!(--"unrecognized"));
                        assert_eq!(
                            unrecognized.remaining().peek().unwrap().unwrap(),
                            token!("abc")
                        );
                    }
                }
            }
        };
    }

    mod integer_parser {
        use super::*;

        #[test]
        fn debug() {
            assert_eq!(
                &format!("{:?}", IntegerParser::<i8>::default()),
                "IntegerParser"
            );
        }

        test_parse!(parse_u8, u8, "15" => Ok(15));
        test_parse!(
            parse_non_zero_u8_zero, std::num::NonZeroU8,
            "0" => Err(ParseError::invalid(token!("0"), Some("cannot be zero")).expected("integer"))
        );
        test_parse!(parse_non_zero_u8_non_zero, std::num::NonZeroU8, "5" => Ok(std::num::NonZeroU8::new(5).unwrap()));
        test_unrecognized_attribute!(unrecognized_attr, i32);
        test_parse!(parse_invalid, u16, "abc" => Err(ParseError::invalid(token!("abc"), None).expected("integer")));
        test_parse!(parse_too_large, u16, "999999999" => Err(ParseError::invalid(token!("999999999"), Some("too large")).expected("integer")));
        test_parse!(parse_empty_string, u16, "" => Err(ParseError::token_required().expected("integer")));
    }

    mod from_str_parser {
        use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

        use super::*;

        #[test]
        fn debug() {
            assert_eq!(
                &format!("{:?}", FromStrParser::<f64>::default()),
                "FromStrParser"
            );
        }

        #[test]
        fn parse_f64() {
            let parser = <f64 as Parsable<()>>::Parser::default();

            let stream = TokenStream::new("3.2");
            let (result, remaining) = Parser::<()>::parse(&parser, stream, ()).unwrap();
            assert!((result - 3.2).abs() < f64::EPSILON);
            assert!(remaining.peek().is_none());

            let stream = TokenStream::new("3.2 abc");
            let (result, remaining) = Parser::<()>::parse(&parser, stream, ()).unwrap();
            assert!((result - 3.2).abs() < f64::EPSILON);
            assert_eq!(remaining.peek().unwrap().unwrap(), token!("abc"));
        }

        test_parse!(parse_f64_error, f64, "abc" => Err(ParseError::invalid(token!("abc"), None).expected("real number")));
        test_parse!(parse_f64_empty, f64, "" => Err(ParseError::token_required().expected("real number")));
        test_unrecognized_attribute!(unrecognized_attr, f32);

        test_parse!(parse_ipv4, Ipv4Addr, "127.0.0.1" => Ok(Ipv4Addr::new(127, 0, 0, 1)));
        test_parse!(parse_ipv4_generic, IpAddr, "127.0.0.1" => Ok(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1))));
        test_parse!(parse_ipv6, Ipv6Addr, "::1" => Ok(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)));
        test_parse!(parse_ipv6_generic, IpAddr, "::1" => Ok(IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1))));
    }

    mod string_parser {
        use super::*;

        test_parse!(parse_string, String, "abc" => Ok("abc".to_string()));
        test_parse!(parse_empty, String, "" => Err(ParseError::token_required().expected("string")));
        test_unrecognized_attribute!(unrecognized_attr, String);
    }

    mod boolean_parser {
        use super::*;

        test_parse!(parse_bool_true, bool, "true" => Ok(true));
        test_parse!(parse_bool_yes, bool, "yes" => Ok(true));
        test_parse!(parse_bool_false, bool, "false" => Ok(false));
        test_parse!(parse_bool_no, bool, "no" => Ok(false));
        test_unrecognized_attribute!(unrecognized_attr, bool);
        test_parse!(parse_empty_string, bool, "" => Err(ParseError::token_required().expected("boolean")));
        test_parse!(parse_invalie, bool, "abc" => Err(ParseError::invalid(token!("abc"), None).expected("boolean")));
    }
}
