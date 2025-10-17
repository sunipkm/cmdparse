extern crate std;
use crate::error::{ParseError, UnrecognizedToken};
use crate::tokens::Token;
use crate::{tokens::TokenStream, Parser};
use crate::{Parsable, ParseResult};
use std::path::PathBuf;

/// Parser implementation for [`PathBuf`]s with support for directory item completion
///
/// This parser consumes exactly one token and doesn’t recognize any attributes. The contents of
/// the token are transformed into a [`PathBuf`]. When performing completion, this parser
/// enumerates the directory at the given path and suggests completions that would produce the path
/// to an existing directory item.
#[derive(Default)]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub struct PathParser;

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<Ctx> Parser<Ctx> for PathParser {
    type Value = PathBuf;

    fn parse<'a>(&self, input: TokenStream<'a>, _ctx: Ctx) -> ParseResult<'a, Self::Value> {
        match input.take() {
            Some(Ok((token, remaining))) => match token {
                Token::Text(text) => Ok((text.parse_string().into(), remaining)),
                Token::Attribute(_) => Err(UnrecognizedToken::new(token, remaining).into()),
            },
            Some(Err(err)) => Err(err.into()),
            None => Err(ParseError::token_required().expected("path").into()),
        }
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<Ctx> Parsable<Ctx> for PathBuf {
    type Parser = PathParser;
}

#[cfg(test)]
mod tests {
    extern crate std;
    use crate::error::ParseError;
    use crate::testing::{test_parse, token};
    use std::path::PathBuf;
    use std::string::ToString;

    test_parse!(
        parse_empty, PathBuf,
        "" => Error(ParseError::token_required().expected("path"))
    );
    test_parse!(
        parse_attribute, PathBuf,
        "--attr remaining" => Unrecognized(token!(--"attr"), Some(token!("remaining")))
    );
    test_parse!(
        parse_path, PathBuf,
        "dir/file.txt remaining" => Ok(PathBuf::from("dir/file.txt".to_string()), Some(token!("remaining")))
    );
}
