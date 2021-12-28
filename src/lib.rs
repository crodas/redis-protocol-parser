//! # A zero-copy redis protocol parser
//!
//! A zero-copy redis protocol parser

#![deny(missing_docs)]
#![deny(warnings)]

#[macro_use]
mod macros;

use std::convert::TryInto;

/// Redis Value.
#[derive(Debug, PartialEq, Clone)]
pub enum Value<'a> {
    /// Vector of values
    Array(Vec<Value<'a>>),
    /// Binary data
    Blob(&'a [u8]),
    /// String. New lines are not allowed
    String(&'a str),
    /// Error
    Error(&'a str, &'a str),
    /// Integer
    Integer(i64),
    /// Boolean
    Boolean(bool),
    /// Float number
    Float(f64),
    /// Big integers
    BigInteger(i128),
    /// Null
    Null,
}

/// Protocol errors
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Error {
    /// The data is incomplete. This it not an error per-se, but rather a
    /// mechanism to let the caller know they should keep buffering data before
    /// calling the parser again.
    Partial,
    /// Unexpected first byte after a new line
    InvalidPrefix,
    /// Invalid data length
    InvalidLength,
    /// Parsed value is not boolean
    InvalidBoolean,
    /// Parsed data is not a number
    InvalidNumber,
    /// Protocol error
    Protocol(u8, u8),
    /// Missing new line
    NewLine,
}

/// Parses data in the format that redis expects
///
/// Redis expects an array of blobs. Although the protocol is much wider at the
/// top level, redis expects an array of blobs.
///
/// The first value is returned along side with the unconsumed stream of bytes.
pub fn parse_server(bytes: &[u8]) -> Result<(&[u8], Vec<&[u8]>), Error> {
    let (bytes, byte) = next!(bytes);
    match byte {
        b'*' => parse_server_array(bytes),
        _ => Err(Error::Protocol(b'*', byte)),
    }
}

/// Parses an array from an steam of bytes
///
/// The first value is returned along side with the unconsumed stream of bytes.
fn parse_server_array(bytes: &[u8]) -> Result<(&[u8], Vec<&[u8]>), Error> {
    let (bytes, len) = read_line_number!(bytes, i32);
    if len <= 0 {
        return Err(Error::Protocol(b'x', b'y'));
    }

    let mut v = vec![];
    let mut bytes = bytes;

    for _i in 0..len {
        let n = next!(bytes);
        let r = match n.1 {
            b'$' => parse_blob(n.0),
            _ => Err(Error::Protocol(b'$', n.1)),
        }?;
        bytes = r.0;
        v.push(match r.1 {
            Value::Blob(x) => Ok(x),
            _ => Err(Error::Protocol(b'x', b'y')),
        }?);
    }

    Ok((bytes, v))
}

/// Parses redis values from an stream of bytes. If the data is incomplete
/// Err(Error::Partial) is returned.
///
/// The first value is returned along side with the unconsumed stream of bytes.
pub fn parse(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, byte) = next!(bytes);
    match byte {
        b'*' => parse_array(bytes),
        b'$' => parse_blob(bytes),
        b':' => parse_integer(bytes),
        b'(' => parse_big_integer(bytes),
        b',' => parse_float(bytes),
        b'#' => parse_boolean(bytes),
        b'+' => parse_str(bytes),
        b'-' => parse_error(bytes),
        _ => Err(Error::InvalidPrefix),
    }
}

fn parse_error(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, err_type) = read_until!(bytes, b' ');
    let (bytes, str) = read_line!(bytes);
    let err_type = unsafe { std::str::from_utf8_unchecked(err_type) };
    let str = unsafe { std::str::from_utf8_unchecked(str) };
    ret!(bytes, Value::Error(err_type, str))
}

fn parse_str(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, str) = read_line!(bytes);
    let str = unsafe { std::str::from_utf8_unchecked(str) };
    ret!(bytes, Value::String(str))
}

fn parse_boolean(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, byte) = next!(bytes);
    let v = match byte {
        b't' => true,
        b'f' => false,
        _ => return Err(Error::InvalidBoolean),
    };
    ret!(bytes, Value::Boolean(v))
}

fn parse_big_integer(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, number) = read_line_number!(bytes, i128);
    ret!(bytes, Value::BigInteger(number))
}

fn parse_integer(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, number) = read_line_number!(bytes, i64);
    ret!(bytes, Value::Integer(number))
}

fn parse_float(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, number) = read_line_number!(bytes, f64);
    ret!(bytes, Value::Float(number))
}

fn parse_blob(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, len) = read_line_number!(bytes, i64);

    if len <= 0 {
        return ret!(bytes, Value::Null);
    }

    let len = len.try_into().expect("Positive number");

    let (bytes, blob) = read_len!(bytes, len);
    let bytes = assert_nl!(bytes);

    ret!(bytes, Value::Blob(blob))
}

fn parse_array(bytes: &[u8]) -> Result<(&[u8], Value), Error> {
    let (bytes, len) = read_line_number!(bytes, i32);
    if len <= 0 {
        return ret!(bytes, Value::Null);
    }

    let mut v = vec![Value::Null; len as usize];
    let mut bytes = bytes;

    for i in 0..len {
        let r = parse(bytes)?;
        bytes = r.0;
        v[i as usize] = r.1;
    }

    ret!(bytes, Value::Array(v))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_partial() {
        let d = b"*-1";
        assert_eq!(Err(Error::Partial), parse(d));
    }

    #[test]
    fn test_parse_partial_2() {
        let d = b"*12\r\n";
        assert_eq!(Err(Error::Partial), parse(d));
    }

    #[test]
    fn test_incomplete_blob_parsing() {
        let d = b"$60\r\nfoobar\r\n";

        assert_eq!(Err(Error::Partial), parse(d));
    }

    #[test]
    fn test_complete_blob_parsing() {
        let d = b"$6\r\nfoobar\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let data = match r.unwrap().1 {
            Value::Blob(x) => unsafe { std::str::from_utf8_unchecked(x) },
            _ => "",
        };

        assert_eq!(data, "foobar");
    }

    #[test]
    fn test_complete_blob_parsing_and_extra_buffer() {
        let d = b"$6\r\nfoobar\r\n$6\r\nfoobar\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let (buf, data) = r.unwrap();

        let data = match data {
            Value::Blob(x) => unsafe { std::str::from_utf8_unchecked(x) },
            _ => "",
        };

        assert_eq!(data, "foobar");
        assert_eq!(b"$6\r\nfoobar\r\n", buf);
    }

    #[test]
    fn test_complete_array_parser() {
        let d = b"*2\r\n$6\r\nfoobar\r\n$3\r\nfoo\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Array(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert_eq!(2, x.len());
    }

    #[test]
    fn test_complete_nested_array_parser() {
        let d = b"*2\r\n$6\r\nfoobar\r\n*1\r\n$3\r\nfoo\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Array(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert_eq!(2, x.len());
    }

    #[test]
    fn test_parse_float() {
        let d = b",0.25887\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Float(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert_eq!(0.25887, x);
    }

    #[test]
    fn test_parse_integer() {
        let d = b":25887\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Integer(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert_eq!(25887, x);
    }

    #[test]
    fn test_parse_big_integer() {
        let d = b"(25887\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::BigInteger(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert_eq!(25887, x);
    }

    #[test]
    fn test_parse_false() {
        let d = b"#f\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Boolean(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert!(!x);
    }

    #[test]
    fn test_parse_true() {
        let d = b"#t\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Boolean(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert!(x);
    }

    #[test]
    fn test_parse_boolean_unexpected() {
        let d = b"#1\r\n";

        assert_eq!(Err(Error::InvalidBoolean), parse(d));
    }

    #[test]
    fn test_parse_str() {
        let d = b"+hello world\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::String(x) => x,
            _ => panic!("Unxpected type"),
        };

        assert_eq!("hello world", x);
    }

    #[test]
    fn test_parse_error() {
        let d = b"-ERR this is the error description\r\n";

        let r = parse(d);
        assert!(r.is_ok());

        let x = match r.unwrap().1 {
            Value::Error(a, b) => (a, b),
            _ => panic!("Unxpected type"),
        };

        assert_eq!("ERR", x.0);
        assert_eq!("this is the error description", x.1);
    }
}