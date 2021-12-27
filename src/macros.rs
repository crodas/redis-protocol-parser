macro_rules! ret {
    ($bytes: ident, $value: expr) => {{
        Ok(($bytes, $value))
    }};
}
macro_rules! next {
    ($bytes:ident) => {{
        let byte = if $bytes.len() > 0 {
            unsafe { *$bytes.get_unchecked(0) }
        } else {
            return Err(Error::Partial);
        };
        (&$bytes[1..], byte)
    }};
}

macro_rules! read_len {
    ($bytes:ident, $len:ident) => {{
        let len: usize = $len.try_into().unwrap();

        if ($bytes.len() < len) {
            return Err(Error::Partial);
        }

        (&$bytes[len..], &$bytes[0..len])
    }};
}

macro_rules! assert_nl {
    ($bytes:ident) => {{
        if ($bytes.len() < 2) {
            return Err(Error::Partial);
        }
        if ($bytes[0] != b'\r' || $bytes[1] != b'\n') {
            return Err(Error::NewLine);
        }
        &$bytes[2..]
    }};
}

macro_rules! read_until {
    ($bytes:ident, $next:expr) => {{
        let len = $bytes.len();
        let mut i = 0;
        loop {
            if (i >= len) {
                return Err(Error::Partial);
            }

            if ($bytes[i] == $next) {
                break;
            }
            i += 1;
        }
        (&$bytes[i + 1..], &$bytes[0..i])
    }};
}

macro_rules! read_line {
    ($bytes:ident) => {{
        let ($bytes, prev) = read_until!($bytes, b'\r');
        let ($bytes, next) = next!($bytes);

        if (next != b'\n') {
            return Err(Error::NewLine);
        }

        ($bytes, prev)
    }};
}

macro_rules! read_line_number {
    ($bytes:ident, $type:ident) => {{
        let ($bytes, n) = read_line!($bytes);
        let n = unsafe { std::str::from_utf8_unchecked(n) };
        let n = match n.parse::<$type>() {
            Ok(x) => x,
            _ => return Err(Error::InvalidNumber),
        };
        ($bytes, n)
    }};
}
