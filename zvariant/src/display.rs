/// Implemented based on https://gitlab.gnome.org/GNOME/glib/-/blob/e1d47f0b0d0893ac9171e24cc7bf635495376546/glib/gvariant.c#L2213
use std::{
    ffi::CStr,
    fmt::{Display, Write},
};

use crate::{Array, Dict, Structure, Value};

#[cfg(feature = "gvariant")]
use crate::Maybe;

impl Display for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        value_display_fmt(self, f, true)
    }
}

impl Display for Array<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        array_display_fmt(self, f, true)
    }
}

impl Display for Structure<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        structure_display_fmt(self, f, true)
    }
}

impl Display for Dict<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        dict_display_fmt(self, f, true)
    }
}

#[cfg(feature = "gvariant")]
impl Display for Maybe<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        maybe_display_fmt(self, f, true)
    }
}

fn array_display_fmt(
    array: &Array<'_>,
    f: &mut std::fmt::Formatter<'_>,
    type_annotate: bool,
) -> std::fmt::Result {
    // Print as string if it is a bytestring (i.e., first nul character is the last byte)
    if array
        .iter()
        .position(|value| value == &Value::U8(b'\0'))
        .is_some_and(|position| position == array.len() - 1)
    {
        let vec = array
            .iter()
            .map(|item| {
                if let Value::U8(val) = item {
                    *val
                } else {
                    unreachable!("item must have a signature of byte");
                }
            })
            .collect::<Vec<_>>();
        let string = CStr::from_bytes_with_nul(&vec)
            .expect("nul character must be the last byte")
            .to_string_lossy();

        if string.find('\'').is_some() {
            write!(f, "b\"{}\"", string)?;
        } else {
            write!(f, "b'{}'", string)?;
        }

        return Ok(());
    }

    if array.is_empty() {
        if type_annotate {
            write!(f, "@{} ", array.full_signature())?;
        }
        f.write_str("[]")?;
    } else {
        f.write_char('[')?;

        // Annotate only the first item as the rest will be
        // of the same type.
        let mut type_annotate = type_annotate;

        for (i, item) in array.iter().enumerate() {
            value_display_fmt(item, f, type_annotate)?;
            type_annotate = false;

            if i + 1 < array.len() {
                f.write_str(", ")?;
            }
        }

        f.write_char(']')?;
    }

    Ok(())
}

fn structure_display_fmt(
    structure: &Structure<'_>,
    f: &mut std::fmt::Formatter<'_>,
    type_annotate: bool,
) -> std::fmt::Result {
    f.write_char('(')?;

    let fields = structure.fields();

    match fields.len() {
        0 => {}
        1 => {
            value_display_fmt(&fields[0], f, type_annotate)?;
            f.write_char(',')?;
        }
        _ => {
            for (i, field) in fields.iter().enumerate() {
                value_display_fmt(field, f, type_annotate)?;

                if i + 1 < fields.len() {
                    f.write_str(", ")?;
                }
            }
        }
    }

    f.write_char(')')
}

fn dict_display_fmt(
    dict: &Dict<'_, '_>,
    f: &mut std::fmt::Formatter<'_>,
    type_annotate: bool,
) -> std::fmt::Result {
    let entries = dict.entries();

    if entries.is_empty() {
        if type_annotate {
            write!(f, "@{} ", dict.full_signature())?;
        }
        f.write_str("{}")?;
    } else {
        f.write_char('{')?;

        // Annotate only the first entry as the rest will be
        // of the same type.
        let mut type_annotate = type_annotate;

        for (i, entry) in entries.iter().enumerate() {
            value_display_fmt(entry.key(), f, type_annotate)?;
            f.write_str(": ")?;
            value_display_fmt(entry.value(), f, type_annotate)?;
            type_annotate = false;

            if i + 1 < entries.len() {
                f.write_str(", ")?;
            }
        }

        f.write_char('}')?;
    }

    Ok(())
}

#[cfg(feature = "gvariant")]
fn maybe_display_fmt(
    maybe: &Maybe<'_>,
    f: &mut std::fmt::Formatter<'_>,
    type_annotate: bool,
) -> std::fmt::Result {
    if type_annotate {
        write!(f, "@{} ", maybe.full_signature())?;
    }

    let (last_inner, depth) = {
        let mut curr = maybe.inner();
        let mut depth = 0;

        while let Some(Value::Maybe(child_maybe)) = curr {
            curr = child_maybe.inner();
            depth += 1;
        }

        (curr, depth)
    };

    if let Some(last_inner) = last_inner {
        // There are no Nothings, so print out the inner
        // value with no prefixes.
        value_display_fmt(last_inner, f, false)?;
    } else {
        // One of the maybes was Nothing, so print out the
        // right number of justs.
        for _ in 0..depth {
            f.write_str("just ")?;
        }
        f.write_str("nothing")?;
    }

    Ok(())
}

fn value_display_fmt(
    value: &Value<'_>,
    f: &mut std::fmt::Formatter<'_>,
    type_annotate: bool,
) -> std::fmt::Result {
    match value {
        Value::U8(num) => {
            if type_annotate {
                f.write_str("byte ")?;
            }
            write!(f, "0x{:02x}", num)
        }
        Value::Bool(boolean) => {
            write!(f, "{}", boolean)
        }
        Value::I16(num) => {
            if type_annotate {
                f.write_str("int16 ")?;
            }
            write!(f, "{}", num)
        }
        Value::U16(num) => {
            if type_annotate {
                f.write_str("uint16 ")?;
            }
            write!(f, "{}", num)
        }
        Value::I32(num) => {
            // Never annotate this type because it is the default for numbers
            write!(f, "{}", num)
        }
        Value::U32(num) => {
            if type_annotate {
                f.write_str("uint32 ")?;
            }
            write!(f, "{}", num)
        }
        Value::I64(num) => {
            if type_annotate {
                f.write_str("int64 ")?;
            }
            write!(f, "{}", num)
        }
        Value::U64(num) => {
            if type_annotate {
                f.write_str("uint64 ")?;
            }
            write!(f, "{}", num)
        }
        Value::F64(num) => {
            if num.fract() == 0. {
                // Add a dot to make it clear that this is a float
                write!(f, "{}.", num)
            } else {
                write!(f, "{}", num)
            }
        }
        Value::Str(string) => {
            if string.find('\'').is_some() {
                write!(f, "\"{}\"", string)
            } else {
                write!(f, "'{}'", string)
            }
        }
        Value::Signature(val) => {
            if type_annotate {
                f.write_str("signature ")?;
            }
            write!(f, "'{}'", val)
        }
        Value::ObjectPath(val) => {
            if type_annotate {
                f.write_str("objectpath ")?;
            }
            write!(f, "'{}'", val)
        }
        Value::Value(child) => {
            f.write_char('<')?;

            // Always annotate types in nested variants, because they
            // are (by nature) of varible type.
            value_display_fmt(child, f, true)?;

            f.write_char('>')?;
            Ok(())
        }
        Value::Array(array) => array_display_fmt(array, f, type_annotate),
        Value::Dict(dict) => dict_display_fmt(dict, f, type_annotate),
        Value::Structure(structure) => structure_display_fmt(structure, f, type_annotate),
        #[cfg(feature = "gvariant")]
        Value::Maybe(maybe) => maybe_display_fmt(maybe, f, type_annotate),
        #[cfg(unix)]
        Value::Fd(handle) => {
            if type_annotate {
                f.write_str("handle ")?;
            }
            write!(f, "{}", handle)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, convert::TryFrom};

    use crate::{Fd, ObjectPath, Signature};

    use super::*;

    #[test]
    fn u8_display() {
        assert_eq!(Value::new(0_u8).to_string(), "byte 0x00");
        assert_eq!(Value::new(1_u8).to_string(), "byte 0x01");
        assert_eq!(Value::new(255_u8).to_string(), "byte 0xff");
    }

    #[test]
    fn bool_display() {
        assert_eq!(Value::new(true).to_string(), "true");
        assert_eq!(Value::new(false).to_string(), "false");
    }

    #[test]
    fn i16_display() {
        assert_eq!(Value::new(0_i16).to_string(), "int16 0");
        assert_eq!(Value::new(1_i16).to_string(), "int16 1");
        assert_eq!(Value::new(-1_i16).to_string(), "int16 -1");
        assert_eq!(Value::new(32767_i16).to_string(), "int16 32767");
        assert_eq!(Value::new(-32768_i16).to_string(), "int16 -32768");
    }

    #[test]
    fn u16_display() {
        assert_eq!(Value::new(0_u16).to_string(), "uint16 0");
        assert_eq!(Value::new(1_u16).to_string(), "uint16 1");
        assert_eq!(Value::new(65535_u16).to_string(), "uint16 65535");
    }

    #[test]
    fn i32_display() {
        assert_eq!(Value::new(0_i32).to_string(), "0");
        assert_eq!(Value::new(1_i32).to_string(), "1");
        assert_eq!(Value::new(-1_i32).to_string(), "-1");
        assert_eq!(Value::new(2147483647_i32).to_string(), "2147483647");
        assert_eq!(Value::new(-2147483648_i32).to_string(), "-2147483648");
    }

    #[test]
    fn u32_display() {
        assert_eq!(Value::new(0_u32).to_string(), "uint32 0");
        assert_eq!(Value::new(1_u32).to_string(), "uint32 1");
        assert_eq!(Value::new(4294967295_u32).to_string(), "uint32 4294967295");
    }

    #[test]
    fn i64_display() {
        assert_eq!(Value::new(0_i64).to_string(), "int64 0");
        assert_eq!(Value::new(1_i64).to_string(), "int64 1");
        assert_eq!(Value::new(-1_i64).to_string(), "int64 -1");
        assert_eq!(
            Value::new(9223372036854775807_i64).to_string(),
            "int64 9223372036854775807"
        );
        assert_eq!(
            Value::new(-9223372036854775808_i64).to_string(),
            "int64 -9223372036854775808"
        );
    }

    #[test]
    fn u64_display() {
        assert_eq!(Value::new(0_u64).to_string(), "uint64 0");
        assert_eq!(Value::new(1_u64).to_string(), "uint64 1");
        assert_eq!(
            Value::new(18446744073709551615_u64).to_string(),
            "uint64 18446744073709551615"
        );
    }

    #[test]
    fn f64_display() {
        assert_eq!(Value::new(0.).to_string(), "0.");
        assert_eq!(Value::new(1.).to_string(), "1.");
        assert_eq!(Value::new(-1.).to_string(), "-1.");
        assert_eq!(Value::new(1.1).to_string(), "1.1");
        assert_eq!(Value::new(-1.1).to_string(), "-1.1");
        assert_eq!(Value::new(1.1e10).to_string(), "11000000000.");
        assert_eq!(Value::new(-1.1e10).to_string(), "-11000000000.");
        assert_eq!(Value::new(1.1e-10).to_string(), "0.00000000011");
        assert_eq!(Value::new(-1.1e-10).to_string(), "-0.00000000011");
    }

    #[test]
    fn str_display() {
        assert_eq!(Value::new("").to_string(), "''");
        assert_eq!(Value::new("a").to_string(), "'a'");
        assert_eq!(Value::new("abc").to_string(), "'abc'");
        assert_eq!(Value::new(r#"""#).to_string(), r#"'"'"#);

        assert_eq!(Value::new("'").to_string(), r#""'""#);
        assert_eq!(Value::new("a'b").to_string(), r#""a'b""#);
        // assert_eq!(Value::new("a'\"b").to_string(), r#""a'\"b""#);

        // assert_eq!(Value::new(r#"\"#).to_string(), r#"'\\'"#);
        // assert_eq!(Value::new(r#"\a"#).to_string(), r#"'\\a'"#);
        // assert_eq!(
        //     Value::new(r#"\a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z"#).to_string(),
        //     r#"'\\a\\b\\c\\d\\e\\f\\g\\h\\i\\j\\k\\l\\m\\n\\o\\p\\q\\r\\s\\t\\u\\v\\w\\x\\y\\z'"#
        // );
    }

    #[test]
    fn signature_display() {
        #[track_caller]
        fn assert_valid_display(signature_str: &str, expected_display: &str) {
            assert_eq!(
                Value::new(Signature::try_from(signature_str).expect("signature must be valid"))
                    .to_string(),
                expected_display
            );
        }

        assert_valid_display("", "signature ''");
        assert_valid_display("y", "signature 'y'");
        assert_valid_display("xs", "signature 'xs'");
        assert_valid_display("(ysa{sd})", "signature '(ysa{sd})'");
        assert_valid_display("a{sd}", "signature 'a{sd}'");
    }

    #[test]
    fn object_path_display() {
        #[track_caller]
        fn assert_valid_display(object_path_str: &str, expected_display: &str) {
            assert_eq!(
                Value::new(
                    ObjectPath::try_from(object_path_str).expect("object path must be valid")
                )
                .to_string(),
                expected_display
            );
        }

        assert_valid_display("/", "objectpath '/'");
        assert_valid_display("/Path/t0/0bject", "objectpath '/Path/t0/0bject'");
        assert_valid_display(
            "/a/very/looooooooooooooooooooooooo0000o0ng/path",
            "objectpath '/a/very/looooooooooooooooooooooooo0000o0ng/path'",
        );
    }

    #[test]
    fn value_display() {
        assert_eq!(Value::new(Value::new(0_u8)).to_string(), "<byte 0x00>");
        assert_eq!(Value::new(Value::new(true)).to_string(), "<true>");
        assert_eq!(Value::new(Value::new((51, 51))).to_string(), "<(51, 51)>");
        assert_eq!(
            Value::new(Value::new(Value::new(0_u8))).to_string(),
            "<<byte 0x00>>"
        );
    }

    #[test]
    fn array_display() {
        assert_eq!(Value::new(vec![] as Vec<i32>).to_string(), "@ai []");
        assert_eq!(
            Value::new(vec![] as Vec<Vec<Vec<i32>>>).to_string(),
            "@aaai []"
        );
        assert_eq!(Value::new(vec![0_i16]).to_string(), "[int16 0]");
        assert_eq!(Value::new(vec![0_i16, 1_i16]).to_string(), "[int16 0, 1]");
        assert_eq!(
            Value::new(vec![
                vec![0_i16, 1_i16],
                vec![2_i16, 3_i16],
                vec![4_i16, 5_i16]
            ])
            .to_string(),
            "[[int16 0, 1], [2, 3], [4, 5]]"
        );

        assert_eq!(
            Value::new(b"Hello".to_vec()).to_string(),
            "[byte 0x48, 0x65, 0x6c, 0x6c, 0x6f]"
        );
        assert_eq!(
            Value::new(b"Hell\0o".to_vec()).to_string(),
            "[byte 0x48, 0x65, 0x6c, 0x6c, 0x00, 0x6f]"
        );

        assert_eq!(Value::new(b"Hello\0".to_vec()).to_string(), "b'Hello'");
        assert_eq!(Value::new(b"\0".to_vec()).to_string(), "b''");
    }

    #[test]
    fn dict_display() {
        assert_eq!(
            Value::new(HashMap::<bool, bool>::new()).to_string(),
            "@a{bb} {}"
        );
        assert_eq!(
            Value::new(vec![(true, 0_i64)].into_iter().collect::<HashMap<_, _>>()).to_string(),
            "{true: int64 0}",
        );

        // The order of the entries may vary
        let val = Value::new(
            vec![(32_u16, 64_i64), (100_u16, 200_i64)]
                .into_iter()
                .collect::<HashMap<_, _>>(),
        )
        .to_string();
        assert!(val.starts_with('{'));
        assert!(val.ends_with('}'));
        assert_eq!(val.matches("uint16").count(), 1);
        assert_eq!(val.matches("int64").count(), 1);

        let items_str = val.split(", ").collect::<Vec<_>>();
        assert_eq!(items_str.len(), 2);
        assert!(items_str
            .iter()
            .any(|str| str.contains("32") && str.contains(": ") && str.contains("64")));
        assert!(items_str
            .iter()
            .any(|str| str.contains("100") && str.contains(": ") && str.contains("200")));
    }

    #[test]
    fn structure_display() {
        assert_eq!(Value::new(Structure::default()).to_string(), "()");
        assert_eq!(Value::new((true,)).to_string(), "(true,)");
        assert_eq!(Value::new((true, true)).to_string(), "(true, true)");
        assert_eq!(
            Value::new((true, true, true)).to_string(),
            "(true, true, true)"
        );
    }

    #[test]
    fn maybe_display() {
        assert_eq!(Value::new(Some(0_i16)).to_string(), "@mn 0");
        assert_eq!(Value::new(Some(Some(0_i16))).to_string(), "@mmn 0");
        assert_eq!(Value::new(Some(Some(Some(0_i16)))).to_string(), "@mmmn 0");

        assert_eq!(Value::new(None::<i16>).to_string(), "@mn nothing");
        assert_eq!(
            Value::new(Some(None::<i16>)).to_string(),
            "@mmn just nothing"
        );
        assert_eq!(
            Value::new(Some(Some(None::<i16>))).to_string(),
            "@mmmn just just nothing"
        );
    }

    #[test]
    fn fd_display() {
        assert_eq!(Value::new(Fd::from(0)).to_string(), "handle 0");
        assert_eq!(Value::new(Fd::from(-1)).to_string(), "handle -1");
        assert_eq!(Value::new(Fd::from(100)).to_string(), "handle 100");
    }

    #[test]
    fn mixed_display() {
        assert_eq!(
            Value::new((
                None::<bool>,
                None::<bool>,
                Some(
                    vec![("size", Value::new((800, 600)))]
                        .into_iter()
                        .collect::<HashMap<_, _>>()
                ),
                7777,
                8888
            ))
            .to_string(),
            "(@mb nothing, @mb nothing, @ma{sv} {'size': <(800, 600)>}, 7777, 8888)"
        );

        assert_eq!(
            Value::new((123, None::<i32>, 123, None::<i32>, Some(None::<i32>), 123)).to_string(),
            "(123, @mi nothing, 123, @mi nothing, @mmi just nothing, 123)"
        );

        assert_eq!(
            Value::new((b'a', 1, 22, 33, 44_u64, 5.5)).to_string(),
            "(byte 0x61, 1, 22, 33, uint64 44, 5.5)"
        );

        assert_eq!(
            Value::new((b'a', b'b', b'c', (b'd',), Value::new(b'e'))).to_string(),
            "(byte 0x61, byte 0x62, byte 0x63, (byte 0x64,), <byte 0x65>)"
        );
    }
}
