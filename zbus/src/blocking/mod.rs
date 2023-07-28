//! The blocking API.
//!
//! This module hosts all our blocking API. All the types under this module are thin wrappers
//! around the corresponding asynchronous types. Most of the method calls are simply calling their
//! asynchronous counterparts on the underlying types and use [`async_io::block_on`] to turn them
//! into blocking calls.
//!
//! # Caveats
//!
//! Since methods provided by these types run their own little runtime (`block_on`), you must not
//! use them in async contexts because of the infamous [async sandwich footgun][asf]. This is
//! an especially important fact to keep in mind for [`crate::dbus_interface`]. While
//! `dbus_interface` allows non-async methods for convenience, these methods are called from an
//! async context. The [`blocking` crate] provides an easy way around this problem though.
//!
//! [asf]: https://rust-lang.github.io/wg-async/vision/shiny_future/users_manual.html#caveat-beware-the-async-sandwich
//! [`blocking` crate]: https://docs.rs/blocking/

mod connection;
pub use connection::*;
mod connection_builder;
pub use connection_builder::*;
mod message_iterator;
pub use message_iterator::*;
mod object_server;
pub use object_server::*;
pub mod proxy;
pub use proxy::Proxy;

#[deprecated(note = "Use `proxy::OwnerChangedIterator` instead")]
#[doc(hidden)]
pub use proxy::OwnerChangedIterator;
#[deprecated(note = "Use `proxy::PropertyChanged` instead")]
#[doc(hidden)]
pub use proxy::PropertyChanged;
#[deprecated(note = "Use `proxy::PropertyIterator` instead")]
#[doc(hidden)]
pub use proxy::PropertyIterator;
#[deprecated(note = "Use `proxy::ProxyBuilder` instead")]
#[doc(hidden)]
pub use proxy::ProxyBuilder;
#[deprecated(note = "Use `proxy::SignalIterator` instead")]
#[doc(hidden)]
pub use proxy::SignalIterator;

pub mod fdo;
