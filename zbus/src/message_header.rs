use std::convert::TryFrom;

use enumflags2::BitFlags;
use serde::{Deserialize, Serialize};
use serde_repr::{Deserialize_repr, Serialize_repr};

use zvariant::{ObjectPath, Signature};
use zvariant_derive::Type;

use crate::{MessageError, MessageField, MessageFieldCode, MessageFields};

pub(crate) const PRIMARY_HEADER_SIZE: usize = 12;
pub(crate) const MIN_MESSAGE_SIZE: usize = PRIMARY_HEADER_SIZE + 4;

#[repr(u8)]
#[derive(Debug, Copy, Clone, Deserialize_repr, PartialEq, Serialize_repr, Type)]
pub enum EndianSig {
    Big = b'B',
    Little = b'l',
}

// Such a shame I've to do this manually
impl TryFrom<u8> for EndianSig {
    type Error = MessageError;

    fn try_from(val: u8) -> Result<EndianSig, MessageError> {
        match val {
            b'B' => Ok(EndianSig::Big),
            b'l' => Ok(EndianSig::Little),
            _ => Err(MessageError::IncorrectEndian),
        }
    }
}

#[cfg(target_endian = "big")]
/// Signature of the target's native endian.
pub const NATIVE_ENDIAN_SIG: EndianSig = EndianSig::Big;
#[cfg(target_endian = "little")]
/// Signature of the target's native endian.
pub const NATIVE_ENDIAN_SIG: EndianSig = EndianSig::Little;

#[repr(u8)]
#[derive(Debug, Copy, Clone, Deserialize_repr, PartialEq, Serialize_repr, Type)]
pub enum MessageType {
    Invalid = 0,
    MethodCall = 1,
    MethodReturn = 2,
    Error = 3,
    Signal = 4,
}

// Such a shame I've to do this manually
impl From<u8> for MessageType {
    fn from(val: u8) -> MessageType {
        match val {
            1 => MessageType::MethodCall,
            2 => MessageType::MethodReturn,
            3 => MessageType::Error,
            4 => MessageType::Signal,
            _ => MessageType::Invalid,
        }
    }
}

#[repr(u8)]
#[derive(Debug, Copy, Clone, PartialEq, BitFlags, Type)]
pub enum MessageFlags {
    /// This message does not expect method return replies or error replies, even if it is of a type
    /// that can have a reply; the reply should be omitted.
    ///
    /// Note that `MessageType::MethodCall` is the only message type currently defined in the
    /// specification that can expect a reply, so the presence or absence of this flag in the other
    /// three message types that are currently documented is meaningless: replies to those message
    /// types should not be sent, whether this flag is present or not.
    NoReplyExpected = 0x1,
    /// The bus must not launch an owner for the destination name in response to this message.
    NoAutoStart = 0x2,
    /// This flag may be set on a method call message to inform the receiving side that the caller
    /// is prepared to wait for interactive authorization, which might take a considerable time to
    /// complete. For instance, if this flag is set, it would be appropriate to query the user for
    /// passwords or confirmation via Polkit or a similar framework.
    AllowInteractiveAuth = 0x4,
}

#[derive(Debug, Serialize, Deserialize, Type)]
pub struct MessagePrimaryHeader {
    endian_sig: EndianSig,
    msg_type: MessageType,
    flags: BitFlags<MessageFlags>,
    protocol_version: u8,
    body_len: u32,
    serial_num: u32,
}

#[derive(Debug, Serialize, Deserialize, Type)]
pub struct MessageHeader<'m> {
    primary: MessagePrimaryHeader,
    #[serde(borrow)]
    fields: MessageFields<'m>,
    end: ((),), // To ensure header end on 8-byte boundry
}

impl MessagePrimaryHeader {
    pub fn new(msg_type: MessageType, body_len: u32) -> Self {
        Self {
            endian_sig: NATIVE_ENDIAN_SIG,
            msg_type,
            flags: BitFlags::empty(),
            protocol_version: 1,
            body_len,
            serial_num: u32::max_value(),
        }
    }
    pub fn endian_sig(&self) -> EndianSig {
        self.endian_sig
    }

    pub fn set_endian_sig(&mut self, sig: EndianSig) {
        self.endian_sig = sig;
    }

    pub fn msg_type(&self) -> MessageType {
        self.msg_type
    }

    pub fn set_msg_type(&mut self, msg_type: MessageType) {
        self.msg_type = msg_type;
    }

    pub fn flags(&self) -> BitFlags<MessageFlags> {
        self.flags
    }

    pub fn set_flags(&mut self, flags: BitFlags<MessageFlags>) {
        self.flags = flags;
    }

    pub fn protocol_version(&self) -> u8 {
        self.protocol_version
    }

    pub fn set_protocol_version(&mut self, version: u8) {
        self.protocol_version = version;
    }

    pub fn body_len(&self) -> u32 {
        self.body_len
    }

    pub fn set_body_len(&mut self, len: u32) {
        self.body_len = len;
    }

    pub fn serial_num(&self) -> u32 {
        self.serial_num
    }

    pub fn set_serial_num(&mut self, serial: u32) {
        self.serial_num = serial;
    }
}

impl<'m> MessageHeader<'m> {
    pub fn new(primary: MessagePrimaryHeader, fields: MessageFields<'m>) -> Self {
        Self {
            primary,
            fields,
            end: ((),),
        }
    }

    pub fn primary(&self) -> &MessagePrimaryHeader {
        &self.primary
    }

    pub fn primary_mut(&mut self) -> &mut MessagePrimaryHeader {
        &mut self.primary
    }

    pub fn into_primary(self) -> MessagePrimaryHeader {
        self.primary
    }

    pub fn fields<'s>(&'s self) -> &'s MessageFields<'m> {
        &self.fields
    }

    pub fn fields_mut<'s>(&'s mut self) -> &'s mut MessageFields<'m> {
        &mut self.fields
    }

    pub fn into_fields(self) -> MessageFields<'m> {
        self.fields
    }

    /// The message type
    pub fn message_type(&self) -> Result<MessageType, MessageError> {
        Ok(self.primary().msg_type())
    }

    /// The object to send a call to, or the object a signal is emitted from.
    pub fn path(&self) -> Result<Option<ObjectPath>, MessageError> {
        match self.fields().get_field(MessageFieldCode::Path) {
            Some(MessageField::Path(path)) => Ok(Some(path.clone())),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The interface to invoke a method call on, or that a signal is emitted from.
    pub fn interface(&self) -> Result<Option<&str>, MessageError> {
        match self.fields().get_field(MessageFieldCode::Interface) {
            Some(MessageField::Interface(interface)) => Ok(Some(&interface)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The member, either the method name or signal name.
    pub fn member(&self) -> Result<Option<&str>, MessageError> {
        match self.fields().get_field(MessageFieldCode::Member) {
            Some(MessageField::Member(member)) => Ok(Some(&member)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The name of the error that occurred, for errors.
    pub fn error_name(&self) -> Result<Option<&str>, MessageError> {
        match self.fields().get_field(MessageFieldCode::ErrorName) {
            Some(MessageField::ErrorName(error_name)) => Ok(Some(&error_name)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The serial number of the message this message is a reply to.
    pub fn reply_serial(&self) -> Result<Option<u32>, MessageError> {
        match self.fields().get_field(MessageFieldCode::ReplySerial) {
            Some(MessageField::ReplySerial(reply_serial)) => Ok(Some(*reply_serial)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The name of the connection this message is intended for.
    pub fn destination(&self) -> Result<Option<&str>, MessageError> {
        match self.fields().get_field(MessageFieldCode::Destination) {
            Some(MessageField::Destination(destination)) => Ok(Some(&destination)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// Unique name of the sending connection.
    pub fn sender(&self) -> Result<Option<&str>, MessageError> {
        match self.fields().get_field(MessageFieldCode::Sender) {
            Some(MessageField::Sender(sender)) => Ok(Some(&sender)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The signature of the message body.
    pub fn signature(&self) -> Result<Option<Signature>, MessageError> {
        match self.fields().get_field(MessageFieldCode::Signature) {
            Some(MessageField::Signature(signature)) => Ok(Some(signature.clone())),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }

    /// The number of Unix file descriptors that accompany the message.
    pub fn unix_fds(&self) -> Result<Option<u32>, MessageError> {
        match self.fields().get_field(MessageFieldCode::UnixFDs) {
            Some(MessageField::UnixFDs(fds)) => Ok(Some(*fds)),
            Some(_) => Err(MessageError::InvalidField),
            None => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{MessageField, MessageFields, MessageHeader, MessagePrimaryHeader, MessageType};

    use std::convert::TryFrom;
    use std::error::Error;
    use std::result::Result;
    use zvariant::{ObjectPath, Signature};

    #[test]
    fn header() -> Result<(), Box<dyn Error>> {
        let path = ObjectPath::try_from("/some/path")?;
        let mut f = MessageFields::new();
        f.add(MessageField::Path(path.clone()));
        f.add(MessageField::Interface("some.interface".into()));
        f.add(MessageField::Member("Member".into()));
        f.add(MessageField::Sender(":1.84".into()));
        let h = MessageHeader::new(MessagePrimaryHeader::new(MessageType::Signal, 77), f);

        assert_eq!(h.message_type()?, MessageType::Signal);
        assert_eq!(h.path()?, Some(path));
        assert_eq!(h.interface()?, Some("some.interface".into()));
        assert_eq!(h.member()?, Some("Member".into()));
        assert_eq!(h.error_name()?, None);
        assert_eq!(h.destination()?, None);
        assert_eq!(h.reply_serial()?, None);
        assert_eq!(h.sender()?, Some(":1.84".into()));
        assert_eq!(h.signature()?, None);
        assert_eq!(h.unix_fds()?, None);

        let mut f = MessageFields::new();
        f.add(MessageField::ErrorName("org.zbus.Error".into()));
        f.add(MessageField::Destination(":1.11".into()));
        f.add(MessageField::ReplySerial(88));
        f.add(MessageField::Signature(Signature::from_str_unchecked(
            "say",
        )));
        f.add(MessageField::UnixFDs(12));
        let h = MessageHeader::new(MessagePrimaryHeader::new(MessageType::MethodReturn, 77), f);

        assert_eq!(h.message_type()?, MessageType::MethodReturn);
        assert_eq!(h.path()?, None);
        assert_eq!(h.interface()?, None);
        assert_eq!(h.member()?, None);
        assert_eq!(h.error_name()?, Some("org.zbus.Error".into()));
        assert_eq!(h.destination()?, Some(":1.11".into()));
        assert_eq!(h.reply_serial()?, Some(88));
        assert_eq!(h.sender()?, None);
        assert_eq!(h.signature()?, Some(Signature::from_str_unchecked("say")));
        assert_eq!(h.unix_fds()?, Some(12));

        Ok(())
    }
}
