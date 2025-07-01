//! This module defines a cryptographic abstraction layer for use in
//! hax protocol specifications.

use crate::ProtocolError;

/// An abstract Diffie-Hellman scalar.
#[derive(Clone)]
pub struct DHScalar(Vec<u8>);

impl DHScalar {
    /// Wrap bytes into a Diffie-Hellman scalar. Does *not* perform
    /// input validation.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        DHScalar(bytes.to_vec())
    }
}

/// An abstract Diffie-Hellman group element.
pub struct DHElement(Vec<u8>);

impl DHElement {
    /// Wrap bytes into a Diffie-Hellman group element. Does *not* perform
    /// input validation.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        DHElement(bytes.to_vec())
    }
}

/// Choice of Diffie-Hellman groups.
pub enum DHGroup {
    X25519,
    X448,
    P256,
    P384,
    P521,
}

impl From<DHGroup> for libcrux::ecdh::Algorithm {
    /// Converter to `libcrux` type.
    fn from(value: DHGroup) -> Self {
        match value {
            DHGroup::X25519 => libcrux::ecdh::Algorithm::X25519,
            DHGroup::X448 => libcrux::ecdh::Algorithm::X448,
            DHGroup::P256 => libcrux::ecdh::Algorithm::P256,
            DHGroup::P384 => libcrux::ecdh::Algorithm::P384,
            DHGroup::P521 => libcrux::ecdh::Algorithm::P521,
        }
    }
}

/// Scalar multiplication of `scalar` and `element`.
pub fn dh_scalar_multiply(group: DHGroup, scalar: DHScalar, element: DHElement) -> Vec<u8> {
    libcrux::ecdh::derive(group.into(), element.0, scalar.0).unwrap()
}

/// Scalar multiplication of a fixed generator and `scalar`.
pub fn dh_scalar_multiply_base(group: DHGroup, scalar: DHScalar) -> Vec<u8> {
    libcrux::ecdh::secret_to_public(group.into(), scalar.0).unwrap()
}

/// An abstract AEAD key.
pub struct AEADKey(libcrux::aead::Key);

/// Choice of AEAD algorithms.
pub enum AEADAlgorithm {
    Aes128Gcm,
    Aes256Gcm,
    Chacha20Poly1305,
}

impl From<AEADAlgorithm> for libcrux::aead::Algorithm {
    /// Converter to `libcrux` type.
    fn from(value: AEADAlgorithm) -> Self {
        match value {
            AEADAlgorithm::Aes128Gcm => libcrux::aead::Algorithm::Aes128Gcm,
            AEADAlgorithm::Aes256Gcm => libcrux::aead::Algorithm::Aes256Gcm,
            AEADAlgorithm::Chacha20Poly1305 => libcrux::aead::Algorithm::Chacha20Poly1305,
        }
    }
}

impl AEADKey {
    /// Attempt deserialization of `bytes` into an AEAD key for
    /// `algorithm`. Panics on failure.
    pub fn from_bytes(algorithm: AEADAlgorithm, bytes: &[u8]) -> Self {
        AEADKey(libcrux::aead::Key::from_bytes(algorithm.into(), bytes.to_vec()).unwrap())
    }
}

/// An abstract AEAD initialization vector.
pub struct AEADIV(libcrux::aead::Iv);

impl AEADIV {
    /// Attempt construction of an AEAD IV from `bytes`. Panics if
    /// number of `bytes` is insufficient.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        AEADIV(libcrux::aead::Iv::new(bytes).unwrap())
    }
}

/// An abstract AEAD authentication tag.
pub struct AEADTag(libcrux::aead::Tag);
impl AEADTag {
    /// Attempt deserialization of an AEAD tag from `bytes`. Panics if
    /// number of `bytes` is insufficient.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let bytes: [u8; 16] = bytes.try_into().unwrap();
        AEADTag(libcrux::aead::Tag::from(bytes))
    }
}

/// Abstract AEAD encryption using `algorithm`. Returns a pair of byte
/// vectors `(ciphertext, tag)`.
pub fn aead_encrypt(key: AEADKey, iv: AEADIV, aad: &[u8], plain: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let (tag, cip) = libcrux::aead::encrypt_detached(&key.0, plain, iv.0, aad).unwrap();
    (cip, tag.as_ref().to_vec())
}

/// Abstract AEAD decryption using `algorithm`. On success returns the
/// decrypted plaintext, otherwise a `CryptoError`.
pub fn aead_decrypt(
    key: AEADKey,
    iv: AEADIV,
    aad: &[u8],
    cip: &[u8],
    tag: AEADTag,
) -> Result<Vec<u8>, ProtocolError> {
    libcrux::aead::decrypt_detached(&key.0, cip, iv.0, aad, &tag.0)
        .map_err(|_| ProtocolError::CryptoError)
}

/// Choice of hashing algorithms.
pub enum HashAlgorithm {
    Sha1,
    Sha224,
    Sha256,
    Sha384,
    Sha512,
    Blake2s,
    Blake2b,
    Sha3_224,
    Sha3_256,
    Sha3_384,
    Sha3_512,
}

impl From<HashAlgorithm> for libcrux::digest::Algorithm {
    /// Converter to `libcrux` type.
    fn from(value: HashAlgorithm) -> Self {
        match value {
            HashAlgorithm::Sha1 => libcrux::digest::Algorithm::Sha1,
            HashAlgorithm::Sha224 => libcrux::digest::Algorithm::Sha224,
            HashAlgorithm::Sha256 => libcrux::digest::Algorithm::Sha256,
            HashAlgorithm::Sha384 => libcrux::digest::Algorithm::Sha384,
            HashAlgorithm::Sha512 => libcrux::digest::Algorithm::Sha512,
            HashAlgorithm::Blake2s => libcrux::digest::Algorithm::Blake2s,
            HashAlgorithm::Blake2b => libcrux::digest::Algorithm::Blake2b,
            HashAlgorithm::Sha3_224 => libcrux::digest::Algorithm::Sha3_224,
            HashAlgorithm::Sha3_256 => libcrux::digest::Algorithm::Sha3_256,
            HashAlgorithm::Sha3_384 => libcrux::digest::Algorithm::Sha3_384,
            HashAlgorithm::Sha3_512 => libcrux::digest::Algorithm::Sha3_512,
        }
    }
}

/// Abstract hashing using `algorithm`.
pub fn hash(algorithm: HashAlgorithm, input: &[u8]) -> Vec<u8> {
    libcrux::digest::hash(algorithm.into(), input)
}

/// Choice of algorithms for instantiation of HMAC.
pub enum HMACAlgorithm {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

impl From<HMACAlgorithm> for libcrux::hmac::Algorithm {
    /// Converter to `libcrux` type.
    fn from(value: HMACAlgorithm) -> Self {
        match value {
            HMACAlgorithm::Sha1 => libcrux::hmac::Algorithm::Sha1,
            HMACAlgorithm::Sha256 => libcrux::hmac::Algorithm::Sha256,
            HMACAlgorithm::Sha384 => libcrux::hmac::Algorithm::Sha384,
            HMACAlgorithm::Sha512 => libcrux::hmac::Algorithm::Sha512,
        }
    }
}

/// Abstract HMAC using `algorithm` as the hash function.
pub fn hmac(algorithm: HMACAlgorithm, key: &[u8], input: &[u8]) -> Vec<u8> {
    libcrux::hmac::hmac(algorithm.into(), key, input, None)
}
