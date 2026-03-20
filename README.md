# ETHCryptoLean

Pure Lean 4 implementations of Ethereum's core cryptographic primitives. No FFI, no opaque definitions, no axioms. Everything is transparent and amenable to formal reasoning.

## What's here

**Keccak-256** is the hash function Ethereum uses everywhere: transaction hashes, storage slot computation, address derivation, event topics. This is the Keccak variant (padding byte `0x01`), not NIST SHA-3 (`0x06`). Full sponge construction with all five Keccak-f[1600] permutation steps, 24 rounds.

**secp256k1** is the elliptic curve Ethereum uses for signatures. Point addition, doubling, scalar multiplication (double-and-add), modular inverse via extended GCD. Includes the curve parameters, generator point G, and y-coordinate recovery from x.

**ecrecover** is Ethereum's ECDSA public key recovery precompile. Given a message hash and signature `(v, r, s)`, it recovers the signer's Ethereum address. This is what `ecrecover` does at EVM address `0x01` and what Solidity's `ECDSA.recover` wraps.

**UInt256** provides 256-bit unsigned integer arithmetic. Modular add/sub/mul/div, bitwise operations, big-endian byte conversion.

## Why pure Lean?

These primitives are typically implemented as opaque FFI bindings that call out to C or Python. That's fast, but you can't prove anything about them since they're black boxes to the type checker.

With pure Lean implementations, you can:
- Prove correctness properties (e.g., keccak256 matches the spec for known test vectors)
- Reason about smart contract behavior that depends on hashing or signatures
- Verify that ecrecover returns the right signer in formal verification of ERC-2612 permit flows
- Eliminate opaque axioms from your verification model

The tradeoff is performance. These are not optimized for speed, they're optimized for transparency.

## Usage

```lean
import ETHCryptoLean

-- Hash some bytes
#eval Keccak.keccak256 "hello".toUTF8.toArray |> bytesToHex

-- Recover a signer from a signature
#eval ecrecover hash v r s
```

## Test vectors

The test suite validates against known Ethereum test vectors:
- Keccak-256 of empty string, "abc", single zero byte
- Generator point on curve, scalar multiplication identity
- ecrecover with a known signature/address pair
- Rejection of invalid inputs (bad v, r=0, s=0)

```bash
lake build Test
```

## Structure

```
ETHCryptoLean/
  UInt256.lean      256-bit integer type
  Keccak256.lean    Keccak-256 sponge construction
  Secp256k1.lean    secp256k1 curve arithmetic
  Ecrecover.lean    ECDSA recovery (ecrecover precompile)
  Test.lean         Test vectors
```

## License

MIT
