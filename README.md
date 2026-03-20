# ETHCryptoLean

Pure Lean 4 implementations of every EVM precompiled contract cryptographic primitive. No FFI, no opaque definitions, no axioms. Everything is transparent and amenable to formal reasoning.

## Primitives

| Primitive | EVM Precompile | File |
|-----------|---------------|------|
| ecrecover (secp256k1 ECDSA recovery) | 0x01 | `Ecrecover.lean` + `Secp256k1.lean` |
| SHA-256 | 0x02 | `SHA256.lean` |
| RIPEMD-160 | 0x03 | `RIPEMD160.lean` |
| ModExp (modular exponentiation) | 0x05 | `ModExp.lean` |
| alt_bn128 point addition | 0x06 | `BN256.lean` |
| alt_bn128 scalar multiplication | 0x07 | `BN256.lean` |
| alt_bn128 pairing check | 0x08 | `BN256.lean` |
| BLAKE2f compression | 0x09 | `Blake2f.lean` |
| KZG point evaluation (BLS12-381) | 0x0A | `KZG.lean` + `BLS12381/` |
| Keccak-256 | opcode 0x20 | `Keccak256.lean` |

## Why pure Lean?

These primitives are typically implemented as opaque FFI bindings that call out to C or Python. That's fast, but you can't prove anything about them since they're black boxes to the type checker.

With pure Lean implementations, you can:
- Prove correctness properties against known test vectors
- Reason about smart contract behavior that depends on hashing or signatures
- Verify that ecrecover returns the right signer in formal verification of permit flows
- Eliminate opaque axioms from your verification model

The tradeoff is performance. These are not optimized for speed, they're optimized for transparency.

## Usage

```lean
import ETHCryptoLean

-- Keccak-256
#eval Keccak.keccak256 "hello".toUTF8.data

-- SHA-256
#eval SHA256.hash "hello".toUTF8.data

-- ecrecover
#eval ecrecover hash v r s

-- ModExp
#eval ETHCryptoLean.ModExp.modExp 2 10 1000

-- alt_bn128 point addition
#eval ETHCryptoLean.BN256.ecAdd p1x p1y p2x p2y

-- BLS12-381 pairing
#eval BLS12381.pairingCheck p1 q1 p2 q2
```

## Tests

```bash
lake build Test
```

The test suite validates UInt256 arithmetic, Keccak-256, SHA-256, RIPEMD-160, ModExp, BLAKE2f, secp256k1, ecrecover, BLS12-381, and alt_bn128 against known test vectors.

## Structure

```
ETHCryptoLean/
  UInt256.lean          256-bit integer type
  Keccak256.lean        Keccak-256 sponge construction
  SHA256.lean           SHA-256 (FIPS 180-4)
  RIPEMD160.lean        RIPEMD-160
  ModExp.lean           Modular exponentiation
  Blake2f.lean          BLAKE2b compression function
  Secp256k1.lean        secp256k1 curve arithmetic
  Ecrecover.lean        ECDSA recovery
  BN256.lean            alt_bn128 curve + pairing
  BLS12381/
    Fields.lean         Fp, Fp2, Fp6, Fp12 tower
    Curve.lean          G1, G2 point operations
    Pairing.lean        Optimal Ate pairing
  KZG.lean              KZG point evaluation (EIP-4844)
Test.lean               Test vectors for all primitives
```

## License

MIT
