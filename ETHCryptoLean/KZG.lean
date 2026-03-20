/-
  KZG Point Evaluation Precompile (EIP-4844)
  Precompile address 0x0A for blob transaction verification.
-/

import ETHCryptoLean.BLS12381.Pairing
import ETHCryptoLean.SHA256

namespace KZG

open BLS12381

-- ═══════════════════════════════════════════
-- Constants
-- ═══════════════════════════════════════════

-- Number of field elements per blob (EIP-4844)
def FIELD_ELEMENTS_PER_BLOB : Nat := 4096

-- BLS modulus (the curve order r)
def BLS_MODULUS : Nat := R

-- Version byte for the versioned hash
def VERSIONED_HASH_VERSION_KZG : UInt8 := 0x01

-- ═══════════════════════════════════════════
-- KZG Verification
-- ═══════════════════════════════════════════

-- The KZG verification equation:
-- e(C - y·G1, G2_gen) == e(proof, s·G2 - z·G2_gen)
-- Equivalently:
-- e(C - y·G1, G2_gen) · e(-proof, s·G2 - z·G2_gen) == 1
--
-- Where:
-- - C is the commitment (G1 point)
-- - y is the claimed evaluation (scalar)
-- - z is the evaluation point (scalar)
-- - proof is the KZG proof (G1 point)
-- - G1 is the G1 generator
-- - G2_gen is the G2 generator
-- - s·G2 is from the trusted setup

-- KZG verification given all components
-- sG2 is the trusted setup point s·G2_gen
def kzgVerify
    (commitment : G1Point)
    (z : Nat)
    (y : Nat)
    (proof : G1Point)
    (sG2 : G2Point) : Bool :=
  -- P1 = C - y·G1
  let yG1 := g1ScalarMul (y % R) G1_GEN
  let p1 := g1Add commitment (g1Neg yG1)
  -- Q1 = G2_gen
  let q1 := G2_GEN
  -- P2 = -proof
  let p2 := g1Neg proof
  -- Q2 = s·G2 - z·G2_gen
  let zG2 := g2ScalarMul (z % R) G2_GEN
  let q2 := g2Add sG2 (g2Neg zG2)
  -- Check: e(P1, Q1) · e(P2, Q2) == 1
  pairingCheck p1 q1 p2 q2

-- ═══════════════════════════════════════════
-- Versioned hash
-- ═══════════════════════════════════════════

-- Compute versioned hash from commitment bytes
-- SHA256(commitment)[1:] with version byte 0x01 prepended
def versionedHash (commitmentBytes : Array UInt8) : Array UInt8 :=
  let h := SHA256.hash commitmentBytes
  -- Replace first byte with version byte
  if h.size >= 32 then
    let h := h.set! 0 VERSIONED_HASH_VERSION_KZG.toNat.toUInt8
    h.extract 0 32
  else
    h  -- shouldn't happen with valid SHA256

-- ═══════════════════════════════════════════
-- Precompile interface
-- ═══════════════════════════════════════════

-- Convert Nat to 32-byte big-endian
private def natTo32BytesBE (n : Nat) : Array UInt8 :=
  natToBytesBE n 32

-- Success output: FIELD_ELEMENTS_PER_BLOB and BLS_MODULUS as 32-byte big-endian values
private def successOutput : Array UInt8 :=
  natTo32BytesBE FIELD_ELEMENTS_PER_BLOB ++ natTo32BytesBE BLS_MODULUS

/--
  KZG point evaluation precompile (EIP-4844, address 0x0A).

  Input (192 bytes):
  - Bytes 0-31:    versioned hash
  - Bytes 32-63:   z (evaluation point, big-endian scalar)
  - Bytes 64-95:   y (claimed evaluation, big-endian scalar)
  - Bytes 96-143:  commitment C (48-byte compressed G1 point)
  - Bytes 144-191: proof π (48-byte compressed G1 point)

  Output on success: 64 bytes
  - Bytes 0-31:  FIELD_ELEMENTS_PER_BLOB (= 4096, big-endian)
  - Bytes 32-63: BLS_MODULUS (= r, big-endian)

  Returns none on failure.

  Note: This function is parameterized by `sG2`, the trusted setup point s·G2.
  In a full deployment, this would come from the Ethereum KZG ceremony.
-/
def pointEvaluation (input : Array UInt8) (sG2 : G2Point) : Option (Array UInt8) :=
  -- Check input length
  if input.size != 192 then none
  else
    -- Parse versioned hash
    let vHash := input.extract 0 32

    -- Parse z (evaluation point)
    let zBytes := input.extract 32 64
    let z := bytesToNatBE zBytes

    -- Parse y (claimed evaluation)
    let yBytes := input.extract 64 96
    let y := bytesToNatBE yBytes

    -- Check z < BLS_MODULUS and y < BLS_MODULUS
    if z >= BLS_MODULUS then none
    else if y >= BLS_MODULUS then none
    else
      -- Parse commitment (48-byte compressed G1)
      let commitmentBytes := input.extract 96 144
      match g1Decompress commitmentBytes with
      | none => none
      | some commitment =>
        -- Verify versioned hash matches commitment
        let expectedHash := versionedHash commitmentBytes
        if vHash != expectedHash then none
        else
          -- Parse proof (48-byte compressed G1)
          let proofBytes := input.extract 144 192
          match g1Decompress proofBytes with
          | none => none
          | some proof =>
            -- Verify KZG proof
            if kzgVerify commitment z y proof sG2 then
              some successOutput
            else
              none

end KZG
