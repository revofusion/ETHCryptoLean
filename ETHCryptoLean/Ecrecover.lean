/-
  ECDSA public key recovery (ecrecover) for secp256k1.
  Pure Lean 4 implementation of Ethereum's ecrecover precompile.

  Given a message hash and signature (v, r, s), recovers the
  signer's Ethereum address. No FFI, no opaque, no axiom.
-/
import ETHCryptoLean.UInt256
import ETHCryptoLean.Keccak256
import ETHCryptoLean.Secp256k1

open Secp256k1

/-- Convert a recovered public key point to an Ethereum address.
    Address = last 20 bytes of keccak256(x_bytes ++ y_bytes). -/
def pubkeyToAddress (pt : Point) : Option UInt256 :=
  match pt with
  | Point.infinity => none
  | Point.affine x y =>
    let xBytes := List.range 32 |>.map fun i =>
      UInt8.ofNat ((x >>> ((31 - i) * 8)) &&& 0xFF)
    let yBytes := List.range 32 |>.map fun i =>
      UInt8.ofNat ((y >>> ((31 - i) * 8)) &&& 0xFF)
    let pubkeyBytes := (xBytes ++ yBytes).toArray
    let hash := Keccak.keccak256 pubkeyBytes
    let hashNum := hash.foldl (fun acc b => acc * 256 + b.toNat) 0
    let mask := 2^160 - 1
    let addr := hashNum &&& mask
    some (UInt256.ofNat addr)

/-- ECDSA public key recovery.

    Given:
    - hash: the message hash (32 bytes as UInt256)
    - v: recovery id (27 or 28 in Ethereum)
    - r: signature r value
    - s: signature s value

    Returns the recovered Ethereum address, or none if invalid.

    Algorithm:
    1. Validate: r, s ∈ [1, n-1], v ∈ {27, 28}
    2. Compute R = point with x-coordinate r and y parity from v
    3. Compute u1 = (-hash · r⁻¹) mod n
    4. Compute u2 = (s · r⁻¹) mod n
    5. Recover Q = u1·G + u2·R
    6. Return keccak256(Q) masked to 20 bytes -/
def ecrecover (hash : UInt256) (v : UInt256) (r : UInt256) (s : UInt256) : Option UInt256 := do
  let hashN := hash.toNat
  let vN := v.toNat
  let rN := r.toNat
  let sN := s.toNat
  guard (vN == 27 || vN == 28)
  guard (rN >= 1 && rN <= Secp256k1.n - 1)
  guard (sN >= 1 && sN <= Secp256k1.n - 1)
  let recId := vN - 27
  let yParity := recId
  let y ← computeYFromX rN yParity
  let rPoint := Point.affine rN y
  guard (isOnCurve rPoint)
  let rInv := modInv rN Secp256k1.n
  guard (rInv != 0)
  let u1 := modMul (Secp256k1.n - (hashN % Secp256k1.n)) rInv Secp256k1.n
  let u2 := modMul sN rInv Secp256k1.n
  let q1 := scalarMul u1 G
  let q2 := scalarMul u2 rPoint
  let pubkey := pointAdd q1 q2
  match pubkey with
  | Point.infinity => none
  | _ => pubkeyToAddress pubkey
