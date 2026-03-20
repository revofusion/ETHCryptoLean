/-!
# Modular Exponentiation

EVM precompile at address 0x05. Computes `base^exp mod modulus` using
binary square-and-multiply.
-/

namespace ETHCryptoLean.ModExp

/-- Binary modular exponentiation: `base ^ exp % modulus`.
    Returns 0 if `modulus = 0`. -/
def modExp (base exp modulus : Nat) : Nat :=
  if modulus == 0 then 0
  else if modulus == 1 then 0
  else modExpGo (base % modulus) exp modulus 1
where
  modExpGo (base exp modulus acc : Nat) : Nat :=
    if h : exp = 0 then acc
    else
      let acc' := if exp % 2 == 1 then (acc * base) % modulus else acc
      modExpGo ((base * base) % modulus) (exp / 2) modulus acc'
  termination_by exp
  decreasing_by omega

/-- Read a big-endian unsigned integer from a byte array slice. -/
def bytesToNat (input : Array UInt8) (offset len : Nat) : Nat :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    if i >= len then acc
    else
      let idx := offset + i
      let b := if idx < input.size then input[idx]!.toNat else 0
      go (i + 1) (acc * 256 + b)
  go 0 0

/-- Write a natural number as big-endian bytes of a given length. -/
def natToBytes (n : Nat) (len : Nat) : Array UInt8 :=
  if len == 0 then #[]
  else
    let bytes := (List.range len).map (fun i =>
      let shift := (len - 1 - i) * 8
      ((n >>> shift) % 256).toUInt8)
    bytes.toArray

/-- Read a 32-byte big-endian value from the input, zero-padded if needed. -/
def read32 (input : Array UInt8) (offset : Nat) : Nat :=
  bytesToNat input offset 32

/-- EVM modexp precompile wrapper.

    Input format: 3×32-byte big-endian lengths (Bsize, Esize, Msize),
    followed by base (Bsize bytes), exp (Esize bytes), modulus (Msize bytes).
    Output: result as big-endian bytes, left-padded to Msize bytes. -/
def modExpPrecompile (input : Array UInt8) : Array UInt8 :=
  let bSize := read32 input 0
  let eSize := read32 input 32
  let mSize := read32 input 64
  let base := bytesToNat input 96 bSize
  let exp := bytesToNat input (96 + bSize) eSize
  let modulus := bytesToNat input (96 + bSize + eSize) mSize
  let result := modExp base exp modulus
  natToBytes result mSize

end ETHCryptoLean.ModExp
