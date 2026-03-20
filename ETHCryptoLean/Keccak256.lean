/-
  Keccak-256 hash function — pure Lean 4 implementation.

  This is the Ethereum variant (Keccak padding 0x01), NOT NIST SHA-3 (0x06).
  Implements the full Keccak sponge construction with Keccak-f[1600]:
    - State: 5×5 array of 64-bit words (1600 bits)
    - Rate: 1088 bits (136 bytes)
    - Capacity: 512 bits
    - 24 rounds: θ, ρ, π, χ, ι
-/
import ETHCryptoLean.UInt256

namespace Keccak

abbrev State := Array UInt64

def emptyState : State := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

@[inline] def stIdx (x y : Nat) : Nat := (x % 5) + 5 * (y % 5)

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

def rotationOffsets : Array Nat := #[
   0, 36,  3, 41, 18,
   1, 44, 10, 45,  2,
  62,  6, 43, 15, 61,
  28, 55, 25, 21, 56,
  27, 20, 39,  8, 14
]

@[inline] def rotl64 (x : UInt64) (n : Nat) : UInt64 :=
  let n := n % 64
  if n == 0 then x
  else (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

def theta (st : State) : State := Id.run do
  let mut c : Array UInt64 := #[0,0,0,0,0]
  for x in [:5] do
    c := c.set! x (st[stIdx x 0]! ^^^ st[stIdx x 1]! ^^^ st[stIdx x 2]! ^^^ st[stIdx x 3]! ^^^ st[stIdx x 4]!)
  let mut d : Array UInt64 := #[0,0,0,0,0]
  for x in [:5] do
    d := d.set! x (c[(x + 4) % 5]! ^^^ rotl64 c[(x + 1) % 5]! 1)
  let mut result := st
  for i in [:25] do
    let x := i % 5
    result := result.set! i (st[i]! ^^^ d[x]!)
  return result

def rhoPi (st : State) : State := Id.run do
  let mut result := emptyState
  for x in [:5] do
    for y in [:5] do
      let newX := y
      let newY := (2 * x + 3 * y) % 5
      let rot := rotationOffsets[x * 5 + y]!
      result := result.set! (stIdx newX newY) (rotl64 st[stIdx x y]! rot)
  return result

def chi (st : State) : State := Id.run do
  let mut result := emptyState
  for y in [:5] do
    for x in [:5] do
      let idx := stIdx x y
      let v := st[idx]! ^^^ ((~~~ st[stIdx ((x+1)%5) y]!) &&& st[stIdx ((x+2)%5) y]!)
      result := result.set! idx v
  return result

def iota (st : State) (round : Nat) : State :=
  st.set! 0 (st[0]! ^^^ roundConstants[round]!)

def keccakRound (st : State) (round : Nat) : State :=
  iota (chi (rhoPi (theta st))) round

def keccakF (st : State) : State := Id.run do
  let mut s := st
  for i in [:24] do
    s := keccakRound s i
  return s

def absorbBlock (st : State) (block : Array UInt64) (rateWords : Nat) : State := Id.run do
  let mut s := st
  for i in [:min rateWords block.size] do
    s := s.set! i (s[i]! ^^^ block[i]!)
  return s

def bytesToWords (bytes : Array UInt8) : Array UInt64 := Id.run do
  let numWords := (bytes.size + 7) / 8
  let mut result : Array UInt64 := #[]
  for i in [:numWords] do
    let mut w : UInt64 := 0
    for j in [:8] do
      let idx := i * 8 + j
      if h : idx < bytes.size then
        w := w ||| ((bytes[idx]).toUInt64 <<< (j * 8).toUInt64)
    result := result.push w
  return result

def wordsToBytes (words : Array UInt64) (numBytes : Nat) : Array UInt8 := Id.run do
  let mut result : Array UInt8 := #[]
  for i in [:numBytes] do
    let wordIdx := i / 8
    let byteIdx := i % 8
    if h : wordIdx < words.size then
      result := result.push ((words[wordIdx] >>> (byteIdx * 8).toUInt64).toUInt8)
    else
      result := result.push 0
  return result

def padMessage (msg : Array UInt8) (rateBytes : Nat) : Array UInt8 := Id.run do
  let msgLen := msg.size
  let r := msgLen % rateBytes
  let padLen := if r == rateBytes - 1 then rateBytes + 1 else rateBytes - r
  let mut padded := msg
  padded := padded.push 0x01
  for _ in [:padLen - 2] do
    padded := padded.push 0x00
  padded := padded.push 0x80
  return padded

/-- Keccak-256: arbitrary-length byte input → 32-byte output.
    Ethereum variant (Keccak padding 0x01), not NIST SHA-3. -/
def keccak256 (msg : Array UInt8) : Array UInt8 := Id.run do
  let rateBytes : Nat := 136
  let rateWords : Nat := 17
  let padded := padMessage msg rateBytes
  let numBlocks := padded.size / rateBytes
  let mut st := emptyState
  for blockIdx in [:numBlocks] do
    let mut blockBytes : Array UInt8 := #[]
    for i in [:rateBytes] do
      blockBytes := blockBytes.push padded[blockIdx * rateBytes + i]!
    let blockWords := bytesToWords blockBytes
    st := absorbBlock st blockWords rateWords
    st := keccakF st
  return wordsToBytes st 32

end Keccak

namespace UInt256

/-- Keccak-256 of a byte array, returning UInt256 (big-endian). -/
def keccak256Bytes (bytes : Array UInt8) : UInt256 :=
  let hash := Keccak.keccak256 bytes
  let n := hash.foldl (fun acc b => acc * 256 + b.toNat) 0
  UInt256.ofNat n

end UInt256
