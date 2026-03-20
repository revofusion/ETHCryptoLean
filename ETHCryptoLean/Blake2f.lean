/-!
# BLAKE2b Compression Function

EIP-152 BLAKE2b F compression function. EVM precompile at address 0x09.
-/

namespace ETHCryptoLean.Blake2f

/-- BLAKE2b IV constants. -/
def iv : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
  0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f,
  0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
]

/-- BLAKE2b sigma permutation table (10 rows × 16 entries). -/
def sigma : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
]

/-- Rotate right for UInt64. -/
@[inline] def rotr64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- BLAKE2b G mixing function. -/
@[inline] def gMix (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va := v[a]! + v[b]! + x
  let v := v.set! a va
  let vd := rotr64 (v[d]! ^^^ va) 32
  let v := v.set! d vd
  let vc := v[c]! + vd
  let v := v.set! c vc
  let vb := rotr64 (v[b]! ^^^ vc) 24
  let v := v.set! b vb
  let va2 := v[a]! + vb + y
  let v := v.set! a va2
  let vd2 := rotr64 (v[d]! ^^^ va2) 16
  let v := v.set! d vd2
  let vc2 := v[c]! + vd2
  let v := v.set! c vc2
  let vb2 := rotr64 (v[b]! ^^^ vc2) 63
  v.set! b vb2

/-- BLAKE2b compression function.

    - `rounds`: number of rounds
    - `h`: state vector (8 × UInt64)
    - `m`: message block (16 × UInt64)
    - `t0`, `t1`: counter values
    - `f`: finalization flag -/
def blake2Compress (rounds : Nat) (h : Array UInt64) (m : Array UInt64)
    (t0 t1 : UInt64) (f : Bool) : Array UInt64 :=
  -- Initialize working vector v[0..15]
  let v := h  -- v[0..7] = h[0..7]
    |>.push iv[0]!    -- v[8]
    |>.push iv[1]!    -- v[9]
    |>.push (iv[2]! ^^^ t0)  -- v[10]
    |>.push (iv[3]! ^^^ t1)  -- v[11]
    |>.push (iv[4]! ^^^ (if f then 0xFFFFFFFFFFFFFFFF else 0))  -- v[12]
    |>.push iv[5]!    -- v[13]
    |>.push iv[6]!    -- v[14]
    |>.push iv[7]!    -- v[15]

  -- Perform rounds
  let v := (List.range rounds).foldl (fun v i =>
    let s := sigma[i % 10]!
    -- Column step
    let v := gMix v 0 4 8  12 m[s[0]!]!  m[s[1]!]!
    let v := gMix v 1 5 9  13 m[s[2]!]!  m[s[3]!]!
    let v := gMix v 2 6 10 14 m[s[4]!]!  m[s[5]!]!
    let v := gMix v 3 7 11 15 m[s[6]!]!  m[s[7]!]!
    -- Diagonal step
    let v := gMix v 0 5 10 15 m[s[8]!]!  m[s[9]!]!
    let v := gMix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    let v := gMix v 2 7 8  13 m[s[12]!]! m[s[13]!]!
    let v := gMix v 3 4 9  14 m[s[14]!]! m[s[15]!]!
    v) v

  -- Finalize: h'[i] = h[i] XOR v[i] XOR v[i+8]
  (List.range 8).foldl (fun result i =>
    result.push (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)) #[]

/-- Read a little-endian UInt64 from 8 bytes. -/
def readLE64 (data : Array UInt8) (offset : Nat) : UInt64 :=
  let get (i : Nat) : UInt64 :=
    if offset + i < data.size then data[offset + i]!.toUInt64 else 0
  get 0 ||| (get 1 <<< 8) ||| (get 2 <<< 16) ||| (get 3 <<< 24) |||
  (get 4 <<< 32) ||| (get 5 <<< 40) ||| (get 6 <<< 48) ||| (get 7 <<< 56)

/-- Write a UInt64 as 8 little-endian bytes. -/
def writeLE64 (x : UInt64) : Array UInt8 := #[
  x.toUInt8,
  (x >>> 8).toUInt8,
  (x >>> 16).toUInt8,
  (x >>> 24).toUInt8,
  (x >>> 32).toUInt8,
  (x >>> 40).toUInt8,
  (x >>> 48).toUInt8,
  (x >>> 56).toUInt8
]

/-- Read a big-endian UInt32 (as Nat) from 4 bytes. -/
def readBE32Nat (data : Array UInt8) (offset : Nat) : Nat :=
  let get (i : Nat) : Nat :=
    if offset + i < data.size then data[offset + i]!.toNat else 0
  (get 0 * 256 + get 1) * 256 * 256 + (get 2 * 256 + get 3)

/-- BLAKE2b F compression function precompile (EIP-152).

    Input: exactly 213 bytes:
    - 4 bytes: rounds (big-endian uint32)
    - 64 bytes: h (8 × little-endian uint64)
    - 128 bytes: m (16 × little-endian uint64)
    - 8 bytes: t0 (little-endian uint64)
    - 8 bytes: t1 (little-endian uint64)
    - 1 byte: f (must be 0 or 1)

    Returns `none` if input is invalid. -/
def blake2FPrecompile (input : Array UInt8) : Option (Array UInt8) := do
  -- Must be exactly 213 bytes
  guard (input.size == 213)

  let rounds := readBE32Nat input 0

  -- Read h (8 × UInt64, little-endian, starting at offset 4)
  let h := (List.range 8).foldl (fun arr i =>
    arr.push (readLE64 input (4 + i * 8))) #[]

  -- Read m (16 × UInt64, little-endian, starting at offset 68)
  let m := (List.range 16).foldl (fun arr i =>
    arr.push (readLE64 input (68 + i * 8))) #[]

  -- Read t0, t1 (little-endian UInt64, at offsets 196 and 204)
  let t0 := readLE64 input 196
  let t1 := readLE64 input 204

  -- Read f flag (offset 212, must be 0 or 1)
  let fByte := input[212]!
  guard (fByte == 0 || fByte == 1)
  let f := fByte == 1

  let result := blake2Compress rounds h m t0 t1 f

  -- Output 64 bytes (8 × little-endian UInt64)
  some (result.foldl (fun acc w => acc ++ writeLE64 w) #[])

end ETHCryptoLean.Blake2f
