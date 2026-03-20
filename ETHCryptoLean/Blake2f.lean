import ETHCryptoLean.Utils

open ETHCryptoLean.Utils

namespace ETHCryptoLean.Blake2f

-- BLAKE2b IV constants
def iv : Array UInt64 := #[
  0x6A09E667F3BCC908, 0xBB67AE8584CAA73B,
  0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
  0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
  0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179
]

/-- BLAKE2b sigma (precomputed message schedule permutations).
    Uses the Go go-ethereum layout where:
    - s[0..3]: first message word indices for columns 0-3
    - s[4..7]: second message word indices for columns 0-3
    - s[8..11]: first message word indices for diagonals 0-3
    - s[12..15]: second message word indices for diagonals 0-3 -/
def sigma : Array (Array UInt8) := #[
  #[0, 2, 4, 6, 1, 3, 5, 7, 8, 10, 12, 14, 9, 11, 13, 15],
  #[14, 4, 9, 13, 10, 8, 15, 6, 1, 0, 11, 5, 12, 2, 7, 3],
  #[11, 12, 5, 15, 8, 0, 2, 13, 10, 3, 7, 9, 14, 6, 1, 4],
  #[7, 3, 13, 11, 9, 1, 12, 14, 2, 5, 4, 15, 6, 10, 0, 8],
  #[9, 5, 2, 10, 0, 7, 4, 15, 14, 11, 6, 3, 1, 12, 8, 13],
  #[2, 6, 0, 8, 12, 10, 11, 3, 4, 7, 15, 1, 13, 5, 14, 9],
  #[12, 1, 14, 4, 5, 15, 13, 10, 0, 6, 9, 8, 7, 3, 2, 11],
  #[13, 7, 12, 3, 11, 14, 1, 9, 5, 15, 8, 2, 0, 4, 6, 10],
  #[6, 14, 11, 0, 15, 9, 3, 8, 12, 13, 1, 10, 2, 7, 4, 5],
  #[10, 8, 7, 1, 2, 4, 6, 5, 15, 9, 3, 13, 11, 14, 12, 0]
]

/-- Rotate a UInt64 right by `n` bits. -/
@[inline] def ror64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- The BLAKE2b G mixing half-round.
    Given a state vector `v` (16 UInt64s), mix positions (a,b,c,d) with message word `mx`.
    `r1` and `r2` are the two rotation amounts. -/
@[inline] def gHalf (v : Array UInt64) (a b c d : Nat) (mx : UInt64)
    (r1 r2 : UInt64) : Array UInt64 :=
  let va := v[a]! + mx + v[b]!
  let vd := ror64 (v[d]! ^^^ va) r1
  let vc := v[c]! + vd
  let vb := ror64 (v[b]! ^^^ vc) r2
  v |>.set! a va |>.set! b vb |>.set! c vc |>.set! d vd

/-- One round of BLAKE2b compression, matching the Go reference exactly.
    Uses the Go precomputed sigma table layout. -/
def round (v : Array UInt64) (m : Array UInt64) (s : Array UInt8) : Array UInt64 :=
  -- Column step, first half (rotations 32, 24)
  let v := gHalf v 0 4 8  12 (m[s[0]!.toNat]!) 32 24
  let v := gHalf v 1 5 9  13 (m[s[1]!.toNat]!) 32 24
  let v := gHalf v 2 6 10 14 (m[s[2]!.toNat]!) 32 24
  let v := gHalf v 3 7 11 15 (m[s[3]!.toNat]!) 32 24
  -- Column step, second half (rotations 16, 63)
  let v := gHalf v 0 4 8  12 (m[s[4]!.toNat]!) 16 63
  let v := gHalf v 1 5 9  13 (m[s[5]!.toNat]!) 16 63
  let v := gHalf v 2 6 10 14 (m[s[6]!.toNat]!) 16 63
  let v := gHalf v 3 7 11 15 (m[s[7]!.toNat]!) 16 63
  -- Diagonal step, first half (rotations 32, 24)
  let v := gHalf v 0 5 10 15 (m[s[8]!.toNat]!)  32 24
  let v := gHalf v 1 6 11 12 (m[s[9]!.toNat]!)  32 24
  let v := gHalf v 2 7 8  13 (m[s[10]!.toNat]!) 32 24
  let v := gHalf v 3 4 9  14 (m[s[11]!.toNat]!) 32 24
  -- Diagonal step, second half (rotations 16, 63)
  let v := gHalf v 0 5 10 15 (m[s[12]!.toNat]!) 16 63
  let v := gHalf v 1 6 11 12 (m[s[13]!.toNat]!) 16 63
  let v := gHalf v 2 7 8  13 (m[s[14]!.toNat]!) 16 63
  gHalf v 3 4 9  14 (m[s[15]!.toNat]!) 16 63

/-- The core BLAKE2b compression function `F`.
    - `h`: 8-element array of UInt64 (chain value)
    - `m`: 16-element array of UInt64 (message block)
    - `t0`, `t1`: counter values
    - `flag`: 0xFFFFFFFFFFFFFFFF if final block, 0 otherwise
    - `rounds`: number of rounds -/
def compress (h : Array UInt64) (m : Array UInt64) (t0 t1 : UInt64)
    (flag : UInt64) (rounds : Nat) : Array UInt64 :=
  -- Initialize working vector v[0..15]
  let v : Array UInt64 := #[
    h[0]!, h[1]!, h[2]!, h[3]!,
    h[4]!, h[5]!, h[6]!, h[7]!,
    iv[0]!, iv[1]!, iv[2]!, iv[3]!,
    iv[4]!, iv[5]!, iv[6]!, iv[7]!
  ]
  -- XOR counter and flag into v12..v14
  let v := v.set! 12 (v[12]! ^^^ t0)
  let v := v.set! 13 (v[13]! ^^^ t1)
  let v := v.set! 14 (v[14]! ^^^ flag)
  -- Run rounds
  let v := Nat.fold rounds (fun i _ (acc : Array UInt64) =>
    round acc m (sigma[i % 10]!)
  ) v
  -- Finalize: h[i] ^= v[i] ^ v[i+8]
  Array.ofFn fun (i : Fin 8) =>
    h[i.val]! ^^^ v[i.val]! ^^^ v[i.val + 8]!

/-- The BLAKE2b F compression precompile (EIP-152).
    Input: exactly 213 bytes.
    - bytes [0..3]: rounds (big-endian uint32)
    - bytes [4..67]: h (8 little-endian uint64s)
    - bytes [68..195]: m (16 little-endian uint64s)
    - bytes [196..203]: t0 (little-endian uint64)
    - bytes [204..211]: t1 (little-endian uint64)
    - byte [212]: f (0x01 for final, 0x00 for non-final)
    Returns: 64 bytes (8 little-endian uint64s) on success, or none on invalid input. -/
def blake2fPrecompile (input : ByteArray) : Option ByteArray :=
  if input.size != 213 then none
  else
    let rounds := (readBE32BA input 0).toNat
    -- Parse h (8 × uint64, little-endian)
    let h : Array UInt64 := Array.ofFn fun (i : Fin 8) => readLE64 input (4 + i.val * 8)
    -- Parse m (16 × uint64, little-endian)
    let m : Array UInt64 := Array.ofFn fun (i : Fin 16) => readLE64 input (68 + i.val * 8)
    -- Parse counters
    let t0 := readLE64 input 196
    let t1 := readLE64 input 204
    -- Parse final block flag
    let fByte := input[212]!
    if fByte != 0 && fByte != 1 then none
    else
      let flag : UInt64 := if fByte == 1 then 0xFFFFFFFFFFFFFFFF else 0
      let result := compress h m t0 t1 flag rounds
      -- Serialize result as 64 bytes (8 little-endian uint64s)
      let out := result.foldl (fun (acc : ByteArray) (v : UInt64) =>
        let bytes := writeLE64 v
        bytes.foldl (fun a b => a.push b) acc
      ) ByteArray.empty
      some out

end ETHCryptoLean.Blake2f
