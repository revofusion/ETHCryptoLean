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

/-- Read a little-endian UInt64 from 8 bytes starting at `offset`. -/
def readLE64 (data : ByteArray) (offset : Nat) : UInt64 :=
  let b0 := (data[offset]!).toUInt64
  let b1 := (data[offset + 1]!).toUInt64
  let b2 := (data[offset + 2]!).toUInt64
  let b3 := (data[offset + 3]!).toUInt64
  let b4 := (data[offset + 4]!).toUInt64
  let b5 := (data[offset + 5]!).toUInt64
  let b6 := (data[offset + 6]!).toUInt64
  let b7 := (data[offset + 7]!).toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
  (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

/-- Read a big-endian UInt32 from 4 bytes starting at `offset`. -/
def readBE32 (data : ByteArray) (offset : Nat) : UInt32 :=
  let b0 := (data[offset]!).toUInt32
  let b1 := (data[offset + 1]!).toUInt32
  let b2 := (data[offset + 2]!).toUInt32
  let b3 := (data[offset + 3]!).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Write a UInt64 as 8 little-endian bytes. -/
def writeLE64 (v : UInt64) : Array UInt8 :=
  #[ (v &&& 0xFF).toUInt8,
     ((v >>> 8) &&& 0xFF).toUInt8,
     ((v >>> 16) &&& 0xFF).toUInt8,
     ((v >>> 24) &&& 0xFF).toUInt8,
     ((v >>> 32) &&& 0xFF).toUInt8,
     ((v >>> 40) &&& 0xFF).toUInt8,
     ((v >>> 48) &&& 0xFF).toUInt8,
     ((v >>> 56) &&& 0xFF).toUInt8 ]

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
    let rounds := (readBE32 input 0).toNat
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

/-! ## Hex utilities for test vectors -/

private def hexDigitVal (c : Char) : UInt8 :=
  if '0' ≤ c && c ≤ '9' then c.toNat.toUInt8 - 48
  else if 'a' ≤ c && c ≤ 'f' then c.toNat.toUInt8 - 87
  else if 'A' ≤ c && c ≤ 'F' then c.toNat.toUInt8 - 55
  else 0

def hexToByteArray (s : String) : ByteArray :=
  let chars := s.toList
  let rec go (cs : List Char) (acc : ByteArray) : ByteArray :=
    match cs with
    | c1 :: c2 :: rest =>
      let byte := (hexDigitVal c1) <<< 4 ||| (hexDigitVal c2)
      go rest (acc.push byte)
    | _ => acc
  go chars ByteArray.empty

def byteArrayToHex (ba : ByteArray) : String :=
  let hexChar (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat)
    else Char.ofNat (87 + n.toNat)
  ba.foldl (fun acc b =>
    acc ++ String.singleton (hexChar (b >>> 4)) ++ String.singleton (hexChar (b &&& 0x0F))
  ) ""

/-! ## EIP-152 test vectors proved by native_decide -/

/-- EIP-152 test vector 4: 0 rounds, final=true -/
theorem test_vector_0rounds : blake2fPrecompile
    (hexToByteArray (
      "00000000" ++
      "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
      "6162630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
      "0300000000000000" ++ "0000000000000000" ++ "01"))
    = some (hexToByteArray
      "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b") := by
  native_decide

/-- EIP-152 test vector: 1 round, final=true -/
theorem test_vector_1round : blake2fPrecompile
    (hexToByteArray (
      "00000001" ++
      "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
      "6162630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
      "0300000000000000" ++ "0000000000000000" ++ "01"))
    = some (hexToByteArray
      "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fba551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421") := by
  native_decide

/-- EIP-152 test vector 5: 12 rounds, final=true (the standard BLAKE2b("abc") test) -/
theorem test_vector_12rounds_final : blake2fPrecompile
    (hexToByteArray (
      "0000000c" ++
      "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
      "6162630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
      "0300000000000000" ++ "0000000000000000" ++ "01"))
    = some (hexToByteArray
      "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923") := by
  native_decide

/-- EIP-152 test vector 6: 12 rounds, non-final (f=0) -/
theorem test_vector_12rounds_nonfinal : blake2fPrecompile
    (hexToByteArray (
      "0000000c" ++
      "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
      "6162630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
      "0300000000000000" ++ "0000000000000000" ++ "00"))
    = some (hexToByteArray
      "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735") := by
  native_decide

/-- EIP-152: wrong input size returns none -/
theorem test_wrong_size : blake2fPrecompile (hexToByteArray "00") = none := by
  native_decide

/-- EIP-152: invalid flag byte (not 0 or 1) returns none -/
theorem test_invalid_flag : blake2fPrecompile
    (hexToByteArray (
      "0000000c" ++
      "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
      "6162630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
      "0300000000000000" ++ "0000000000000000" ++ "02"))
    = none := by
  native_decide

end ETHCryptoLean.Blake2f
