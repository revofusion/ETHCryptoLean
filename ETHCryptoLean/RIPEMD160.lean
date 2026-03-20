namespace ETHCryptoLean.RIPEMD160

-- Nonlinear functions
@[inline] private def f0 (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
@[inline] private def f1 (x y z : UInt32) : UInt32 := (x &&& y) ||| ((~~~x) &&& z)
@[inline] private def f2 (x y z : UInt32) : UInt32 := (x ||| (~~~y)) ^^^ z
@[inline] private def f3 (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& (~~~z))
@[inline] private def f4 (x y z : UInt32) : UInt32 := x ^^^ (y ||| (~~~z))

@[inline] private def rotl (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

-- Left round constants
private def kL : Array UInt32 := #[0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
-- Right round constants
private def kR : Array UInt32 := #[0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]

-- Left message word selection
private def rL : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13
]

-- Right message word selection
private def rR : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11
]

-- Left shift amounts
private def sL : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6
]

-- Right shift amounts
private def sR : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11
]

-- Initial hash values
private def h0Init : Array UInt32 := #[
  0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0
]

/-- Read a little-endian UInt32 from 4 bytes starting at index `i`. -/
@[inline] private def readLE32 (data : Array UInt8) (i : Nat) : UInt32 :=
  data[i]!.toUInt32 ||| (data[i+1]!.toUInt32 <<< 8) |||
  (data[i+2]!.toUInt32 <<< 16) ||| (data[i+3]!.toUInt32 <<< 24)

/-- Write a little-endian UInt32 to 4 bytes. -/
@[inline] private def writeLE32 (v : UInt32) : Array UInt8 :=
  #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

/-- Select the nonlinear function for round j (0..79). -/
@[inline] private def selectF (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then f0 x y z
  else if j < 32 then f1 x y z
  else if j < 48 then f2 x y z
  else if j < 64 then f3 x y z
  else f4 x y z

/-- Select the nonlinear function for the right (parallel) round j (0..79). -/
@[inline] private def selectFR (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then f4 x y z
  else if j < 32 then f3 x y z
  else if j < 48 then f2 x y z
  else if j < 64 then f1 x y z
  else f0 x y z

/-- Process a single 64-byte block. -/
private def processBlock (h : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  -- Parse block into 16 little-endian 32-bit words
  let x : Array UInt32 := Id.run do
    let mut w := Array.mkEmpty 16
    for i in [:16] do
      w := w.push (readLE32 block (i * 4))
    return w
  -- Left rounds
  let (al, bl, cl, dl, el) := Id.run do
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    for j in [:80] do
      let round := j / 16
      let fv := selectF j b c d
      let t := rotl (a + fv + x[rL[j]!]! + kL[round]!) sL[j]! + e
      a := e
      e := d
      d := rotl c 10
      c := b
      b := t
    return (a, b, c, d, e)
  -- Right rounds
  let (ar, br, cr, dr, er) := Id.run do
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    for j in [:80] do
      let round := j / 16
      let fv := selectFR j b c d
      let t := rotl (a + fv + x[rR[j]!]! + kR[round]!) sR[j]! + e
      a := e
      e := d
      d := rotl c 10
      c := b
      b := t
    return (a, b, c, d, e)
  -- Final addition
  let t := h[1]! + cl + dr
  #[t,
    h[2]! + dl + er,
    h[3]! + el + ar,
    h[4]! + al + br,
    h[0]! + bl + cr]

/-- Pad the message according to RIPEMD-160 padding rules. -/
private def pad (msg : Array UInt8) : Array UInt8 :=
  let msgLen := msg.size
  let bitLen : UInt64 := msgLen.toUInt64 * 8
  -- Append 0x80
  let padded := msg.push 0x80
  -- Need total length ≡ 56 (mod 64)
  let currentLen := padded.size
  let remainder := currentLen % 64
  let zerosNeeded := if remainder <= 56 then 56 - remainder else (64 - remainder) + 56
  let padded := Id.run do
    let mut p := padded
    for _ in [:zerosNeeded] do
      p := p.push 0x00
    return p
  -- Append 64-bit little-endian bit length
  let padded := padded.push bitLen.toUInt8
  let padded := padded.push (bitLen >>> 8).toUInt8
  let padded := padded.push (bitLen >>> 16).toUInt8
  let padded := padded.push (bitLen >>> 24).toUInt8
  let padded := padded.push (bitLen >>> 32).toUInt8
  let padded := padded.push (bitLen >>> 40).toUInt8
  let padded := padded.push (bitLen >>> 48).toUInt8
  let padded := padded.push (bitLen >>> 56).toUInt8
  padded

/-- Compute RIPEMD-160 hash of a byte array. Returns 20-byte hash. -/
def ripemd160 (input : Array UInt8) : Array UInt8 :=
  let padded := pad input
  let numBlocks := padded.size / 64
  let finalH := Id.run do
    let mut h := h0Init
    for i in [:numBlocks] do
      let block := padded.extract (i * 64) ((i + 1) * 64)
      h := processBlock h block
    return h
  -- Convert hash state to bytes (little-endian)
  Id.run do
    let mut result : Array UInt8 := Array.mkEmpty 20
    for i in [:5] do
      result := result ++ writeLE32 finalH[i]!
    return result

/-- Convert a byte array to a hex string. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (bytes : Array UInt8) : String :=
  bytes.foldl (fun acc b =>
    let hi := (b.toNat >>> 4) &&& 0x0F
    let lo := b.toNat &&& 0x0F
    acc ++ String.ofList [hexDigit hi, hexDigit lo]
  ) ""

end ETHCryptoLean.RIPEMD160
