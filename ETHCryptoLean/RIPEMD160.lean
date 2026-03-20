/-!
# RIPEMD-160

RIPEMD-160 hash function. EVM precompile at address 0x03.
-/

namespace ETHCryptoLean.RIPEMD160

/-- Rotate left for UInt32. -/
@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- Read a little-endian UInt32 from 4 bytes. -/
def readLE32 (data : Array UInt8) (offset : Nat) : UInt32 :=
  let b0 := data[offset]!.toUInt32
  let b1 := data[offset + 1]!.toUInt32
  let b2 := data[offset + 2]!.toUInt32
  let b3 := data[offset + 3]!.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Write a UInt32 as 4 little-endian bytes. -/
def writeLE32 (x : UInt32) : Array UInt8 := #[
  x.toUInt8,
  (x >>> 8).toUInt8,
  (x >>> 16).toUInt8,
  (x >>> 24).toUInt8
]

-- Boolean functions for each round group
@[inline] def f0 (x y z : UInt32) : UInt32 := x ^^^ y ^^^ z
@[inline] def f1 (x y z : UInt32) : UInt32 := (x &&& y) ||| (~~~ x &&& z)
@[inline] def f2 (x y z : UInt32) : UInt32 := (x ||| ~~~ y) ^^^ z
@[inline] def f3 (x y z : UInt32) : UInt32 := (x &&& z) ||| (y &&& ~~~ z)
@[inline] def f4 (x y z : UInt32) : UInt32 := x ^^^ (y ||| ~~~ z)

/-- Select boolean function by group index. -/
def selectF (group : Nat) (x y z : UInt32) : UInt32 :=
  match group with
  | 0 => f0 x y z
  | 1 => f1 x y z
  | 2 => f2 x y z
  | 3 => f3 x y z
  | _ => f4 x y z

-- Left-path constants
def klLeft : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]

-- Right-path constants
def klRight : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

-- Left-path message word selection (80 rounds)
def rLeft : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13
]

-- Right-path message word selection (80 rounds)
def rRight : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11
]

-- Left-path shift amounts (80 rounds)
def sLeft : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6
]

-- Right-path shift amounts (80 rounds)
def sRight : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11
]

/-- Pad message per MD-strengthening (like MD4/MD5). -/
def pad (msg : Array UInt8) : Array UInt8 :=
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let msg := msg.push 0x80
  let padLen := (56 - msg.size % 64) % 64
  let msg := (List.range padLen).foldl (fun m _ => m.push 0x00) msg
  -- 64-bit little-endian length
  let msg := msg.push bitLen.toUInt8
  let msg := msg.push (bitLen >>> 8).toUInt8
  let msg := msg.push (bitLen >>> 16).toUInt8
  let msg := msg.push (bitLen >>> 24).toUInt8
  let msg := msg.push (bitLen >>> 32).toUInt8
  let msg := msg.push (bitLen >>> 40).toUInt8
  let msg := msg.push (bitLen >>> 48).toUInt8
  let msg := msg.push (bitLen >>> 56).toUInt8
  msg

/-- Process one 64-byte block, updating the hash state. -/
def processBlock (hState : Array UInt32) (data : Array UInt8) (blockOffset : Nat) : Array UInt32 :=
  -- Read 16 words (little-endian)
  let x : Array UInt32 := (List.range 16).foldl (fun w i =>
    w.push (readLE32 data (blockOffset + i * 4))) #[]

  let h0 := hState[0]!
  let h1 := hState[1]!
  let h2 := hState[2]!
  let h3 := hState[3]!
  let h4 := hState[4]!

  -- Left path
  let (al, bl, cl, dl, el) := (List.range 80).foldl (fun (a, b, c, d, e) j =>
    let group := j / 16
    let fVal := selectF group b c d
    let t := rotl (a + fVal + x[rLeft[j]!]! + klLeft[group]!) sLeft[j]! + e
    (e, t, b, rotl c 10, d)) (h0, h1, h2, h3, h4)

  -- Right path (note: reversed boolean function order)
  let (ar, br, cr, dr, er) := (List.range 80).foldl (fun (a, b, c, d, e) j =>
    let group := j / 16
    -- Right path uses f in reverse order: f4, f3, f2, f1, f0
    let fVal := selectF (4 - group) b c d
    let t := rotl (a + fVal + x[rRight[j]!]! + klRight[group]!) sRight[j]! + e
    (e, t, b, rotl c 10, d)) (h0, h1, h2, h3, h4)

  -- Final addition
  let t := h1 + cl + dr
  let h1' := h2 + dl + er
  let h2' := h3 + el + ar
  let h3' := h4 + al + br
  let h4' := h0 + bl + cr
  let h0' := t

  #[h0', h1', h2', h3', h4']

/-- Initial hash values. -/
def initHash : Array UInt32 := #[
  0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0
]

/-- RIPEMD-160 hash function. Output is 20 bytes. -/
def ripemd160 (input : Array UInt8) : Array UInt8 :=
  let padded := pad input
  let numBlocks := padded.size / 64
  let h := (List.range numBlocks).foldl (fun h i =>
    processBlock h padded (i * 64)) initHash
  h.foldl (fun acc w => acc ++ writeLE32 w) #[]

-- Hex utilities for tests
end ETHCryptoLean.RIPEMD160
