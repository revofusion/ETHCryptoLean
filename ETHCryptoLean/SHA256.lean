namespace SHA256

-- SHA-256 constants: first 32 bits of the fractional parts of the cube roots of the first 64 primes
private def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- Initial hash values: first 32 bits of fractional parts of square roots of first 8 primes
private def h0Init : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] private def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

@[inline] private def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] private def bigSigma0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

@[inline] private def bigSigma1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

@[inline] private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

@[inline] private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Read a big-endian UInt32 from 4 bytes starting at index `i`. -/
@[inline] private def readBE32 (data : Array UInt8) (i : Nat) : UInt32 :=
  (data[i]!.toUInt32 <<< 24) ||| (data[i+1]!.toUInt32 <<< 16) |||
  (data[i+2]!.toUInt32 <<< 8) ||| data[i+3]!.toUInt32

/-- Write a big-endian UInt32 to 4 bytes. -/
@[inline] private def writeBE32 (v : UInt32) : Array UInt8 :=
  #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]

/-- Process a single 64-byte block and return updated hash state. -/
private def processBlock (h : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  -- Prepare message schedule
  let w : Array UInt32 := Id.run do
    let mut w := Array.mkEmpty 64
    -- First 16 words from block (big-endian)
    for i in [:16] do
      w := w.push (readBE32 block (i * 4))
    -- Extend to 64 words
    for i in [16:64] do
      let s0 := smallSigma0 w[i - 15]!
      let s1 := smallSigma1 w[i - 2]!
      w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
    return w
  -- Compression
  let (a, b, c, d, e, f, g, hh) := Id.run do
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for i in [:64] do
      let t1 := hh + bigSigma1 e + ch e f g + k[i]! + w[i]!
      let t2 := bigSigma0 a + maj a b c
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    return (a, b, c, d, e, f, g, hh)
  #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
    h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- Pad the message according to SHA-256 padding rules. -/
private def pad (msg : Array UInt8) : Array UInt8 :=
  let msgLen := msg.size
  let bitLen : UInt64 := msgLen.toUInt64 * 8
  -- Append 0x80 byte
  let padded := msg.push 0x80
  -- Calculate number of zero bytes needed
  -- We need total length ≡ 56 (mod 64), i.e., room for 8 bytes of length at the end
  let currentLen := padded.size
  let remainder := currentLen % 64
  let zerosNeeded := if remainder <= 56 then 56 - remainder else (64 - remainder) + 56
  let padded := Id.run do
    let mut p := padded
    for _ in [:zerosNeeded] do
      p := p.push 0x00
    return p
  -- Append 64-bit big-endian bit length
  let padded := padded.push (bitLen >>> 56).toUInt8
  let padded := padded.push (bitLen >>> 48).toUInt8
  let padded := padded.push (bitLen >>> 40).toUInt8
  let padded := padded.push (bitLen >>> 32).toUInt8
  let padded := padded.push (bitLen >>> 24).toUInt8
  let padded := padded.push (bitLen >>> 16).toUInt8
  let padded := padded.push (bitLen >>> 8).toUInt8
  let padded := padded.push bitLen.toUInt8
  padded

/-- Compute SHA-256 hash of a byte array. Returns 32-byte hash. -/
partial def hash (msg : Array UInt8) : Array UInt8 :=
  let padded := pad msg
  let numBlocks := padded.size / 64
  let finalH := Id.run do
    let mut h := h0Init
    for i in [:numBlocks] do
      let block := padded.extract (i * 64) ((i + 1) * 64)
      h := processBlock h block
    return h
  -- Convert hash state to bytes (big-endian)
  Id.run do
    let mut result : Array UInt8 := Array.mkEmpty 32
    for i in [:8] do
      result := result ++ writeBE32 finalH[i]!
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

end SHA256
