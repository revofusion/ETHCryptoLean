/-
  SHA-256 implementation in pure Lean 4
-/

namespace SHA256

private def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] private def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x.complement &&& z)
@[inline] private def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
@[inline] private def sigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
@[inline] private def sigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
@[inline] private def gamma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
@[inline] private def gamma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

private def getWord (block : Array UInt8) (i : Nat) : UInt32 :=
  let b0 := (block[i * 4]!).toUInt32
  let b1 := (block[i * 4 + 1]!).toUInt32
  let b2 := (block[i * 4 + 2]!).toUInt32
  let b3 := (block[i * 4 + 3]!).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

private def processBlock (hsh : Array UInt32) (block : Array UInt8) : Array UInt32 :=
  -- Build message schedule
  let w := (List.range 16).foldl (fun (acc : Array UInt32) i =>
    acc.push (getWord block i)
  ) #[]
  let w := (List.range 48).foldl (fun (acc : Array UInt32) i =>
    let idx := i + 16
    let s0 := gamma0 acc[idx - 15]!
    let s1 := gamma1 acc[idx - 2]!
    acc.push (acc[idx - 16]! + s0 + acc[idx - 7]! + s1)
  ) w

  let a := hsh[0]!; let b := hsh[1]!; let c := hsh[2]!; let d := hsh[3]!
  let e := hsh[4]!; let f := hsh[5]!; let g := hsh[6]!; let h := hsh[7]!

  let (a, b, c, d, e, f, g, h) := (List.range 64).foldl
    (fun (state : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32) i =>
      let (a, b, c, d, e, f, g, h) := state
      let t1 := h + sigma1 e + ch e f g + K[i]! + w[i]!
      let t2 := sigma0 a + maj a b c
      (t1 + t2, a, b, c, d + t1, e, f, g)
    ) (a, b, c, d, e, f, g, h)

  #[hsh[0]! + a, hsh[1]! + b, hsh[2]! + c, hsh[3]! + d,
    hsh[4]! + e, hsh[5]! + f, hsh[6]! + g, hsh[7]! + h]

private def pad (msg : Array UInt8) : Array UInt8 :=
  let bitLen := msg.size * 8
  let padded := msg.push 0x80
  let targetLen := ((padded.size + 63) / 64) * 64 - 8
  let targetLen := if padded.size > targetLen then targetLen + 64 else targetLen
  let padded := (List.range (targetLen - padded.size)).foldl (fun acc _ => acc.push 0) padded
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 56) % 256))
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 48) % 256))
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 40) % 256))
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 32) % 256))
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 24) % 256))
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 16) % 256))
  let padded := padded.push (UInt8.ofNat ((bitLen >>> 8) % 256))
  let padded := padded.push (UInt8.ofNat (bitLen % 256))
  padded

-- Convert UInt32 to 4 big-endian bytes
private def u32ToBytes (w : UInt32) : Array UInt8 :=
  #[UInt8.ofNat ((w >>> 24).toNat % 256),
    UInt8.ofNat ((w >>> 16).toNat % 256),
    UInt8.ofNat ((w >>> 8).toNat % 256),
    UInt8.ofNat (w.toNat % 256)]

partial def hash (msg : Array UInt8) : Array UInt8 :=
  let padded := pad msg
  let numBlocks := padded.size / 64
  let finalHash := (List.range numBlocks).foldl (fun h i =>
    let block := padded.extract (i * 64) ((i + 1) * 64)
    processBlock h block
  ) H0
  finalHash.foldl (fun (acc : Array UInt8) w => acc ++ u32ToBytes w) #[]

end SHA256
