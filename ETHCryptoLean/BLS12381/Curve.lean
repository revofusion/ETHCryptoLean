/-
  BLS12-381 curve point operations: G1 (over Fp) and G2 (over Fp2)
  E:  y² = x³ + 4 (over Fp)
  E': y² = x³ + 4(1+u) (over Fp2, sextic twist)
-/

import ETHCryptoLean.BLS12381.Fields

namespace BLS12381

-- ═══════════════════════════════════════════
-- G1: Points on E: y² = x³ + 4 over Fp
-- ═══════════════════════════════════════════

-- b coefficient for E
def G1_B : Nat := 4

inductive G1Point where
  | infinity : G1Point
  | affine : (x : Nat) → (y : Nat) → G1Point
  deriving BEq, Repr

def g1IsOnCurve (pt : G1Point) : Bool :=
  match pt with
  | .infinity => true
  | .affine x y =>
    fpEq (fpMul y y) (fpAdd (fpMul (fpMul x x) x) G1_B)

def g1Neg (pt : G1Point) : G1Point :=
  match pt with
  | .infinity => .infinity
  | .affine x y => .affine (x % P) (fpNeg y)

def g1Add (p1 p2 : G1Point) : G1Point :=
  match p1, p2 with
  | .infinity, q => q
  | p, .infinity => p
  | .affine x1 y1, .affine x2 y2 =>
    if fpEq x1 x2 then
      if fpEq y1 y2 then
        if fpEq y1 0 then .infinity
        else
          let lam := fpDiv (fpMul 3 (fpMul x1 x1)) (fpMul 2 y1)
          let x3 := fpSub (fpMul lam lam) (fpMul 2 x1)
          let y3 := fpSub (fpMul lam (fpSub x1 x3)) y1
          .affine x3 y3
      else .infinity
    else
      let lam := fpDiv (fpSub y2 y1) (fpSub x2 x1)
      let x3 := fpSub (fpSub (fpMul lam lam) x1) x2
      let y3 := fpSub (fpMul lam (fpSub x1 x3)) y1
      .affine x3 y3

def g1Double (pt : G1Point) : G1Point := g1Add pt pt

partial def g1ScalarMul (n : Nat) (pt : G1Point) : G1Point :=
  if n == 0 then .infinity
  else if n == 1 then pt
  else
    let half := g1ScalarMul (n / 2) pt
    let doubled := g1Add half half
    if n % 2 == 0 then doubled
    else g1Add doubled pt

-- G1 generator
def G1_GEN : G1Point :=
  .affine
    0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
    0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

-- ═══════════════════════════════════════════
-- G2: Points on E': y² = x³ + 4(1+u) over Fp2
-- ═══════════════════════════════════════════

def G2_B : Fp2 := fp2Mul ⟨4, 0⟩ XI

inductive G2Point where
  | infinity : G2Point
  | affine : (x : Fp2) → (y : Fp2) → G2Point
  deriving BEq, Repr

def g2IsOnCurve (pt : G2Point) : Bool :=
  match pt with
  | .infinity => true
  | .affine x y =>
    fp2Eq (fp2Sq y) (fp2Add (fp2Mul (fp2Sq x) x) G2_B)

def g2Neg (pt : G2Point) : G2Point :=
  match pt with
  | .infinity => .infinity
  | .affine x y => .affine x (fp2Neg y)

def g2Add (p1 p2 : G2Point) : G2Point :=
  match p1, p2 with
  | .infinity, q => q
  | p, .infinity => p
  | .affine x1 y1, .affine x2 y2 =>
    if fp2Eq x1 x2 then
      if fp2Eq y1 y2 then
        if fp2IsZero y1 then .infinity
        else
          let lam := fp2Div (fp2MulScalar (fp2Sq x1) 3) (fp2MulScalar y1 2)
          let x3 := fp2Sub (fp2Sq lam) (fp2MulScalar x1 2)
          let y3 := fp2Sub (fp2Mul lam (fp2Sub x1 x3)) y1
          .affine x3 y3
      else .infinity
    else
      let lam := fp2Div (fp2Sub y2 y1) (fp2Sub x2 x1)
      let x3 := fp2Sub (fp2Sub (fp2Sq lam) x1) x2
      let y3 := fp2Sub (fp2Mul lam (fp2Sub x1 x3)) y1
      .affine x3 y3

def g2Double (pt : G2Point) : G2Point := g2Add pt pt

partial def g2ScalarMul (n : Nat) (pt : G2Point) : G2Point :=
  if n == 0 then .infinity
  else if n == 1 then pt
  else
    let half := g2ScalarMul (n / 2) pt
    let doubled := g2Add half half
    if n % 2 == 0 then doubled
    else g2Add doubled pt

-- G2 generator (standard BLS12-381)
def G2_GEN : G2Point :=
  .affine
    ⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
     0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩
    ⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
     0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩

-- ═══════════════════════════════════════════
-- Points on E over Fp12 (for pairing computation)
-- ═══════════════════════════════════════════

inductive G12Point where
  | infinity : G12Point
  | affine : (x : Fp12) → (y : Fp12) → G12Point
  deriving Repr

def g12Eq (p1 p2 : G12Point) : Bool :=
  match p1, p2 with
  | .infinity, .infinity => true
  | .affine x1 y1, .affine x2 y2 => fp12Eq x1 x2 && fp12Eq y1 y2
  | _, _ => false

def g12Neg (pt : G12Point) : G12Point :=
  match pt with
  | .infinity => .infinity
  | .affine x y => .affine x (fp12Neg y)

def g12Add (p1 p2 : G12Point) : G12Point :=
  match p1, p2 with
  | .infinity, q => q
  | p, .infinity => p
  | .affine x1 y1, .affine x2 y2 =>
    if fp12Eq x1 x2 then
      if fp12Eq y1 y2 then
        if fp12IsZero y1 then .infinity
        else
          let x1sq := fp12Mul x1 x1
          let lam := fp12Div
            (fp12Mul (fpToFp12 3) x1sq)
            (fp12Mul (fpToFp12 2) y1)
          let x3 := fp12Sub (fp12Mul lam lam) (fp12Mul (fpToFp12 2) x1)
          let y3 := fp12Sub (fp12Mul lam (fp12Sub x1 x3)) y1
          .affine x3 y3
      else .infinity
    else
      let lam := fp12Div (fp12Sub y2 y1) (fp12Sub x2 x1)
      let x3 := fp12Sub (fp12Sub (fp12Mul lam lam) x1) x2
      let y3 := fp12Sub (fp12Mul lam (fp12Sub x1 x3)) y1
      .affine x3 y3

partial def g12ScalarMul (n : Nat) (pt : G12Point) : G12Point :=
  if n == 0 then .infinity
  else if n == 1 then pt
  else
    let half := g12ScalarMul (n / 2) pt
    let doubled := g12Add half half
    if n % 2 == 0 then doubled
    else g12Add doubled pt

-- ═══════════════════════════════════════════
-- Twist / Untwist maps
-- ═══════════════════════════════════════════

def g1ToG12 (pt : G1Point) : G12Point :=
  match pt with
  | .infinity => .infinity
  | .affine x y => .affine (fpToFp12 x) (fpToFp12 y)

def g2ToG12 (pt : G2Point) : G12Point :=
  match pt with
  | .infinity => .infinity
  | .affine x' y' =>
    let xiInv := fp2Inv XI
    let xE : Fp12 := ⟨⟨fp2Zero, fp2Zero, fp2Mul x' xiInv⟩, fp6Zero⟩
    let yE : Fp12 := ⟨fp6Zero, ⟨fp2Zero, fp2Mul y' xiInv, fp2Zero⟩⟩
    .affine xE yE

-- ═══════════════════════════════════════════
-- Point compression / decompression
-- ═══════════════════════════════════════════

-- Convert Nat to big-endian byte array of given length
def natToBytesBE (n : Nat) (len : Nat) : Array UInt8 :=
  let arr := Array.replicate len (0 : UInt8)
  (List.range len).foldl (fun acc i =>
    acc.set! (len - 1 - i) (UInt8.ofNat ((n >>> (i * 8)) % 256))
  ) arr

-- Convert big-endian byte array to Nat
def bytesToNatBE (bytes : Array UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

-- Compress G1 point to 48 bytes
def g1Compress (pt : G1Point) : Array UInt8 :=
  match pt with
  | .infinity =>
    let bytes := Array.replicate 48 (0 : UInt8)
    bytes.set! 0 0xC0
  | .affine x y =>
    let bytes := natToBytesBE (x % P) 48
    let flag : UInt8 := 0x80 ||| (if fpSign y then 0x20 else 0x00)
    bytes.set! 0 (bytes[0]! ||| flag)

-- Decompress 48 bytes to G1 point
def g1Decompress (bytes : Array UInt8) : Option G1Point :=
  if bytes.size != 48 then none
  else
    let flagByte := bytes[0]!
    let isCompressed := (flagByte &&& 0x80) != 0
    let isInfinity := (flagByte &&& 0x40) != 0
    let signBit := (flagByte &&& 0x20) != 0
    if !isCompressed then none
    else if isInfinity then some .infinity
    else
      let maskedBytes := bytes.set! 0 (flagByte &&& 0x1F)
      let x := bytesToNatBE maskedBytes
      if x >= P then none
      else
        let rhs := fpAdd (fpMul (fpMul x x) x) G1_B
        match fpSqrt rhs with
        | none => none
        | some y =>
          let y' := if fpSign y == signBit then y else fpNeg y
          some (.affine x y')

-- Compress G2 point to 96 bytes
def g2Compress (pt : G2Point) : Array UInt8 :=
  match pt with
  | .infinity =>
    let bytes := Array.replicate 96 (0 : UInt8)
    bytes.set! 0 0xC0
  | .affine x y =>
    let hi := natToBytesBE (x.c1 % P) 48
    let lo := natToBytesBE (x.c0 % P) 48
    let bytes := hi ++ lo
    let flag : UInt8 := 0x80 ||| (if fp2Sign y then 0x20 else 0x00)
    bytes.set! 0 (bytes[0]! ||| flag)

-- Decompress 96 bytes to G2 point
def g2Decompress (bytes : Array UInt8) : Option G2Point :=
  if bytes.size != 96 then none
  else
    let flagByte := bytes[0]!
    let isCompressed := (flagByte &&& 0x80) != 0
    let isInfinity := (flagByte &&& 0x40) != 0
    let signBit := (flagByte &&& 0x20) != 0
    if !isCompressed then none
    else if isInfinity then some .infinity
    else
      let hiBytes := (bytes.extract 0 48).set! 0 (flagByte &&& 0x1F)
      let loBytes := bytes.extract 48 96
      let c1 := bytesToNatBE hiBytes
      let c0 := bytesToNatBE loBytes
      if c0 >= P || c1 >= P then none
      else
        let x : Fp2 := ⟨c0, c1⟩
        let rhs := fp2Add (fp2Mul (fp2Sq x) x) G2_B
        match fp2Sqrt rhs with
        | none => none
        | some y =>
          let y' := if fp2Sign y == signBit then y else fp2Neg y
          some (.affine x y')

end BLS12381
