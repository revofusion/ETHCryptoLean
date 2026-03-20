/-
  BN256 / alt_bn128 Pairing Implementation for EVM Precompiles
  Pure Lean 4, no FFI, no opaque.
-/

namespace ETHCryptoLean.BN256

-- ============================================================
-- Field prime and curve parameters
-- ============================================================

def fieldPrime : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

def curveOrder : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

-- BN parameter u
def bnU : Nat := 4965661367192848881

-- Ate loop count = |6u + 2|
def ateLoopCount : Nat := 29793968203157093288

-- Number of bits in ateLoopCount (it's a 65-bit number, MSB at position 64)
def ateLoopCountBits : Nat := 64

-- ============================================================
-- Modular exponentiation
-- ============================================================

def natPowMod (base exp mod : Nat) : Nat :=
  if mod <= 1 then 0
  else if exp = 0 then 1
  else
    let half := natPowMod (base % mod) (exp / 2) mod
    let halfSq := (half * half) % mod
    if exp % 2 == 0 then halfSq
    else (halfSq * (base % mod)) % mod
termination_by exp
decreasing_by omega

-- ============================================================
-- Fp arithmetic (integers mod fieldPrime)
-- ============================================================

abbrev Fp := Nat

@[inline] def fpAdd (a b : Fp) : Fp := (a + b) % fieldPrime
@[inline] def fpSub (a b : Fp) : Fp := (a + fieldPrime - b % fieldPrime) % fieldPrime
@[inline] def fpMul (a b : Fp) : Fp := (a * b) % fieldPrime
@[inline] def fpNeg (a : Fp) : Fp := if a % fieldPrime == 0 then 0 else fieldPrime - a % fieldPrime
@[inline] def fpInv (a : Fp) : Fp := natPowMod a (fieldPrime - 2) fieldPrime

-- ============================================================
-- Fp2 = Fp[i] / (i² + 1)
-- ============================================================

structure Fp2 where
  c0 : Fp  -- real part
  c1 : Fp  -- imaginary part (coefficient of i)
deriving BEq, Repr, Inhabited

def fp2Zero : Fp2 := ⟨0, 0⟩
def fp2One : Fp2 := ⟨1, 0⟩

@[inline] def fp2IsZero (a : Fp2) : Bool := a.c0 % fieldPrime == 0 && a.c1 % fieldPrime == 0

@[inline] def fp2Add (a b : Fp2) : Fp2 := ⟨fpAdd a.c0 b.c0, fpAdd a.c1 b.c1⟩
@[inline] def fp2Sub (a b : Fp2) : Fp2 := ⟨fpSub a.c0 b.c0, fpSub a.c1 b.c1⟩
@[inline] def fp2Neg (a : Fp2) : Fp2 := ⟨fpNeg a.c0, fpNeg a.c1⟩
@[inline] def fp2Conj (a : Fp2) : Fp2 := ⟨a.c0, fpNeg a.c1⟩

-- (a + bi)(c + di) = (ac - bd) + (ad + bc)i
@[inline] def fp2Mul (a b : Fp2) : Fp2 :=
  ⟨fpSub (fpMul a.c0 b.c0) (fpMul a.c1 b.c1),
   fpAdd (fpMul a.c0 b.c1) (fpMul a.c1 b.c0)⟩

@[inline] def fp2Sq (a : Fp2) : Fp2 := fp2Mul a a

-- Scalar multiplication by Fp element
@[inline] def fp2ScalarMul (s : Fp) (a : Fp2) : Fp2 :=
  ⟨fpMul s a.c0, fpMul s a.c1⟩

-- (a + bi)^(-1) = (a - bi)/(a² + b²)
def fp2Inv (a : Fp2) : Fp2 :=
  let norm := fpAdd (fpMul a.c0 a.c0) (fpMul a.c1 a.c1)
  let normInv := fpInv norm
  ⟨fpMul a.c0 normInv, fpMul (fpNeg a.c1) normInv⟩

@[inline] def fp2Div (a b : Fp2) : Fp2 := fp2Mul a (fp2Inv b)

-- Exponentiation by repeated squaring
def fp2Pow (base : Fp2) (exp : Nat) : Fp2 :=
  if h : exp = 0 then fp2One
  else if exp = 1 then base
  else
    let half := fp2Pow base (exp / 2)
    let halfSq := fp2Mul half half
    if exp % 2 == 0 then halfSq
    else fp2Mul halfSq base
termination_by exp
decreasing_by all_goals omega

-- ============================================================
-- Fp6 = Fp2[v] / (v³ - ξ) where ξ = 9 + i
-- An element is c0 + c1·v + c2·v²
-- ============================================================

-- ξ = 9 + i (the non-residue used in the extension)
def xi : Fp2 := ⟨9, 1⟩

structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
deriving BEq, Repr, Inhabited

def fp6Zero : Fp6 := ⟨fp2Zero, fp2Zero, fp2Zero⟩
def fp6One : Fp6 := ⟨fp2One, fp2Zero, fp2Zero⟩

@[inline] def fp6Add (a b : Fp6) : Fp6 :=
  ⟨fp2Add a.c0 b.c0, fp2Add a.c1 b.c1, fp2Add a.c2 b.c2⟩

@[inline] def fp6Sub (a b : Fp6) : Fp6 :=
  ⟨fp2Sub a.c0 b.c0, fp2Sub a.c1 b.c1, fp2Sub a.c2 b.c2⟩

@[inline] def fp6Neg (a : Fp6) : Fp6 :=
  ⟨fp2Neg a.c0, fp2Neg a.c1, fp2Neg a.c2⟩

-- Multiply by v: (c0, c1, c2) * v = (c2·ξ, c0, c1)
@[inline] def fp6MulByV (a : Fp6) : Fp6 :=
  ⟨fp2Mul a.c2 xi, a.c0, a.c1⟩

-- Multiplication:
-- (a0 + a1·v + a2·v²)(b0 + b1·v + b2·v²)
-- = [a0·b0 + (a1·b2 + a2·b1)·ξ]
-- + [a0·b1 + a1·b0 + a2·b2·ξ]·v
-- + [a0·b2 + a1·b1 + a2·b0]·v²
def fp6Mul (a b : Fp6) : Fp6 :=
  let t0 := fp2Mul a.c0 b.c0
  let t1 := fp2Mul a.c1 b.c1
  let t2 := fp2Mul a.c2 b.c2
  let c0 := fp2Add t0 (fp2Mul (fp2Add (fp2Mul a.c1 b.c2) (fp2Mul a.c2 b.c1)) xi)
  let c1 := fp2Add (fp2Add (fp2Mul a.c0 b.c1) (fp2Mul a.c1 b.c0)) (fp2Mul t2 xi)
  let c2 := fp2Add (fp2Add (fp2Mul a.c0 b.c2) t1) (fp2Mul a.c2 b.c0)
  ⟨c0, c1, c2⟩

-- Scalar multiplication by Fp2 element (embeds s as Fp6(s, 0, 0))
@[inline] def fp6ScalarMul (s : Fp2) (a : Fp6) : Fp6 :=
  ⟨fp2Mul s a.c0, fp2Mul s a.c1, fp2Mul s a.c2⟩

-- Scalar multiplication by Fp element
@[inline] def fp6ScalarMulFp (s : Fp) (a : Fp6) : Fp6 :=
  ⟨fp2ScalarMul s a.c0, fp2ScalarMul s a.c1, fp2ScalarMul s a.c2⟩

-- Inverse using Cramer's rule
def fp6Inv (a : Fp6) : Fp6 :=
  let A := fp2Sub (fp2Sq a.c0) (fp2Mul xi (fp2Mul a.c1 a.c2))
  let B := fp2Sub (fp2Mul xi (fp2Sq a.c2)) (fp2Mul a.c0 a.c1)
  let C := fp2Sub (fp2Sq a.c1) (fp2Mul a.c0 a.c2)
  let D := fp2Add (fp2Mul a.c0 A) (fp2Mul xi (fp2Add (fp2Mul a.c2 B) (fp2Mul a.c1 C)))
  let DInv := fp2Inv D
  ⟨fp2Mul A DInv, fp2Mul B DInv, fp2Mul C DInv⟩

-- ============================================================
-- Fp12 = Fp6[w] / (w² - v)
-- An element is c0 + c1·w where c0, c1 ∈ Fp6 and w² = v
-- ============================================================

structure Fp12 where
  c0 : Fp6
  c1 : Fp6
deriving BEq, Repr, Inhabited

def fp12Zero : Fp12 := ⟨fp6Zero, fp6Zero⟩
def fp12One : Fp12 := ⟨fp6One, fp6Zero⟩

@[inline] def fp12Add (a b : Fp12) : Fp12 :=
  ⟨fp6Add a.c0 b.c0, fp6Add a.c1 b.c1⟩

@[inline] def fp12Sub (a b : Fp12) : Fp12 :=
  ⟨fp6Sub a.c0 b.c0, fp6Sub a.c1 b.c1⟩

@[inline] def fp12Neg (a : Fp12) : Fp12 :=
  ⟨fp6Neg a.c0, fp6Neg a.c1⟩

-- Conjugation (p^6 Frobenius): negate the w coefficient
@[inline] def fp12Conj (a : Fp12) : Fp12 :=
  ⟨a.c0, fp6Neg a.c1⟩

-- Multiplication: (a + bw)(c + dw) = (ac + bd·v_fp6) + (ad + bc)w
def fp12Mul (a b : Fp12) : Fp12 :=
  let ac := fp6Mul a.c0 b.c0
  let bd := fp6Mul a.c1 b.c1
  ⟨fp6Add ac (fp6MulByV bd),
   fp6Add (fp6Mul a.c0 b.c1) (fp6Mul a.c1 b.c0)⟩

def fp12Sq (a : Fp12) : Fp12 := fp12Mul a a

-- Inverse: (a + bw)^(-1) = (a - bw) / (a² - b²·v)
def fp12Inv (a : Fp12) : Fp12 :=
  let t := fp6Sub (fp6Mul a.c0 a.c0) (fp6MulByV (fp6Mul a.c1 a.c1))
  let tInv := fp6Inv t
  ⟨fp6Mul a.c0 tInv, fp6Neg (fp6Mul a.c1 tInv)⟩

-- Exponentiation by repeated squaring
def fp12Pow (base : Fp12) (exp : Nat) : Fp12 :=
  if h : exp = 0 then fp12One
  else if exp = 1 then base
  else
    let half := fp12Pow base (exp / 2)
    let halfSq := fp12Mul half half
    if exp % 2 == 0 then halfSq
    else fp12Mul halfSq base
termination_by exp
decreasing_by all_goals omega

-- ============================================================
-- Frobenius endomorphisms
-- ============================================================

-- Frobenius constants
def frobGamma1 : Fp2 := fp2Pow xi ((fieldPrime - 1) / 3)
def frobGamma12 : Fp2 := fp2Sq frobGamma1
def frobGammaW : Fp2 := fp2Pow xi ((fieldPrime - 1) / 6)

-- For p²-Frobenius (Fp elements: norms)
def xiNorm : Fp := 82
def frob2Delta1 : Fp := natPowMod xiNorm ((fieldPrime - 1) / 3) fieldPrime
def frob2Delta2 : Fp := fpMul frob2Delta1 frob2Delta1
def frob2DeltaW : Fp := natPowMod xiNorm ((fieldPrime - 1) / 6) fieldPrime

-- p-Frobenius on Fp6
def fp6Frob (a : Fp6) : Fp6 :=
  ⟨fp2Conj a.c0,
   fp2Mul (fp2Conj a.c1) frobGamma1,
   fp2Mul (fp2Conj a.c2) frobGamma12⟩

-- p-Frobenius on Fp12
def fp12Frob (a : Fp12) : Fp12 :=
  ⟨fp6Frob a.c0,
   fp6ScalarMul frobGammaW (fp6Frob a.c1)⟩

-- p²-Frobenius on Fp6
def fp6Frob2 (a : Fp6) : Fp6 :=
  ⟨a.c0,
   fp2ScalarMul frob2Delta1 a.c1,
   fp2ScalarMul frob2Delta2 a.c2⟩

-- p²-Frobenius on Fp12
def fp12Frob2 (a : Fp12) : Fp12 :=
  ⟨fp6Frob2 a.c0,
   fp6ScalarMulFp frob2DeltaW (fp6Frob2 a.c1)⟩

-- ============================================================
-- Frobenius on G2 points (in Fp2)
-- ============================================================

def g2FrobC1 : Fp2 := fp2Pow xi ((fieldPrime - 1) / 3)
def g2FrobC2 : Fp2 := fp2Pow xi ((fieldPrime - 1) / 2)
def g2Frob2C1 : Fp := natPowMod xiNorm ((fieldPrime - 1) / 3) fieldPrime
def g2Frob2C2 : Fp := natPowMod xiNorm ((fieldPrime - 1) / 2) fieldPrime

-- ============================================================
-- G1 point (on E(Fp): y² = x³ + 3)
-- ============================================================

structure G1Point where
  x : Fp
  y : Fp
  inf : Bool
deriving BEq, Repr, Inhabited

def g1Inf : G1Point := ⟨0, 0, true⟩

def g1IsOnCurve (p : G1Point) : Bool :=
  if p.inf then true
  else
    let lhs := fpMul p.y p.y
    let rhs := fpAdd (fpMul (fpMul p.x p.x) p.x) 3
    lhs == rhs

def g1Neg (p : G1Point) : G1Point :=
  if p.inf then p
  else ⟨p.x, fpNeg p.y, false⟩

def g1Add (p q : G1Point) : G1Point :=
  if p.inf then q
  else if q.inf then p
  else if p.x == q.x then
    if p.y == q.y then
      if p.y == 0 then g1Inf
      else
        let lam := fpMul (fpMul 3 (fpMul p.x p.x)) (fpInv (fpMul 2 p.y))
        let x3 := fpSub (fpMul lam lam) (fpMul 2 p.x)
        let y3 := fpSub (fpMul lam (fpSub p.x x3)) p.y
        ⟨x3, y3, false⟩
    else g1Inf
  else
    let lam := fpMul (fpSub q.y p.y) (fpInv (fpSub q.x p.x))
    let x3 := fpSub (fpSub (fpMul lam lam) p.x) q.x
    let y3 := fpSub (fpMul lam (fpSub p.x x3)) p.y
    ⟨x3, y3, false⟩

def g1ScalarMul (n : Nat) (p : G1Point) : G1Point :=
  if h : n = 0 then g1Inf
  else if n = 1 then p
  else
    let half := g1ScalarMul (n / 2) p
    let doubled := g1Add half half
    if n % 2 == 0 then doubled
    else g1Add doubled p
termination_by n
decreasing_by all_goals omega

-- ============================================================
-- G2 point (on twist E'(Fp2): y² = x³ + 3/ξ)
-- ============================================================

def twistB : Fp2 := fp2Div ⟨3, 0⟩ xi

structure G2Point where
  x : Fp2
  y : Fp2
  inf : Bool
deriving BEq, Repr, Inhabited

def g2Inf : G2Point := ⟨fp2Zero, fp2Zero, true⟩

def g2IsOnCurve (p : G2Point) : Bool :=
  if p.inf then true
  else
    let lhs := fp2Sq p.y
    let rhs := fp2Add (fp2Mul (fp2Sq p.x) p.x) twistB
    lhs == rhs

def g2Neg (p : G2Point) : G2Point :=
  if p.inf then p
  else ⟨p.x, fp2Neg p.y, false⟩

def g2Double (p : G2Point) : G2Point :=
  if p.inf then p
  else if fp2IsZero p.y then g2Inf
  else
    let lam := fp2Div (fp2ScalarMul 3 (fp2Sq p.x)) (fp2ScalarMul 2 p.y)
    let x3 := fp2Sub (fp2Sq lam) (fp2ScalarMul 2 p.x)
    let y3 := fp2Sub (fp2Mul lam (fp2Sub p.x x3)) p.y
    ⟨x3, y3, false⟩

def g2Add (p q : G2Point) : G2Point :=
  if p.inf then q
  else if q.inf then p
  else if p.x == q.x then
    if p.y == q.y then g2Double p
    else g2Inf
  else
    let lam := fp2Div (fp2Sub q.y p.y) (fp2Sub q.x p.x)
    let x3 := fp2Sub (fp2Sub (fp2Sq lam) p.x) q.x
    let y3 := fp2Sub (fp2Mul lam (fp2Sub p.x x3)) p.y
    ⟨x3, y3, false⟩

def g2ScalarMul (n : Nat) (p : G2Point) : G2Point :=
  if h : n = 0 then g2Inf
  else if n = 1 then p
  else
    let half := g2ScalarMul (n / 2) p
    let doubled := g2Add half half
    if n % 2 == 0 then doubled
    else g2Add doubled p
termination_by n
decreasing_by all_goals omega

-- Frobenius on G2
def g2Frobenius (q : G2Point) : G2Point :=
  if q.inf then q
  else ⟨fp2Mul (fp2Conj q.x) g2FrobC1,
        fp2Mul (fp2Conj q.y) g2FrobC2,
        false⟩

def g2Frobenius2 (q : G2Point) : G2Point :=
  if q.inf then q
  else ⟨fp2ScalarMul g2Frob2C1 q.x,
        fp2ScalarMul g2Frob2C2 q.y,
        false⟩

-- ============================================================
-- Line function evaluation
-- ============================================================

-- The line function value at G1 point P=(px,py) given slope λ and
-- reference point R=(rx,ry) on E'(Fp2):
--
-- l(P) = py + (-λ·px)·w + (λ·rx - ry)·w³
--
-- In tower representation:
-- c0 = Fp6((py,0), 0, 0)
-- c1 = Fp6(-λ·(px,0), λ·rx - ry, 0)
def lineFunc (slope : Fp2) (rx ry : Fp2) (px py : Fp) : Fp12 :=
  let c0 : Fp6 := ⟨⟨py, 0⟩, fp2Zero, fp2Zero⟩
  let t1 := fp2Neg (fp2Mul slope ⟨px, 0⟩)
  let t2 := fp2Sub (fp2Mul slope rx) ry
  let c1 : Fp6 := ⟨t1, t2, fp2Zero⟩
  ⟨c0, c1⟩

-- Compute tangent slope at R = (rx, ry) on E'(Fp2)
@[inline] def tangentSlope (rx ry : Fp2) : Fp2 :=
  fp2Div (fp2ScalarMul 3 (fp2Sq rx)) (fp2ScalarMul 2 ry)

-- Compute chord slope through R and Q
@[inline] def chordSlope (rx ry qx qy : Fp2) : Fp2 :=
  fp2Div (fp2Sub qy ry) (fp2Sub qx rx)

-- ============================================================
-- Miller loop
-- ============================================================

structure MillerState where
  rx : Fp2
  ry : Fp2
  rInf : Bool
  f : Fp12

-- Process one bit of the Miller loop
def millerStep (s : MillerState) (qx qy : Fp2) (px py : Fp) (bit : Bool) : MillerState :=
  if s.rInf then
    { s with f := fp12Sq s.f }
  else
    -- Doubling step
    let f' := fp12Sq s.f
    let (f'', rx', ry', rInf') :=
      if fp2IsZero s.ry then
        (f', fp2Zero, fp2Zero, true)
      else
        let slope := tangentSlope s.rx s.ry
        let lv := lineFunc slope s.rx s.ry px py
        let f2 := fp12Mul f' lv
        let nx := fp2Sub (fp2Sq slope) (fp2ScalarMul 2 s.rx)
        let ny := fp2Sub (fp2Mul slope (fp2Sub s.rx nx)) s.ry
        (f2, nx, ny, false)
    -- Addition step
    if bit && !rInf' then
      if rx' == qx then
        if ry' == qy then
          { rx := rx', ry := ry', rInf := rInf', f := f'' }
        else
          { rx := fp2Zero, ry := fp2Zero, rInf := true, f := f'' }
      else
        let slope := chordSlope rx' ry' qx qy
        let lv := lineFunc slope rx' ry' px py
        let f3 := fp12Mul f'' lv
        let nx := fp2Sub (fp2Sub (fp2Sq slope) rx') qx
        let ny := fp2Sub (fp2Mul slope (fp2Sub rx' nx)) ry'
        { rx := nx, ry := ny, rInf := false, f := f3 }
    else
      { rx := rx', ry := ry', rInf := rInf', f := f'' }

-- Get bit at position pos (0-indexed from LSB)
@[inline] def getBit (n : Nat) (pos : Nat) : Bool := (n >>> pos) &&& 1 == 1

-- Frobenius correction step: add a point to the running state
def addCorrectionPoint (s : MillerState) (qx qy : Fp2) (qInf : Bool) (px py : Fp) : MillerState :=
  if s.rInf || qInf then s
  else if s.rx == qx then
    if s.ry == qy then
      if fp2IsZero s.ry then s
      else
        let slope := tangentSlope s.rx s.ry
        let lv := lineFunc slope s.rx s.ry px py
        let f' := fp12Mul s.f lv
        let r := g2Double ⟨s.rx, s.ry, false⟩
        { rx := r.x, ry := r.y, rInf := r.inf, f := f' }
    else
      { s with rInf := true }
  else
    let slope := chordSlope s.rx s.ry qx qy
    let lv := lineFunc slope s.rx s.ry px py
    let f' := fp12Mul s.f lv
    let nx := fp2Sub (fp2Sub (fp2Sq slope) s.rx) qx
    let ny := fp2Sub (fp2Mul slope (fp2Sub s.rx nx)) s.ry
    { rx := nx, ry := ny, rInf := false, f := f' }

-- Main Miller loop
def millerLoop (q : G2Point) (p : G1Point) : Fp12 :=
  if p.inf || q.inf then fp12One
  else
    let px := p.x
    let py := p.y
    let qx := q.x
    let qy := q.y

    -- Initialize: R = Q, f = 1
    let initState : MillerState := {
      rx := qx, ry := qy, rInf := false, f := fp12One
    }

    -- Iterate from bit (ateLoopCountBits - 1) down to 0
    let state := (List.range ateLoopCountBits).foldl
      (fun s i =>
        let bitPos := ateLoopCountBits - 1 - i
        let bit := getBit ateLoopCount bitPos
        millerStep s qx qy px py bit)
      initState

    -- Frobenius corrections
    let q1 := g2Frobenius q
    let nq2 := g2Neg (g2Frobenius2 q)

    let state := addCorrectionPoint state q1.x q1.y q1.inf px py
    let state := addCorrectionPoint state nq2.x nq2.y nq2.inf px py

    state.f

-- ============================================================
-- Final exponentiation
-- ============================================================

def finalExp (f : Fp12) : Fp12 :=
  -- Easy part 1: f^(p^6 - 1) = conj(f) · f^(-1)
  let f1 := fp12Mul (fp12Conj f) (fp12Inv f)
  -- Easy part 2: f1^(p^2 + 1) = frob2(f1) · f1
  let f2 := fp12Mul (fp12Frob2 f1) f1
  -- Hard part: f2^((p^4 - p^2 + 1) / n)
  let hardExp := (fieldPrime ^ 4 - fieldPrime ^ 2 + 1) / curveOrder
  fp12Pow f2 hardExp

-- ============================================================
-- Pairing computation
-- ============================================================

def pairing (q : G2Point) (p : G1Point) : Fp12 :=
  finalExp (millerLoop q p)

-- Multi-pairing: product of Miller loops, then single final exponentiation
def multiMillerLoop (pairs : List (G2Point × G1Point)) : Fp12 :=
  pairs.foldl (fun acc ⟨q, p⟩ => fp12Mul acc (millerLoop q p)) fp12One

def multiPairing (pairs : List (G2Point × G1Point)) : Fp12 :=
  finalExp (multiMillerLoop pairs)

-- ============================================================
-- Byte encoding/decoding for EVM precompile
-- ============================================================

def readUint256 (data : ByteArray) (offset : Nat) : Nat := Id.run do
  let mut result : Nat := 0
  for i in [:32] do
    let idx := offset + i
    let byte : UInt8 := if idx < data.size then data[idx]! else 0
    result := result * 256 + byte.toNat
  return result

def writeUint256 (n : Nat) : ByteArray := Id.run do
  let mut bytes : Array UInt8 := Array.empty
  let mut val := n
  for _ in [:32] do
    bytes := bytes.push (val % 256).toUInt8
    val := val / 256
  -- Reverse to get big-endian
  let mut result := ByteArray.empty
  for i in [:32] do
    result := result.push (bytes[31 - i]!)
  return result

-- Zero-pad input to required length
def padInput (data : ByteArray) (len : Nat) : ByteArray := Id.run do
  let mut result := data
  for _ in [:len - data.size] do
    result := result.push 0
  return result

-- Decode G1 point from 64 bytes at offset
def decodeG1 (data : ByteArray) (offset : Nat) : Option G1Point :=
  let x := readUint256 data offset
  let y := readUint256 data (offset + 32)
  if x == 0 && y == 0 then
    some g1Inf
  else if x >= fieldPrime || y >= fieldPrime then
    none
  else
    let p : G1Point := ⟨x, y, false⟩
    if g1IsOnCurve p then some p
    else none

-- Decode G2 point from 128 bytes at offset
-- Encoding: x_imag(32) || x_real(32) || y_imag(32) || y_real(32)
def decodeG2 (data : ByteArray) (offset : Nat) : Option G2Point :=
  let xImag := readUint256 data offset
  let xReal := readUint256 data (offset + 32)
  let yImag := readUint256 data (offset + 64)
  let yReal := readUint256 data (offset + 96)
  if xImag == 0 && xReal == 0 && yImag == 0 && yReal == 0 then
    some g2Inf
  else if xImag >= fieldPrime || xReal >= fieldPrime ||
          yImag >= fieldPrime || yReal >= fieldPrime then
    none
  else
    let p : G2Point := ⟨⟨xReal, xImag⟩, ⟨yReal, yImag⟩, false⟩
    if g2IsOnCurve p then some p
    else none

def encodeResult (b : Bool) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for _ in [:31] do
    result := result.push 0
  result := result.push (if b then 1 else 0)
  return result

-- ============================================================
-- EVM Precompiles
-- ============================================================

-- bn256Add precompile (EIP-196)
def ecAddPrecompile (input : ByteArray) : Option ByteArray :=
  let data := padInput input 128
  let p1 := decodeG1 data 0
  let p2 := decodeG1 data 64
  match p1, p2 with
  | some p1, some p2 =>
    let result := g1Add p1 p2
    if result.inf then
      some (writeUint256 0 ++ writeUint256 0)
    else
      some (writeUint256 result.x ++ writeUint256 result.y)
  | _, _ => none

-- bn256ScalarMul precompile (EIP-196)
def ecMulPrecompile (input : ByteArray) : Option ByteArray :=
  let data := padInput input 96
  let p := decodeG1 data 0
  let s := readUint256 data 64
  match p with
  | some p =>
    let result := g1ScalarMul s p
    if result.inf then
      some (writeUint256 0 ++ writeUint256 0)
    else
      some (writeUint256 result.x ++ writeUint256 result.y)
  | none => none

-- bn256Pairing precompile (EIP-197)
def ecPairingPrecompile (input : ByteArray) : Option ByteArray :=
  if input.size % 192 != 0 then none
  else
    let numPairs := input.size / 192
    -- Decode all pairs
    let rec decodePairs (i : Nat) (acc : List (G2Point × G1Point)) : Option (List (G2Point × G1Point)) :=
      if i >= numPairs then some acc.reverse
      else
        let offset := i * 192
        match decodeG1 input offset, decodeG2 input (offset + 64) with
        | some p, some q => decodePairs (i + 1) ((q, p) :: acc)
        | _, _ => none
    termination_by numPairs - i
    match decodePairs 0 [] with
    | none => none
    | some pairs =>
      let result := multiPairing pairs
      some (encodeResult (result == fp12One))

end ETHCryptoLean.BN256
