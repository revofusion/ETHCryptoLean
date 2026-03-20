/-
  BLS12-381 field arithmetic: Fp, Fp2, Fp6, Fp12
  All arithmetic uses Nat with explicit modular reduction.
-/

namespace BLS12381

-- BLS12-381 field prime
def P : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

-- BLS12-381 curve order (subgroup order)
def R : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

-- Ate loop parameter |x| (the actual x is negative)
def X_ABS : Nat := 0xd201000000010000

-- ═══════════════════════════════════════════
-- Fp: integers mod P
-- ═══════════════════════════════════════════

@[inline] def fpAdd (a b : Nat) : Nat := (a + b) % P
@[inline] def fpSub (a b : Nat) : Nat := (a % P + P - b % P) % P
@[inline] def fpMul (a b : Nat) : Nat := (a * b) % P
@[inline] def fpNeg (a : Nat) : Nat := if a % P == 0 then 0 else P - a % P
@[inline] def fpEq  (a b : Nat) : Bool := a % P == b % P

partial def fpPow (base exp : Nat) : Nat :=
  if exp == 0 then 1
  else if exp == 1 then base % P
  else
    let half := fpPow base (exp / 2)
    let sq := (half * half) % P
    if exp % 2 == 0 then sq
    else (sq * (base % P)) % P

def fpInv (a : Nat) : Nat := fpPow a (P - 2)
def fpDiv (a b : Nat) : Nat := fpMul a (fpInv b)

-- Square root in Fp
def fpSqrt (a : Nat) : Option Nat :=
  let s := fpPow a ((P + 1) / 4)
  if fpMul s s == a % P then some s else none

-- Lexicographic "sign": true if a > (P-1)/2
def fpSign (a : Nat) : Bool := a % P > (P - 1) / 2

-- ═══════════════════════════════════════════
-- Fp2 = Fp[u] / (u² + 1)
-- Element: c0 + c1 * u
-- ═══════════════════════════════════════════

structure Fp2 where
  c0 : Nat
  c1 : Nat
  deriving BEq, Repr

def fp2Zero : Fp2 := ⟨0, 0⟩
def fp2One  : Fp2 := ⟨1, 0⟩

@[inline] def fp2IsZero (a : Fp2) : Bool := a.c0 % P == 0 && a.c1 % P == 0

def fp2Add (a b : Fp2) : Fp2 := ⟨fpAdd a.c0 b.c0, fpAdd a.c1 b.c1⟩
def fp2Sub (a b : Fp2) : Fp2 := ⟨fpSub a.c0 b.c0, fpSub a.c1 b.c1⟩
def fp2Neg (a : Fp2) : Fp2 := ⟨fpNeg a.c0, fpNeg a.c1⟩

def fp2Mul (a b : Fp2) : Fp2 :=
  ⟨fpSub (fpMul a.c0 b.c0) (fpMul a.c1 b.c1),
   fpAdd (fpMul a.c0 b.c1) (fpMul a.c1 b.c0)⟩

def fp2Sq (a : Fp2) : Fp2 := fp2Mul a a

def fp2MulScalar (a : Fp2) (s : Nat) : Fp2 := ⟨fpMul a.c0 s, fpMul a.c1 s⟩

-- Conjugate: (a + bu) → (a - bu)
def fp2Conj (a : Fp2) : Fp2 := ⟨a.c0 % P, fpNeg a.c1⟩

-- Norm: N(a+bu) = a² + b²
def fp2Norm (a : Fp2) : Nat := fpAdd (fpMul a.c0 a.c0) (fpMul a.c1 a.c1)

def fp2Inv (a : Fp2) : Fp2 :=
  let n := fp2Norm a
  let nInv := fpInv n
  ⟨fpMul (a.c0 % P) nInv, fpMul (fpNeg a.c1) nInv⟩

def fp2Div (a b : Fp2) : Fp2 := fp2Mul a (fp2Inv b)

-- Multiply by u
def fp2MulByU (a : Fp2) : Fp2 := ⟨fpNeg a.c1, a.c0 % P⟩

partial def fp2Pow (base : Fp2) (exp : Nat) : Fp2 :=
  if exp == 0 then fp2One
  else if exp == 1 then ⟨base.c0 % P, base.c1 % P⟩
  else
    let half := fp2Pow base (exp / 2)
    let sq := fp2Mul half half
    if exp % 2 == 0 then sq
    else fp2Mul sq ⟨base.c0 % P, base.c1 % P⟩

-- Fp2 sign for point compression (lexicographic, imaginary part first)
def fp2Sign (a : Fp2) : Bool :=
  if a.c1 % P != 0 then fpSign a.c1
  else fpSign a.c0

-- Square root in Fp2
def fp2Sqrt (a : Fp2) : Option Fp2 :=
  if fp2IsZero a then some fp2Zero
  else if a.c1 % P == 0 then
    match fpSqrt a.c0 with
    | some s => some ⟨s, 0⟩
    | none =>
      -- Try sqrt(-a0) * u
      match fpSqrt (fpNeg a.c0) with
      | some s => some ⟨0, s⟩
      | none => none
  else
    let norm := fp2Norm a
    match fpSqrt norm with
    | none => none
    | some sqrtNorm =>
      let two_inv := fpInv 2
      let b0sq := fpMul (fpAdd (a.c0 % P) sqrtNorm) two_inv
      match fpSqrt b0sq with
      | some b0 =>
        let b1 := fpDiv (a.c1 % P) (fpMul 2 b0)
        some ⟨b0, b1⟩
      | none =>
        let b0sq' := fpMul (fpSub (a.c0 % P) sqrtNorm) two_inv
        match fpSqrt b0sq' with
        | some b0 =>
          let b1 := fpDiv (a.c1 % P) (fpMul 2 b0)
          some ⟨b0, b1⟩
        | none => none

def fp2Eq (a b : Fp2) : Bool := fpEq a.c0 b.c0 && fpEq a.c1 b.c1

-- ═══════════════════════════════════════════
-- Fp6 = Fp2[v] / (v³ - ξ) where ξ = 1 + u
-- Element: c0 + c1·v + c2·v²
-- ═══════════════════════════════════════════

-- The non-residue ξ = 1 + u in Fp2
def XI : Fp2 := ⟨1, 1⟩

structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving BEq, Repr

def fp6Zero : Fp6 := ⟨fp2Zero, fp2Zero, fp2Zero⟩
def fp6One  : Fp6 := ⟨fp2One, fp2Zero, fp2Zero⟩

@[inline] def fp6IsZero (a : Fp6) : Bool :=
  fp2IsZero a.c0 && fp2IsZero a.c1 && fp2IsZero a.c2

def fp6Add (a b : Fp6) : Fp6 :=
  ⟨fp2Add a.c0 b.c0, fp2Add a.c1 b.c1, fp2Add a.c2 b.c2⟩

def fp6Sub (a b : Fp6) : Fp6 :=
  ⟨fp2Sub a.c0 b.c0, fp2Sub a.c1 b.c1, fp2Sub a.c2 b.c2⟩

def fp6Neg (a : Fp6) : Fp6 :=
  ⟨fp2Neg a.c0, fp2Neg a.c1, fp2Neg a.c2⟩

-- Multiply an Fp2 element by ξ = 1 + u
def fp2MulByXi (x : Fp2) : Fp2 := fp2Mul x XI

-- Multiply Fp6 element by v
def fp6MulByV (a : Fp6) : Fp6 :=
  ⟨fp2MulByXi a.c2, a.c0, a.c1⟩

def fp6Mul (a b : Fp6) : Fp6 :=
  let t0 := fp2Mul a.c0 b.c0
  let t1 := fp2Mul a.c1 b.c1
  let t2 := fp2Mul a.c2 b.c2
  let c0 := fp2Add t0 (fp2MulByXi (fp2Sub (fp2Mul (fp2Add a.c1 a.c2) (fp2Add b.c1 b.c2)) (fp2Add t1 t2)))
  let c1 := fp2Add (fp2Sub (fp2Mul (fp2Add a.c0 a.c1) (fp2Add b.c0 b.c1)) (fp2Add t0 t1)) (fp2MulByXi t2)
  let c2 := fp2Add (fp2Sub (fp2Mul (fp2Add a.c0 a.c2) (fp2Add b.c0 b.c2)) (fp2Add t0 t2)) t1
  ⟨c0, c1, c2⟩

def fp6Sq (a : Fp6) : Fp6 := fp6Mul a a

def fp6MulScalar (a : Fp6) (s : Fp2) : Fp6 :=
  ⟨fp2Mul a.c0 s, fp2Mul a.c1 s, fp2Mul a.c2 s⟩

-- Inverse in Fp6 via cofactor method
def fp6Inv (a : Fp6) : Fp6 :=
  let t0 := fp2Sq a.c0
  let t1 := fp2Sq a.c1
  let t2 := fp2Sq a.c2
  let t3 := fp2Mul a.c0 a.c1
  let t4 := fp2Mul a.c0 a.c2
  let t5 := fp2Mul a.c1 a.c2
  let c0 := fp2Sub t0 (fp2MulByXi t5)
  let c1 := fp2Sub (fp2MulByXi t2) t3
  let c2 := fp2Sub t1 t4
  let det := fp2Add (fp2Mul a.c0 c0) (fp2MulByXi (fp2Add (fp2Mul a.c2 c1) (fp2Mul a.c1 c2)))
  let detInv := fp2Inv det
  ⟨fp2Mul c0 detInv, fp2Mul c1 detInv, fp2Mul c2 detInv⟩

partial def fp6Pow (base : Fp6) (exp : Nat) : Fp6 :=
  if exp == 0 then fp6One
  else if exp == 1 then base
  else
    let half := fp6Pow base (exp / 2)
    let sq := fp6Mul half half
    if exp % 2 == 0 then sq
    else fp6Mul sq base

def fp6Eq (a b : Fp6) : Bool :=
  fp2Eq a.c0 b.c0 && fp2Eq a.c1 b.c1 && fp2Eq a.c2 b.c2

-- ═══════════════════════════════════════════
-- Fp12 = Fp6[w] / (w² - v)
-- Element: c0 + c1·w where c0, c1 ∈ Fp6
-- ═══════════════════════════════════════════

structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving BEq, Repr

def fp12Zero : Fp12 := ⟨fp6Zero, fp6Zero⟩
def fp12One  : Fp12 := ⟨fp6One, fp6Zero⟩

@[inline] def fp12IsZero (a : Fp12) : Bool :=
  fp6IsZero a.c0 && fp6IsZero a.c1

def fp12Add (a b : Fp12) : Fp12 :=
  ⟨fp6Add a.c0 b.c0, fp6Add a.c1 b.c1⟩

def fp12Sub (a b : Fp12) : Fp12 :=
  ⟨fp6Sub a.c0 b.c0, fp6Sub a.c1 b.c1⟩

def fp12Neg (a : Fp12) : Fp12 :=
  ⟨fp6Neg a.c0, fp6Neg a.c1⟩

def fp12Mul (a b : Fp12) : Fp12 :=
  let t0 := fp6Mul a.c0 b.c0
  let t1 := fp6Mul a.c1 b.c1
  let c0 := fp6Add t0 (fp6MulByV t1)
  let c1 := fp6Sub (fp6Mul (fp6Add a.c0 a.c1) (fp6Add b.c0 b.c1)) (fp6Add t0 t1)
  ⟨c0, c1⟩

def fp12Sq (a : Fp12) : Fp12 := fp12Mul a a

-- Conjugate in Fp12: (a + bw) → (a - bw)
def fp12Conj (a : Fp12) : Fp12 := ⟨a.c0, fp6Neg a.c1⟩

def fp12Inv (a : Fp12) : Fp12 :=
  let t0 := fp6Sq a.c0
  let t1 := fp6Sq a.c1
  let det := fp6Sub t0 (fp6MulByV t1)
  let detInv := fp6Inv det
  ⟨fp6Mul a.c0 detInv, fp6Neg (fp6Mul a.c1 detInv)⟩

def fp12Div (a b : Fp12) : Fp12 := fp12Mul a (fp12Inv b)

partial def fp12Pow (base : Fp12) (exp : Nat) : Fp12 :=
  if exp == 0 then fp12One
  else if exp == 1 then base
  else
    let half := fp12Pow base (exp / 2)
    let sq := fp12Mul half half
    if exp % 2 == 0 then sq
    else fp12Mul sq base

def fp12Eq (a b : Fp12) : Bool :=
  fp6Eq a.c0 b.c0 && fp6Eq a.c1 b.c1

-- Embed Fp into Fp12
def fpToFp12 (a : Nat) : Fp12 :=
  ⟨⟨⟨a % P, 0⟩, fp2Zero, fp2Zero⟩, fp6Zero⟩

-- Embed Fp2 into Fp12
def fp2ToFp12 (a : Fp2) : Fp12 :=
  ⟨⟨a, fp2Zero, fp2Zero⟩, fp6Zero⟩

-- Embed Fp2 into Fp6
def fp2ToFp6 (a : Fp2) : Fp6 :=
  ⟨a, fp2Zero, fp2Zero⟩

end BLS12381
