/-!
# BN256 (alt_bn128) Elliptic Curve

Implements the alt_bn128 elliptic curve operations for EVM precompiles
at addresses 0x06 (ecAdd), 0x07 (ecMul), and 0x08 (ecPairing).

Curve: y² = x³ + 3 over Fp
p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
n = 21888242871839275222246405745257275088548364400416034343698204186575808495617
-/

namespace ETHCryptoLean.BN256

-- ============================================================
-- Field Parameters
-- ============================================================

/-- The prime field modulus for alt_bn128. -/
def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The curve order. -/
def n : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

-- ============================================================
-- Fp: Prime Field Arithmetic (mod p)
-- ============================================================

def fpAdd (a b : Nat) : Nat := (a + b) % p
def fpSub (a b : Nat) : Nat := (a + p - b % p) % p
def fpMul (a b : Nat) : Nat := (a * b) % p
def fpNeg (a : Nat) : Nat := if a == 0 then 0 else p - a % p

partial def fpPow (base exp : Nat) : Nat :=
  if exp == 0 then 1
  else if exp == 1 then base % p
  else
    let half := fpPow base (exp / 2)
    let sq := fpMul half half
    if exp % 2 == 0 then sq
    else fpMul sq (base % p)

def fpInv (a : Nat) : Nat := fpPow a (p - 2)
def fpDiv (a b : Nat) : Nat := fpMul a (fpInv b)

-- ============================================================
-- G1: Points on y² = x³ + 3 over Fp
-- ============================================================

inductive G1Point where
  | infinity : G1Point
  | affine : (x : Nat) → (y : Nat) → G1Point
  deriving Repr, BEq

def g1OnCurve : G1Point → Bool
  | .infinity => true
  | .affine x y =>
    let lhs := fpMul y y
    let rhs := fpAdd (fpMul (fpMul x x) x) 3
    lhs == rhs

def g1Gen : G1Point := .affine 1 2

def g1Add (p1 p2 : G1Point) : G1Point :=
  match p1, p2 with
  | .infinity, q => q
  | q, .infinity => q
  | .affine x1 y1, .affine x2 y2 =>
    if x1 == x2 then
      if y1 == y2 then
        if y1 == 0 then .infinity
        else
          let s := fpDiv (fpMul 3 (fpMul x1 x1)) (fpMul 2 y1)
          let x3 := fpSub (fpMul s s) (fpAdd x1 x2)
          let y3 := fpSub (fpMul s (fpSub x1 x3)) y1
          .affine x3 y3
      else .infinity
    else
      let s := fpDiv (fpSub y2 y1) (fpSub x2 x1)
      let x3 := fpSub (fpSub (fpMul s s) x1) x2
      let y3 := fpSub (fpMul s (fpSub x1 x3)) y1
      .affine x3 y3

def g1Neg : G1Point → G1Point
  | .infinity => .infinity
  | .affine x y => .affine x (fpNeg y)

partial def g1Mul (pt : G1Point) (scalar : Nat) : G1Point :=
  if scalar == 0 then .infinity
  else if scalar == 1 then pt
  else
    let half := g1Mul pt (scalar / 2)
    let doubled := g1Add half half
    if scalar % 2 == 0 then doubled
    else g1Add doubled pt

-- ============================================================
-- Fp2: Quadratic Extension Field (a + b*i, where i² = -1)
-- ============================================================

structure Fp2 where
  a : Nat
  b : Nat
  deriving Repr, BEq

def fp2Zero : Fp2 := ⟨0, 0⟩
def fp2One : Fp2 := ⟨1, 0⟩

def fp2IsZero (x : Fp2) : Bool := x.a % p == 0 && x.b % p == 0

def fp2Add (x y : Fp2) : Fp2 := ⟨fpAdd x.a y.a, fpAdd x.b y.b⟩
def fp2Sub (x y : Fp2) : Fp2 := ⟨fpSub x.a y.a, fpSub x.b y.b⟩
def fp2Neg (x : Fp2) : Fp2 := ⟨fpNeg x.a, fpNeg x.b⟩

/-- (a+bi)(c+di) = (ac-bd) + (ad+bc)i -/
def fp2Mul (x y : Fp2) : Fp2 :=
  ⟨fpSub (fpMul x.a y.a) (fpMul x.b y.b),
   fpAdd (fpMul x.a y.b) (fpMul x.b y.a)⟩

def fp2Sq (x : Fp2) : Fp2 :=
  ⟨fpSub (fpMul x.a x.a) (fpMul x.b x.b),
   fpMul 2 (fpMul x.a x.b)⟩

def fp2ScalarMul (s : Nat) (x : Fp2) : Fp2 := ⟨fpMul s x.a, fpMul s x.b⟩

def fp2Norm (x : Fp2) : Nat := fpAdd (fpMul x.a x.a) (fpMul x.b x.b)

def fp2Inv (x : Fp2) : Fp2 :=
  let invNorm := fpInv (fp2Norm x)
  ⟨fpMul x.a invNorm, fpMul (fpNeg x.b) invNorm⟩

def fp2Div (x y : Fp2) : Fp2 := fp2Mul x (fp2Inv y)
def fp2Conj (x : Fp2) : Fp2 := ⟨x.a, fpNeg x.b⟩

partial def fp2Pow (base : Fp2) (exp : Nat) : Fp2 :=
  if exp == 0 then fp2One
  else if exp == 1 then base
  else
    let half := fp2Pow base (exp / 2)
    let sq := fp2Mul half half
    if exp % 2 == 0 then sq
    else fp2Mul sq base

/-- Multiply by ξ = 9 + i. (a+bi)(9+i) = (9a-b) + (a+9b)i -/
def fp2MulByNonResidue (x : Fp2) : Fp2 :=
  ⟨fpSub (fpMul 9 x.a) x.b, fpAdd x.a (fpMul 9 x.b)⟩

-- ============================================================
-- G2: Points on twisted curve y² = x³ + 3/(9+i) over Fp2
-- ============================================================

def twistB : Fp2 := fp2Div ⟨3, 0⟩ ⟨9, 1⟩

inductive G2Point where
  | infinity : G2Point
  | affine : (x : Fp2) → (y : Fp2) → G2Point
  deriving Repr, BEq

def g2OnCurve : G2Point → Bool
  | .infinity => true
  | .affine x y =>
    let lhs := fp2Sq y
    let rhs := fp2Add (fp2Mul (fp2Sq x) x) twistB
    lhs == rhs

def g2Add (p1 p2 : G2Point) : G2Point :=
  match p1, p2 with
  | .infinity, q => q
  | q, .infinity => q
  | .affine x1 y1, .affine x2 y2 =>
    if x1 == x2 then
      if y1 == y2 then
        if fp2IsZero y1 then .infinity
        else
          let s := fp2Div (fp2ScalarMul 3 (fp2Sq x1)) (fp2ScalarMul 2 y1)
          let x3 := fp2Sub (fp2Sq s) (fp2Add x1 x2)
          let y3 := fp2Sub (fp2Mul s (fp2Sub x1 x3)) y1
          .affine x3 y3
      else .infinity
    else
      let s := fp2Div (fp2Sub y2 y1) (fp2Sub x2 x1)
      let x3 := fp2Sub (fp2Sub (fp2Sq s) x1) x2
      let y3 := fp2Sub (fp2Mul s (fp2Sub x1 x3)) y1
      .affine x3 y3

def g2Neg : G2Point → G2Point
  | .infinity => .infinity
  | .affine x y => .affine x (fp2Neg y)

partial def g2Mul (pt : G2Point) (scalar : Nat) : G2Point :=
  if scalar == 0 then .infinity
  else if scalar == 1 then pt
  else
    let half := g2Mul pt (scalar / 2)
    let doubled := g2Add half half
    if scalar % 2 == 0 then doubled
    else g2Add doubled pt

-- ============================================================
-- Fp6 = Fp2[v] / (v³ - ξ), where ξ = 9 + i
-- ============================================================

structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving Repr, BEq

def fp6Zero : Fp6 := ⟨fp2Zero, fp2Zero, fp2Zero⟩
def fp6One : Fp6 := ⟨fp2One, fp2Zero, fp2Zero⟩

def fp6Add (x y : Fp6) : Fp6 :=
  ⟨fp2Add x.c0 y.c0, fp2Add x.c1 y.c1, fp2Add x.c2 y.c2⟩

def fp6Sub (x y : Fp6) : Fp6 :=
  ⟨fp2Sub x.c0 y.c0, fp2Sub x.c1 y.c1, fp2Sub x.c2 y.c2⟩

def fp6Neg (x : Fp6) : Fp6 :=
  ⟨fp2Neg x.c0, fp2Neg x.c1, fp2Neg x.c2⟩

def fp6Mul (x y : Fp6) : Fp6 :=
  let t0 := fp2Mul x.c0 y.c0
  let t1 := fp2Mul x.c1 y.c1
  let t2 := fp2Mul x.c2 y.c2
  let c0 := fp2Add t0 (fp2MulByNonResidue (fp2Sub (fp2Sub (fp2Mul (fp2Add x.c1 x.c2) (fp2Add y.c1 y.c2)) t1) t2))
  let c1 := fp2Add (fp2Sub (fp2Sub (fp2Mul (fp2Add x.c0 x.c1) (fp2Add y.c0 y.c1)) t0) t1) (fp2MulByNonResidue t2)
  let c2 := fp2Add (fp2Sub (fp2Sub (fp2Mul (fp2Add x.c0 x.c2) (fp2Add y.c0 y.c2)) t0) t2) t1
  ⟨c0, c1, c2⟩

def fp6Sq (x : Fp6) : Fp6 := fp6Mul x x

def fp6Inv (x : Fp6) : Fp6 :=
  let a := x.c0; let b := x.c1; let c := x.c2
  let t0 := fp2Sub (fp2Sq a) (fp2MulByNonResidue (fp2Mul b c))
  let t1 := fp2Sub (fp2MulByNonResidue (fp2Sq c)) (fp2Mul a b)
  let t2 := fp2Sub (fp2Sq b) (fp2Mul a c)
  let det := fp2Add (fp2Mul a t0) (fp2MulByNonResidue (fp2Add (fp2Mul c t1) (fp2Mul b t2)))
  let detInv := fp2Inv det
  ⟨fp2Mul t0 detInv, fp2Mul t1 detInv, fp2Mul t2 detInv⟩

/-- Multiply by v: shifts components with ξ-twist on overflow. -/
def fp6MulByNonResidue (x : Fp6) : Fp6 :=
  ⟨fp2MulByNonResidue x.c2, x.c0, x.c1⟩

-- ============================================================
-- Fp12 = Fp6[w] / (w² - v)
-- ============================================================

structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving Repr, BEq

def fp12Zero : Fp12 := ⟨fp6Zero, fp6Zero⟩
def fp12One : Fp12 := ⟨fp6One, fp6Zero⟩

def fp12Add (x y : Fp12) : Fp12 := ⟨fp6Add x.c0 y.c0, fp6Add x.c1 y.c1⟩
def fp12Sub (x y : Fp12) : Fp12 := ⟨fp6Sub x.c0 y.c0, fp6Sub x.c1 y.c1⟩
def fp12Neg (x : Fp12) : Fp12 := ⟨fp6Neg x.c0, fp6Neg x.c1⟩

/-- (a0 + a1*w)(b0 + b1*w) = (a0*b0 + a1*b1*v) + (a0*b1 + a1*b0)*w -/
def fp12Mul (x y : Fp12) : Fp12 :=
  let t0 := fp6Mul x.c0 y.c0
  let t1 := fp6Mul x.c1 y.c1
  ⟨fp6Add t0 (fp6MulByNonResidue t1),
   fp6Sub (fp6Sub (fp6Mul (fp6Add x.c0 x.c1) (fp6Add y.c0 y.c1)) t0) t1⟩

def fp12Sq (x : Fp12) : Fp12 := fp12Mul x x

def fp12Inv (x : Fp12) : Fp12 :=
  let t := fp6Sub (fp6Sq x.c0) (fp6MulByNonResidue (fp6Sq x.c1))
  let tInv := fp6Inv t
  ⟨fp6Mul x.c0 tInv, fp6Neg (fp6Mul x.c1 tInv)⟩

def fp12Conj (x : Fp12) : Fp12 := ⟨x.c0, fp6Neg x.c1⟩

partial def fp12Pow (base : Fp12) (exp : Nat) : Fp12 :=
  if exp == 0 then fp12One
  else if exp == 1 then base
  else
    let half := fp12Pow base (exp / 2)
    let sq := fp12Sq half
    if exp % 2 == 0 then sq
    else fp12Mul sq base

-- ============================================================
-- Line Functions for Optimal Ate Pairing
-- ============================================================

/-- Evaluate line through T and Q at point P (for addition step).
    Returns a sparse Fp12 element. -/
def lineFuncAdd (t q : G2Point) (pG1 : G1Point) : Fp12 :=
  match t, q, pG1 with
  | .affine xt yt, .affine xq yq, .affine xp yp =>
    let slope := fp2Div (fp2Sub yq yt) (fp2Sub xq xt)
    -- Line evaluation at P encoded in Fp12
    ⟨⟨fp2Sub (fp2Mul slope xt) yt, ⟨fpNeg yp, 0⟩, fp2Zero⟩,
     ⟨fp2Neg slope, ⟨xp, 0⟩, fp2Zero⟩⟩
  | _, _, _ => fp12One

/-- Evaluate tangent line at T at point P (for doubling step). -/
def lineFuncDouble (t : G2Point) (pG1 : G1Point) : Fp12 :=
  match t, pG1 with
  | .affine xt yt, .affine xp yp =>
    if fp2IsZero yt then fp12One
    else
      let slope := fp2Div (fp2ScalarMul 3 (fp2Sq xt)) (fp2ScalarMul 2 yt)
      ⟨⟨fp2Sub (fp2Mul slope xt) yt, ⟨fpNeg yp, 0⟩, fp2Zero⟩,
       ⟨fp2Neg slope, ⟨xp, 0⟩, fp2Zero⟩⟩
  | _, _ => fp12One

-- ============================================================
-- Optimal Ate Pairing
-- ============================================================

/-- The ate loop count: 6t + 2 = 29793968203157093289. -/
def ateLoopCount : Nat := 29793968203157093289

/-- Get bits of ate loop count (LSB first). -/
partial def natToBits (nn : Nat) : Array Bool :=
  if nn == 0 then #[]
  else
    let rest := natToBits (nn / 2)
    #[nn % 2 == 1] ++ rest

/-- Miller loop for optimal Ate pairing. -/
partial def millerLoop (q : G2Point) (pPt : G1Point) : Fp12 :=
  match q, pPt with
  | .infinity, _ => fp12One
  | _, .infinity => fp12One
  | .affine _ _, .affine _ _ =>
    let bits := natToBits ateLoopCount
    if bits.size <= 1 then fp12One
    else
      -- Start from the most significant bit (which is always 1)
      -- and iterate down to bit 0
      let topIdx := bits.size - 1
      -- Initialize: T = Q, f = 1
      go (topIdx - 1) q pPt bits fp12One q
  where
    go (idx : Nat) (q : G2Point) (pPt : G1Point) (bits : Array Bool)
        (f : Fp12) (t : G2Point) : Fp12 :=
      -- Doubling step
      let lf := lineFuncDouble t pPt
      let f := fp12Mul (fp12Sq f) lf
      let t := g2Add t t
      -- Addition step if bit is set
      let (f, t) :=
        if bits[idx]! then
          let lf := lineFuncAdd t q pPt
          (fp12Mul f lf, g2Add t q)
        else (f, t)
      if idx == 0 then f
      else go (idx - 1) q pPt bits f t

/-- Final exponentiation: f^((p^12 - 1) / n). -/
def finalExp (f : Fp12) : Fp12 :=
  -- Easy part: f^(p^6 - 1)
  let f1 := fp12Conj f
  let f2 := fp12Inv f
  let t0 := fp12Mul f1 f2

  -- f^(p^2 + 1) on the result
  let t1 := fp12Pow t0 (p * p)
  let t0 := fp12Mul t1 t0

  -- Hard part: exponentiation by (p^4 - p^2 + 1) / n
  let hardExp := ((p ^ 4 - p ^ 2 + 1) / n)
  fp12Pow t0 hardExp

/-- Compute the optimal Ate pairing e(P, Q). -/
def pairing (pPt : G1Point) (q : G2Point) : Fp12 :=
  let f := millerLoop q pPt
  finalExp f

-- ============================================================
-- Precompile Interfaces
-- ============================================================

/-- Read a 32-byte big-endian number from input. -/
partial def readBytes32 (input : Array UInt8) (offset : Nat) : Nat :=
  let rec go (i : Nat) (acc : Nat) : Nat :=
    if i >= 32 then acc
    else
      let idx := offset + i
      let b := if idx < input.size then input[idx]!.toNat else 0
      go (i + 1) (acc * 256 + b)
  go 0 0

/-- Write a natural number as 32 big-endian bytes. -/
def writeBytes32 (nn : Nat) : Array UInt8 :=
  (List.range 32).map (fun i =>
    let shift := (31 - i) * 8
    ((nn >>> shift) % 256).toUInt8) |>.toArray

/-- EC Add precompile (0x06). -/
def ecAdd (p1x p1y p2x p2y : Nat) : Option (Nat × Nat) :=
  let pt1 := if p1x == 0 && p1y == 0 then G1Point.infinity
             else G1Point.affine (p1x % p) (p1y % p)
  let pt2 := if p2x == 0 && p2y == 0 then G1Point.infinity
             else G1Point.affine (p2x % p) (p2y % p)
  if !g1OnCurve pt1 || !g1OnCurve pt2 then none
  else
    match g1Add pt1 pt2 with
    | .infinity => some (0, 0)
    | .affine x y => some (x, y)

/-- EC Mul precompile (0x07). -/
def ecMul (px py s : Nat) : Option (Nat × Nat) :=
  let pt := if px == 0 && py == 0 then G1Point.infinity
            else G1Point.affine (px % p) (py % p)
  if !g1OnCurve pt then none
  else
    match g1Mul pt s with
    | .infinity => some (0, 0)
    | .affine x y => some (x, y)

/-- EC Pairing precompile (0x08). -/
def ecPairing (pairs : Array (Nat × Nat × Nat × Nat × Nat × Nat)) : Bool :=
  let result := pairs.foldl (fun acc ⟨g1x, g1y, g2xi, g2xr, g2yi, g2yr⟩ =>
    let p1 := if g1x == 0 && g1y == 0 then G1Point.infinity
              else G1Point.affine (g1x % p) (g1y % p)
    let q := if g2xr == 0 && g2xi == 0 && g2yr == 0 && g2yi == 0 then G2Point.infinity
             else G2Point.affine ⟨g2xr % p, g2xi % p⟩ ⟨g2yr % p, g2yi % p⟩
    let f := pairing p1 q
    fp12Mul acc f) fp12One
  result == fp12One

/-- EC Add precompile wrapper (bytes). -/
def ecAddPrecompile (input : Array UInt8) : Option (Array UInt8) :=
  let p1x := readBytes32 input 0
  let p1y := readBytes32 input 32
  let p2x := readBytes32 input 64
  let p2y := readBytes32 input 96
  match ecAdd p1x p1y p2x p2y with
  | none => none
  | some (rx, ry) => some (writeBytes32 rx ++ writeBytes32 ry)

/-- EC Mul precompile wrapper (bytes). -/
def ecMulPrecompile (input : Array UInt8) : Option (Array UInt8) :=
  let px := readBytes32 input 0
  let py := readBytes32 input 32
  let s := readBytes32 input 64
  match ecMul px py s with
  | none => none
  | some (rx, ry) => some (writeBytes32 rx ++ writeBytes32 ry)

/-- EC Pairing precompile wrapper (bytes). -/
def ecPairingPrecompile (input : Array UInt8) : Option (Array UInt8) :=
  if input.size % 192 != 0 then none
  else
    let numPairs := input.size / 192
    let pairs := (List.range numPairs).foldl (fun arr i =>
      let off := i * 192
      arr.push (readBytes32 input off,
                readBytes32 input (off + 32),
                readBytes32 input (off + 64),
                readBytes32 input (off + 96),
                readBytes32 input (off + 128),
                readBytes32 input (off + 160))) #[]
    let valid := pairs.all (fun ⟨g1x, g1y, g2xi, g2xr, g2yi, g2yr⟩ =>
      let p1 := if g1x == 0 && g1y == 0 then G1Point.infinity
                else G1Point.affine (g1x % p) (g1y % p)
      let q := if g2xr == 0 && g2xi == 0 && g2yr == 0 && g2yi == 0 then G2Point.infinity
               else G2Point.affine ⟨g2xr % p, g2xi % p⟩ ⟨g2yr % p, g2yi % p⟩
      g1OnCurve p1 && g2OnCurve q)
    if !valid then none
    else
      let result := ecPairing pairs
      if result then some (writeBytes32 1)
      else some (writeBytes32 0)

-- ============================================================
end ETHCryptoLean.BN256
