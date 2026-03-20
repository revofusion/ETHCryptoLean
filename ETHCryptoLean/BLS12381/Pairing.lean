/-
  BLS12-381 optimal Ate pairing
  e : G1 × G2 → GT ⊂ Fp12*
-/

import ETHCryptoLean.BLS12381.Curve

namespace BLS12381

-- ═══════════════════════════════════════════
-- Line functions for Miller loop
-- ═══════════════════════════════════════════

-- Tangent line at T evaluated at P
private def lineDouble (t : G12Point) (p : G12Point) : Fp12 :=
  match t, p with
  | .affine xt yt, .affine xp yp =>
    let xt_sq := fp12Mul xt xt
    let lam := fp12Div (fp12Mul (fpToFp12 3) xt_sq) (fp12Mul (fpToFp12 2) yt)
    fp12Sub yp (fp12Add yt (fp12Mul lam (fp12Sub xp xt)))
  | _, _ => fp12One

-- Line through T and Q evaluated at P
private def lineAdd (t q : G12Point) (p : G12Point) : Fp12 :=
  match t, q, p with
  | .affine xt yt, .affine xq yq, .affine xp yp =>
    if fp12Eq xt xq then
      -- Vertical line: xP - xT
      fp12Sub xp xt
    else
      let lam := fp12Div (fp12Sub yq yt) (fp12Sub xq xt)
      fp12Sub yp (fp12Add yt (fp12Mul lam (fp12Sub xp xt)))
  | _, _, _ => fp12One

-- ═══════════════════════════════════════════
-- Miller loop
-- ═══════════════════════════════════════════

-- Get bits of n in MSB-first order (excluding leading zero)
partial def toBitsMSB (n : Nat) : List Bool :=
  if n == 0 then []
  else if n == 1 then [true]
  else toBitsMSB (n / 2) ++ [n % 2 == 1]

-- Miller loop for f_{|x|, Q}(P)
partial def millerLoop (p12 q12 : G12Point) : Fp12 :=
  match p12, q12 with
  | .infinity, _ => fp12One
  | _, .infinity => fp12One
  | _, _ =>
    let bits := toBitsMSB X_ABS
    match bits with
    | [] => fp12One
    | _ :: rest =>
      -- Start with f = 1, T = Q
      let (f, _) := rest.foldl (fun (acc : Fp12 × G12Point) bit =>
        let (f, t) := acc
        -- Doubling step
        let l_double := lineDouble t p12
        let f' := fp12Mul (fp12Sq f) l_double
        let t' := g12Add t t
        if bit then
          -- Addition step
          let l_add := lineAdd t' q12 p12
          let f'' := fp12Mul f' l_add
          let t'' := g12Add t' q12
          (f'', t'')
        else
          (f', t')
      ) (fp12One, q12)
      -- x is negative, so conjugate the result
      fp12Conj f

-- ═══════════════════════════════════════════
-- Final exponentiation
-- ═══════════════════════════════════════════

-- Easy part: f^(p^6 - 1)
private def easyPart1 (f : Fp12) : Fp12 :=
  fp12Mul (fp12Conj f) (fp12Inv f)

-- Frobenius constants: γ₁ = ξ^((p-1)/3), γ₂ = ξ^(2(p-1)/3)
private def GAMMA_1_1 : Fp2 := fp2Pow XI ((P - 1) / 3)
private def GAMMA_1_2 : Fp2 := fp2Pow XI (2 * (P - 1) / 3)

-- Frobenius on Fp12: γ_w = ξ^((p-1)/6)
private def GAMMA_W : Fp2 := fp2Pow XI ((P - 1) / 6)

private def fp6Frobenius (a : Fp6) : Fp6 :=
  ⟨fp2Conj a.c0,
   fp2Mul (fp2Conj a.c1) GAMMA_1_1,
   fp2Mul (fp2Conj a.c2) GAMMA_1_2⟩

private def fp12Frobenius (a : Fp12) : Fp12 :=
  ⟨fp6Frobenius a.c0,
   fp6MulScalar (fp6Frobenius a.c1) GAMMA_W⟩

-- Frobenius^2 constants
private def GAMMA_2_1 : Fp2 := fp2Pow XI ((P * P - 1) / 3)
private def GAMMA_2_2 : Fp2 := fp2Pow XI (2 * (P * P - 1) / 3)
private def GAMMA_2_W : Fp2 := fp2Pow XI ((P * P - 1) / 6)

private def fp6Frobenius2 (a : Fp6) : Fp6 :=
  ⟨a.c0,
   fp2Mul a.c1 GAMMA_2_1,
   fp2Mul a.c2 GAMMA_2_2⟩

private def fp12Frobenius2 (a : Fp12) : Fp12 :=
  ⟨fp6Frobenius2 a.c0,
   fp6MulScalar (fp6Frobenius2 a.c1) GAMMA_2_W⟩

-- Frobenius^3
private def GAMMA_3_1 : Fp2 := fp2Pow XI ((P ^ 3 - 1) / 3)
private def GAMMA_3_2 : Fp2 := fp2Pow XI (2 * (P ^ 3 - 1) / 3)
private def GAMMA_3_W : Fp2 := fp2Pow XI ((P ^ 3 - 1) / 6)

private def fp6Frobenius3 (a : Fp6) : Fp6 :=
  ⟨fp2Conj a.c0,
   fp2Mul (fp2Conj a.c1) GAMMA_3_1,
   fp2Mul (fp2Conj a.c2) GAMMA_3_2⟩

private def fp12Frobenius3 (a : Fp12) : Fp12 :=
  ⟨fp6Frobenius3 a.c0,
   fp6MulScalar (fp6Frobenius3 a.c1) GAMMA_3_W⟩

-- Hard part exponent: (p^4 - p^2 + 1) / r
private def hardPartExponent : Nat :=
  (P ^ 4 - P ^ 2 + 1) / R

private def finalExponentiation (f : Fp12) : Fp12 :=
  if fp12IsZero f then fp12Zero
  else
    let f1 := easyPart1 f
    let f2 := fp12Mul (fp12Frobenius2 f1) f1
    fp12Pow f2 hardPartExponent

-- ═══════════════════════════════════════════
-- Pairing function
-- ═══════════════════════════════════════════

-- Ate pairing: e(P, Q) for P ∈ G1, Q ∈ G2
-- Returns element of GT ⊂ Fp12*
def atePairing (p1 : G1Point) (q : G2Point) : Fp12 :=
  match p1, q with
  | .infinity, _ => fp12One
  | _, .infinity => fp12One
  | _, _ =>
    let p12 := g1ToG12 p1
    let q12 := g2ToG12 q
    let f := millerLoop p12 q12
    finalExponentiation f

-- Pairing check: e(P1, Q1) * e(P2, Q2) == 1
def pairingCheck (p1 : G1Point) (q1 : G2Point) (p2 : G1Point) (q2 : G2Point) : Bool :=
  let f1 := match p1, q1 with
    | .infinity, _ => fp12One
    | _, .infinity => fp12One
    | _, _ =>
      let p12 := g1ToG12 p1
      let q12 := g2ToG12 q1
      millerLoop p12 q12
  let f2 := match p2, q2 with
    | .infinity, _ => fp12One
    | _, .infinity => fp12One
    | _, _ =>
      let p12 := g1ToG12 p2
      let q12 := g2ToG12 q2
      millerLoop p12 q12
  let f := fp12Mul f1 f2
  let result := finalExponentiation f
  fp12Eq result fp12One

end BLS12381
