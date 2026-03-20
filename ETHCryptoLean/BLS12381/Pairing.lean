/-
  BLS12-381 optimal Ate pairing
  e : G1 × G2 → GT ⊂ Fp12*
-/

import ETHCryptoLean.BLS12381.Curve

namespace BLS12381

-- ═══════════════════════════════════════════
-- Line functions for Miller loop
-- ═══════════════════════════════════════════

-- Line function evaluation: tangent line at T evaluated at P
-- T is on E(Fp12), P is on E(Fp12)
-- Returns: yP - yT - λ(xP - xT) where λ = 3xT²/(2yT)
private def lineDouble (t : G12Point) (p : G12Point) : Fp12 :=
  match t, p with
  | .affine xt yt, .affine xp yp =>
    let xt_sq := fp12Mul xt xt
    let lam := fp12Div (fp12Mul (fpToFp12 3) xt_sq) (fp12Mul (fpToFp12 2) yt)
    fp12Sub yp (fp12Add yt (fp12Mul lam (fp12Sub xp xt)))
  | _, _ => fp12One

-- Line function evaluation: line through T and Q evaluated at P
-- Returns: yP - yT - λ(xP - xT) where λ = (yQ - yT)/(xQ - xT)
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
-- Iterates over bits of |x| from second-MSB to LSB
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

-- Final exponentiation: f^((p^12 - 1) / r)
-- Decomposed as:
--   (p^12 - 1) / r = (p^6 - 1) · (p^2 + 1) · ((p^4 - p^2 + 1) / r)

-- Easy part step 1: f^(p^6 - 1)
-- f^(p^6) = conjugate(f), so f^(p^6-1) = conj(f) / f
private def easyPart1 (f : Fp12) : Fp12 :=
  fp12Mul (fp12Conj f) (fp12Inv f)

-- Easy part step 2: f^(p^2 + 1)
-- We compute f^(p^2) using Frobenius and multiply by f
-- For now, use naive exponentiation for f^(p^2)
-- f^(p^2+1) = f^(p^2) · f
-- Since after easy part 1 we have an element of order dividing p^6+1,
-- f^(p^2) can be computed via the Frobenius p^2 map.
-- For a generic implementation, we use:
--   f^(p²) via fp12Pow
-- But p² is huge. Instead, note that after easyPart1, the element
-- is in the p^6+1 torsion. We can compute the Frobenius.
--
-- For simplicity and correctness, we just compute the full exponent.

-- Frobenius endomorphism on Fp2: σ(a + bu) = a - bu (conjugation)
-- This is already fp2Conj

-- Frobenius constants for Fp6 and Fp12
-- These are ξ^((p-1)/3), ξ^(2(p-1)/3), etc.
-- We compute them on the fly using fp2Pow.

-- Frobenius on Fp6: given a = a0 + a1·v + a2·v²
-- σ(a) = σ(a0) + σ(a1)·v^p + σ(a2)·v^(2p)
-- v^p = v · ξ^((p-1)/3), v^(2p) = v² · ξ^(2(p-1)/3)
-- So σ(a) = conj(a0) + conj(a1)·γ₁·v + conj(a2)·γ₂·v²
-- where γ₁ = ξ^((p-1)/3), γ₂ = ξ^(2(p-1)/3)

private def GAMMA_1_1 : Fp2 := fp2Pow XI ((P - 1) / 3)
private def GAMMA_1_2 : Fp2 := fp2Pow XI (2 * (P - 1) / 3)

-- v^((p-1)/2) needed for Frobenius on Fp12
-- v^p = γ₁ · v, so v^((p-1)/2) = ?
-- w^p = w · (v^((p-1)/2))... hmm
-- Actually w² = v, so w^p = w · (w²)^((p-1)/2) = w · v^((p-1)/2)
-- v^((p-1)/2) = (v³)^((p-1)/6) = ξ^((p-1)/6)
private def GAMMA_W : Fp2 := fp2Pow XI ((P - 1) / 6)

private def fp6Frobenius (a : Fp6) : Fp6 :=
  ⟨fp2Conj a.c0,
   fp2Mul (fp2Conj a.c1) GAMMA_1_1,
   fp2Mul (fp2Conj a.c2) GAMMA_1_2⟩

private def fp12Frobenius (a : Fp12) : Fp12 :=
  ⟨fp6Frobenius a.c0,
   fp6MulScalar (fp6Frobenius a.c1) GAMMA_W⟩

-- Frobenius^2 on Fp2: identity (p²-Frobenius fixes Fp2)
-- Frobenius^2 on Fp6:
-- v^(p²) = v · ξ^((p²-1)/3)
private def GAMMA_2_1 : Fp2 := fp2Pow XI ((P * P - 1) / 3)
private def GAMMA_2_2 : Fp2 := fp2Pow XI (2 * (P * P - 1) / 3)
private def GAMMA_2_W : Fp2 := fp2Pow XI ((P * P - 1) / 6)

private def fp6Frobenius2 (a : Fp6) : Fp6 :=
  -- p²-Frobenius fixes Fp2, so no conjugation
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

-- Hard part of final exponentiation
-- Exponent: (p^4 - p^2 + 1) / r
-- Using the BLS12 decomposition from Devegili et al.
-- The exponent can be written as:
--   d = (x-1)² · (x+p) · (x²+p²) / 3 + ... (not exactly)
-- For a correct but possibly slow implementation, we compute:
--   d = (p^4 - p^2 + 1) / r directly and use fp12Pow
-- But that's a ~1269-bit exponent.
--
-- Better approach using the parameterized formula for BLS12:
-- From Algorithm 31 of "Guide to Pairing-Based Cryptography" or
-- Bowe's implementation, the hard part can be computed using:
--   a few exponentiations by |x|, Frobenius maps, and multiplications.
--
-- The formula (following gnark/bls12-381):
-- Let t = f^|x| (exponentiation by the curve parameter)
-- Then the hard part uses specific combinations of f, t, t², Frobenius maps.
--
-- For BLS12 curves, the hard part exponent is:
--   h = (x^3 - x^2 + 1)/r + x^2 · (p - 1) + (x - 1) · p^2 + p^3
-- Wait, that's not right either. Let me use a known correct decomposition.
--
-- From the paper "Faster Hashing to G2" (Budroni & Pintore) and
-- implementations in gnark, the BLS12-381 hard part uses:
--
--   result = f^λ₀ · frob(f)^λ₁ · frob²(f)^λ₂ · frob³(f)^λ₃
-- where λᵢ are specific small(ish) values.
--
-- Actually, the simplest correct approach for BLS12:
-- The hard part exponent (p^4 - p^2 + 1)/r = 1 + (x-1)²·p·(p²+1)/3·r^(-1)...
-- This is getting complicated. Let me just compute the exponent directly.

private def hardPartExponent : Nat :=
  (P ^ 4 - P ^ 2 + 1) / R

private def finalExponentiation (f : Fp12) : Fp12 :=
  if fp12IsZero f then fp12Zero
  else
    -- Easy part: f^(p^6-1) then ^(p^2+1)
    let f1 := easyPart1 f
    -- f^(p^2+1): use Frobenius for f^(p^2), then multiply by f
    let f2 := fp12Mul (fp12Frobenius2 f1) f1
    -- Hard part: f^((p^4 - p^2 + 1)/r)
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
-- More efficient: compute both Miller loops and do single final exponentiation
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
