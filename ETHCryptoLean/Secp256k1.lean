/-
  secp256k1 elliptic curve operations for ECDSA recovery.
  Pure Lean 4 implementation — no FFI, no opaque, no axiom.
  Curve: y² = x³ + 7 (mod p)
-/
import ETHCryptoLean.UInt256

namespace Secp256k1

-- secp256k1 field prime
def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

-- secp256k1 curve order
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

-- Generator point G
def Gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def Gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def modAdd (a b m : Nat) : Nat := (a + b) % m
def modSub (a b m : Nat) : Nat := (a + m - b % m) % m
def modMul (a b m : Nat) : Nat := (a * b) % m

def extGcd (a b : Int) : Int × Int × Int :=
  if h : b = 0 then (a, 1, 0)
  else
    let (g, x, y) := extGcd b (a % b)
    (g, y, x - (a / b) * y)
termination_by b.natAbs
decreasing_by
  have h1 : 0 ≤ a % b := Int.emod_nonneg a h
  rcases Int.lt_or_lt_of_ne h with hb | hb
  · have hpos : 0 < (-b) := Int.neg_pos.mpr hb
    have hmod : a % b < -b := by
      rw [← Int.emod_neg] at *
      exact Int.emod_lt_of_pos a hpos
    omega
  · have hmod := Int.emod_lt_of_pos a hb
    omega

def modInv (a m : Nat) : Nat :=
  let (g, x, _) := extGcd (Int.ofNat (a % m)) (Int.ofNat m)
  if g == 1 then
    ((x % Int.ofNat m + Int.ofNat m) % Int.ofNat m).toNat
  else 0

def modPow (base exp m : Nat) : Nat :=
  if h : exp = 0 then 1 % m
  else if exp == 1 then base % m
  else
    let half := modPow base (exp / 2) m
    let halfSq := modMul half half m
    if exp % 2 == 0 then halfSq
    else modMul halfSq (base % m) m
termination_by exp
decreasing_by omega

inductive Point where
  | infinity : Point
  | affine : (x : Nat) → (y : Nat) → Point
  deriving Repr, BEq

def pointDouble (pt : Point) : Point :=
  match pt with
  | Point.infinity => Point.infinity
  | Point.affine x y =>
    if y == 0 then Point.infinity
    else
      let num := modMul 3 (modMul x x p) p
      let den := modMul 2 y p
      let denInv := modInv den p
      let lam := modMul num denInv p
      let x3 := modSub (modMul lam lam p) (modMul 2 x p) p
      let y3 := modSub (modMul lam (modSub x x3 p) p) y p
      Point.affine x3 y3

def pointAdd (p1 p2 : Point) : Point :=
  match p1, p2 with
  | Point.infinity, q => q
  | q, Point.infinity => q
  | Point.affine x1 y1, Point.affine x2 y2 =>
    if x1 == x2 then
      if y1 == y2 then pointDouble p1
      else Point.infinity
    else
      let num := modSub y2 y1 p
      let den := modSub x2 x1 p
      let denInv := modInv den p
      let lam := modMul num denInv p
      let x3 := modSub (modSub (modMul lam lam p) x1 p) x2 p
      let y3 := modSub (modMul lam (modSub x1 x3 p) p) y1 p
      Point.affine x3 y3

def scalarMul (k : Nat) (pt : Point) : Point :=
  if h : k = 0 then Point.infinity
  else if k == 1 then pt
  else
    let half := scalarMul (k / 2) pt
    let doubled := pointDouble half
    if k % 2 == 0 then doubled
    else pointAdd doubled pt
termination_by k
decreasing_by omega

def G : Point := Point.affine Gx Gy

def isOnCurve (pt : Point) : Bool :=
  match pt with
  | Point.infinity => true
  | Point.affine x y =>
    let lhs := modMul y y p
    let rhs := modAdd (modMul x (modMul x x p) p) 7 p
    lhs == rhs

def computeYFromX (x : Nat) (parity : Nat) : Option Nat :=
  let rhs := modAdd (modMul x (modMul x x p) p) 7 p
  let exp := (p + 1) / 4
  let y := modPow rhs exp p
  if modMul y y p != rhs then none
  else
    let y := if y % 2 == parity then y else p - y
    some y

end Secp256k1
