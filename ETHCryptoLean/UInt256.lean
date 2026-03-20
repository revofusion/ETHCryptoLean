/-
  UInt256: 256-bit unsigned integer for Ethereum/secp256k1 computations.
  Represented as a natural number with modular arithmetic.
-/

def UInt256.MOD : Nat := 2 ^ 256

private theorem UInt256.MOD_pos : 0 < UInt256.MOD := by decide

structure UInt256 where
  val : Fin UInt256.MOD
  deriving DecidableEq, Repr

namespace UInt256

instance : Inhabited UInt256 := ⟨⟨0, MOD_pos⟩⟩

def zero : UInt256 := ⟨0, MOD_pos⟩
def one : UInt256 := ⟨1, by native_decide⟩

instance (n : Nat) : OfNat UInt256 n := ⟨⟨⟨n % MOD, Nat.mod_lt _ MOD_pos⟩⟩⟩

def toNat (x : UInt256) : Nat := x.val.val

def ofNat (n : Nat) : UInt256 := ⟨⟨n % MOD, Nat.mod_lt _ MOD_pos⟩⟩

instance : Add UInt256 where
  add a b := ofNat (a.toNat + b.toNat)

instance : Sub UInt256 where
  sub a b := ofNat (a.toNat + MOD - b.toNat)

instance : Mul UInt256 where
  mul a b := ofNat (a.toNat * b.toNat)

instance : Mod UInt256 where
  mod a b := if b.toNat = 0 then a else ofNat (a.toNat % b.toNat)

instance : Div UInt256 where
  div a b := if b.toNat = 0 then 0 else ofNat (a.toNat / b.toNat)

instance : BEq UInt256 where
  beq a b := a.toNat == b.toNat

instance : Ord UInt256 where
  compare a b := compare a.toNat b.toNat

instance : LT UInt256 where
  lt a b := a.toNat < b.toNat

instance : LE UInt256 where
  le a b := a.toNat ≤ b.toNat

instance (a b : UInt256) : Decidable (a < b) := Nat.decLt _ _
instance (a b : UInt256) : Decidable (a ≤ b) := Nat.decLe _ _

instance : ToString UInt256 where
  toString x := s!"0x{Nat.toDigits 16 x.toNat |> String.ofList}"

instance : ShiftLeft UInt256 where
  shiftLeft a n := ofNat (a.toNat <<< n.toNat)

instance : ShiftRight UInt256 where
  shiftRight a n := ofNat (a.toNat >>> n.toNat)

instance : AndOp UInt256 where
  and a b := ofNat (a.toNat &&& b.toNat)

instance : OrOp UInt256 where
  or a b := ofNat (a.toNat ||| b.toNat)

instance : HXor UInt256 UInt256 UInt256 where
  hXor a b := ofNat (a.toNat ^^^ b.toNat)

def toBytesBE (x : UInt256) : List UInt8 :=
  let n := x.toNat
  List.range 32 |>.map fun i =>
    let shift := (31 - i) * 8
    UInt8.ofNat ((n >>> shift) &&& 0xFF)

def fromBytesBE (bytes : List UInt8) : UInt256 :=
  let n := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0
  ofNat n

end UInt256
