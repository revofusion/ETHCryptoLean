/-
  Ethereum ABI Encoding in Pure Lean 4
  Based on go-ethereum reference implementation (accounts/abi/pack.go)
-/

namespace ETHCryptoLean.ABI

/-- Convert a natural number to big-endian bytes (no padding). -/
def natToBytesBE (n : Nat) : Array UInt8 :=
  if n = 0 then #[0]
  else
    let rec go (n : Nat) (acc : List UInt8) : List UInt8 :=
      if n = 0 then acc
      else go (n / 256) ((UInt8.ofNat (n % 256)) :: acc)
    (go n []).toArray

/-- Left-pad a byte array with zeros to the given length. -/
def leftPadBytes (bytes : Array UInt8) (len : Nat) : Array UInt8 :=
  if bytes.size ≥ len then bytes
  else
    let padding := (List.replicate (len - bytes.size) (0 : UInt8)).toArray
    padding ++ bytes

/-- Pack a uint256 as 32 bytes big-endian. Left-pad with zeros to 32 bytes.
    Equivalent to `math.U256Bytes` in go-ethereum. -/
def encodeUint256 (v : Nat) : Array UInt8 :=
  leftPadBytes (natToBytesBE v) 32

/-- Concatenate encodeUint256 for each argument.
    This is `abi.encode(uint256, uint256, ...)`. -/
def abiEncode (args : List Nat) : Array UInt8 :=
  args.foldl (fun acc v => acc ++ encodeUint256 v) #[]

/-- Concatenate raw byte arrays without padding.
    This is `abi.encodePacked(...)`. -/
def abiEncodePacked (args : List (Array UInt8)) : Array UInt8 :=
  args.foldl (fun acc v => acc ++ v) #[]

/-- EIP-712: `abi.encodePacked("\x19\x01", domainSeparator, structHash)`
    = `[0x19, 0x01] ++ encodeUint256(domainSeparator) ++ encodeUint256(structHash)`. -/
def toTypedDataHash (domainSeparator structHash : Nat) : Array UInt8 :=
  #[0x19, 0x01] ++ encodeUint256 domainSeparator ++ encodeUint256 structHash

/-- Convenience wrapper for encoding 1 uint256 argument. -/
def abiEncode1 (a : Nat) : Array UInt8 :=
  encodeUint256 a

/-- Convenience wrapper for encoding 2 uint256 arguments. -/
def abiEncode2 (a b : Nat) : Array UInt8 :=
  encodeUint256 a ++ encodeUint256 b

/-- Convenience wrapper for encoding 3 uint256 arguments. -/
def abiEncode3 (a b c : Nat) : Array UInt8 :=
  encodeUint256 a ++ encodeUint256 b ++ encodeUint256 c

/-- Convenience wrapper for encoding 4 uint256 arguments. -/
def abiEncode4 (a b c d : Nat) : Array UInt8 :=
  encodeUint256 a ++ encodeUint256 b ++ encodeUint256 c ++ encodeUint256 d

/-- Convenience wrapper for encoding 5 uint256 arguments. -/
def abiEncode5 (a b c d e : Nat) : Array UInt8 :=
  encodeUint256 a ++ encodeUint256 b ++ encodeUint256 c ++ encodeUint256 d ++ encodeUint256 e

/-- Convenience wrapper for encoding 6 uint256 arguments. -/
def abiEncode6 (a b c d e f : Nat) : Array UInt8 :=
  encodeUint256 a ++ encodeUint256 b ++ encodeUint256 c ++ encodeUint256 d ++ encodeUint256 e ++ encodeUint256 f

-- ============================================================
-- Helper for test vectors
-- ============================================================

/-- Convert a byte array to a hex string for display. -/
def toHexString (bytes : Array UInt8) : String :=
  let hexDigit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
  bytes.foldl (fun s b =>
    s ++ String.ofList [hexDigit (b / 16), hexDigit (b % 16)]) ""

-- ============================================================
end ETHCryptoLean.ABI
