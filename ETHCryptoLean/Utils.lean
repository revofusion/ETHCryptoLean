/-
  Shared utilities for ETHCryptoLean.
  Hex encoding/decoding and byte-level read/write helpers.
-/

namespace ETHCryptoLean.Utils

-- Hex encoding

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (bytes : Array UInt8) : String :=
  bytes.foldl (fun acc b =>
    let hi := (b.toNat >>> 4) &&& 0x0F
    let lo := b.toNat &&& 0x0F
    acc.push (hexChar hi) |>.push (hexChar lo)
  ) ""

def baToHex (bytes : ByteArray) : String :=
  bytes.foldl (fun acc b =>
    let hi := (b.toNat >>> 4) &&& 0x0F
    let lo := b.toNat &&& 0x0F
    acc.push (hexChar hi) |>.push (hexChar lo)
  ) ""

-- Hex decoding

private def hexNibble (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

def fromHex (s : String) : Array UInt8 :=
  let chars := s.toList
  if chars.length % 2 != 0 then #[]
  else
    let rec go (cs : List Char) (acc : Array UInt8) : Array UInt8 :=
      match cs with
      | hi :: lo :: rest =>
        match hexNibble hi, hexNibble lo with
        | some h, some l => go rest (acc.push (h * 16 + l))
        | _, _ => #[]
      | _ => acc
    go chars #[]

def fromHexBA (s : String) : ByteArray :=
  let arr := fromHex s
  arr.foldl (fun (ba : ByteArray) b => ba.push b) ByteArray.empty

-- Byte-level read/write helpers

@[inline] def readLE32 (data : Array UInt8) (i : Nat) : UInt32 :=
  data[i]!.toUInt32 ||| (data[i+1]!.toUInt32 <<< 8) |||
  (data[i+2]!.toUInt32 <<< 16) ||| (data[i+3]!.toUInt32 <<< 24)

@[inline] def writeLE32 (v : UInt32) : Array UInt8 :=
  #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

@[inline] def readBE32 (data : Array UInt8) (i : Nat) : UInt32 :=
  (data[i]!.toUInt32 <<< 24) ||| (data[i+1]!.toUInt32 <<< 16) |||
  (data[i+2]!.toUInt32 <<< 8) ||| data[i+3]!.toUInt32

@[inline] def writeBE32 (v : UInt32) : Array UInt8 :=
  #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]

@[inline] def readLE64 (data : ByteArray) (offset : Nat) : UInt64 :=
  (data[offset]!).toUInt64 ||| ((data[offset+1]!).toUInt64 <<< 8) |||
  ((data[offset+2]!).toUInt64 <<< 16) ||| ((data[offset+3]!).toUInt64 <<< 24) |||
  ((data[offset+4]!).toUInt64 <<< 32) ||| ((data[offset+5]!).toUInt64 <<< 40) |||
  ((data[offset+6]!).toUInt64 <<< 48) ||| ((data[offset+7]!).toUInt64 <<< 56)

@[inline] def writeLE64 (v : UInt64) : Array UInt8 :=
  #[(v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8,
    ((v >>> 16) &&& 0xFF).toUInt8, ((v >>> 24) &&& 0xFF).toUInt8,
    ((v >>> 32) &&& 0xFF).toUInt8, ((v >>> 40) &&& 0xFF).toUInt8,
    ((v >>> 48) &&& 0xFF).toUInt8, ((v >>> 56) &&& 0xFF).toUInt8]

@[inline] def readBE32BA (data : ByteArray) (offset : Nat) : UInt32 :=
  ((data[offset]!).toUInt32 <<< 24) ||| ((data[offset+1]!).toUInt32 <<< 16) |||
  ((data[offset+2]!).toUInt32 <<< 8) ||| (data[offset+3]!).toUInt32

end ETHCryptoLean.Utils
