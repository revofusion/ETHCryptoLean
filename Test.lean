/-
  Test suite for ETHCryptoLean.
  Validates cryptographic primitives against known test vectors
  and official Ethereum JSON test vectors from vectors/.
-/
import ETHCryptoLean
import Lean.Data.Json

open Secp256k1

-- ═══════════════════════════════════════════════════════════════
-- Hex utilities
-- ═══════════════════════════════════════════════════════════════

private def hexCharToNibble (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- Decode a hex string (no 0x prefix) to bytes. Returns empty on invalid input. -/
def hexToBytes (s : String) : Array UInt8 :=
  let chars := s.toList
  if chars.length % 2 != 0 then #[]
  else
    let rec go (cs : List Char) (acc : Array UInt8) : Array UInt8 :=
      match cs with
      | hi :: lo :: rest =>
        match hexCharToNibble hi, hexCharToNibble lo with
        | some h, some l => go rest (acc.push (h * 16 + l))
        | _, _ => #[]
      | _ => acc
    go chars #[]

private def toHex (b : UInt8) : String :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  let hexChar := fun n => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  s!"{hexChar hi}{hexChar lo}"

/-- Encode bytes to lowercase hex string (no 0x prefix). -/
def bytesToHex (bs : Array UInt8) : String :=
  bs.foldl (fun acc b => acc ++ toHex b) ""

-- ═══════════════════════════════════════════════════════════════
-- Test helpers
-- ═══════════════════════════════════════════════════════════════

private def assert (name : String) (cond : Bool) : IO Unit :=
  if cond then IO.println s!"  PASS  {name}"
  else IO.println s!"  FAIL  {name}"

structure TestStats where
  passed : Nat := 0
  failed : Nat := 0

def TestStats.add (s : TestStats) (ok : Bool) : TestStats :=
  if ok then { s with passed := s.passed + 1 }
  else { s with failed := s.failed + 1 }

-- ═══════════════════════════════════════════════════════════════
-- JSON test vector parsing
-- ═══════════════════════════════════════════════════════════════

structure TestVector where
  name : String
  input : String
  expected : String

/-- Parse a JSON array of test vector objects. -/
def parseTestVectors (json : Lean.Json) : List TestVector :=
  match json with
  | .arr items =>
    items.toList.filterMap fun item => do
      let name ← (item.getObjValAs? String "Name").toOption
      let input ← (item.getObjValAs? String "Input").toOption
      -- Success cases have "Expected", fail cases have "ExpectedError"
      let expected := match (item.getObjValAs? String "Expected").toOption with
        | some e => e
        | none => ""  -- failure cases
      pure ⟨name, input, expected⟩
  | _ => []

/-- Read and parse a JSON test vector file. Returns empty list on error. -/
def loadVectors (path : String) : IO (List TestVector) := do
  try
    let content ← IO.FS.readFile path
    match Lean.Json.parse content with
    | .ok json => pure (parseTestVectors json)
    | .error e =>
      IO.eprintln s!"  WARNING: Failed to parse {path}: {e}"
      pure []
  catch e =>
    IO.eprintln s!"  WARNING: Failed to read {path}: {e}"
    pure []

-- ═══════════════════════════════════════════════════════════════
-- UInt256 tests (inline, no JSON vectors)
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "UInt256 arithmetic"

  -- Basic construction
  assert "ofNat 0" (UInt256.ofNat 0 == (0 : UInt256))
  assert "ofNat 1" (UInt256.ofNat 1 == (1 : UInt256))
  assert "ofNat 42 roundtrip" ((UInt256.ofNat 42).toNat == 42)

  -- Addition
  assert "0 + 0 = 0" ((UInt256.ofNat 0 + UInt256.ofNat 0).toNat == 0)
  assert "1 + 1 = 2" ((UInt256.ofNat 1 + UInt256.ofNat 1).toNat == 2)
  assert "100 + 200 = 300" ((UInt256.ofNat 100 + UInt256.ofNat 200).toNat == 300)

  -- Addition wraps at 2^256
  let max := UInt256.ofNat (2^256 - 1)
  assert "max + 1 wraps to 0" ((max + UInt256.ofNat 1).toNat == 0)
  assert "max + max wraps" ((max + max).toNat == 2^256 - 2)

  -- Subtraction
  assert "5 - 3 = 2" ((UInt256.ofNat 5 - UInt256.ofNat 3).toNat == 2)
  assert "0 - 1 wraps to max" ((UInt256.ofNat 0 - UInt256.ofNat 1).toNat == 2^256 - 1)

  -- Multiplication
  assert "7 * 6 = 42" ((UInt256.ofNat 7 * UInt256.ofNat 6).toNat == 42)
  assert "0 * anything = 0" ((UInt256.ofNat 0 * UInt256.ofNat 999).toNat == 0)
  assert "1 * x = x" ((UInt256.ofNat 1 * UInt256.ofNat 12345).toNat == 12345)

  -- Division
  assert "42 / 7 = 6" ((UInt256.ofNat 42 / UInt256.ofNat 7).toNat == 6)
  assert "10 / 3 = 3" ((UInt256.ofNat 10 / UInt256.ofNat 3).toNat == 3)
  assert "x / 0 = 0" ((UInt256.ofNat 42 / UInt256.ofNat 0).toNat == 0)

  -- Modulo
  assert "10 % 3 = 1" ((UInt256.ofNat 10 % UInt256.ofNat 3).toNat == 1)
  assert "42 % 7 = 0" ((UInt256.ofNat 42 % UInt256.ofNat 7).toNat == 0)

  -- Comparison
  assert "0 < 1" (UInt256.ofNat 0 < UInt256.ofNat 1)
  assert "not 1 < 0" (!(UInt256.ofNat 1 < UInt256.ofNat 0))
  assert "1 <= 1" (UInt256.ofNat 1 ≤ UInt256.ofNat 1)
  assert "0 <= 1" (UInt256.ofNat 0 ≤ UInt256.ofNat 1)

  -- Bitwise
  assert "0xFF & 0x0F = 0x0F" ((UInt256.ofNat 0xFF &&& UInt256.ofNat 0x0F).toNat == 0x0F)
  assert "0xF0 | 0x0F = 0xFF" ((UInt256.ofNat 0xF0 ||| UInt256.ofNat 0x0F).toNat == 0xFF)
  assert "0xFF ^ 0x0F = 0xF0" ((UInt256.ofNat 0xFF ^^^ UInt256.ofNat 0x0F).toNat == 0xF0)
  assert "1 << 8 = 256" ((UInt256.ofNat 1 <<< (8 : UInt256)).toNat == 256)
  assert "256 >> 8 = 1" ((UInt256.ofNat 256 >>> (8 : UInt256)).toNat == 1)

  -- Byte conversion roundtrip
  let val := UInt256.ofNat 0xDEADBEEF
  let bytes := val.toBytesBE
  let back := UInt256.fromBytesBE bytes
  assert "toBytesBE/fromBytesBE roundtrip" (back == val)

  -- Large value roundtrip
  let large := UInt256.ofNat 0x123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0
  assert "large value roundtrip" ((UInt256.fromBytesBE large.toBytesBE) == large)

-- ═══════════════════════════════════════════════════════════════
-- Keccak-256 test vectors (inline)
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "\nKeccak-256"

  -- Empty string
  let hash := Keccak.keccak256 #[]
  let hex := bytesToHex hash
  assert "keccak256(\"\")" (hex == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")

  -- "abc"
  let hash := Keccak.keccak256 "abc".toUTF8.data
  let hex := bytesToHex hash
  assert "keccak256(\"abc\")" (hex == "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")

  -- Single zero byte
  let hash := Keccak.keccak256 #[0]
  let hex := bytesToHex hash
  assert "keccak256(0x00)" (hex == "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a")

  -- "hello"
  let hash := Keccak.keccak256 "hello".toUTF8.data
  let hex := bytesToHex hash
  assert "keccak256(\"hello\")" (hex == "1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8")

  -- 32 zero bytes (common in Ethereum: empty storage slot hash)
  let hash := Keccak.keccak256 (List.replicate 32 (0 : UInt8)).toArray
  let hex := bytesToHex hash
  assert "keccak256(32 zero bytes)" (hex == "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563")

  -- Output is always 32 bytes
  assert "output length (empty)" ((Keccak.keccak256 #[]).size == 32)
  assert "output length (1 byte)" ((Keccak.keccak256 #[0x42]).size == 32)
  assert "output length (136 bytes)" ((Keccak.keccak256 (List.replicate 136 (0xFF : UInt8)).toArray).size == 32)
  assert "output length (137 bytes)" ((Keccak.keccak256 (List.replicate 137 (0xFF : UInt8)).toArray).size == 32)

  -- Deterministic: same input always gives same output
  let h1 := Keccak.keccak256 "test".toUTF8.data
  let h2 := Keccak.keccak256 "test".toUTF8.data
  assert "deterministic" (h1 == h2)

  -- Different inputs give different outputs
  let h1 := bytesToHex (Keccak.keccak256 "a".toUTF8.data)
  let h2 := bytesToHex (Keccak.keccak256 "b".toUTF8.data)
  assert "different inputs differ" (h1 != h2)

-- ═══════════════════════════════════════════════════════════════
-- secp256k1 curve tests (inline)
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "\nsecp256k1"

  -- Generator point is on the curve
  assert "G is on curve" (isOnCurve G)

  -- 1*G = G
  assert "1*G == G" (scalarMul 1 G == G)

  -- 2*G is on the curve
  assert "2*G on curve" (isOnCurve (scalarMul 2 G))

  -- 3*G is on the curve
  assert "3*G on curve" (isOnCurve (scalarMul 3 G))

  -- Point at infinity
  assert "infinity on curve" (isOnCurve Point.infinity)

  -- G + infinity = G
  assert "G + infinity = G" (pointAdd G Point.infinity == G)

  -- infinity + G = G
  assert "infinity + G = G" (pointAdd Point.infinity G == G)

  -- G + G = 2*G
  assert "G + G == 2*G" (pointAdd G G == scalarMul 2 G)

  -- 2*G + G = 3*G
  assert "2*G + G == 3*G" (pointAdd (scalarMul 2 G) G == scalarMul 3 G)

  -- Associativity: (2*G + 3*G) = 5*G
  assert "(2+3)*G == 5*G" (pointAdd (scalarMul 2 G) (scalarMul 3 G) == scalarMul 5 G)

  -- Known 2*G coordinates (from SEC 2 standard)
  match scalarMul 2 G with
  | Point.affine x _ =>
    assert "2*G.x matches" (x == 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5)
  | _ => assert "2*G is not infinity" false

  -- Y recovery from x coordinate
  match computeYFromX Gx 0 with
  | some y => assert "Y recovery (even)" (y == Gy || y == p - Gy)
  | none => assert "Y recovery should succeed" false

-- ═══════════════════════════════════════════════════════════════
-- n*G = infinity (curve order)
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "\nsecp256k1 (curve order)"
  let nG := scalarMul Secp256k1.n G
  assert "n*G == infinity" (nG == Point.infinity)

-- ═══════════════════════════════════════════════════════════════
-- UInt256 keccak256 integration (inline)
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "\nUInt256 keccak256 integration"

  -- keccak256Bytes returns a UInt256
  let hash := UInt256.keccak256Bytes #[]
  assert "keccak256Bytes empty" (hash.toNat != 0)

  -- Should match byte-level keccak
  let bytesHash := Keccak.keccak256 #[]
  let expected := Array.foldl (fun acc (b : UInt8) => acc * 256 + b.toNat) 0 bytesHash
  assert "keccak256Bytes matches bytes" (hash.toNat == expected)

  -- Ethereum address(0) hash (32 zero bytes)
  let zeroHash := UInt256.keccak256Bytes (List.replicate 32 (0 : UInt8)).toArray
  assert "zero-slot hash nonzero" (zeroHash.toNat != 0)

-- ═══════════════════════════════════════════════════════════════
-- SHA-256 test vectors (inline, no JSON vectors)
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "\nSHA-256"

  -- Empty string
  let hash := SHA256.hash #[]
  let hex := bytesToHex hash
  assert "sha256(\"\")" (hex == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")

  -- "abc"
  let hash := SHA256.hash "abc".toUTF8.data
  let hex := bytesToHex hash
  assert "sha256(\"abc\")" (hex == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")

  -- "hello"
  let hash := SHA256.hash "hello".toUTF8.data
  let hex := bytesToHex hash
  assert "sha256(\"hello\")" (hex == "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824")

  -- Output is always 32 bytes
  assert "output length (empty)" ((SHA256.hash #[]).size == 32)
  assert "output length (1 byte)" ((SHA256.hash #[0x42]).size == 32)

  -- Deterministic
  let h1 := SHA256.hash "test".toUTF8.data
  let h2 := SHA256.hash "test".toUTF8.data
  assert "deterministic" (h1 == h2)

  -- Different from keccak
  let sha := bytesToHex (SHA256.hash "abc".toUTF8.data)
  let kec := bytesToHex (Keccak.keccak256 "abc".toUTF8.data)
  assert "sha256 != keccak256" (sha != kec)

-- ═══════════════════════════════════════════════════════════════
-- BLS12-381 curve tests (inline)
-- ═══════════════════════════════════════════════════════════════

open BLS12381 in
#eval do
  IO.println "\nBLS12-381"

  -- G1 generator is on the curve
  assert "G1 generator on curve" (g1IsOnCurve G1_GEN)

  -- G2 generator is on the curve
  assert "G2 generator on curve" (g2IsOnCurve G2_GEN)

  -- G1 point at infinity is on the curve
  assert "G1 infinity on curve" (g1IsOnCurve .infinity)

  -- G2 point at infinity is on the curve
  assert "G2 infinity on curve" (g2IsOnCurve .infinity)

  -- G1: point + infinity = point
  assert "G1: P + O = P" (g1Add G1_GEN .infinity == G1_GEN)
  assert "G1: O + P = P" (g1Add .infinity G1_GEN == G1_GEN)

  -- G1: 1*G = G
  assert "G1: 1*G = G" (g1ScalarMul 1 G1_GEN == G1_GEN)

  -- G1: 2*G is on the curve
  let twoG := g1ScalarMul 2 G1_GEN
  assert "G1: 2*G on curve" (g1IsOnCurve twoG)

  -- G1: G + G = 2*G
  assert "G1: G + G = 2*G" (g1Add G1_GEN G1_GEN == twoG)

  -- G1: 3*G is on the curve
  assert "G1: 3*G on curve" (g1IsOnCurve (g1ScalarMul 3 G1_GEN))

  -- G1: 2*G + G = 3*G
  assert "G1: 2G + G = 3G" (g1Add twoG G1_GEN == g1ScalarMul 3 G1_GEN)

  -- Fp2 arithmetic basics
  let a : Fp2 := ⟨3, 4⟩
  let b : Fp2 := ⟨1, 2⟩
  let sum := fp2Add a b
  assert "Fp2 add" (sum.c0 == 4 && sum.c1 == 6)

  -- Fp2 multiplication: (3+4i)(1+2i) = 3+6i+4i+8i² = 3+10i-8 = -5+10i
  let prod := fp2Mul a b
  let expected_c0 := (BLS12381.P - 5) % BLS12381.P
  assert "Fp2 mul c0" (prod.c0 == expected_c0)
  assert "Fp2 mul c1" (prod.c1 == 10)

-- ═══════════════════════════════════════════════════════════════
-- RIPEMD-160 test vectors (inline, no JSON vectors)
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.RIPEMD160 in
#eval do
  IO.println "\nRIPEMD-160"

  let hash := ripemd160 #[]
  assert "ripemd160(\"\")" (bytesToHex hash == "9c1185a5c5e9fc54612808977ee8f548b2258d31")

  let hash := ripemd160 #[0x61]
  assert "ripemd160(\"a\")" (bytesToHex hash == "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe")

  let hash := ripemd160 #[0x61, 0x62, 0x63]
  assert "ripemd160(\"abc\")" (bytesToHex hash == "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc")

  assert "output length" ((ripemd160 #[]).size == 20)

-- ═══════════════════════════════════════════════════════════════
-- ecRecover - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

#eval do
  IO.println "\necRecover (JSON vectors)"
  let vectors ← loadVectors "vectors/ecRecover.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      -- ecrecover input: hash(32) + v(32) + r(32) + s(32)
      -- We need to pad input to 128 bytes if shorter
      let padded := if input.size < 128 then
        input ++ (List.replicate (128 - input.size) (0 : UInt8)).toArray
      else input
      let hash := UInt256.fromBytesBE (padded.extract 0 32).toList
      let vVal := UInt256.fromBytesBE (padded.extract 32 64).toList
      let r := UInt256.fromBytesBE (padded.extract 64 96).toList
      let s := UInt256.fromBytesBE (padded.extract 96 128).toList
      let result := ecrecover hash vVal r s
      if v.expected == "" then
        -- Expect failure
        let ok := result.isNone
        stats := stats.add ok
        if ok then IO.println s!"  PASS  {v.name} (expected failure)"
        else IO.println s!"  FAIL  {v.name} (expected failure but got result)"
      else
        -- Expect success: output is 32 bytes (address left-padded)
        let expectedBytes := hexToBytes v.expected
        match result with
        | some addr =>
          let addrBytes := addr.toBytesBE.toArray
          let ok := addrBytes == expectedBytes
          stats := stats.add ok
          if ok then IO.println s!"  PASS  {v.name}"
          else
            IO.println s!"  FAIL  {v.name}"
            IO.println s!"         expected: {v.expected}"
            IO.println s!"         got:      {bytesToHex addrBytes}"
        | none =>
          stats := stats.add false
          IO.println s!"  FAIL  {v.name} (got none, expected {v.expected})"
    IO.println s!"  ecRecover: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- BN256 ecAdd - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.BN256 in
#eval do
  IO.println "\nbn256Add (JSON vectors)"
  let vectors ← loadVectors "vectors/bn256Add.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      let result := ecAddPrecompile input
      let expectedBytes := hexToBytes v.expected
      match result with
      | some output =>
        let ok := output == expectedBytes
        stats := stats.add ok
        if ok then IO.println s!"  PASS  {v.name}"
        else
          IO.println s!"  FAIL  {v.name}"
          IO.println s!"         expected: {v.expected}"
          IO.println s!"         got:      {bytesToHex output}"
      | none =>
        if v.expected == "" then
          stats := stats.add true
          IO.println s!"  PASS  {v.name} (expected failure)"
        else
          stats := stats.add false
          IO.println s!"  FAIL  {v.name} (got none, expected {v.expected})"
    IO.println s!"  bn256Add: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- BN256 ecMul - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.BN256 in
#eval do
  IO.println "\nbn256ScalarMul (JSON vectors)"
  let vectors ← loadVectors "vectors/bn256ScalarMul.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      let result := ecMulPrecompile input
      let expectedBytes := hexToBytes v.expected
      match result with
      | some output =>
        let ok := output == expectedBytes
        stats := stats.add ok
        if ok then IO.println s!"  PASS  {v.name}"
        else
          IO.println s!"  FAIL  {v.name}"
          IO.println s!"         expected: {v.expected}"
          IO.println s!"         got:      {bytesToHex output}"
      | none =>
        if v.expected == "" then
          stats := stats.add true
          IO.println s!"  PASS  {v.name} (expected failure)"
        else
          stats := stats.add false
          IO.println s!"  FAIL  {v.name} (got none, expected {v.expected})"
    IO.println s!"  bn256ScalarMul: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- BN256 ecPairing - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.BN256 in
#eval do
  IO.println "\nbn256Pairing (JSON vectors)"
  let vectors ← loadVectors "vectors/bn256Pairing.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      let result := ecPairingPrecompile input
      let expectedBytes := hexToBytes v.expected
      match result with
      | some output =>
        let ok := output == expectedBytes
        stats := stats.add ok
        if ok then IO.println s!"  PASS  {v.name}"
        else
          IO.println s!"  FAIL  {v.name}"
          IO.println s!"         expected: {v.expected}"
          IO.println s!"         got:      {bytesToHex output}"
      | none =>
        if v.expected == "" then
          stats := stats.add true
          IO.println s!"  PASS  {v.name} (expected failure)"
        else
          stats := stats.add false
          IO.println s!"  FAIL  {v.name} (got none, expected {v.expected})"
    IO.println s!"  bn256Pairing: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- BLAKE2f - JSON test vectors (success + failure)
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.Blake2f in
#eval do
  IO.println "\nblake2F (JSON vectors)"
  let vectors ← loadVectors "vectors/blake2F.json"
  let failVectors ← loadVectors "vectors/fail-blake2f.json"
  let allVectors := vectors ++ failVectors
  if allVectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in allVectors do
      let input := hexToBytes v.input
      let result := blake2FPrecompile input
      if v.expected == "" then
        -- Expect failure
        let ok := result.isNone
        stats := stats.add ok
        if ok then IO.println s!"  PASS  {v.name} (expected failure)"
        else IO.println s!"  FAIL  {v.name} (expected failure but got result)"
      else
        let expectedBytes := hexToBytes v.expected
        match result with
        | some output =>
          let ok := output == expectedBytes
          stats := stats.add ok
          if ok then IO.println s!"  PASS  {v.name}"
          else
            IO.println s!"  FAIL  {v.name}"
            IO.println s!"         expected: {v.expected}"
            IO.println s!"         got:      {bytesToHex output}"
        | none =>
          stats := stats.add false
          IO.println s!"  FAIL  {v.name} (got none, expected output)"
    IO.println s!"  blake2F: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- ModExp - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.ModExp in
#eval do
  IO.println "\nmodexp (JSON vectors)"
  let vectors ← loadVectors "vectors/modexp.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      let result := modExpPrecompile input
      let expectedBytes := hexToBytes v.expected
      let ok := result == expectedBytes
      stats := stats.add ok
      if ok then IO.println s!"  PASS  {v.name}"
      else
        IO.println s!"  FAIL  {v.name}"
        IO.println s!"         expected: {v.expected}"
        IO.println s!"         got:      {bytesToHex result}"
    IO.println s!"  modexp: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- ModExp EIP-2565 - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.ModExp in
#eval do
  IO.println "\nmodexp EIP-2565 (JSON vectors)"
  let vectors ← loadVectors "vectors/modexp_eip2565.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      let result := modExpPrecompile input
      let expectedBytes := hexToBytes v.expected
      let ok := result == expectedBytes
      stats := stats.add ok
      if ok then IO.println s!"  PASS  {v.name}"
      else
        IO.println s!"  FAIL  {v.name}"
        IO.println s!"         expected: {v.expected}"
        IO.println s!"         got:      {bytesToHex result}"
    IO.println s!"  modexp_eip2565: {stats.passed}/{stats.passed + stats.failed} passed"

-- ═══════════════════════════════════════════════════════════════
-- ModExp EIP-7883 - JSON test vectors
-- ═══════════════════════════════════════════════════════════════

open ETHCryptoLean.ModExp in
#eval do
  IO.println "\nmodexp EIP-7883 (JSON vectors)"
  let vectors ← loadVectors "vectors/modexp_eip7883.json"
  if vectors.isEmpty then
    IO.println "  WARNING: No vectors loaded"
  else
    let mut stats : TestStats := {}
    for v in vectors do
      let input := hexToBytes v.input
      let result := modExpPrecompile input
      let expectedBytes := hexToBytes v.expected
      let ok := result == expectedBytes
      stats := stats.add ok
      if ok then IO.println s!"  PASS  {v.name}"
      else
        IO.println s!"  FAIL  {v.name}"
        IO.println s!"         expected: {v.expected}"
        IO.println s!"         got:      {bytesToHex result}"
    IO.println s!"  modexp_eip7883: {stats.passed}/{stats.passed + stats.failed} passed"
