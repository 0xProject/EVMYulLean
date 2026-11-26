import EvmYul.UInt256

namespace EvmYul

namespace SpongeHash

namespace Keccak256

/-- Keccak-256 sponge rate in bytes (`1088 / 8 = 136`). -/
def rateBytes : ℕ := 136

/-- Keccak-256 digest size in bytes (`256 / 8 = 32`). -/
def digestBytes : ℕ := 32

/-- Keccak-f[1600] 24 round constants. -/
def roundConstants : List UInt64 :=
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000
  , 0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009
  , 0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
  , 0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003
  , 0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a
  , 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
  ]

/-- 64-bit left circular rotation (`rotl64`). -/
def rotl64 (x : UInt64) (n : UInt64) : UInt64 :=
  let s := n % 64
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

/-- Keccak multi-rate `pad10*1` domain separator (`0x01 ... 0x80`) for `rateBytes = 136`. -/
def pad101 (msg : ByteArray) : ByteArray :=
  let rem := msg.size % rateBytes
  let padLen := rateBytes - rem
  if padLen == 1 then
    msg.push 0x81
  else
    let withStart := msg.push 0x01
    let withZeros := (List.replicate (padLen - 2) (0 : UInt8)).foldl ByteArray.push withStart
    withZeros.push 0x80

end Keccak256

end SpongeHash

end EvmYul
