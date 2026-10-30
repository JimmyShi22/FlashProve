-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Blake2b/Test/Salted.lean

Build-time tests of BLAKE2b with a salt and a personalization (Run/Blake2b/Salted.lean).
The expected digests were computed with `hashlib.blake2b` of CPython 3.13 (`digest_size`, `salt`,
`person`). The message of n bytes is `pattern n` of Util.lean; the salt is the bytes 0, .., 15 and
the personalization the bytes 16, .., 31, a beginning of these, or these and more. Compiling this
file runs the tests in Lean's interpreter; if one fails, it does not compile. Nothing imports it.
Limits: the longest message has 1,580 bytes, the longest with a known answer 1,000, so the counter's
high word is zero in all tests. That bytes after the sixteenth of a salt are not read is this
library's rule: hashlib takes no longer salt. A `#guard` is not checked by Lean's kernel.
-/
import Run.Blake2b.SaltedPlain
import Run.Blake2b.Test.Util

namespace Run.Blake2b.Test

/-- The bytes first, .., first + n - 1, modulo 256. -/
def count (first n : Nat) : ByteArray :=
  (List.range n).foldl (fun o i => o.push (first + i).toUInt8) (ByteArray.emptyWithCapacity n)

/-- The salt of the tests. -/
def salt16 : ByteArray := count 0 16

/-- The personalization of the tests. -/
def personal16 : ByteArray := count 16 16

/-- Digest length, message length, digest: with the salt and the personalization. -/
def saltedAnswers : List (Nat × Nat × String) := [
  (1, 0, "76"),
  (1, 1, "fc"),
  (1, 127, "bb"),
  (1, 128, "5f"),
  (1, 129, "4e"),
  (1, 255, "89"),
  (1, 256, "80"),
  (1, 257, "4c"),
  (1, 1000, "55"),
  (20, 0, "8fbe8f993d7c320c18547eaec8be17f90d1c48b1"),
  (20, 1, "1b1eb700039b12d8daaa424d332c46bb9fc97264"),
  (20, 127, "8d9964d4339740f3e8951fe3c1954ec7b2e54987"),
  (20, 128, "b7c2bc4994bf17d313d5d0040e71fda406089861"),
  (20, 129, "e084482899b2c7d3afe8825a142921c5be598f51"),
  (20, 255, "c34c421a5286ccacc02e359abaf33aea197f4fc9"),
  (20, 256, "64e3ba82a759d992ebb1e6354e4dd3bae7b365ac"),
  (20, 257, "c4c951e018ad2cb695491d04d4bd3844e110b34a"),
  (20, 1000, "1c502622c99066bbbe50f8b028c49bc01e11391a"),
  (32, 0, "bb5c60a1db29ea2905f46b203b7c51a5d33c4b863ec94852b810a696090db92f"),
  (32, 1, "f159324ab5a3b9e125135d554943a970f1156aa1e6115af76cf47b2db1f45c58"),
  (32, 127, "55492fc1aa4f48f352d3746b4f9bc031dcda34cab43dd7cee0d739c0bb4c1ba0"),
  (32, 128, "55d5bb5611234b643b647259255319394ec8287638a8047e8702a2e86c7ae74d"),
  (32, 129, "2a119af519e298a4e5182309ac468bc85bc44b612eee8ff1519e45ef717be658"),
  (32, 255, "c5bef375ebcca05bf9b5554d0c1bf285f509433428fee643c7fb93f041406cf5"),
  (32, 256, "5ce4a565943c1a93d6befbf348245d3c16bcc483f2cfd675e19749c1472e62e1"),
  (32, 257, "be0862e6a65c8f4e6f83e74286501537f309e5bb11834882cceca1d92cbf9b60"),
  (32, 1000, "c0a38ed0f74bfbade5524405479cd9efd098a806af6dbbee7f65c9373d9d7800"),
  (48, 0, "de355d9fa0977b42c9b40b8cc2c263db153031f38f6c07b37528090ab221f400" ++
    "00832cfa50cfcafdce4233440f6af490"),
  (48, 1, "30ac910f81ca67147b437f524bee4c271f76ec79a46cec7dfa9284b355710f6c" ++
    "a47bee678599f68669dea6f010fa570c"),
  (48, 127, "7dad5d85b3e3ede79986033c5573806b8d1af1d02ce6c64bff1622847ac035e3" ++
    "afa8d72e4503d1b9c8400ce6d11716a5"),
  (48, 128, "e35aa5c3daaabd59d1f47df63cd72c45c54ba507c59dc2ab952d43c38bdfecf7" ++
    "748aa83646f8e8380c303427da92677e"),
  (48, 129, "71bb886345482c6e43533ee407c07e2dbe88804ec7e25ca9c4817b9f5a608d33" ++
    "d9c613a55e92462f7811a211f7925fee"),
  (48, 255, "48d3029b5dd3e73f0b00b62ffde308d2c5ab7657aedecda71e75bcc31a4f32ad" ++
    "3dd8b8fedd84750c6f41feb570ffac93"),
  (48, 256, "a140be94a22cf7d1949e69e8fdfb6f17a9d46ae29135f68a536c4e08f10d0528" ++
    "0dbe0c4102bdef5c05a321b9968d701c"),
  (48, 257, "b5e1085bd44c07067ce38c889b4990435187f08aed13ec50498a1c19e50dd132" ++
    "e9e8f24969597e926004a65963224d2d"),
  (48, 1000, "b58295f7c6545133a052e3baab850adb3eb31232a2f4dc4975591bb1ec1aec44" ++
    "80e9d87099018f165acfbca75be49d2d"),
  (64, 0, "74c2ec64d30ad73440243630afc59020af3758aaaf8f1a666f320385d234e9b2" ++
    "cb4c80d3a5cf32abbe6abfd353893fc959ed178f0061637dde6446b20fd6f86c"),
  (64, 1, "595f075cf8aebb0849249217e70a99f0f4d6eda5c24d38f117e8ca2b16fd0da3" ++
    "14df28418f945a8db2236445b4626c4593beecf474670eb5c1b80c80a932c1d9"),
  (64, 127, "7ea4cff9711a0bf48074c177137fcf7ce76c29feb51828e96e222edb312139fd" ++
    "259bb330e48741edbfdf1c590c2c5cd34c3530d6e77e1b7dbf2352556cb484a3"),
  (64, 128, "dece2c34a6350908fad7bf08ab697e2be77db6888ac454693316268022c6b900" ++
    "5e3814229660554bd735a5eb93cff4eba3c23a2d13d9b5de1cf0f9b669e34aef"),
  (64, 129, "3990cb90585dbbab03954d8776ecfd693e6a2cdd51bfdb706dfd20a9a0195da5" ++
    "d44429677e2b346e2e6013cb4b5f8e2d872d233dc4e9151a9ae70a06c796f1ef"),
  (64, 255, "8431d0481ec9b78ae42eddd5ef711b1487e3bafe2490a8af7bcc9b332441a9bd" ++
    "36f5c6ec4e616dfa0c5d185916d3c0552f72a76ee817601c59af45222ab97bf2"),
  (64, 256, "54b576880b7b80532425d5a5a955b49729e932b185493955df6fef88134c9985" ++
    "50b2a204b2eb91263c5d36d720a1e3a0dd416931d8ce9aa8a7c65dc6c7bcf74b"),
  (64, 257, "e9ed25b0e1dffb905cbb8e390b0bd1f167b5e6ca5c1c823ee9b6750556cbaff5" ++
    "65634aeca763b6920fc29e44262ac26e58a96778a667aeee11160d857334b358"),
  (64, 1000, "ea45b54ca1b09b9d3f433665a397d4507bd71ff52e68b80811144ef4f5ffaa24" ++
    "d3372961130ce5901a97378d372b1979e39247799c209c3fd1e7e75441c8186a")]

#guard saltedAnswers.all fun (d, n, h) =>
  (blake2bSalted salt16 personal16 (pattern n) d).data == (hex h).data

/-- Message length, digest of 32 bytes: with the salt only. -/
def saltAnswers : List (Nat × String) := [
  (0, "b839dbf8972530abda22eb6fe1547894fdf7aa94f90787ce52daa9ab88bdab6f"),
  (3, "778f55601d9ee06d742e390752b527319257a3de3d3e3b7a52d5f68538b61f21"),
  (200, "3d6c84e544e612ade6f2cf17686084f6e352a695931999d5a3560f13ac12e322")]

#guard saltAnswers.all fun (n, h) =>
  (blake2bSalted salt16 ByteArray.empty (pattern n) 32).data == (hex h).data

/-- Message length, digest of 32 bytes: with the personalization only. -/
def personalAnswers : List (Nat × String) := [
  (0, "05ecc5e3811f7e58f53848a9e955a31348ba1a608620cfc276f9d24e2e1bb9a3"),
  (3, "ec99601269d45ee8950910b761a29bf82ae4c17bc9fcbf77d6c4b35d4fbbbff8"),
  (200, "5b7598fb8547ca6f752571bb78a6966976c96c7daf7d3d40706af150f9f139f0")]

#guard personalAnswers.all fun (n, h) =>
  (blake2bSalted ByteArray.empty personal16 (pattern n) 32).data == (hex h).data

/-- The first k bytes of the salt and of the personalization, which hashlib fills up with zeros;
digest of 32 bytes of `pattern 5`. -/
def shortAnswers : List (Nat × String) := [
  (0, "663694ac6520bdce7caab1cf3929ffe78cb2fea67a3dfc8559753a9f512a0c85"),
  (1, "e792d42c7dc67b7fac1f08840e0abd4e34a4329d5c9dcc6b46f47ae91009d633"),
  (8, "5eab0164f2d48ec5d366082690fbafa42e65b0ee00476b058c41411659b60110"),
  (15, "3a580222a672640b3dbadc94782c4bb863908c4aaf924da1ea31d03641a9fef0")]

#guard shortAnswers.all fun (k, h) =>
  (blake2bSalted (count 0 k) (count 16 k) (pattern 5) 32).data == (hex h).data

-- Bytes after the sixteenth are not read.
#guard (blake2bSalted (count 0 20) (count 16 40) (pattern 5) 32).data ==
  (blake2bSalted salt16 personal16 (pattern 5) 32).data

-- No digest for a length of 0 or above 64.
#guard [0, 65, 256].all fun d => (blake2bSalted salt16 personal16 (pattern 5) d).size == 0

-- A beginning of whole blocks and a rest, against the whole message.
#guard [0, 128, 256, 1280].all fun p => [1, 127, 128, 129, 300].all fun r =>
  resumeBytes (absorbBytes (firstStateSalted 64 salt16 personal16) (pattern p) (p / 128))
      (count 3 r) ==
    stateSalted salt16 personal16 (pattern p ++ count 3 r) 64

-- A beginning fed in two parts, a blocks from one array and b blocks from another, against all
-- a + b blocks at once.
#guard ([(1, 1), (1, 9), (4, 6)] : List (Nat × Nat)).all fun (a, b) =>
  absorbBytes (absorbBytes (firstStateSalted 64 salt16 personal16) (pattern (128 * a)) a)
      (count 3 (128 * b)) b ==
    absorbBytes (firstStateSalted 64 salt16 personal16) (pattern (128 * a) ++ count 3 (128 * b))
      (a + b)

-- The condition "the rest is not empty" is needed: the chaining values differ.
#guard (resumeBytes (absorbBytes (firstStateSalted 64 salt16 personal16) (pattern 128) 1)
    ByteArray.empty).h != (stateSalted salt16 personal16 (pattern 128) 64).h

-- The condition "the beginning has whole blocks only" is needed, whether the bytes after the last
-- whole block are added to the counter (100) or not (0): the chaining values differ.
#guard ([100, 0] : List UInt64).all fun fed =>
  (resumeBytes
      (incrementCounter (absorbBytes (firstStateSalted 64 salt16 personal16) (pattern 100) 0) fed)
      (count 3 5)).h != (stateSalted salt16 personal16 (pattern 100 ++ count 3 5) 64).h

-- The form for Lean's kernel gives the same digests.
#guard saltedAnswers.all fun (d, n, h) =>
  (blake2bSaltedPlain salt16 personal16 (pattern n) d).data == (hex h).data

end Run.Blake2b.Test
