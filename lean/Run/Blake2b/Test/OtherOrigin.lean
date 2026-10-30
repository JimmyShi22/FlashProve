-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Blake2b/Test/OtherOrigin.lean

Build-time tests of both Lean texts of BLAKE2b, the fast one (Run/Blake2b/Hash.lean) and the plain
definition (Run/Blake2b/Spec.lean), against 39 digests of another code origin than the BLAKE2
authors' source code package, from which both texts are adapted. BLAKE2b-512, no key: 38 messages of
0 to 100,000 bytes, and "abc". Compiling this file runs the tests in Lean's interpreter; if one
fails, the file does not compile. Nothing imports this file; a build of all default targets compiles
it. Where the digests come from, and limits: the two sections below.
-/
import Run.Blake2b.Spec
import Run.Blake2b.Test.Util

namespace Run.Blake2b.Test

/-! ## Where the digests come from

Each digest was computed with two implementations, which agreed on every row. They take neither
their compression function nor their constants from the BLAKE2 authors' package:
- `hashlib.blake2b` of CPython 3.14.7, whose implementation is HACL*;
- a BLAKE2b in pure Python written after the algorithm of RFC 7693, which is not part of this
  repository and whose writer was not blind to that package.
The digest of "abc" equals the one that RFC 7693 prints in its Appendix A; it prints none of the
others. Sixteen digests, those of messages of up to 193 bytes, equal entries of the BLAKE2 authors'
own table of known answers (blake2-kat.h of libb2), since `pattern n` is that table's message up to
251 bytes: no further origin. The other 22 rest only on the two implementations. A reader can
compute all 39 again with `hashlib.blake2b` of CPython 3.14.7. The hashlib of CPython 3.13 gives the
same 39, but is compiled from the BLAKE2 authors' package and does not count as another origin. -/

/-! ## What these tests do not show

- The other origin is one of code only. Both implementations follow the one algorithm of RFC 7693,
  as every BLAKE2b does: a misreading of it that all implementers share is not noticed.
- No row has a key or a digest shorter than 64 bytes. For these see Vectors.lean and SpecKnown.lean,
  whose expected values are not of another origin.
- Of the fast text this file runs only `blake2b`, without a key and with a digest of 64 bytes. Other
  files hash with other functions of the fast text: Fmt/Blake2bFast.lean with `blake2bSalted`,
  `absorbBytes` and `resumeBytes` (Run/Blake2b/Salted.lean), Fmt/Blake2b.lean with
  `blake2bSaltedPlain` (Run/Blake2b/SaltedPlain.lean), and OnBytes/Hash/SecondHashFunction.lean with `compress`
  on its own counter words. No line of this file runs the first four, and none runs `compress` in
  that way. Theorems tie `blake2bSalted` to this table only for a salt and a personalization that
  read as zeros (`blake2bSalted_zero`, Run/Blake2b/SaltedThm.lean), `blake2bSaltedPlain` to
  `blake2bSalted` (`blake2bSaltedPlain_eq`, Run/Blake2b/SaltedPlain.lean), and a message in two
  parts to the whole message (`stateSalted_append`, Run/Blake2b/SaltedThm.lean). For another salt or
  personalization there are only known answers that are not of another origin (Salted.lean of this
  directory, Fmt/Blake2bKnown.lean).
- No row reaches the counter's high word: the longest message has 100,000 bytes. The tests of that
  word (section 4 of Vectors.lean) run the fast text only. They compare the library with itself and
  with six digests that are not of another origin.
- The expected values are typed into this file. Nothing here notices a change of them together with
  the text under test.
- A `#guard` is run by Lean's interpreter, not checked by its kernel, and it is not a run of
  compiled code.
-/

/-- The length of the message and its digest. The message of n bytes is `pattern n`: byte i is
i mod 251. -/
def otherOrigin : List (Nat × String) := [
  (0, "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419" ++
    "d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"),
  (1, "2fa3f686df876995167e7c2e5d74c4c7b6e48f8068fe0e44208344d480f7904c" ++
    "36963e44115fe3eb2a3ac8694c28bcb4f5a0f3276f2e79487d8219057a506e4b"),
  (2, "1c08798dc641aba9dee435e22519a4729a09b2bfe0ff00ef2dcd8ed6f8a07d15" ++
    "eaf4aee52bbf18ab5608a6190f70b90486c8a7d4873710b1115d3debbb4327b5"),
  (3, "40a374727302d9a4769c17b5f409ff32f58aa24ff122d7603e4fda1509e919d4" ++
    "107a52c57570a6d94e50967aea573b11f86f473f537565c66f7039830a85d186"),
  (7, "8f945ba700f2530e5c2a7df7d5dce0f83f9efc78c073fe71ae1f88204a4fd1cf" ++
    "70a073f5d1f942ed623aa16e90a871246c90c45b621b3401a5ddbd9df6264165"),
  (8, "e998e0dc03ec30eb99bb6bfaaf6618acc620320d7220b3af2b23d112d8e9cb12" ++
    "62f3c0d60d183b1ee7f096d12dae42c958418600214d04f5ed6f5e718be35566"),
  (9, "6a9a090c61b3410aede7ec9138146ceb2c69662f460c3da53c6515c1eb31f41c" ++
    "a3d280e567882f95cf664a94147d78f42cfc714a40d22ef19470e053493508a2"),
  (63, "d10bf9a15b1c9fc8d41f89bb140bf0be08d2f3666176d13baac4d381358ad074" ++
    "c9d4748c300520eb026daeaea7c5b158892fde4e8ec17dc998dcd507df26eb63"),
  (64, "2fc6e69fa26a89a5ed269092cb9b2a449a4409a7a44011eecad13d7c4b045660" ++
    "2d402fa5844f1a7a758136ce3d5d8d0e8b86921ffff4f692dd95bdc8e5ff0052"),
  (65, "fcbe8be7dcb49a32dbdf239459e26308b84dff1ea480df8d104eeff34b46fae9" ++
    "8627b450c2267d48c0946a697c5b59531452ac0484f1c84e3a33d0c339bb2e28"),
  (127, "b6292669ccd38d5f01caae96ba272c76a879a45743afa0725d83b9ebb26665b7" ++
    "31f1848c52f11972b6644f554c064fa90780dbbbf3a89d4fc31f67df3e5857ef"),
  (128, "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e" ++
    "8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115"),
  (129, "f59711d44a031d5f97a9413c065d1e614c417ede998590325f49bad2fd444d3e" ++
    "4418be19aec4e11449ac1a57207898bc57d76a1bcf3566292c20c683a5c4648f"),
  (191, "b9d7ca81cc60bb9578e44024e5a0a0be80f27336a6a9f4e53df3999cb191280b" ++
    "090e2ac2d29c5baad9d71415bdc129e69aa2667af6a7fd5e189fccdcee817340"),
  (192, "a755e113386572c75ced61d719706070b9146048e42a9f8cd35667a088b42f08" ++
    "808abdf77e618abd959afc757379ca2c00bcc1a48390fa2bff618b1e0078a613"),
  (193, "a73c7debed326f1c0db0795ee7d6e3946894b826b1f8101c56c823ba17168312" ++
    "e7f53fc7dbe52c3e11e69852c40485e2ef182477862ea6a34ec136e2dfeea6f4"),
  (255, "fe2c02da499516b0e9fb2dd70c49eb3629039f632e20a880946fb7bc97a7ab09" ++
    "deb7d48774d7f0648141c9d9ede19ae6e0dbf07863a128cf4b00195f0f179f74"),
  (256, "93463ac058b6163eb43be3f5bb32b28541498f4e3366f1effe253ad44e1e076e" ++
    "41c3616046027c82a7124f8f4746668ad10b12e8e25a95ac8f3151df01cd5a93"),
  (257, "9ca40e2ddee9436dbbd08efc65dbaf4870059f5eb3d76efd20241ae5bf13c60f" ++
    "250b882ea5c564838257a3fc95c496819ace2c6490b55b268535208dfc31822c"),
  (383, "304ccf9523cedcc53d6fb2af0b84d5b56b9826ad9ebf13884d9897b42c6b8abc" ++
    "1563c998017a2922f04704334d188a298f5da9d4cd711e56fd6e08153fb2afc0"),
  (384, "341ed9e809e36bd2017e29c12c46fd0bc0684e7f0f4cdcde4da7bc8de96248a8" ++
    "aa4f2086392d29ef8ccf3bc17ded4eff49be2524f9e275d4481f18e211dee384"),
  (385, "83b28603193249c295cc95d20091b885fe0c282c27055ee342ecdbc3687dae32" ++
    "f32023dc04adc9cb73c14036b2101ac5c38a5795cf91bb57d422c991d14cbad0"),
  (511, "1b4f20f55a9a973172babeb97dbf2b36c0ac86b08a7371fbc2aa66bbead4fc53" ++
    "dbe4a9342494bb3911971c6a7a1a06e5c4432c9c202adcb84137e83d09699a5b"),
  (512, "57cfa337c698dfb59527a8c569c96f90cd0a87420b1073b7ae83b9556f9523de" ++
    "001f45c384c33f74f5076b6ab0c14910c345e410b6df084ca83b519d5cb35f33"),
  (513, "852267f9bb00f298f5bee46f5a6aecec28262f25450f31915c1c765732800b82" ++
    "88232c93313a08dd7be7820d097b8e0bef5737106ad6acb4b73cbc3cbea3c9e4"),
  (777, "dbd99d5f32aaf89848e946e5895975a9b86d2aca73cd35a64a0e82a87f838a0e" ++
    "2a8f8b2a48cbce9a32aa8df9f71dc6ffb699149d308017f89d7c4565bbcf2d73"),
  (1000, "c11e1c0340bd7e5a1b275f1230c962fad215ecb1391486e74e31b960a2f29963" ++
    "81a5fad092da06841d5f26e38f6ecfeaf441acbcd1c2de61aef121e7927175f5"),
  (1023, "e55fd611a16696f8295ea5120a151e312e5dfb1488ac74be64118ffe1bc1d539" ++
    "e725ad0440e5213de297ba435d381c66edf88eebf28b8d640e31103842d3be29"),
  (1024, "8d1090909017add40e749df2d0ebac43273d6fc816bc4ffaf2a6dfabe4206dea" ++
    "13677d2002399e4a38e700d8083db4af8341ee9b3a5147110b6a963a3894e4e2"),
  (1025, "7a9e5283a15d13b995755360fde4c65c2ae1bc0cf33e8db2ce8416e5d10697c7" ++
    "3fc4b2622a29b938a1faec43d931b02e71ad8635e071265633643a9d9396ec28"),
  (4095, "d745504d13996a7960709a8061b8be4010e32c1294a8e6372e55069587e967e1" ++
    "766d95c75099ac4742f881ef02820d8fecc6bdbfa0c4340370f290a7dd2989aa"),
  (4096, "c7a3d6a53bd11772ecf077c1dc9633a39c6fe691ec07a530e0e765c0a9d5a01a" ++
    "16f00995536578b83e54c2821766ac7ac6ae86e22269a5d14208ccac954cc95f"),
  (4097, "a1aca2bd515e5a87ed22476d9209f748754ebaeddef9cd1e1d57c12cc4b90293" ++
    "42cb74899a9f23cfece0ee8be2fd86e9e72a9289921231a6e40883d01694e0dd"),
  (8191, "e8344176abf9e56e2f3bd4c97bf3c4e086d74da59e753386ec834e39b836ff4a" ++
    "d8c8a6e4b208897f8f9cdf60fd94f8c423ab02499aaea9b70cea94231559d5f0"),
  (8192, "6e02a28235a5fea5bb41fe376b384a8f83376b633ae67572d73b4152c94b07a5" ++
    "fadb1478a2debefb3ac30cb5594e0352b108b73163f9e09f260e4f483900a039"),
  (8193, "00f382e50aa061d8e3eac0a7bec89c711d2ec4c315d894fef92a8c71d79b4f9b" ++
    "8b6182bd2965b2428c12001c0748efff0e7a9610cea33f83a055c695d5ab767f"),
  (65536, "d6d3390ba29d4ea324b3f42d316d70106e4c6a7aa6fc131f8968daaf9fb09488" ++
    "430dac26ccdbe968b51c3d585735feab052cec27a5a035258c383566ac69fd38"),
  (100000, "a0b4e1c912a57364ed019d57296b9f14fd4ac7a36dc5b324706ba2b1497cf7b5" ++
    "8b813ef6d86efab3a9461768ea9a552ab97554f8c4b010ed26d04ae6158bcedf")]

/-- The digest of the three bytes "abc". -/
def otherOriginAbc : String :=
  "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
  "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"

#guard otherOrigin.length == 38
#guard otherOrigin.all fun (_, d) => (hex d).size == 64

-- The fast function.
#guard otherOrigin.all fun (n, d) => blake2b ByteArray.empty (pattern n) 64 == hex d
#guard blake2b ByteArray.empty ⟨#[0x61, 0x62, 0x63]⟩ 64 == hex otherOriginAbc

-- The plain definition.
#guard otherOrigin.all fun (n, d) => Spec.blake2b #[] (pattern n).data 64 == (hex d).data
#guard Spec.blake2b #[] #[0x61, 0x62, 0x63] 64 == (hex otherOriginAbc).data

end Run.Blake2b.Test
