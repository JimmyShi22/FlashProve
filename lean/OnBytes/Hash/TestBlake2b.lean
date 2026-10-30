-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/TestBlake2b.lean: tests of the hash as OnBytes/Hash/H.lean and Query.lean call it.

The known answers were made with the function blake2b of Python's module hashlib. The messages have
lengths around the borders of blocks of 128 bytes. They are given to `Fmt.blake2bF`, the form of
BLAKE2b that the program calls. `formatHashFastForm` and `queryH` are tested on known answers of the format
page's list (docs/format/format-vectors.txt, R2.x, R3.x, R5.x and R6.x) and compared with the
functions of Fmt/ to which they are proved equal. The program does not import this file.
-/
import OnBytes.Hash.H
import OnBytes.Hash.Query

namespace OnBytes.HashTest

open Fmt (hex)

/-- n bytes: byte i is (a i + b) modulo 251. -/
def pat (n a b : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => UInt8.ofNat ((a * i + b) % 251)⟩

/-- Rows (digest length, salt length, personalization length, message length, digest). The salt is
`pat s 5 1`, the personalization `pat p 9 4`, the message `pat n 7 3`. -/
def rowsB : List (Nat × Nat × Nat × Nat × String) := [
  (32, 16, 16, 0,
   "fc9bc2515b2e1138b165d28985450b049b80ec02218b66c2fcd48b91ff13c096"),
  (64, 16, 16, 0,
   "49378860a5c35fdce398418135c248f7b497770cf1d028dba5c67ead7fb8e624" ++
   "394d3783fcb4cb680a4144fbdc9e222a48b7e80137e3c23d1471451e5f6d28ff"),
  (32, 16, 16, 1,
   "141d5050dfcb8fc2f803ecc83e0ee8b6fbcf3964649e6d483c5dfdd6564a4a4d"),
  (64, 16, 16, 1,
   "fb19830a48ec3f631e818f22826144a2c7cced57fc7cf447c47c033b6d714b71" ++
   "f810428ddd1aa362710c5ce907b521f0a1ea748d3ab47cd0556e3efdf35e6e45"),
  (32, 16, 16, 3,
   "8182dd1824436cd3201b6eb699a0920c32a7fa0e5f3e081c32821700edfb886e"),
  (64, 16, 16, 3,
   "580f850de315a59359f725f3f31d6cd9421802bb1a6d7bfe53dfcfe81c540f13" ++
   "f92ba5934af8f86296caf4e66692beb81452dd705dd0e60e98d22333e549503f"),
  (32, 16, 16, 63,
   "ad20e8c0443aa8cfb11f35470ac7a9919218ae6858a759445f52fca19144b4ce"),
  (64, 16, 16, 63,
   "16d2e4add60c8565d4e9c3d082d2fc62dfe1c10c34c67d9883e2c84f494dd3a0" ++
   "812786cb250e0e5380ec9f9f159c6b2debdfba88400be90011061db89063a618"),
  (32, 16, 16, 64,
   "eeb5b24691321cb41060215efe329e58fe4687a14fe0567195bdbdcc4384d34a"),
  (64, 16, 16, 64,
   "468e3118db6360fc59271ee12b83b62e583d8d5515f8b3649af2f5d555b78684" ++
   "14e6c3c8317c6cc886d67a41065175cccb465637e5b2a4ced1387bfd52659f76"),
  (32, 16, 16, 111,
   "70543354def77d75a2795bb569000d3f562334a9ecae19ac870dd68a4a7173cf"),
  (64, 16, 16, 111,
   "a7eb81b232594619b9f1191fee37419bde6bc430ac06efa938941553556d3d4a" ++
   "7ca539ff93181752da180598f7ab9bb2a05b0a89ce48d9cee9402ea10ab9aef5"),
  (32, 16, 16, 112,
   "221d0eca32e0dc99be702929e4c7020e4e4f3ffd8556f029ee32a3db435ededc"),
  (64, 16, 16, 112,
   "6900c63d3c2028a67be206cb4b1ed2889d43ce0d57c9860bcb1cd134989c9248" ++
   "d1caa59296aa7a92329d33e7e9f52600301dfa25f2fe16070817fe31742fe1ea"),
  (32, 16, 16, 127,
   "0182bad86dbc09562833b7ef70826f6fc70742cac0361a7593bdba224c847ea0"),
  (64, 16, 16, 127,
   "1b457febf34cbfb83f373348c74c816c14014e4b39a70787ab446d72d337015d" ++
   "7572f0c0f5fe9a3d6eb7730d096d2d9197786be82cc9e7b427861ce2f032f3e8"),
  (32, 16, 16, 128,
   "529cc34815d6047e010b3c1c86f5fa51e566b529a14ff972d87433a8212c1370"),
  (64, 16, 16, 128,
   "29e49d036d03cf3c3b2d36f37b46af00611996f0e73e686332a9cddfceff7243" ++
   "ca1f523d2400fe9880f2487b8a3a46ede4d50e8ec08bcefe07a15c73397cb58e"),
  (32, 16, 16, 129,
   "79283d6e59913df4fdf0ce40c8ca7779c0dd7632240d49bda9f559a32be7c172"),
  (64, 16, 16, 129,
   "1c4e104fbd5de1a5d1b809ae0ce049cb5483edd9c3b97f83a845eb40ba0c38c9" ++
   "6894b92b2a3f5fc59e8701f01bfe0bc1f335690fc5266dfa5e03e3eea435432b"),
  (32, 16, 16, 255,
   "f4af0df131a085370e33e8c58480e17fc1999fe23a382cecc4fb4b3c09393be3"),
  (64, 16, 16, 255,
   "4d962f032a4fe7c79e5ed98d1c9b4ffa0e9369ec76ae318f2d6252b8dd34d9f4" ++
   "f1c024baaf961f887a45abe71943e108beb29799bcf3e4d7816527b909fcc499"),
  (32, 16, 16, 256,
   "9931c3f7368ca8ae0c314e486034c189d46931f2c5890edd6016ff4e5ce6283b"),
  (64, 16, 16, 256,
   "a3baf77c912b8ce0f504c591d652174917fcb133525a8e47c2f2b075c2ae2364" ++
   "43845a43fa524b1eb3f191c66c2ea2fdc52963d85479487f25150190e49ae2d3"),
  (32, 16, 16, 257,
   "510a773609bba35e4cedd7b50ea9076c74c14e20f18eede999bb12213551227b"),
  (64, 16, 16, 257,
   "902e3a0f8bba1d3569d16dada131c9f4710b52715b1000733ed6aae23b838cc3" ++
   "09a6137cfc0d28878840ca97aefe78438dbc5c2ef5c2a2bc4f6c11c8656344b0"),
  (32, 16, 16, 384,
   "8a3cf65f2aa6f615365a6bbde65829b1ccdecedada9e00239b638e0bb43e1319"),
  (64, 16, 16, 384,
   "5f10f2c5af038397261e1e8e8c20b95c5b1cfa8534e5565293c24af7125db616" ++
   "ced565709422c44cfa23c236c28e62600e92449bc4a4e8ac072118860dd06baa"),
  (32, 16, 16, 1000,
   "f0e3100ce4874dd626ce7887a20018736065c4bac13ca02601dd1878f9239b6b"),
  (64, 16, 16, 1000,
   "fcf1edb6138f84ad939eb10f4cfbe3c3adff53f5687272533e21a8ada5d1b716" ++
   "389b3377bf1e28ff05e384fcd18b976e1baffa267e6e4f60ca309e0d62833559"),
  (32, 16, 16, 4096,
   "d83a05f243a545c95a5f69d2359b09456eb67412d02e5227009394e5cbdc659c"),
  (64, 16, 16, 4096,
   "e700195ce163dd0ffd8d6b9dc1c86aced54a2c290894b2f655381971c97020b5" ++
   "c0150cda0fd736bb0b4fdda39bafc19417d52e40165455d7d00510b971c94022"),
  (32, 16, 16, 4097,
   "83a195e748503c7882b404faa7070dbf079aae75ed0a58cd5b15265063f1623f"),
  (64, 16, 16, 4097,
   "e4af1062aa6cb8918c347e99244a0dc3dbfb97e99cd4c62eeae19321730285a7" ++
   "e8566d742cf1bdeac61b442a58ba705ddf40e2aab73b8425a9777dbce7b50350"),
  (32, 0, 0, 0,
   "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"),
  (64, 0, 0, 3,
   "76ce7e90c577d436a65b691e51f0a1ad536130d70a18df3bf5368551327258b6" ++
   "f706f4a47c45f2d0d8147cfbb5623077e798247972e4f9338603a13abc05a4db"),
  (1, 16, 0, 5,
   "74"),
  (20, 0, 16, 200,
   "da9dd820fc24d5f80eb547af08618551339d41ca"),
  (48, 7, 9, 130,
   "b54402440214f8ae41142477b6000308d37a93a7082bf1f289129dbe5a4d2cd3" ++
   "7c55948d0baa62be3acf35c7b5185203"),
  (63, 16, 16, 128,
   "aec0083e010348c3adcb64f0a52641fdd950fb738143176d9e80eaa4b12e1d69" ++
   "7c5e6390b801d21f016b3a89dd59f952d849ac58fd041d97bfa4687ea29af0")]

#guard rowsB.all fun (d, s, p, n, x) =>
  hex (Fmt.blake2bF d (pat s 5 1) (pat p 9 4) (pat n 7 3)) == x
#guard rowsB.all fun (d, s, p, n, _) =>
  (Fmt.blake2bF d (pat s 5 1) (pat p 9 4) (pat n 7 3)).data ==
    (Fmt.blake2b d (pat s 5 1) (pat p 9 4) (pat n 7 3)).data
-- a longer salt is cut; the digest lengths 65 and 0 give no byte
#guard (Fmt.blake2bF 32 (pat 20 5 1) (pat 16 9 4) (pat 5 7 3)).data ==
  (Fmt.blake2bF 32 (pat 16 5 1) (pat 16 9 4) (pat 5 7 3)).data
#guard (Fmt.blake2bF 65 (pat 16 5 1) (pat 16 9 4) (pat 5 7 3)).size == 0
#guard (Fmt.blake2bF 0 (pat 16 5 1) (pat 16 9 4) (pat 5 7 3)).size == 0
-- the format's hash, at each of its numbers
#guard Fmt.numbers.all fun n => [0, 48, 112, 113, 300].all fun k =>
  (formatHashFastForm n 7 5 (pat 32 7 3) (pat k 9 4)).data == (Fmt.formatHash n 7 5 (pat 32 7 3) (pat k 9 4)).data
-- known answers of the format page for H, with varied labels, digest lengths and starts
#guard hex (formatHashFastForm 168 0 0 (Fmt.zeroBytes 32) ByteArray.empty) ==
  "8313e9c466ac5287097eff32299fb13cd2f38c4149e5c06db3672e05c4c584df"
#guard hex (formatHashFastForm 168 0 5 (Fmt.zeroBytes 32) (pat 128 7 3)) ==
  "4d26351ed3e9aacf02412551771a4182b2dd254e97c59b70b8276663cc4fde1f"
#guard hex (formatHashFastForm 168 0 (2 ^ 33 + 5) (Fmt.zeroBytes 32) (pat 129 7 3)) ==
  "0dcff0ef969a659d79a3810bcab9ef0716b249a3d129f2659ed88ddf3f5d55fb"
#guard hex (formatHashFastForm 164 (Fmt.leafPlace 9 3 5) 12 (pat 32 7 3) (pat 64 7 3)) ==
  "a88e3190297571af06940920681fc835d3703d831b5c10d2c5c98ade7383b486"
#guard hex (formatHashFastForm 166 0 0 (pat 32 7 3) (pat 64 7 3)) ==
  "af2a19aa20cc89e1e740e2ec4d34a275eae7bff385fcfc64e3064ccd7cc1b3f8"
#guard hex (formatHashFastForm 178 0 0 (pat 32 7 3) (pat 64 7 3)) ==
  "5060c36d8a53d1f4d4fcce8b2678190f7a3ab70d9a7e09c978a808fb3a01f408"
#guard hex (formatHashFastForm 162 0 3 (pat 32 7 3) (Fmt.u64n 1 ++ Fmt.u64n 0)) ==
  "7dd1787fe5dee7994c6410b994bcd7aec9789019b120012e63ba79f094be483d" ++
  "62ab614467bab4323df78f9a77004db3462e2a38d4eb8e0d431ae6dc57c997ea"
-- known answers of the format page for the toy chain: the value after round 1, the value after
-- round 3 (eight bits of work) under the least nonce, and none under the nonce before it
#guard (queryH ⟨7, Fmt.unhex "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72", 0⟩
    (Fmt.cat ([4, 5, 6, 7, 8, 9].map Fmt.u64n)) .elems 0 0 1).map (hex ·.1.rho) ==
  some "3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd"
#guard (queryH ⟨7, Fmt.unhex "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f", 2⟩
    (pat 32 11 2) .positions 8 116 1).map (hex ·.1.rho) ==
  some "28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495"
#guard (queryH ⟨7, Fmt.unhex "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f", 2⟩
    (pat 32 11 2) .positions 8 115 1).isNone
-- `queryH` draws the same blocks as `Fmt.Chain.query`
#guard [0, 8, 112, 120, 240, 1000].all fun n =>
  (queryH ⟨7, pat 32 5 1, 2⟩ (pat n 7 3) .elems 0 0 3).map (·.2.map (·.data)) ==
    ((⟨7, pat 32 5 1, 2⟩ : Fmt.Chain).query (pat n 7 3) .elems 0 0 3).map (·.2.map (·.data))

end OnBytes.HashTest
