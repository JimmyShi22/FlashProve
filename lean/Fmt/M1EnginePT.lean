-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1EnginePT.lean: the programs' own proof file of the first toy (a product test), read by the
strict reader in Lean; the values named in part 2 that the programs print on the way are read
from the file or recomputed.

The honest proof file of Fmt/M1ProgPTFiles.lean was written by the programs (the C++ implementation
that comes with this Lean code). Here it is read by the strict reader (this library's rendering of
the format
page's verifier up to its decision: it cuts the file, recomputes the hash chain from which the
challenges are drawn, tests the proof of work and checks every Merkle opening against its root), and
what the reader computes on the way is compared with the lists that the programs' tool wrote beside
the proof.

Sources. Made by a program. Every literal is the programs' own value, taken from the lists beside
the proof (tiny.plan.tsv, .digests.tsv, .chain.tsv in honest-and-altered/product/) in the programs'
archive of files (sha256 f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1; the
archive is not in this repository): the run at tiny parameters (sizes for reading by eye, which
reach no security level). By the archive's README its files were made by a script of the programs'
tests; that script is not in this repository. Made-up toy data only. No Mathlib is imported.

1. What the file contains. Tests (#guard) only, but for `S`, a short name for the description. The
description, that is, what a verifier knows before it sees a file, is `Theirs.specTiny`
(Fmt/M1TheirsSpec.lean). At this term the theorems that connect a run to the compiled verifier are
proved (`vbs_N`, `vbsP_N`, Run/M1RunTieTheirs.lean). The reader is `Fmt.wholeChainF`
(Fmt/Rules8Fast.lean), which is proved equal to the reader of Fmt/Rules8.lean at the identity monad
and the format's hash.

2. What is checked when the file compiles.
   The parameter bytes and the public file are those of Fmt/M1Theirs.lean, and the ten parts of the
     check of the parameters hold (`check`, Fmt/M1ParOf.lean).
   The programs' table of the plan agrees line for line with the description's rounds: name, kind,
     bytes of the prover's message, roots, answers, elements drawn, of these not 0, positions, their
     range, matrix entries drawn, work, rows batched, the most words of the verifier's message, its
     blocks.
   The configuration's digest, the parameters' digest, the chain's random bytes, the run's value and
     the chain's first value agree.
   For every round: the nonce, all drawn elements, all drawn positions and the chain's value after
     the round (computed again from what was read: `rhosOf`, Fmt/M1Prog.lean) agree.
   No byte is left over (the reader reads the whole file).

3. Theorems. No theorem in this file. A test (#guard) is an evaluation made while the file compiles;
the compile fails if the result moves; it leaves no theorem.

4. What is not claimed. No verdict of the decision stands here. Whether the proof is accepted, and
what is answered on the altered copies and the false proofs, is tested in other files
(Fmt/M1FullProg*.lean, Run/M1Engine*.lean, Run/PlanQSFProg*.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1TheirsSpec
import Fmt.M1ProgPTFiles

namespace Fmt
namespace M1
namespace EnginePT
open ProgPT

abbrev S : Spec := Theirs.specTiny

-- the files' parameters and public file are those of Fmt/M1Theirs.lean
#guard params = Theirs.tiny && pubs = [Theirs.pubTiny]
#guard check params = allHold
-- the programs' table of the plan
#guard S.rounds.map (fun r => (r.entry.name, [r.kind.num, r.entry.msg, r.entry.roots, r.entry.answers, r.entry.drawE, r.entry.drawNZ, r.entry.poss, r.entry.logN, r.entry.trits, r.entry.work, r.entry.rows, wordsAtMost r.entry r.kind, blocksFor (wordsAtMost r.entry r.kind)])) == [
  ("SEND seed", [3, 32, 1, 0, 8, 1, 0, 0, 0, 0, 0, 162, 41]),
  ("SEND answer", [7, 24, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  ("ZERO", [1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 72, 18]),
  ("PSC epsilon", [2, 24, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("PSC round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("PSC round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("PSC round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("PSC round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("PSC Y", [1, 48, 0, 0, 1, 1, 0, 0, 0, 0, 0, 36, 9]),
  ("PSC values", [7, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  ("BAT", [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4, 18, 5]),
  ("FOLD epsilon", [2, 24, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("FOLD round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("FOLD round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("SEND seed", [3, 32, 1, 0, 8, 1, 0, 0, 0, 0, 0, 162, 41]),
  ("CS", [4, 24, 0, 1, 1, 0, 3, 7, 0, 6, 11, 21, 6]),
  ("FOLD epsilon", [2, 24, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("FOLD round", [1, 48, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("SEND seed", [3, 32, 1, 0, 9, 1, 0, 0, 0, 0, 0, 180, 45]),
  ("CS", [4, 24, 0, 1, 1, 0, 3, 8, 0, 6, 11, 21, 6]),
  ("BASE lambda", [1, 24, 0, 0, 1, 0, 0, 0, 0, 0, 0, 18, 5]),
  ("BASE", [4, 3504, 0, 0, 0, 0, 5, 9, 0, 6, 0, 5, 2])]
-- the programs' digests: the configuration's, the parameters'; the chain's random bytes are the
-- file's first 32; the run's value, the chain's first value
#guard hex (configDigest pubs) = "17bbf2135e917055958937b0fde41e72baaf4cfd37f9c049829e28bb75557f3e" && hex (paramsDigest params) = "26d712eca24f846337fa037bfbe0cf44fb9e9922d3ace3dd4e0f37285835f76b"
#guard hex (proof.extract 0 32) = "2f7ae1e015fbf18838aad498fa01aaa9e703c535e4e3e3a0fd6dbb77b6124b1b"
#guard ((wholeChainF S proof).map fun o => (hex o.pd, o.run.map hex, hex o.rho0)) = some ("26d712eca24f846337fa037bfbe0cf44fb9e9922d3ace3dd4e0f37285835f76b", some "7b7c14d7e6a420e498fb2482d1bf4afb9f7a9c4302c974dcb3bbfcc52be57e63", "1a9f1184480f47bb9328bb6fbff82a22e987aa8399def17dc360fc7c92723e96")
-- Every round, by the programs' list: nonce, drawn elements, drawn positions, the value after it.
#guard ((wholeChainF S proof).map fun o => (o.rounds.toList.zip (rhosOf S o)).map fun y => (y.1.nonce, y.1.drawn.elems, y.1.drawn.poss, y.2)) == some [
  (0, [(13687998085695180131, 15078660302969289606, 13072569935785817272), (11604388674945287352, 18296811957248839872, 18325149893542607951), (5017609362519688062, 11634076539864343619, 11741852906451164481), (17561252779901757386, 12756709628166060805, 8120066246937373690), (14431280221072657083, 6456017649796571241, 17875511605289188935), (10659336847354208591, 3585888256358595421, 12013770344281327446), (11761706773243800992, 12671540633004077958, 13693091768220163491), (14415539598498275946, 2772036203333018155, 18053418615872539107)], [], "2740cb3a58e4e9c0164d8b77c868a19bf1c7d73838a771b7b59c6df2c7e77717"),
  (0, [], [], "dd5ef667a80e2a4811841033cc4d5f9e6fc726cd147e97bca27b5f89eee527d8"),
  (0, [(18414736942881606807, 1653093503231472141, 3104197552606522182), (13565825890557449430, 16093016466650434616, 1652522928127171548), (3523844486081094524, 872656994931678877, 5122146877325924076), (10905907452036257658, 15449396827784739523, 9807222231576922292)], [], "568ccad2056c6336f8b8bde5f776ffbf113228b226f08681070de4adb9ecb8f2"),
  (0, [(5219349334529071811, 16389328956135504626, 725114036961496383)], [], "a9a9882ab8c614756ef275e27e9d9e26da43c3fdb498da2e4cfcd37bd74cb69b"),
  (0, [(2711557016612978381, 3144043008677514166, 14794591228173240362)], [], "e0cad38c010cc1f84a5e8d78a56da2702f68a245e7cd9596ad42231839a33eb3"),
  (0, [(1622504090771189761, 2018496021160596494, 6358308274864574629)], [], "80b861745eb0f0ccc20a101ed98b8bf8c3a351e789336653bbdbf4d56aa042e6"),
  (0, [(14604729417698132026, 17021875685653423846, 4571146807163862296)], [], "56a5044355522236fc29966254bc5c78e1eae4572c28b855a1b30c0f78d5850d"),
  (0, [(11950194489743360738, 1865070005233460777, 12321983241953407775)], [], "412bb1ee327cf7ca832fa0ce260c877264be567f7c6233bc7b94437a182b68cc"),
  (0, [(10715428792119245939, 7585322159111163763, 6973838780464400222)], [], "748b6d891edf1d4e611da97555534bc4a1a5e9adb176de6425c3811a03055cca"),
  (0, [], [], "3225aa69738d536c6348bf12bbfb2d54b79df4cc497abcf3cec41fc5cd63a815"),
  (0, [(13091983006581150347, 140330185526336669, 5320233745131420568)], [], "586283cad14db4adfda461ab8930abe5681c4b9eeea309d6bcf4c6f01bdf5e1b"),
  (0, [(15287796829700624518, 14802042837437902587, 8664769984755802272)], [], "3b7cbeb5a9f87feaf1227c5e6e8085f2700d63a27498befa12414b5c619dc387"),
  (0, [(8017710333395057052, 10338354543840796572, 17983681626081791619)], [], "442897b0c2a54d5b51bfecff4016689dfc992c8ac38df51ff3f485cadf18aa38"),
  (0, [(14939747007014084897, 3478149504310199851, 6386200473323710616)], [], "b7bc4c3c37baed897e2092b0da205223413f79969cd8d78cad11f9958af9a230"),
  (0, [(16501130625969572208, 13873503765878959547, 1970761351906415524), (14829865440578217717, 11860045582159247019, 7871895385741920404), (13630851965508719420, 11163397620405405038, 14340253042771783862), (16609605999349807293, 1111284745005059814, 17640938648241123259), (3263263450319596072, 12048222370595771379, 7614425210082325415), (3067878326482921015, 14540421720061150292, 13220638781286928317), (10119270100959620546, 13636727436840500893, 13784902569473639504), (7880747710632824746, 2962707614315577063, 12163278746015304377)], [], "d1ff6f7db2e2e99d42ae4d64aa6a5f23dd36f42d498f9863f958c751931c7b4b"),
  (26, [(11986731499721366523, 14094707017210580023, 16570735699357130310)], [38, 41, 24], "57eac1169f24f03656d117118c7e4e30f3803420839b227dd47d50ef208a53bd"),
  (0, [(14819538055066626554, 11758822069013772912, 7786735257262031782)], [], "05a30279fd992ddaee0827fe70b58e2492bf5c386ac47b81d04c74a7a346a469"),
  (0, [(6650717545069142827, 144943768124958519, 7857276415384397918)], [], "21dca6f8930b43e548537041dad14383f1efed1821fd8be27ff9c8fe51b5021c"),
  (0, [(4031362976504714315, 6178863725670055747, 14612791307056348077), (4902082631659289631, 14897300983642656809, 1799105528389835928), (17350824951405420638, 6682744244382947077, 14064023412206936543), (12170483392633261622, 13693289355410283702, 1318071482920682422), (4432198819228682282, 15802590569325262595, 15842504380099390664), (14710913871205510537, 17972350865533758283, 3677377209846596823), (14062555780798043369, 15287941395299863036, 7135151554606509141), (5201109485531807596, 5427244787820914070, 7762289171465079193), (3049000697814690079, 4866219189195096645, 12251059608638168505)], [], "d02f6ce7e39c3e6d2dc588800e936a09bd334b054db0b91d51016ba998ff3622"),
  (48, [(10849126835845408644, 6864537644623159802, 16946378054932931671)], [142, 117, 115], "423ef9325e0dcfc879c6c9b4b98b3aac4b05f5c99d203eec41b200ae0220ee83"),
  (0, [(17613901505362582302, 3018087776984247639, 15156562054194667886)], [], "3cc80614896c298befb0c90eca7a930ffab2d33c7022e4a5acc4a3e82d1d9981"),
  (155, [], [55, 451, 49, 361, 207], "8f858fa7eb60909d20873f8158458cfdafe13dc968f128ca467cc736b1843ac3")]

end EnginePT
end M1
end Fmt
