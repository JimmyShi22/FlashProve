-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1EnginePR.lean: the programs' own proof file of the first toy (a product test), read by the
strict reader in Lean; the values named in part 2 that the programs print on the way are read
from the file or recomputed.

The honest proof file of Fmt/M1ProgPRFiles.lean was written by the programs (the C++ implementation
that comes with this Lean code). Here it is read by the strict reader (this library's rendering of
the format
page's verifier up to its decision: it cuts the file, recomputes the hash chain from which the
challenges are drawn, tests the proof of work and checks every Merkle opening against its root), and
what the reader computes on the way is compared with the lists that the programs' tool wrote beside
the proof.

Sources. Made by a program. Every literal is the programs' own value, taken from the lists beside
the proof (tiny.plan.tsv, .digests.tsv, .chain.tsv in
honest-and-altered/product/tiny-with-a-repeat/) in the programs' archive of files (sha256
f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1; the archive is not in this
repository): the run at tiny parameters with a repeated position (under another key of the prover's
coins, at which one position is drawn twice). By the archive's README its files were made by a
script of the programs' tests; that script is not in this repository. Made-up toy data only. No
Mathlib is imported.

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
what is answered on the altered copies, is tested in other files (Fmt/M1FullProg*.lean,
Run/M1Engine*.lean, Run/PlanQSFProg*.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1TheirsSpec
import Fmt.M1ProgPRFiles

namespace Fmt
namespace M1
namespace EnginePR
open ProgPR

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
#guard hex (proof.extract 0 32) = "2f6d45b09f700df2a167a097728f421a23403cfb3d0b17d35f8bc6bcba74915d"
#guard ((wholeChainF S proof).map fun o => (hex o.pd, o.run.map hex, hex o.rho0)) = some ("26d712eca24f846337fa037bfbe0cf44fb9e9922d3ace3dd4e0f37285835f76b", some "36e216d08fd752e333bf98d8cd2a367dc0ca536fd7026e2c8f93273fc6bf7b50", "83d444954904e9aafa59cba7217fc3716650a36a01e367e559370f63dabb3478")
-- Every round, by the programs' list: nonce, drawn elements, drawn positions, the value after it.
#guard ((wholeChainF S proof).map fun o => (o.rounds.toList.zip (rhosOf S o)).map fun y => (y.1.nonce, y.1.drawn.elems, y.1.drawn.poss, y.2)) == some [
  (0, [(4520577247823612145, 13075914283606540519, 11013286993131627592), (11932900307405198902, 10474684206685288163, 15701410296074470784), (8567504525326133770, 7844982871451786413, 3740531961563520486), (4291204208299252968, 16260356532127302301, 10394361048127712830), (3389645307361335513, 1227798610368548336, 3767263134933123433), (6837858105864252892, 3690499220737003444, 15849051947507395784), (10689345964279536009, 16257496529231787683, 11144628213652390916), (2291581054899290486, 4321816997909301240, 2968389291433044198)], [], "ad96e53e3d7664d5a390a0c54dcb3e3c44e25484661edf534bab8f26c9f38f3e"),
  (0, [], [], "27b43eb857512e52f457db6ceebb4749f4ad4143c33792952438e74513a89b40"),
  (0, [(13959407985928804081, 18391256806802822674, 2469792810681703843), (5965874190815778719, 12007368122294674337, 16590626073459715782), (1077324843817731078, 11930515701535445254, 422455545114603359), (10355407736092882509, 2119144348030766242, 18292240348448943030)], [], "88323d259001035ce5b01250f2c344d6a699b0016555427cf923c93a49894e45"),
  (0, [(9163911301878993398, 14985543076377434121, 7193018564510291432)], [], "b169f1ddd073341c8bf56f33926e119389ed5e0ca2c42b8e5edbaf3ebc4af5a4"),
  (0, [(13703198663849564944, 5452026488616254170, 14937367557353305982)], [], "da86e60ee16287c46efa6827fcfa6dcf00b506c165893bf5975df9c5bc814b71"),
  (0, [(8635503606589068759, 3786594969618891838, 4047297507169622615)], [], "a43c37331d1d706b3564724d6eb255719b5a2b5363468ab5f418ab8fe05b7549"),
  (0, [(15535256310204415613, 179612953697708529, 728804388039042344)], [], "d4b0ea2945861aecfb54c92fa8c535b9a965b50942513e1c1d2c35d043a5bdfd"),
  (0, [(100855565555054396, 16914967875429415837, 10356554760037692956)], [], "07f7e2eeb5eaab061ccb98a438092bac948720d1d2525d15626622155ca72bde"),
  (0, [(1404052983919573496, 17501461063847535205, 12259544467595089126)], [], "0cb7c3517b03c3b81400faed3ad8901c0624c702a08afd46190cae3fbcf19c26"),
  (0, [], [], "2e07a0ad933d46063a28ea853692ba43b942622d5294e4bcf51971885d57a122"),
  (0, [(5910248260972485507, 10322421928975258655, 18121153151149426239)], [], "204be88d9804010f998b8e3711330cc24e359e72d91d6f033136a55f48f87226"),
  (0, [(3125495426926409082, 10420083814432682107, 3287433409261237837)], [], "b02ca8c14804269528fc41ef61c070c9322230b5998d3a407d8823b49d7f62d6"),
  (0, [(3040056932293084788, 6377503856110835970, 14879845952756359664)], [], "610350e14781a0ac9584a6d790eba6f28dc7ea5bbbf9ae20dc318b5caf97205a"),
  (0, [(908042138258735460, 4338781409867095928, 4911546058399001337)], [], "505ccef8fb5a0e97dddee106c30dfb5ab79a5d9015d691b74b79c085cad0021f"),
  (0, [(1285654859763469312, 3485791309009003033, 14990387398628590138), (16404150576448422743, 819840977953370517, 16795765106045418720), (13511227523192954644, 14969906753848897916, 6760955940497876573), (9969313133327957271, 16895437570878619927, 727530309621968692), (17873869245747110686, 9076033784969318409, 2128363071924813916), (13304968010856501106, 6715473528681072592, 1607888663184767438), (17682124199372452184, 15066896518199386441, 10224058311131039200), (14987141518351424317, 7845953765230191418, 14120233769810951725)], [], "fd6e4915da03eb684ce3ace81c07320930358a21c2af8bea485dd9ea6c42be28"),
  (133, [(17387616284698610396, 8554593230726710870, 10726893579866967051)], [92, 23, 27], "5860bf48b84a91200b1df10e1ac86986375777edf7fbb219ef458be74c6f0c88"),
  (0, [(2467345137845504190, 10101715733871567581, 10597142195011884425)], [], "a15f587f84ac34c161b6d6e7353f8fc7e787514673d0fd32870129038e3b798c"),
  (0, [(14924366624249866431, 14815837759805123210, 14036009957636379636)], [], "52f35e5369d03c123a707607393946c7e1f5f669cfe1c3394cf5dc22a081e765"),
  (0, [(4578153979149509986, 7176545710059599150, 1796344528851291933), (922925607929550155, 13722423808166405241, 9575291190703481432), (18407237827589998996, 4188738787771652857, 5677126293102309212), (4775132661397847295, 18392543411733346743, 16001657848970385634), (9660074396719188466, 11943817368176089616, 7026633805586115381), (18364435143887117123, 17716017238876888032, 17399922028180751872), (2972268632528768205, 1457920531284759564, 6095909838370513718), (15556250498792967715, 7559489020703827166, 11269890618659612346), (3380974583285565200, 9742507405473061472, 5760450976301098547)], [], "c25c416fb36c5d3f60fc17789a9ff53c10053a26e3f5dd991988a1bf75f6019c"),
  (64, [(12414347949320097399, 13284334758892917133, 6418974975113748478)], [222, 208, 208], "36efc3dce1a6d17b7c430a13cc6ebc72e30ee429b5ad9ca2102cd265bac70d49"),
  (0, [(15962529283727429068, 12195162928016864705, 3565613225288218313)], [], "ca833ec6722b27e26ef9cd0adf548408aaa180a19b1f163e28c37c19a1a842c7"),
  (10, [], [66, 125, 405, 278, 488], "4a917a34f8d8c7aa7add32d302f676e4bc0779244aa71e7e2769de0dfb8cb203")]

end EnginePR
end M1
end Fmt
