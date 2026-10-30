-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/FoldAtWritten.lean: the stages that are folded in the nine proximity tests of a key
file, an entry file and a proof file, and the groups of a proof file's links as they are closed, at
two sizes, as written numbers; and at each of the sixty: what the fold asks of its codes holds, with
no hypothesis on codes, the fold is taken off, and each of its rounds' error counts is at most
2^-128 of the round's written verifier messages.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions, and statements that are proved by evaluation on natural numbers and the theorems of
Johnson/Bridge/FoldPriced.lean.

Main names:
  `foldFull` (36 places), `foldSmall` (24 places): in the order: the key file's proof of the ranges,
    folded row, Omega, own test; the entry file's test; the proof file's links' groups, each
    different one once; its last test behind the links, folded row, Omega, own test. A place
    (`FoldedPlace`) is: the main code and the mask code (logarithm of the length, entries of a
    message, random entries), the numbers of row variables of the mask rows and of the others, the
    number of drawn positions, the radius, and two brackets of `Cb.bchksBound`.
  `fold_good`, `fold_priced`: all sixty pass the two tests.
  `foldFull_key`, `foldFull_entry`: the key file's fourteen at full size, stage and radius, are the
    `keyFolded` (Johnson/Top/H/KeyValues.lean); the entry file's four stages are `frSg1` to
    `frSg4` (OnBytes/Slice/FullRecSz.lean).
  `FoldedPlacesPaid`, `foldedPlacesPaid`: THE STATEMENT: `FoldedPlace.Paid` at each of the sixty.

Limits: THAT THESE NUMBERS ARE THOSE OF A FILE's PLAN IS NOT PROVED HERE, and that they are the
stages of the description of the protocol that a verifier runs is open. The numerals are tied to
nothing but typed numbers: at fourteen places stage and radius, at four more the stage alone (not
the radius), and nowhere the brackets, equal definitions elsewhere, which were themselves read off a
print (their heads say so). They were read off a print made by evaluating this library's port of
the planner at the public files that the head of Johnson/Bridge/BaseAtWritten.lean names
(`Model.Verify.planned`; `stageOf` and `radiusOf` of Johnson/Top/H/StageJ.lean; the links' groups:
`framesFrom`, OnBytes/Plan/ReqFrames.lean, field `closed`). `stageOf` does not read a group's number
of slots: at the links' groups but the last that number is not 1 (16, 4 | 8, 2), so there the stage
is not the whole of the group: the counts, which do not depend on the number of rows, are the
group's by reading, not by a theorem here; `FoldHolds` is said of the stage as written. At full
size the plan has 59 folds with 59 first and 329 repeated rounds: 25 folds at links' groups, of
which two differ. The brackets were reckoned outside Lean in exact integers, and Lean's kernel
checks them here. The tightest round has 128.0018 bits at full size (the key file's proof of the
ranges, stage 1) and 128.0008 at the small size (the proof file's last test, stage 2). No work is
counted. No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.FoldPriced
import OnBytes.Slice.FullRecSz
import Johnson.Top.H.KeyValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb

/-- The stages that are folded, at full size. -/
def foldFull : List FoldedPlace := [
  -- key: proof of the ranges, stage 1
  ⟨⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 0, 49⟩, 3131959,
    ⟨77, 4612108211566870325, 4612108211566870326, 500193289808492387⟩,
    ⟨138, 4638628911841119210, 4638628911841119211, 8962058789237062632⟩⟩,
  -- key: proof of the ranges, stage 2
  ⟨⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩, 431022,
    ⟨195, 3264733890588537296, 3264733890588537297, 18006457154025524701⟩,
    ⟨3, 2327136786579556697, 2327136786579556698, 91446925450⟩⟩,
  -- key: proof of the ranges, stage 3
  ⟨⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩, 114481,
    ⟨208, 2323787583424143510, 2323787583424143511, 17223398529421648723⟩,
    ⟨3, 1655757452438728716, 1655757452438728717, 63468531239⟩⟩,
  -- key: folded row, stage 1
  ⟨⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 0, 7, 97⟩, 8342420,
    ⟨182, 9223477589367069439, 9223477589367069440, 18114154088539623242⟩,
    ⟨3, 2946441981012053085, 2946441981012053086, 1441748185679⟩⟩,
  -- key: folded row, stage 2
  ⟨⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩, 1519572,
    ⟨10, 4612583132657550687, 4612583132657550688, 11413375904292⟩,
    ⟨167, 5050204171033392320, 5050204171033392321, 8983489520705672442⟩⟩,
  -- key: folded row, stage 3
  ⟨⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 95065,
    ⟨11, 4626018969097650822, 4626018969097650823, 1114413867203⟩,
    ⟨292, 5050204171033392320, 5050204171033392321, 9117596699681141319⟩⟩,
  -- key: folded row, stage 4
  ⟨⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 5944,
    ⟨22, 4835918222100210788, 4835918222100210789, 1747968995432⟩,
    ⟨427, 5050204171033392320, 5050204171033392321, 3800245370618256297⟩⟩,
  -- key: Omega, stage 1
  ⟨⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 0, 4, 49⟩, 3138896,
    ⟨158, 4612539160536728799, 4612539160536728800, 17891796372602289609⟩,
    ⟨3, 2946441981012053085, 2946441981012053086, 360460126566⟩⟩,
  -- key: Omega, stage 2
  ⟨⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩, 196275,
    ⟨277, 4618436477300632084, 4618436477300632085, 18324740943425337402⟩,
    ⟨3, 1911904021756458006, 1911904021756458007, 82448869728⟩⟩,
  -- key: Omega, stage 3
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩, 12184,
    ⟨461, 4718534616742505246, 4718534616742505247, 13662335249885330219⟩,
    ⟨3, 2156918632041367840, 2156918632041367841, 3588979038⟩⟩,
  -- key: own test, stage 1
  ⟨⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 1, 4, 49⟩, 3138896,
    ⟨158, 4612539160536728799, 4612539160536728800, 17891796372602289609⟩,
    ⟨4, 3553542733661254395, 3553542733661254396, 721854837584⟩⟩,
  -- key: own test, stage 2
  ⟨⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩, 196275,
    ⟨277, 4618436477300632084, 4618436477300632085, 18324740943425337402⟩,
    ⟨3, 1351920298761823949, 1351920298761823950, 233191245997⟩⟩,
  -- key: own test, stage 3
  ⟨⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩, 24460,
    ⟨404, 4665416211977019035, 4665416211977019036, 14623094635993291384⟩,
    ⟨3, 1525171791184062903, 1525171791184062904, 20301303539⟩⟩,
  -- key: own test, stage 4
  ⟨⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩, 6631,
    ⟨409, 3506473864298787529, 3506473864298787530, 9156206187091346831⟩,
    ⟨3, 2078458800722539360, 2078458800722539361, 2005480427⟩⟩,
  -- entry: the entry's test, stage 1
  ⟨⟨⟨24, 4194304, 97⟩, ⟨13, 64, 97⟩, 0, 8, 97⟩, 8342420,
    ⟨182, 9223477589367069439, 9223477589367069440, 18114154088539623242⟩,
    ⟨3, 2578010857022246786, 2578010857022246787, 2152365184600⟩⟩,
  -- entry: the entry's test, stage 2
  ⟨⟨⟨21, 131072, 49⟩, ⟨12, 128, 49⟩, 2, 3, 49⟩, 1569886,
    ⟨182, 4612530366062261080, 4612530366062261081, 18104829799822748029⟩,
    ⟨5, 3823808043512916013, 3823808043512916014, 790034243611⟩⟩,
  -- entry: the entry's test, stage 3
  ⟨⟨⟨17, 8192, 49⟩, ⟨12, 128, 49⟩, 2, 2, 49⟩, 98104,
    ⟨316, 4625177083870788382, 4625177083870788383, 17606024865515151515⟩,
    ⟨5, 3823808043512916013, 3823808043512916014, 49377139883⟩⟩,
  -- entry: the entry's test, stage 4
  ⟨⟨⟨13, 512, 50⟩, ⟨12, 128, 50⟩, 2, 2, 50⟩, 6044,
    ⟨506, 4827321027350916341, 4827321027350916342, 10158663074719008228⟩,
    ⟨4, 3834655747700258926, 3834655747700258927, 1121997607⟩⟩,
  -- proof: a link's group as it is closed
  ⟨⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, 8, 219⟩, 2433820,
    ⟨258, 13044156798776087384, 13044156798776087385, 18256289497540868099⟩,
    ⟨3, 4672644678352822300, 4672644678352822301, 180755102387⟩⟩,
  -- proof: a link's group as it is closed
  ⟨⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, 7, 219⟩, 2433820,
    ⟨258, 13044156798776087384, 13044156798776087385, 18256289497540868099⟩,
    ⟨3, 4672644678352822300, 4672644678352822301, 180755102387⟩⟩,
  -- proof: last test behind the links, stage 1
  ⟨⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, 1, 219⟩, 2433820,
    ⟨258, 13044156798776087384, 13044156798776087385, 18256289497540868099⟩,
    ⟨3, 4672644678352822300, 4672644678352822301, 180755102387⟩⟩,
  -- proof: last test behind the links, stage 2
  ⟨⟨⟨22, 262144, 55⟩, ⟨17, 4096, 55⟩, 3, 1, 55⟩, 3138982,
    ⟨158, 4612160982991925307, 4612160982991925308, 17896197886645129614⟩,
    ⟨3, 3282379621777433489, 3282379621777433490, 260738081209⟩⟩,
  -- proof: last test behind the links, stage 3
  ⟨⟨⟨19, 32768, 55⟩, ⟨16, 2048, 55⟩, 3, 0, 55⟩, 392563,
    ⟨241, 4615484366386020384, 4615484366386020385, 18330387617046682139⟩,
    ⟨3, 3303665842157800268, 3303665842157800269, 31966416313⟩⟩,
  -- proof: last test behind the links, stage 4
  ⟨⟨⟨16, 4096, 55⟩, ⟨15, 1024, 55⟩, 3, 0, 55⟩, 48999,
    ⟨364, 4641985777974716572, 4641985777974716573, 17641035978733203298⟩,
    ⟨3, 3345832038073801511, 3345832038073801512, 3846647774⟩⟩,
  -- proof: last test behind the links, stage 5
  ⟨⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 4, 0, 46⟩, 6617,
    ⟨333, 3535965332883209267, 3535965332883209268, 3198991218400469305⟩,
    ⟨333, 3535965332883209267, 3535965332883209268, 3198991218400469305⟩⟩,
  -- proof: folded row, stage 1
  ⟨⟨⟨24, 4194304, 101⟩, ⟨13, 64, 152⟩, 0, 7, 101⟩, 8342416,
    ⟨182, 9223481987362201220, 9223481987362201221, 18114128176658313456⟩,
    ⟨3, 2988436145658779760, 2988436145658779761, 1381824007158⟩⟩,
  -- proof: folded row, stage 2
  ⟨⟨⟨21, 131072, 54⟩, ⟨12, 256, 54⟩, 2, 3, 54⟩, 1517714,
    ⟨10, 4612618310052393905, 4612618310052393906, 11413114702386⟩,
    ⟨168, 5066627642583988803, 5066627642583988804, 9165166916903628728⟩⟩,
  -- proof: folded row, stage 3
  ⟨⟨⟨17, 8192, 54⟩, ⟨12, 256, 54⟩, 2, 2, 54⟩, 94948,
    ⟨11, 4626580140807011558, 4626580140807011559, 1114008400330⟩,
    ⟨292, 5066627642583988803, 5066627642583988804, 9029219735089379855⟩⟩,
  -- proof: folded row, stage 4
  ⟨⟨⟨13, 512, 54⟩, ⟨12, 256, 54⟩, 2, 2, 54⟩, 5937,
    ⟨21, 4844500160034822506, 4844500160034822507, 1385170967225⟩,
    ⟨454, 5066627642583988803, 5066627642583988804, 5111758468946177906⟩⟩,
  -- proof: Omega, stage 1
  ⟨⟨⟨22, 262144, 3571⟩, ⟨13, 64, 152⟩, 0, 4, 51⟩, 3131972,
    ⟨159, 4642981880397424060, 4642981880397424061, 18102572006498875288⟩,
    ⟨3, 2988436145658779760, 2988436145658779761, 345478608041⟩⟩,
  -- proof: Omega, stage 2
  ⟨⟨⟨18, 16384, 51⟩, ⟨14, 512, 51⟩, 3, 1, 51⟩, 196271,
    ⟨277, 4618717532312442606, 4618717532312442607, 18321395893515385871⟩,
    ⟨3, 3416472352878959345, 3416472352878959346, 14451928243⟩⟩,
  -- proof: Omega, stage 3
  ⟨⟨⟨14, 1024, 51⟩, ⟨13, 256, 51⟩, 3, 1, 51⟩, 12180,
    ⟨457, 4722934183774491208, 4722934183774491209, 13043905961530100492⟩,
    ⟨4, 3565212856155051233, 3565212856155051234, 2792146113⟩⟩,
  -- proof: own test, stage 1
  ⟨⟨⟨22, 262144, 3571⟩, ⟨13, 256, 55⟩, 1, 4, 55⟩, 3131972,
    ⟨159, 4642981880397424060, 4642981880397424061, 18102572006498875288⟩,
    ⟨4, 3588439244179337156, 3588439244179337157, 701000741579⟩⟩,
  -- proof: own test, stage 2
  ⟨⟨⟨18, 16384, 55⟩, ⟨15, 1024, 55⟩, 3, 1, 55⟩, 196263,
    ⟨277, 4619279591034610035, 4619279591034610036, 18314708845964909657⟩,
    ⟨3, 3345832038073801511, 3345832038073801512, 15386596187⟩⟩,
  -- proof: own test, stage 3
  ⟨⟨⟨15, 2048, 55⟩, ⟨14, 512, 55⟩, 3, 0, 55⟩, 24449,
    ⟨422, 4672089039528293851, 4672089039528293852, 18101646406679458073⟩,
    ⟨3, 3428609060205442808, 3428609060205442809, 1787376506⟩⟩,
  -- proof: own test, stage 4
  ⟨⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 3, 0, 46⟩, 6617,
    ⟨333, 3535965332883209267, 3535965332883209268, 3198991218400469305⟩,
    ⟨333, 3535965332883209267, 3535965332883209268, 3198991218400469305⟩⟩]

/-- The stages that are folded, at the small size. -/
def foldSmall : List FoldedPlace := [
  -- key: proof of the ranges, stage 1
  ⟨⟨⟨22, 262144, 49⟩, ⟨16, 1024, 49⟩, 3, 0, 49⟩, 3138994,
    ⟨158, 4612108211566870325, 4612108211566870326, 17896812194871251747⟩,
    ⟨3, 2359267308371252623, 2359267308371252624, 702085049868⟩⟩,
  -- key: proof of the ranges, stage 2
  ⟨⟨⟨19, 16384, 39⟩, ⟨17, 512, 39⟩, 3, 1, 39⟩, 431022,
    ⟨195, 3264733890588537296, 3264733890588537297, 18006457154025524701⟩,
    ⟨3, 1194940013597786254, 1194940013597786255, 675390131967⟩⟩,
  -- key: proof of the ranges, stage 3
  ⟨⟨⟨17, 2048, 33⟩, ⟨17, 256, 33⟩, 3, 0, 33⟩, 114481,
    ⟨208, 2323787583424143510, 2323787583424143511, 17223398529421648723⟩,
    ⟨3, 864691128455135232, 864691128455135232, 445598148878⟩⟩,
  -- key: folded row, stage 1
  ⟨⟨⟨17, 32768, 97⟩, ⟨13, 64, 146⟩, 0, 5, 97⟩, 65304,
    ⟨483, 9236872954601264168, 9236872954601264169, 18390151875512544398⟩,
    ⟨3, 2946441981012053085, 2946441981012053086, 11263660546⟩⟩,
  -- key: folded row, stage 2
  ⟨⟨⟨14, 2048, 66⟩, ⟨12, 256, 66⟩, 2, 2, 66⟩, 10490,
    ⟨579, 6624597576331438045, 6624597576331438046, 15412622631318445410⟩,
    ⟨4, 5164071713816034400, 5164071713816034401, 918868440⟩⟩,
  -- key: Omega, stage 1
  ⟨⟨⟨18, 16384, 98⟩, ⟨13, 64, 146⟩, 0, 2, 49⟩, 196176,
    ⟨276, 4625317408716738386, 4625317408716738387, 17916735607080378685⟩,
    ⟨3, 2946441981012053085, 2946441981012053086, 22528757822⟩⟩,
  -- key: Omega, stage 2
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 128, 49⟩, 3, 1, 49⟩, 12184,
    ⟨461, 4718534616742505246, 4718534616742505247, 13662335249885330219⟩,
    ⟨3, 2703840597523647898, 2703840597523647899, 1822024338⟩⟩,
  -- key: own test, stage 1
  ⟨⟨⟨18, 16384, 98⟩, ⟨13, 256, 49⟩, 0, 3, 49⟩, 196176,
    ⟨276, 4625317408716738386, 4625317408716738387, 17916735607080378685⟩,
    ⟨4, 3553542733661254395, 3553542733661254396, 45115927255⟩⟩,
  -- key: own test, stage 2
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 128, 49⟩, 3, 1, 49⟩, 12184,
    ⟨461, 4718534616742505246, 4718534616742505247, 13662335249885330219⟩,
    ⟨3, 2703840597523647898, 2703840597523647899, 1822024338⟩⟩,
  -- entry: the entry's test, stage 1
  ⟨⟨⟨17, 32768, 97⟩, ⟨13, 64, 97⟩, 0, 6, 97⟩, 65304,
    ⟨483, 9236872954601264168, 9236872954601264169, 18390151875512544398⟩,
    ⟨3, 2578010857022246786, 2578010857022246787, 16815356257⟩⟩,
  -- entry: the entry's test, stage 2
  ⟨⟨⟨14, 2048, 66⟩, ⟨12, 128, 66⟩, 2, 2, 66⟩, 10490,
    ⟨579, 6624597576331438045, 6624597576331438046, 15412622631318445410⟩,
    ⟨3, 4004224356745704092, 4004224356745704093, 561052910⟩⟩,
  -- proof: a link's group as it is closed
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 9, 218⟩, 76267,
    ⟨516, 13054610892900820049, 13054610892900820050, 18124568022926293377⟩,
    ⟨3, 4672366867200143431, 4672366867200143432, 5649607370⟩⟩,
  -- proof: a link's group as it is closed
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 7, 218⟩, 76267,
    ⟨516, 13054610892900820049, 13054610892900820050, 18124568022926293377⟩,
    ⟨3, 4672366867200143431, 4672366867200143432, 5649607370⟩⟩,
  -- proof: a link's group as it is closed
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 8, 218⟩, 76267,
    ⟨516, 13054610892900820049, 13054610892900820050, 18124568022926293377⟩,
    ⟨3, 4672366867200143431, 4672366867200143432, 5649607370⟩⟩,
  -- proof: last test behind the links, stage 1
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 1, 218⟩, 76267,
    ⟨516, 13054610892900820049, 13054610892900820050, 18124568022926293377⟩,
    ⟨3, 4672366867200143431, 4672366867200143432, 5649607370⟩⟩,
  -- proof: last test behind the links, stage 2
  ⟨⟨⟨17, 8192, 55⟩, ⟨17, 4096, 55⟩, 3, 1, 55⟩, 98093,
    ⟨319, 4626860701138418140, 4626860701138418141, 18436262090488804802⟩,
    ⟨3, 3282379621777433489, 3282379621777433490, 8148065054⟩⟩,
  -- proof: last test behind the links, stage 3
  ⟨⟨⟨16, 1024, 44⟩, ⟨16, 2048, 44⟩, 3, 0, 44⟩, 53784,
    ⟨3, 2353758855120180122, 2353758855120180123, 11047402104⟩,
    ⟨256, 3295010277858981818, 3295010277858981819, 8511661924695688634⟩⟩,
  -- proof: last test behind the links, stage 4
  ⟨⟨⟨15, 128, 44⟩, ⟨15, 1024, 44⟩, 3, 0, 44⟩, 26835,
    ⟨3, 1332578525122970398, 1332578525122970399, 30436743702⟩,
    ⟨296, 3328717695466727643, 3328717695466727644, 8519428015344779920⟩⟩,
  -- proof: folded row, stage 1
  ⟨⟨⟨17, 32768, 101⟩, ⟨13, 64, 156⟩, 0, 5, 101⟩, 65300,
    ⟨483, 9237435064624885212, 9237435064624885213, 18386794885306492685⟩,
    ⟨3, 3016107441082465484, 3016107441082465485, 10501115783⟩⟩,
  -- proof: folded row, stage 2
  ⟨⟨⟨14, 2048, 68⟩, ⟨12, 256, 68⟩, 2, 2, 68⟩, 10487,
    ⟨567, 6627731996935651722, 6627731996935651723, 13861887214509903538⟩,
    ⟨4, 5180134184063960054, 5180134184063960055, 910348276⟩⟩,
  -- proof: Omega, stage 1
  ⟨⟨⟨18, 16384, 3831⟩, ⟨13, 64, 156⟩, 0, 2, 55⟩, 189103,
    ⟨295, 5122428347435008428, 5122428347435008429, 18389400861171535141⟩,
    ⟨3, 3016107441082465484, 3016107441082465485, 21003483874⟩⟩,
  -- proof: Omega, stage 2
  ⟨⟨⟨14, 1024, 69⟩, ⟨13, 1024, 69⟩, 3, 1, 69⟩, 10390,
    ⟨3, 4762347391579086293, 4762347391579086294, 333540303⟩,
    ⟨493, 6734976269903276664, 6734976269903276665, 6569244455164824711⟩⟩,
  -- proof: own test, stage 1
  ⟨⟨⟨18, 16384, 3831⟩, ⟨13, 256, 59⟩, 0, 3, 59⟩, 189103,
    ⟨295, 5122428347435008428, 5122428347435008429, 18389400861171535141⟩,
    ⟨3, 3611516261716051999, 3611516261716052000, 12234869609⟩⟩,
  -- proof: own test, stage 2
  ⟨⟨⟨14, 1024, 75⟩, ⟨13, 1024, 75⟩, 3, 1, 75⟩, 10374,
    ⟨3, 4775412841073006427, 4775412841073006428, 330810655⟩,
    ⟨512, 6753453605776079208, 6753453605776079209, 7870085203350272321⟩⟩]

theorem fold_good : ((foldFull ++ foldSmall).all fun x => x.good) = true := by decide +kernel

theorem fold_priced : ((foldFull ++ foldSmall).all fun x => x.priced) = true := by decide +kernel

/-- The key file's fourteen at full size are the list `keyFolded`. -/
theorem foldFull_key : (foldFull.take 14).map (fun x => (x.s, x.e)) = Johnson.Top.H.keyFolded := rfl

/-- The entry file's four at full size are the stages `frSg1` to `frSg4`. -/
theorem foldFull_entry :
    ((foldFull.drop 14).take 4).map (fun x => x.s) = [frSg1, frSg2, frSg3, frSg4] := rfl

/-- **What a fold asks of its codes, the fold taken off, and its rounds' counts against 2^-128, at
the written stages.** -/
def FoldedPlacesPaid : Prop := ∀ x ∈ foldFull ++ foldSmall, x.Paid

theorem foldedPlacesPaid : FoldedPlacesPaid := fun x hx =>
  FoldedPlace.paid (List.all_eq_true.1 fold_good x hx) (List.all_eq_true.1 fold_priced x hx)

end Johnson.Bridge

#print axioms Johnson.Bridge.fold_good
#print axioms Johnson.Bridge.fold_priced
#print axioms Johnson.Bridge.foldedPlacesPaid
