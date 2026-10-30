-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DryProofTestsFull.lean: the tests on public data that stand as premises where the proof
file's protocol is tied to the verifier on bytes, at the written dry lists of
Johnson/G/DryProofLit.lean, at the full-size example: each as a theorem by an evaluation in Lean's
kernel.

The tests: `OnBytes.Maker.okAt` and its eight parts (OnBytes/Maker/Files.lean), `shapesFit`,
`sealBare` (OnBytes/Maker/ViewTests.lean), `saltsFit` (OnBytes/Maker/TablesRow.lean). Each is a
function of the three dry lists, the stored table's depth and the number of bytes of a salt. The
first chain has 48,293 rounds. So that the kernel gets through within Lean's default stack and in
moderate time and memory, five values that the tests ask for again and again stand written out: all
openings, the table of trees, and each chain's trees. Each is shown once, by an evaluation, to be
the computed one; the proofs then rewrite `OnBytes.Three.Whole.of` to a twin over the written
openings (Johnson/G/WholeAt.lean, `whole_eqW`), and three of them unfold the test and rewrite to the
written values (Johnson/G/TestsFlat.lean, TestsEager.lean). Definitions and proofs.
Main names:
  `dryProofFullAll`, `dryProofFullTable`, `dryProofFullTrees1`, `…2`, `…3`: the written values;
    `whole_proofFull`, `table_proofFull`, `trees1_proofFull`, `…2`, `…3`, `t1_proofFull`,
    `t2_proofFull`: that they are the computed ones.
  `fits_proofFull`, `storedFit_proofFull`, `countsFit_proofFull`, `workFit_proofFull`,
    `depthFit_proofFull`, `runFit_proofFull`, `someFit_proofFull`, `rowFit_proofFull`: the eight;
    `okAt_proofFull`: together.
  `shapesFit_proofFull`, `sealBare_proofFull`, `saltsFit_proofFull`: the others.
    `controls_proofFull`: at the depth 31, and at salts of 41 bytes, two of the tests say no;
    `controlRoots_proofFull`: with one root a message allowed, the first test says no.
Whence the five written values: a program computed them from the same print as the lists of
Johnson/G/DryProofLit.lean; the kernel holds each against these lists.
Limits: the theorems speak of the written lists. That these are what `OnBytes.Maker.dryProof`
returns at the planner's answer at the shipped public files, the key of zeros and a made-up request
is held by no test of this library at the full size. The tests say that the lists fit the makers'
map, not that they are the file's: with the entries' draws and sizes changed they would still say
yes. Most of the tests have no control here. Nothing on soundness.

-/
import Johnson.G.DryProofLit
import Johnson.G.WholeAt
import Johnson.G.TestsEager
import Johnson.G.TestsFlat
import OnBytes.Maker.Files
import OnBytes.Maker.ViewTests
import OnBytes.Maker.TablesRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Maker

namespace TreeEq

deriving instance DecidableEq for OnBytes.Three.Tree

end TreeEq

/-! ## Written values, each shown once to be the computed one -/

/-- All openings of the three chains: the tree's number, its shape, the chain, the round. -/
def dryProofFullAll : List (Nat × Fmt.Shape × Nat × Nat) := [
  (0, ⟨23, 124, false, 0⟩, 0, 1981), (2, ⟨23, 3, false, 2⟩, 0, 1981),
  (3, ⟨23, 31, false, 3⟩, 0, 1981), (4, ⟨23, 66, false, 4⟩, 0, 3860),
  (5, ⟨23, 3, false, 5⟩, 0, 3860), (6, ⟨23, 14, false, 6⟩, 0, 3860),
  (7, ⟨23, 131, false, 7⟩, 0, 5838), (8, ⟨23, 3, false, 8⟩, 0, 5838),
  (9, ⟨23, 31, false, 9⟩, 0, 5838), (10, ⟨23, 66, false, 10⟩, 0, 7717),
  (11, ⟨23, 3, false, 11⟩, 0, 7717), (12, ⟨23, 14, false, 12⟩, 0, 7717),
  (13, ⟨23, 131, false, 13⟩, 0, 9695), (14, ⟨23, 3, false, 14⟩, 0, 9695),
  (15, ⟨23, 31, false, 15⟩, 0, 9695), (16, ⟨23, 66, false, 16⟩, 0, 11574),
  (17, ⟨23, 3, false, 17⟩, 0, 11574), (18, ⟨23, 14, false, 18⟩, 0, 11574),
  (19, ⟨23, 131, false, 19⟩, 0, 13552), (20, ⟨23, 3, false, 20⟩, 0, 13552),
  (21, ⟨23, 31, false, 21⟩, 0, 13552), (22, ⟨23, 66, false, 22⟩, 0, 15431),
  (23, ⟨23, 3, false, 23⟩, 0, 15431), (24, ⟨23, 14, false, 24⟩, 0, 15431),
  (25, ⟨23, 131, false, 25⟩, 0, 17409), (26, ⟨23, 3, false, 26⟩, 0, 17409),
  (27, ⟨23, 31, false, 27⟩, 0, 17409), (28, ⟨23, 66, false, 28⟩, 0, 19288),
  (29, ⟨23, 3, false, 29⟩, 0, 19288), (30, ⟨23, 14, false, 30⟩, 0, 19288),
  (31, ⟨23, 131, false, 31⟩, 0, 21266), (32, ⟨23, 3, false, 32⟩, 0, 21266),
  (33, ⟨23, 31, false, 33⟩, 0, 21266), (34, ⟨23, 66, false, 34⟩, 0, 23145),
  (35, ⟨23, 3, false, 35⟩, 0, 23145), (36, ⟨23, 14, false, 36⟩, 0, 23145),
  (37, ⟨23, 131, false, 37⟩, 0, 25123), (38, ⟨23, 3, false, 38⟩, 0, 25123),
  (39, ⟨23, 31, false, 39⟩, 0, 25123), (40, ⟨23, 66, false, 40⟩, 0, 27002),
  (41, ⟨23, 3, false, 41⟩, 0, 27002), (42, ⟨23, 14, false, 42⟩, 0, 27002),
  (43, ⟨23, 131, false, 43⟩, 0, 28980), (44, ⟨23, 3, false, 44⟩, 0, 28980),
  (45, ⟨23, 31, false, 45⟩, 0, 28980), (46, ⟨23, 66, false, 46⟩, 0, 30859),
  (47, ⟨23, 3, false, 47⟩, 0, 30859), (48, ⟨23, 14, false, 48⟩, 0, 30859),
  (49, ⟨23, 131, false, 49⟩, 0, 32837), (50, ⟨23, 3, false, 50⟩, 0, 32837),
  (51, ⟨23, 31, false, 51⟩, 0, 32837), (52, ⟨23, 66, false, 52⟩, 0, 34716),
  (53, ⟨23, 3, false, 53⟩, 0, 34716), (54, ⟨23, 14, false, 54⟩, 0, 34716),
  (55, ⟨23, 131, false, 55⟩, 0, 36694), (56, ⟨23, 3, false, 56⟩, 0, 36694),
  (57, ⟨23, 31, false, 57⟩, 0, 36694), (58, ⟨23, 66, false, 58⟩, 0, 38573),
  (59, ⟨23, 3, false, 59⟩, 0, 38573), (60, ⟨23, 14, false, 60⟩, 0, 38573),
  (61, ⟨23, 131, false, 61⟩, 0, 40551), (62, ⟨23, 3, false, 62⟩, 0, 40551),
  (63, ⟨23, 31, false, 63⟩, 0, 40551), (64, ⟨23, 66, false, 64⟩, 0, 42430),
  (65, ⟨23, 3, false, 65⟩, 0, 42430), (66, ⟨23, 14, false, 66⟩, 0, 42430),
  (67, ⟨23, 131, false, 67⟩, 0, 44408), (68, ⟨23, 3, false, 68⟩, 0, 44408),
  (69, ⟨23, 31, false, 69⟩, 0, 44408), (70, ⟨23, 66, false, 70⟩, 0, 46288),
  (71, ⟨23, 3, false, 71⟩, 0, 46288), (72, ⟨23, 14, false, 72⟩, 0, 46288),
  (73, ⟨23, 118, false, 73⟩, 0, 48236), (74, ⟨23, 3, false, 74⟩, 0, 48236),
  (75, ⟨23, 24, false, 75⟩, 0, 48236), (76, ⟨23, 9, false, 76⟩, 0, 48241),
  (77, ⟨22, 96, false, 77⟩, 0, 48248), (78, ⟨19, 72, false, 78⟩, 0, 48254),
  (79, ⟨16, 72, false, 79⟩, 0, 48260), (80, ⟨13, 144, false, 80⟩, 0, 48267),
  (81, ⟨15, 12, false, 81⟩, 0, 48269), (83, ⟨24, 324, false, 0⟩, 1, 18),
  (85, ⟨13, 3, false, 2⟩, 1, 18), (86, ⟨21, 120, false, 3⟩, 1, 26),
  (87, ⟨17, 72, false, 4⟩, 1, 33), (88, ⟨13, 72, false, 5⟩, 1, 40),
  (89, ⟨14, 12, false, 6⟩, 1, 42), (84, ⟨22, 36, false, 1⟩, 1, 50),
  (85, ⟨13, 3, false, 2⟩, 1, 50), (90, ⟨13, 3, false, 7⟩, 1, 50), (91, ⟨18, 96, false, 8⟩, 1, 57),
  (92, ⟨14, 96, false, 9⟩, 1, 64), (93, ⟨15, 12, false, 10⟩, 1, 66), (1, ⟨13, 3, false, 1⟩, 2, 8),
  (82, ⟨22, 12, false, 82⟩, 2, 8), (84, ⟨22, 36, false, 1⟩, 2, 8),
  (94, ⟨18, 96, false, 84⟩, 2, 15), (95, ⟨15, 72, false, 85⟩, 2, 21),
  (96, ⟨13, 72, false, 86⟩, 2, 27), (97, ⟨15, 12, false, 87⟩, 2, 29)]

/-- The table of the file's 98 trees. -/
def dryProofFullTable : List Three.Tree := [
  ⟨0, 0, 0, ⟨23, 124, false, 0⟩, [(0, 1981)]⟩, ⟨0, 0, 1, ⟨13, 3, false, 1⟩, [(2, 8)]⟩,
  ⟨0, 1218, 0, ⟨23, 3, false, 2⟩, [(0, 1981)]⟩, ⟨0, 1221, 0, ⟨23, 31, false, 3⟩, [(0, 1981)]⟩,
  ⟨0, 1980, 0, ⟨23, 66, false, 4⟩, [(0, 3860)]⟩, ⟨0, 3128, 0, ⟨23, 3, false, 5⟩, [(0, 3860)]⟩,
  ⟨0, 3131, 0, ⟨23, 14, false, 6⟩, [(0, 3860)]⟩, ⟨0, 3859, 0, ⟨23, 131, false, 7⟩, [(0, 5838)]⟩,
  ⟨0, 5075, 0, ⟨23, 3, false, 8⟩, [(0, 5838)]⟩, ⟨0, 5078, 0, ⟨23, 31, false, 9⟩, [(0, 5838)]⟩,
  ⟨0, 5837, 0, ⟨23, 66, false, 10⟩, [(0, 7717)]⟩, ⟨0, 6985, 0, ⟨23, 3, false, 11⟩, [(0, 7717)]⟩,
  ⟨0, 6988, 0, ⟨23, 14, false, 12⟩, [(0, 7717)]⟩, ⟨0, 7716, 0, ⟨23, 131, false, 13⟩, [(0, 9695)]⟩,
  ⟨0, 8932, 0, ⟨23, 3, false, 14⟩, [(0, 9695)]⟩, ⟨0, 8935, 0, ⟨23, 31, false, 15⟩, [(0, 9695)]⟩,
  ⟨0, 9694, 0, ⟨23, 66, false, 16⟩, [(0, 11574)]⟩,
  ⟨0, 10842, 0, ⟨23, 3, false, 17⟩, [(0, 11574)]⟩,
  ⟨0, 10845, 0, ⟨23, 14, false, 18⟩, [(0, 11574)]⟩,
  ⟨0, 11573, 0, ⟨23, 131, false, 19⟩, [(0, 13552)]⟩,
  ⟨0, 12789, 0, ⟨23, 3, false, 20⟩, [(0, 13552)]⟩,
  ⟨0, 12792, 0, ⟨23, 31, false, 21⟩, [(0, 13552)]⟩,
  ⟨0, 13551, 0, ⟨23, 66, false, 22⟩, [(0, 15431)]⟩,
  ⟨0, 14699, 0, ⟨23, 3, false, 23⟩, [(0, 15431)]⟩,
  ⟨0, 14702, 0, ⟨23, 14, false, 24⟩, [(0, 15431)]⟩,
  ⟨0, 15430, 0, ⟨23, 131, false, 25⟩, [(0, 17409)]⟩,
  ⟨0, 16646, 0, ⟨23, 3, false, 26⟩, [(0, 17409)]⟩,
  ⟨0, 16649, 0, ⟨23, 31, false, 27⟩, [(0, 17409)]⟩,
  ⟨0, 17408, 0, ⟨23, 66, false, 28⟩, [(0, 19288)]⟩,
  ⟨0, 18556, 0, ⟨23, 3, false, 29⟩, [(0, 19288)]⟩,
  ⟨0, 18559, 0, ⟨23, 14, false, 30⟩, [(0, 19288)]⟩,
  ⟨0, 19287, 0, ⟨23, 131, false, 31⟩, [(0, 21266)]⟩,
  ⟨0, 20503, 0, ⟨23, 3, false, 32⟩, [(0, 21266)]⟩,
  ⟨0, 20506, 0, ⟨23, 31, false, 33⟩, [(0, 21266)]⟩,
  ⟨0, 21265, 0, ⟨23, 66, false, 34⟩, [(0, 23145)]⟩,
  ⟨0, 22413, 0, ⟨23, 3, false, 35⟩, [(0, 23145)]⟩,
  ⟨0, 22416, 0, ⟨23, 14, false, 36⟩, [(0, 23145)]⟩,
  ⟨0, 23144, 0, ⟨23, 131, false, 37⟩, [(0, 25123)]⟩,
  ⟨0, 24360, 0, ⟨23, 3, false, 38⟩, [(0, 25123)]⟩,
  ⟨0, 24363, 0, ⟨23, 31, false, 39⟩, [(0, 25123)]⟩,
  ⟨0, 25122, 0, ⟨23, 66, false, 40⟩, [(0, 27002)]⟩,
  ⟨0, 26270, 0, ⟨23, 3, false, 41⟩, [(0, 27002)]⟩,
  ⟨0, 26273, 0, ⟨23, 14, false, 42⟩, [(0, 27002)]⟩,
  ⟨0, 27001, 0, ⟨23, 131, false, 43⟩, [(0, 28980)]⟩,
  ⟨0, 28217, 0, ⟨23, 3, false, 44⟩, [(0, 28980)]⟩,
  ⟨0, 28220, 0, ⟨23, 31, false, 45⟩, [(0, 28980)]⟩,
  ⟨0, 28979, 0, ⟨23, 66, false, 46⟩, [(0, 30859)]⟩,
  ⟨0, 30127, 0, ⟨23, 3, false, 47⟩, [(0, 30859)]⟩,
  ⟨0, 30130, 0, ⟨23, 14, false, 48⟩, [(0, 30859)]⟩,
  ⟨0, 30858, 0, ⟨23, 131, false, 49⟩, [(0, 32837)]⟩,
  ⟨0, 32074, 0, ⟨23, 3, false, 50⟩, [(0, 32837)]⟩,
  ⟨0, 32077, 0, ⟨23, 31, false, 51⟩, [(0, 32837)]⟩,
  ⟨0, 32836, 0, ⟨23, 66, false, 52⟩, [(0, 34716)]⟩,
  ⟨0, 33984, 0, ⟨23, 3, false, 53⟩, [(0, 34716)]⟩,
  ⟨0, 33987, 0, ⟨23, 14, false, 54⟩, [(0, 34716)]⟩,
  ⟨0, 34715, 0, ⟨23, 131, false, 55⟩, [(0, 36694)]⟩,
  ⟨0, 35931, 0, ⟨23, 3, false, 56⟩, [(0, 36694)]⟩,
  ⟨0, 35934, 0, ⟨23, 31, false, 57⟩, [(0, 36694)]⟩,
  ⟨0, 36693, 0, ⟨23, 66, false, 58⟩, [(0, 38573)]⟩,
  ⟨0, 37841, 0, ⟨23, 3, false, 59⟩, [(0, 38573)]⟩,
  ⟨0, 37844, 0, ⟨23, 14, false, 60⟩, [(0, 38573)]⟩,
  ⟨0, 38572, 0, ⟨23, 131, false, 61⟩, [(0, 40551)]⟩,
  ⟨0, 39788, 0, ⟨23, 3, false, 62⟩, [(0, 40551)]⟩,
  ⟨0, 39791, 0, ⟨23, 31, false, 63⟩, [(0, 40551)]⟩,
  ⟨0, 40550, 0, ⟨23, 66, false, 64⟩, [(0, 42430)]⟩,
  ⟨0, 41698, 0, ⟨23, 3, false, 65⟩, [(0, 42430)]⟩,
  ⟨0, 41701, 0, ⟨23, 14, false, 66⟩, [(0, 42430)]⟩,
  ⟨0, 42429, 0, ⟨23, 131, false, 67⟩, [(0, 44408)]⟩,
  ⟨0, 43645, 0, ⟨23, 3, false, 68⟩, [(0, 44408)]⟩,
  ⟨0, 43648, 0, ⟨23, 31, false, 69⟩, [(0, 44408)]⟩,
  ⟨0, 44407, 0, ⟨23, 66, false, 70⟩, [(0, 46288)]⟩,
  ⟨0, 45555, 0, ⟨23, 3, false, 71⟩, [(0, 46288)]⟩,
  ⟨0, 45558, 0, ⟨23, 14, false, 72⟩, [(0, 46288)]⟩,
  ⟨0, 46287, 0, ⟨23, 118, false, 73⟩, [(0, 48236)]⟩,
  ⟨0, 47451, 0, ⟨23, 3, false, 74⟩, [(0, 48236)]⟩,
  ⟨0, 47454, 0, ⟨23, 24, false, 75⟩, [(0, 48236)]⟩,
  ⟨0, 48235, 0, ⟨23, 9, false, 76⟩, [(0, 48241)]⟩,
  ⟨0, 48240, 0, ⟨22, 96, false, 77⟩, [(0, 48248)]⟩,
  ⟨0, 48247, 0, ⟨19, 72, false, 78⟩, [(0, 48254)]⟩,
  ⟨0, 48253, 0, ⟨16, 72, false, 79⟩, [(0, 48260)]⟩,
  ⟨0, 48259, 0, ⟨13, 144, false, 80⟩, [(0, 48267)]⟩,
  ⟨0, 48266, 0, ⟨15, 12, false, 81⟩, [(0, 48269)]⟩, ⟨0, 48290, 0, ⟨22, 12, false, 82⟩, [(2, 8)]⟩,
  ⟨1, 1, 0, ⟨24, 324, false, 0⟩, [(1, 18)]⟩, ⟨1, 4, 0, ⟨22, 36, false, 1⟩, [(1, 50), (2, 8)]⟩,
  ⟨1, 4, 1, ⟨13, 3, false, 2⟩, [(1, 18), (1, 50)]⟩, ⟨1, 17, 0, ⟨21, 120, false, 3⟩, [(1, 26)]⟩,
  ⟨1, 25, 0, ⟨17, 72, false, 4⟩, [(1, 33)]⟩, ⟨1, 32, 0, ⟨13, 72, false, 5⟩, [(1, 40)]⟩,
  ⟨1, 39, 0, ⟨14, 12, false, 6⟩, [(1, 42)]⟩, ⟨1, 44, 0, ⟨13, 3, false, 7⟩, [(1, 50)]⟩,
  ⟨1, 49, 0, ⟨18, 96, false, 8⟩, [(1, 57)]⟩, ⟨1, 56, 0, ⟨14, 96, false, 9⟩, [(1, 64)]⟩,
  ⟨1, 63, 0, ⟨15, 12, false, 10⟩, [(1, 66)]⟩, ⟨2, 7, 0, ⟨18, 96, false, 84⟩, [(2, 15)]⟩,
  ⟨2, 14, 0, ⟨15, 72, false, 85⟩, [(2, 21)]⟩, ⟨2, 20, 0, ⟨13, 72, false, 86⟩, [(2, 27)]⟩,
  ⟨2, 26, 0, ⟨15, 12, false, 87⟩, [(2, 29)]⟩]

/-- The shapes of the trees that the first chain sends. -/
def dryProofFullTrees1 : List Fmt.Shape := [
  ⟨23, 124, false, 0⟩, ⟨13, 3, false, 1⟩, ⟨23, 3, false, 2⟩, ⟨23, 31, false, 3⟩,
  ⟨23, 66, false, 4⟩, ⟨23, 3, false, 5⟩, ⟨23, 14, false, 6⟩, ⟨23, 131, false, 7⟩,
  ⟨23, 3, false, 8⟩, ⟨23, 31, false, 9⟩, ⟨23, 66, false, 10⟩, ⟨23, 3, false, 11⟩,
  ⟨23, 14, false, 12⟩, ⟨23, 131, false, 13⟩, ⟨23, 3, false, 14⟩, ⟨23, 31, false, 15⟩,
  ⟨23, 66, false, 16⟩, ⟨23, 3, false, 17⟩, ⟨23, 14, false, 18⟩, ⟨23, 131, false, 19⟩,
  ⟨23, 3, false, 20⟩, ⟨23, 31, false, 21⟩, ⟨23, 66, false, 22⟩, ⟨23, 3, false, 23⟩,
  ⟨23, 14, false, 24⟩, ⟨23, 131, false, 25⟩, ⟨23, 3, false, 26⟩, ⟨23, 31, false, 27⟩,
  ⟨23, 66, false, 28⟩, ⟨23, 3, false, 29⟩, ⟨23, 14, false, 30⟩, ⟨23, 131, false, 31⟩,
  ⟨23, 3, false, 32⟩, ⟨23, 31, false, 33⟩, ⟨23, 66, false, 34⟩, ⟨23, 3, false, 35⟩,
  ⟨23, 14, false, 36⟩, ⟨23, 131, false, 37⟩, ⟨23, 3, false, 38⟩, ⟨23, 31, false, 39⟩,
  ⟨23, 66, false, 40⟩, ⟨23, 3, false, 41⟩, ⟨23, 14, false, 42⟩, ⟨23, 131, false, 43⟩,
  ⟨23, 3, false, 44⟩, ⟨23, 31, false, 45⟩, ⟨23, 66, false, 46⟩, ⟨23, 3, false, 47⟩,
  ⟨23, 14, false, 48⟩, ⟨23, 131, false, 49⟩, ⟨23, 3, false, 50⟩, ⟨23, 31, false, 51⟩,
  ⟨23, 66, false, 52⟩, ⟨23, 3, false, 53⟩, ⟨23, 14, false, 54⟩, ⟨23, 131, false, 55⟩,
  ⟨23, 3, false, 56⟩, ⟨23, 31, false, 57⟩, ⟨23, 66, false, 58⟩, ⟨23, 3, false, 59⟩,
  ⟨23, 14, false, 60⟩, ⟨23, 131, false, 61⟩, ⟨23, 3, false, 62⟩, ⟨23, 31, false, 63⟩,
  ⟨23, 66, false, 64⟩, ⟨23, 3, false, 65⟩, ⟨23, 14, false, 66⟩, ⟨23, 131, false, 67⟩,
  ⟨23, 3, false, 68⟩, ⟨23, 31, false, 69⟩, ⟨23, 66, false, 70⟩, ⟨23, 3, false, 71⟩,
  ⟨23, 14, false, 72⟩, ⟨23, 118, false, 73⟩, ⟨23, 3, false, 74⟩, ⟨23, 24, false, 75⟩,
  ⟨23, 9, false, 76⟩, ⟨22, 96, false, 77⟩, ⟨19, 72, false, 78⟩, ⟨16, 72, false, 79⟩,
  ⟨13, 144, false, 80⟩, ⟨15, 12, false, 81⟩, ⟨22, 12, false, 82⟩]

/-- The same for the second chain. -/
def dryProofFullTrees2 : List Fmt.Shape := [
  ⟨24, 324, false, 0⟩, ⟨22, 36, false, 1⟩, ⟨13, 3, false, 2⟩, ⟨21, 120, false, 3⟩,
  ⟨17, 72, false, 4⟩, ⟨13, 72, false, 5⟩, ⟨14, 12, false, 6⟩, ⟨13, 3, false, 7⟩,
  ⟨18, 96, false, 8⟩, ⟨14, 96, false, 9⟩, ⟨15, 12, false, 10⟩]

/-- The same for the third chain. -/
def dryProofFullTrees3 : List Fmt.Shape := [
  ⟨18, 96, false, 84⟩, ⟨15, 72, false, 85⟩, ⟨13, 72, false, 86⟩, ⟨15, 12, false, 87⟩]

/-- The plain data of the three lists, over the written list of openings. -/
abbrev wProofFull : Three.Whole :=
  wholeW 83 11 dryProofFullAll dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2

set_option maxRecDepth 1000000 in
theorem whole_proofFull :
    Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2 = wProofFull :=
  whole_eqW (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem table_proofFull : wProofFull.table = dryProofFullTable := by decide +kernel

set_option maxRecDepth 1000000 in
theorem trees1_proofFull :
    (WholeD.of 32 wProofFull).ds₁.flatMap (·.trees) = dryProofFullTrees1 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem trees2_proofFull :
    (WholeD.of 32 wProofFull).ds₂.flatMap (·.trees) = dryProofFullTrees2 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem trees3_proofFull :
    (WholeD.of 32 wProofFull).ds₃.flatMap (·.trees) = dryProofFullTrees3 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The number of trees that the first chain's data send, as a numeral. -/
theorem t1_proofFull : (WholeD.of 32 wProofFull).t₁ = 83 := by
  unfold WholeD.t₁
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The same for the second chain. -/
theorem t2_proofFull : (WholeD.of 32 wProofFull).t₂ = 11 := by
  unfold WholeD.t₂
  rw [sum_eq_sumE]
  decide +kernel

/-! ## The tests: the stored table's depth 32; salts of 40 bytes -/

set_option maxRecDepth 1000000 in
/-- The first of the makers' eight tests. -/
theorem fits_proofFull :
    Three.Whole.fits dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2 2 = true := by
  unfold Three.Whole.fits
  rw [whole_proofFull]
  simp only [table_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem storedFit_proofFull : storedFit 32 (wholeAt (some dryProofFull)) = true := by
  show storedFit 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = true
  rw [whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem countsFit_proofFull : countsFit 32 (wholeAt (some dryProofFull)) = true := by
  show countsFit 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = true
  rw [whole_proofFull]
  unfold countsFit
  rw [t1_proofFull, t2_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem workFit_proofFull : (WholeD.of 32 (wholeAt (some dryProofFull))).workFit = true := by
  show (WholeD.of 32
    (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).workFit = true
  rw [whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem depthFit_proofFull : (WholeD.of 32 (wholeAt (some dryProofFull))).depthFit = true := by
  show (WholeD.of 32
    (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).depthFit = true
  rw [whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem runFit_proofFull : (WholeD.of 32 (wholeAt (some dryProofFull))).runFit = true := by
  show (WholeD.of 32
    (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).runFit = true
  rw [whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem someFit_proofFull : someFit dryProofFull = true := by
  unfold someFit
  have h : dryProofFull.1.length = 48293 := congrArg Prod.fst dryProofFull_length
  rw [h]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rowFit_proofFull : rowFitAt 32 (wholeAt (some dryProofFull)) = true := by
  show rowFitAt 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = true
  rw [whole_proofFull]
  unfold rowFitAt rowFitB WholeD.depth leftAfter
  simp only [t1_proofFull, t2_proofFull, treeSh_flat, trees1_proofFull, trees2_proofFull,
    trees3_proofFull, table_proofFull]
  decide +kernel

/-- The makers' eight tests together. -/
theorem okAt_proofFull : okAt 32 (some dryProofFull) = true := by
  simp only [okAt, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨fits_proofFull, storedFit_proofFull⟩, countsFit_proofFull⟩, workFit_proofFull⟩,
    depthFit_proofFull⟩, runFit_proofFull⟩, someFit_proofFull⟩, rowFit_proofFull⟩

set_option maxRecDepth 1000000 in
theorem shapesFit_proofFull : shapesFit 32 (wholeAt (some dryProofFull)) = true := by
  show shapesFit 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = true
  rw [whole_proofFull]
  unfold shapesFit WholeD.shape
  simp only [t1_proofFull, t2_proofFull, treeSh_flat, trees1_proofFull, trees2_proofFull,
    trees3_proofFull, table_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sealBare_proofFull : sealBare (wholeAt (some dryProofFull)) = true := by
  show sealBare (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = true
  rw [whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem saltsFit_proofFull : saltsFit 40 (wholeAt (some dryProofFull)) = true := by
  show saltsFit 40 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = true
  rw [whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one root a message allowed, the first test says no. -/
theorem controlRoots_proofFull :
    Three.Whole.fits dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2 1 = false := by
  unfold Three.Whole.fits
  rw [whole_proofFull]
  simp only [table_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: at another depth, and at salts of another number of bytes, the tests say no. -/
theorem controls_proofFull :
    (storedFit 31 (wholeAt (some dryProofFull)), saltsFit 41 (wholeAt (some dryProofFull))) =
      (false, false) := by
  show (storedFit 31 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2),
    saltsFit 41 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)) =
    (false, false)
  rw [whole_proofFull]
  decide +kernel

end Johnson.G

#print axioms Johnson.G.whole_proofFull
#print axioms Johnson.G.table_proofFull
#print axioms Johnson.G.trees1_proofFull
#print axioms Johnson.G.trees2_proofFull
#print axioms Johnson.G.trees3_proofFull
#print axioms Johnson.G.t1_proofFull
#print axioms Johnson.G.t2_proofFull
#print axioms Johnson.G.fits_proofFull
#print axioms Johnson.G.storedFit_proofFull
#print axioms Johnson.G.countsFit_proofFull
#print axioms Johnson.G.workFit_proofFull
#print axioms Johnson.G.depthFit_proofFull
#print axioms Johnson.G.runFit_proofFull
#print axioms Johnson.G.someFit_proofFull
#print axioms Johnson.G.rowFit_proofFull
#print axioms Johnson.G.okAt_proofFull
#print axioms Johnson.G.shapesFit_proofFull
#print axioms Johnson.G.sealBare_proofFull
#print axioms Johnson.G.saltsFit_proofFull
#print axioms Johnson.G.controlRoots_proofFull
#print axioms Johnson.G.controls_proofFull
