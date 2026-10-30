-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/RowTakers/Defs.lean: WHO IS GIVEN A COIN OF THE MASK ROW THAT THE CODE SWITCH AT THE
LINK 2 g SENDS, g = 1 … 11: THE TEST, THE WALK AND THE TWO WRITTEN LISTS. Eight definitions; four
small statements. Closed facts on ownedIn, not takersIn: AllWants.lean, AllSeg.lean; what follows:
AtFullSide/K1/OwnerEntriesAtSwitches.lean, whose head tells the whole and its limits. A TRIAL THAT
COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

  ownerAt g the address ⟨⟨1, some (2 * g), 1, .K2⟩, 0⟩
  meetsRow e a Bool: the entry names a coin of the extension field among the numbers 439 … 8630
  takersIn l g the walk: the entries of l whose owner is ownerAt g and that pass meetsRow, IN l's
OWN ORDER, each as (spender, start, count, once)
  spentW        WRITTEN OUT: 319 rows (piece, kind, part, first coin, count): the entries that are
                marked as spent
  carriersW     WRITTEN OUT: 48 addresses: who is given the whole message as carried, at g = 1
  rowSpentAt g, rowCarriedAt g, takersW g the lists at the group g: spentW at the link 2 * g;
    carriersW
less its first 4 * (g - 1); the first in front of the second

WHERE THE TWO LISTS COME FROM. THEY WERE PRINTED OFF THE WRITTEN BOOK's ENTRIES BY LEAN's EVALUATOR
AND LAID HERE BY PROGRAM. SO THE CLOSED FACTS THAT HOLD THEM AGAINST THAT BOOK MAKE A LISTING, NOT A
SECOND SOURCE: the twins that say no show that the tests can fail, not that the book is right.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K14.RawAheadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The owner: part 0 of the code switch at the link 2 * g of the first chain. -/
def ownerAt (g : Nat) : Addr := ⟨⟨1, some (2 * g), 1, .K2⟩, 0⟩

/-- The entry names a coin of the extension field among the owner's numbers 439 … 8630. -/
def meetsRow (e : Ahead) : Bool :=
  decide (0 < e.count.e) && decide (e.start.e < 8631) && decide (439 < e.start.e + e.count.e)

/-- **The walk**: in the list's own order. -/
def takersIn (l : List Ahead) (g : Nat) : List (Addr × Due × Due × Bool) :=
  (l.filter fun e => e.owner == ownerAt g && meetsRow e).map fun e =>
    (e.spender, e.start, e.count, e.once)

/-- WRITTEN OUT: piece, kind, part, first coin, count: one row an entry that is marked as spent. -/
def spentW : List (Nat × KindName × Nat × Nat × Nat) := [
  (2, .K3, 2, 439, 4), (2, .K3, 2, 443, 3), (2, .K3, 3, 446, 4), (2, .K3, 3, 450, 2),
  (2, .K3, 4, 452, 4), (2, .K3, 4, 456, 2), (2, .K3, 5, 458, 4), (2, .K3, 5, 462, 2),
  (2, .K3, 6, 464, 4), (2, .K3, 6, 468, 2), (2, .K3, 7, 470, 4), (2, .K3, 7, 474, 2),
  (2, .K3, 8, 476, 4), (2, .K3, 8, 480, 2), (2, .K3, 9, 482, 4), (2, .K3, 9, 486, 2),
  (2, .K3, 10, 488, 4), (2, .K3, 10, 492, 2), (2, .K3, 11, 494, 4), (2, .K3, 11, 498, 2),
  (2, .K3, 12, 500, 4), (2, .K3, 12, 504, 2), (2, .K3, 13, 506, 4), (2, .K3, 13, 510, 2),
  (2, .K3, 14, 512, 4), (2, .K3, 14, 516, 2), (2, .K3, 15, 518, 4), (2, .K3, 15, 522, 2),
  (2, .K3, 16, 524, 4), (2, .K3, 16, 528, 2), (2, .K3, 17, 530, 4), (2, .K3, 17, 534, 2),
  (2, .K3, 18, 536, 4), (2, .K3, 18, 540, 2), (2, .K3, 19, 542, 4), (2, .K3, 19, 546, 2),
  (2, .K3, 20, 548, 4), (2, .K3, 20, 552, 2), (2, .K3, 21, 554, 4), (2, .K3, 21, 558, 2),
  (2, .K3, 22, 560, 4), (2, .K3, 22, 564, 2), (2, .K3, 23, 566, 4), (2, .K3, 23, 570, 2),
  (2, .K3, 24, 572, 4), (2, .K3, 24, 576, 2), (2, .K3, 25, 578, 4), (2, .K3, 25, 582, 2),
  (2, .K3, 26, 584, 4), (2, .K3, 26, 588, 2), (2, .K3, 27, 590, 4), (2, .K3, 27, 594, 2),
  (2, .K3, 28, 596, 4), (2, .K3, 28, 600, 2), (2, .K3, 29, 602, 4), (2, .K3, 29, 606, 2),
  (2, .K3, 30, 608, 4), (2, .K3, 30, 612, 2), (2, .K3, 31, 614, 4), (2, .K3, 31, 618, 2),
  (2, .K3, 32, 620, 4), (2, .K3, 32, 624, 2), (2, .K3, 34, 626, 3), (2, .K3, 34, 629, 2),
  (2, .K3, 36, 631, 5), (2, .K3, 36, 636, 2), (2, .K3, 38, 638, 7), (2, .K3, 38, 645, 2),
  (2, .K3, 40, 647, 9), (2, .K3, 40, 656, 2), (2, .K3, 42, 658, 11), (2, .K3, 42, 669, 2),
  (2, .K3, 44, 671, 13), (2, .K3, 44, 684, 2), (2, .K3, 46, 686, 15), (2, .K3, 46, 701, 2),
  (2, .K3, 48, 703, 17), (2, .K3, 48, 720, 2), (2, .K3, 50, 722, 19), (2, .K3, 50, 741, 2),
  (2, .K3, 52, 743, 21), (2, .K3, 52, 764, 2), (2, .K3, 54, 766, 23), (2, .K3, 54, 789, 2),
  (2, .K3, 56, 791, 25), (2, .K3, 56, 816, 2), (2, .K3, 58, 818, 27), (2, .K3, 58, 845, 2),
  (2, .K3, 60, 847, 29), (2, .K3, 60, 876, 2), (2, .K3, 62, 878, 31), (2, .K3, 62, 909, 2),
  (2, .K3, 64, 911, 33), (2, .K3, 64, 944, 2), (2, .K3, 66, 946, 35), (2, .K3, 66, 981, 2),
  (2, .K3, 68, 983, 37), (2, .K3, 68, 1020, 2), (2, .K3, 70, 1022, 39), (2, .K3, 70, 1061, 2),
  (2, .K3, 72, 1063, 41), (2, .K3, 72, 1104, 2), (2, .K3, 74, 1106, 43), (2, .K3, 74, 1149, 2),
  (2, .K3, 76, 1151, 45), (2, .K3, 76, 1196, 2), (2, .K3, 78, 1198, 47), (2, .K3, 78, 1245, 2),
  (2, .K3, 80, 1247, 49), (2, .K3, 80, 1296, 2), (2, .K3, 82, 1298, 51), (2, .K3, 82, 1349, 2),
  (2, .K3, 84, 1351, 53), (2, .K3, 84, 1404, 2), (2, .K3, 86, 1406, 55), (2, .K3, 86, 1461, 2),
  (2, .K3, 88, 1463, 57), (2, .K3, 88, 1520, 2), (2, .K3, 90, 1522, 59), (2, .K3, 90, 1581, 2),
  (2, .K3, 92, 1583, 61), (2, .K3, 92, 1644, 2), (2, .K3, 94, 1646, 13), (2, .K3, 94, 1659, 2),
  (2, .K3, 96, 1661, 15), (2, .K3, 96, 1676, 2), (2, .K3, 98, 1678, 17), (2, .K3, 98, 1695, 2),
  (2, .K3, 100, 1697, 19), (2, .K3, 100, 1716, 2), (2, .K3, 102, 1718, 21), (2, .K3, 102, 1739, 2),
  (2, .K3, 104, 1741, 23), (2, .K3, 104, 1764, 2), (2, .K3, 106, 1766, 25), (2, .K3, 106, 1791, 2),
  (2, .K3, 108, 1793, 27), (2, .K3, 108, 1820, 2), (2, .K3, 110, 1822, 29), (2, .K3, 110, 1851, 2),
  (2, .K3, 112, 1853, 31), (2, .K3, 112, 1884, 2), (2, .K3, 114, 1886, 33), (2, .K3, 114, 1919, 2),
  (2, .K3, 116, 1921, 35), (2, .K3, 116, 1956, 2), (2, .K3, 118, 1958, 37), (2, .K3, 118, 1995, 2),
  (2, .K3, 120, 1997, 39), (2, .K3, 120, 2036, 2), (2, .K3, 122, 2038, 41), (2, .K3, 122, 2079, 2),
  (2, .K3, 124, 2081, 43), (2, .K3, 124, 2124, 2), (2, .K3, 126, 2126, 45), (2, .K3, 126, 2171, 2),
  (2, .K3, 128, 2173, 47), (2, .K3, 128, 2220, 2), (2, .K3, 130, 2222, 49), (2, .K3, 130, 2271, 2),
  (2, .K3, 132, 2273, 44), (2, .K3, 134, 2317, 51), (2, .K3, 134, 2368, 1), (3, .K4, 1, 2369, 72),
  (3, .K4, 3, 2441, 55), (3, .K4, 3, 2496, 2), (3, .K4, 5, 2498, 56), (3, .K4, 6, 2554, 24),
  (3, .K4, 6, 2578, 32), (3, .K4, 7, 2610, 23), (3, .K4, 7, 2633, 266), (3, .K4, 9, 2899, 49),
  (3, .K4, 9, 2948, 37), (3, .K4, 10, 2985, 55), (3, .K4, 10, 3040, 2), (3, .K4, 13, 3042, 51),
  (3, .K4, 13, 3093, 2), (3, .K4, 16, 3095, 38), (7, .K3, 2, 3134, 4), (7, .K3, 2, 3138, 3),
  (7, .K3, 3, 3141, 4), (7, .K3, 3, 3145, 2), (7, .K3, 4, 3147, 4), (7, .K3, 4, 3151, 2),
  (7, .K3, 5, 3153, 4), (7, .K3, 5, 3157, 2), (7, .K3, 6, 3159, 4), (7, .K3, 6, 3163, 2),
  (7, .K3, 7, 3165, 4), (7, .K3, 7, 3169, 2), (7, .K3, 8, 3171, 4), (7, .K3, 8, 3175, 2),
  (7, .K3, 9, 3177, 4), (7, .K3, 9, 3181, 2), (7, .K3, 10, 3183, 4), (7, .K3, 10, 3187, 2),
  (7, .K3, 11, 3189, 4), (7, .K3, 11, 3193, 2), (7, .K3, 12, 3195, 4), (7, .K3, 12, 3199, 2),
  (7, .K3, 13, 3201, 4), (7, .K3, 13, 3205, 2), (7, .K3, 14, 3207, 4), (7, .K3, 14, 3211, 2),
  (7, .K3, 15, 3213, 4), (7, .K3, 15, 3217, 2), (7, .K3, 16, 3219, 4), (7, .K3, 16, 3223, 2),
  (7, .K3, 17, 3225, 4), (7, .K3, 17, 3229, 2), (7, .K3, 18, 3231, 4), (7, .K3, 18, 3235, 2),
  (7, .K3, 19, 3237, 4), (7, .K3, 19, 3241, 2), (7, .K3, 20, 3243, 4), (7, .K3, 20, 3247, 2),
  (7, .K3, 21, 3249, 4), (7, .K3, 21, 3253, 2), (7, .K3, 22, 3255, 4), (7, .K3, 22, 3259, 2),
  (7, .K3, 23, 3261, 4), (7, .K3, 23, 3265, 2), (7, .K3, 24, 3267, 4), (7, .K3, 24, 3271, 2),
  (7, .K3, 25, 3273, 4), (7, .K3, 25, 3277, 2), (7, .K3, 26, 3279, 4), (7, .K3, 26, 3283, 2),
  (7, .K3, 27, 3285, 4), (7, .K3, 27, 3289, 2), (7, .K3, 28, 3291, 4), (7, .K3, 28, 3295, 2),
  (7, .K3, 29, 3297, 4), (7, .K3, 29, 3301, 2), (7, .K3, 30, 3303, 4), (7, .K3, 30, 3307, 2),
  (7, .K3, 31, 3309, 4), (7, .K3, 31, 3313, 2), (7, .K3, 32, 3315, 4), (7, .K3, 32, 3319, 2),
  (7, .K3, 34, 3321, 3), (7, .K3, 34, 3324, 2), (7, .K3, 36, 3326, 5), (7, .K3, 36, 3331, 2),
  (7, .K3, 38, 3333, 7), (7, .K3, 38, 3340, 2), (7, .K3, 40, 3342, 9), (7, .K3, 40, 3351, 2),
  (7, .K3, 42, 3353, 11), (7, .K3, 42, 3364, 2), (7, .K3, 44, 3366, 13), (7, .K3, 44, 3379, 2),
  (7, .K3, 46, 3381, 15), (7, .K3, 46, 3396, 2), (7, .K3, 48, 3398, 17), (7, .K3, 48, 3415, 2),
  (7, .K3, 50, 3417, 19), (7, .K3, 50, 3436, 2), (7, .K3, 52, 3438, 21), (7, .K3, 52, 3459, 2),
  (7, .K3, 54, 3461, 23), (7, .K3, 54, 3484, 2), (7, .K3, 56, 3486, 25), (7, .K3, 56, 3511, 2),
  (7, .K3, 58, 3513, 27), (7, .K3, 58, 3540, 2), (7, .K3, 60, 3542, 29), (7, .K3, 60, 3571, 2),
  (7, .K3, 62, 3573, 31), (7, .K3, 62, 3604, 2), (7, .K3, 64, 3606, 33), (7, .K3, 64, 3639, 2),
  (7, .K3, 66, 3641, 35), (7, .K3, 66, 3676, 2), (7, .K3, 68, 3678, 37), (7, .K3, 68, 3715, 2),
  (7, .K3, 70, 3717, 39), (7, .K3, 70, 3756, 2), (7, .K3, 72, 3758, 41), (7, .K3, 72, 3799, 2),
  (7, .K3, 74, 3801, 43), (7, .K3, 74, 3844, 2), (7, .K3, 76, 3846, 45), (7, .K3, 76, 3891, 2),
  (7, .K3, 78, 3893, 47), (7, .K3, 78, 3940, 2), (7, .K3, 80, 3942, 49), (7, .K3, 80, 3991, 2),
  (7, .K3, 82, 3993, 51), (7, .K3, 82, 4044, 2), (7, .K3, 84, 4046, 53), (7, .K3, 84, 4099, 2),
  (7, .K3, 86, 4101, 55), (7, .K3, 86, 4156, 2), (7, .K3, 88, 4158, 13), (7, .K3, 88, 4171, 2),
  (7, .K3, 90, 4173, 15), (7, .K3, 90, 4188, 2), (7, .K3, 92, 4190, 17), (7, .K3, 92, 4207, 2),
  (7, .K3, 94, 4209, 19), (7, .K3, 94, 4228, 2), (7, .K3, 96, 4230, 21), (7, .K3, 96, 4251, 2),
  (7, .K3, 98, 4253, 23), (7, .K3, 98, 4276, 2), (7, .K3, 100, 4278, 25), (7, .K3, 100, 4303, 2),
  (7, .K3, 102, 4305, 27), (7, .K3, 102, 4332, 2), (7, .K3, 104, 4334, 29), (7, .K3, 104, 4363, 2),
  (7, .K3, 106, 4365, 31), (7, .K3, 106, 4396, 2), (7, .K3, 108, 4398, 33), (7, .K3, 108, 4431, 2),
  (7, .K3, 110, 4433, 28), (7, .K3, 112, 4461, 35), (7, .K3, 112, 4496, 1)]

/-- WRITTEN OUT: the addresses that are given the whole message as carried, at g = 1. -/
def carriersW : List Addr := [
  ⟨⟨1, some 2, 11, .K10⟩, 0⟩, ⟨⟨1, some 3, 1, .K2⟩, 0⟩, ⟨⟨1, some 3, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 4, 1, .K2⟩, 0⟩, ⟨⟨1, some 4, 11, .K10⟩, 0⟩, ⟨⟨1, some 5, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 5, 11, .K10⟩, 0⟩, ⟨⟨1, some 6, 1, .K2⟩, 0⟩, ⟨⟨1, some 6, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 7, 1, .K2⟩, 0⟩, ⟨⟨1, some 7, 11, .K10⟩, 0⟩, ⟨⟨1, some 8, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 8, 11, .K10⟩, 0⟩, ⟨⟨1, some 9, 1, .K2⟩, 0⟩, ⟨⟨1, some 9, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 10, 1, .K2⟩, 0⟩, ⟨⟨1, some 10, 11, .K10⟩, 0⟩, ⟨⟨1, some 11, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 11, 11, .K10⟩, 0⟩, ⟨⟨1, some 12, 1, .K2⟩, 0⟩, ⟨⟨1, some 12, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 13, 1, .K2⟩, 0⟩, ⟨⟨1, some 13, 11, .K10⟩, 0⟩, ⟨⟨1, some 14, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 14, 11, .K10⟩, 0⟩, ⟨⟨1, some 15, 1, .K2⟩, 0⟩, ⟨⟨1, some 15, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 16, 1, .K2⟩, 0⟩, ⟨⟨1, some 16, 11, .K10⟩, 0⟩, ⟨⟨1, some 17, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 17, 11, .K10⟩, 0⟩, ⟨⟨1, some 18, 1, .K2⟩, 0⟩, ⟨⟨1, some 18, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 19, 1, .K2⟩, 0⟩, ⟨⟨1, some 19, 11, .K10⟩, 0⟩, ⟨⟨1, some 20, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 20, 11, .K10⟩, 0⟩, ⟨⟨1, some 21, 1, .K2⟩, 0⟩, ⟨⟨1, some 21, 11, .K10⟩, 0⟩,
  ⟨⟨1, some 22, 1, .K2⟩, 0⟩, ⟨⟨1, some 22, 11, .K10⟩, 0⟩, ⟨⟨1, some 23, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 23, 11, .K10⟩, 0⟩, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨⟨1, some 24, 13, .K10⟩, 0⟩,
  ⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨⟨1, none, 2, .K12⟩, 0⟩, ⟨⟨1, none, 2, .K12⟩, 1⟩]

/-- The entries marked as spent, at the group g. -/
def rowSpentAt (g : Nat) : List (Addr × Due × Due × Bool) :=
  spentW.map fun r =>
    (⟨⟨1, some (2 * g), r.1, r.2.1⟩, r.2.2.1⟩, ⟨23436, r.2.2.2.1⟩, ⟨0, r.2.2.2.2⟩, true)

/-- The entries marked as carried, at the group g. -/
def rowCarriedAt (g : Nat) : List (Addr × Due × Due × Bool) :=
  (carriersW.drop (4 * (g - 1))).map fun a => (a, ⟨660, 439⟩, ⟨22776, 8411⟩, false)

/-- **The written list at the group g.** -/
def takersW (g : Nat) : List (Addr × Due × Due × Bool) := rowSpentAt g ++ rowCarriedAt g

/-- The walk goes through an append. -/
theorem takersIn_append (a b : List Ahead) (g : Nat) :
    takersIn (a ++ b) g = takersIn a g ++ takersIn b g := by
  unfold takersIn
  rw [List.filter_append, List.map_append]

theorem takersIn_nil (g : Nat) : takersIn [] g = [] := rfl

/-- The rows are 319. -/
theorem spentW_length : spentW.length = 319 := by decide +kernel

/-- The addresses are 48. -/
theorem carriersW_length : carriersW.length = 48 := by decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.takersIn_append
#print axioms AtFullSide.K1.takersIn_nil
#print axioms AtFullSide.K1.spentW_length
#print axioms AtFullSide.K1.carriersW_length
