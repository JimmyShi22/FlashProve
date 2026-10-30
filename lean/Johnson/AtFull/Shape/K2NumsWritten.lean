-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K2NumsWritten.lean: THE NUMBERS OF THE KIND K2 (the code switch) AT THE LINKS 1
TO 24 AND AT THE FINISH OF THE FIRST CHAIN, IN THE FORM (P1K2.prepareAt ‹the written arguments, and
a public record X›).bind fun P => P1K2.numsAt P a, TO WHICH `prepOf_at_head`
(SpentReadersAtHead.lean) BRINGS THEM, ARE NUMERALS, THE SAME AT EVERY X. Closed facts by Lean's
kernel, with a control; the proofs combine them with two theorems of the library. No statement here
has a hypothesis on public files.

Words. X is any value of `Verify.Public` (OnBytes/Model/VerifyPublic.lean). The 25 places are
`asks`: none for the finish, some l for the link l.

Why at every X. Where K2's own test on its arguments (P1K2.tied,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) accepts, what prepareAt returns does not depend on X:
`IM.prepareAt_on` (Johnson/IMR/SendsPinned.lean): it is prepOn at the sizes and the number of links.
At the written arguments that is the library's closed term `IM.prepW`.

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's blocksInOrder list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. To evaluate one of its steps at a code switch means to run prepareAt anew, which
builds the trees of every link. Here that is done once, and the 25 records stand as numerals.

Main names.
* `tiedW`: BY THE KERNEL. **`prep_free`**: at every X: prepareAt at the written arguments =
  IM.prepW.
* `NumsT`, `numsT`, `ofT`, `ofT_numsT`: K2's numbers but for the codes as a tuple, so that they can
  be compared by code, and back with the written codes.
* `k2nLit`: 25 rows. `litAt`, `asks`, `k2nL`. `k2_written`: BY THE KERNEL: at each of the 25 places:
  what numsAt gives at IM.prepW, as a tuple, is the row. `k2_there`: BY THE KERNEL: each of the 25
  has a row. A control: `k2_written_no` (one number changed at link 7: refused); it follows from the
  two facts, and shows only that the kernel's decision is not constant.
* **`k2n_lit`**: a ∈ asks ⊢ (prepareAt … X …).bind (numsAt · a) = k2nL a. The codes: by the
  library's `numsAt_codes` (Johnson/P1K2R/HstInScope.lean) and `prepW_z`. `asks_link`, `asks_none`.

Limits. k2nLit was read off Lean's evaluator; what holds it is k2_written. The field codes of a
record is the written term proofSizedFull.codes, no numeral. One of the written arguments is qFull,
the library's PLACEHOLDER for the first chain's parameters (Johnson/Desc/K1/Law/QFull.lean: four of
its fields are empty fillings); prepareAt reads of it the codes and the shape alone
(`prepareAt_congr`, SpentReadersAtHead.lean). At link 0 and from link 25 on nothing is said. One
control changes one number at one link. Closed facts at written arguments: that the public part's
own arguments are these is prepOf_at_head's to say, under the hypothesis P5J.AtMg. Nothing says that
a step of the table succeeds. Only the full-size parameters are covered. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.SpentReadersAtHead
import Johnson.IMR.SendsPinned
import Johnson.P1K2R.HstInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K1 (qFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2)

/-! ## 1 What K2 prepares does not depend on the public record -/

/-- BY THE KERNEL: K2's own test on its five arguments accepts at the written ones. (Two of its five
clauses hold by definition here: each compares proofSizedFull.request with itself, one of them
through qFull.shape.) -/
theorem tiedW : P1K2.tied proofSizedFull qFull codesFull2 proofSizedFull.request
    proofSizedFull.request.answers = true := by decide +kernel

/-- **AT EVERY X: WHAT K2 PREPARES AT THE WRITTEN ARGUMENTS IS THE LIBRARY's CLOSED TERM.** -/
theorem prep_free (X : Verify.Public) :
    P1K2.prepareAt proofSizedFull X qFull codesFull2 proofSizedFull.request
      proofSizedFull.request.answers = IM.prepW :=
  IM.prepareAt_on tiedW

/-! ## 2 K2's numbers as a tuple -/

/-- K2's numbers but for the codes. -/
abbrev NumsT : Type :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × List OracleNotice ×
    List (Nat × Nat × Nat)

/-- A record of K2's numbers as that tuple: every field but the codes. -/
def numsT (n : P1K2.Nums) : NumsT :=
  (n.grp, n.samples, n.work₁, n.roots, n.seeds, n.nonZero, n.work₂, n.answers, n.positions, n.logN,
    n.sent.toList, n.read)

/-- Back, with the written codes. -/
def ofT : NumsT → P1K2.Nums
  | (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12) =>
    { grp := a1, samples := a2, work₁ := a3, roots := a4, seeds := a5, nonZero := a6, work₂ := a7,
      answers := a8, positions := a9, logN := a10, codes := proofSizedFull.codes,
      sent := a11.toArray, read := a12 }

/-- Back and forth gives the record again, where its codes are the written ones. -/
theorem ofT_numsT (n : P1K2.Nums) (hc : n.codes = proofSizedFull.codes) : ofT (numsT n) = n := by
  cases n
  simp only at hc
  subst hc
  rfl

/-! ## 3 The 25 records -/

/-- K2's numbers at the 24 switches and at the finish, but for the codes. Read off Lean's evaluator;
held by k2_written. -/
def k2nLit : List (Option Nat × Option NumsT) :=
  [(some 1, some (1, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(0, 23, 124), (2, 23, 3), (3, 23, 31)])),
   (some 2, some (2, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(4, 23, 66), (5, 23, 3), (6, 23,
     14)])),
   (some 3, some (3, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(7, 23, 131), (8, 23, 3), (9, 23, 31)])),
   (some 4, some (4, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(10, 23, 66), (11, 23, 3), (12, 23,
     14)])),
   (some 5, some (5, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(13, 23, 131), (14, 23, 3), (15, 23, 31)])),
   (some 6, some (6, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(16, 23, 66), (17, 23, 3), (18, 23,
     14)])),
   (some 7, some (7, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(19, 23, 131), (20, 23, 3), (21, 23, 31)])),
   (some 8, some (8, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(22, 23, 66), (23, 23, 3), (24, 23,
     14)])),
   (some 9, some (9, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(25, 23, 131), (26, 23, 3), (27, 23, 31)])),
   (some 10, some (10, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(28, 23, 66), (29, 23, 3), (30, 23,
     14)])),
   (some 11, some (11, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(31, 23, 131), (32, 23, 3), (33, 23, 31)])),
   (some 12, some (12, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(34, 23, 66), (35, 23, 3), (36, 23,
     14)])),
   (some 13, some (13, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(37, 23, 131), (38, 23, 3), (39, 23, 31)])),
   (some 14, some (14, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(40, 23, 66), (41, 23, 3), (42, 23,
     14)])),
   (some 15, some (15, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(43, 23, 131), (44, 23, 3), (45, 23, 31)])),
   (some 16, some (16, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(46, 23, 66), (47, 23, 3), (48, 23,
     14)])),
   (some 17, some (17, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(49, 23, 131), (50, 23, 3), (51, 23, 31)])),
   (some 18, some (18, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(52, 23, 66), (53, 23, 3), (54, 23,
     14)])),
   (some 19, some (19, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(55, 23, 131), (56, 23, 3), (57, 23, 31)])),
   (some 20, some (20, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(58, 23, 66), (59, 23, 3), (60, 23,
     14)])),
   (some 21, some (21, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(61, 23, 131), (62, 23, 3), (63, 23, 31)])),
   (some 22, some (22, 1, 0, 1, 31, 1, 20, 5, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 104, 1, 1, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(64, 23, 66), (65, 23, 3), (66, 23,
     14)])),
   (some 23, some (23, 1, 0, 1, 30, 1, 20, 4, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 9, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0, 4294967295, 1⟩, 0⟩, ⟨⟨0, 42, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295,
     0, 1, 1, 0, 0⟩, 0⟩], [(67, 23, 131), (68, 23, 3), (69, 23, 31)])),
   (some 24, some (24, 1, 0, 1, 31, 1, 20, 3, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨0, 3, 1, 0,
     4294967295, 1⟩, 0⟩, ⟨⟨0, 103, 1, 1, 0, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1, 1, 0, 0⟩, 0⟩], [(70, 23,
     66), (71, 23, 3), (72, 23, 14)])),
   (none, some (25, 1, 0, 1, 24, 1, 20, 1, 219, 23, [⟨⟨0, 2, 3, 0, 0, 1⟩, 0⟩, ⟨⟨4294967295, 0, 1,
     1, 0, 0⟩, 0⟩], [(73, 23, 118), (74, 23, 3), (75, 23, 24)]))]

/-- The row of k2nLit at a: the first with that key. -/
def litAt (a : Option Nat) : Option NumsT := (k2nLit.find? (·.1 == a)).bind (·.2)

/-- The 25 places of which this file speaks: the finish (none), and the links 1 to 24. -/
def asks : List (Option Nat) := none :: (List.range 24).map fun i => some (i + 1)

/-- K2's numbers in numerals. -/
def k2nL (a : Option Nat) : Option P1K2.Nums := (litAt a).map ofT

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: at each of the 25 places K2's numbers off IM.prepW, as a tuple, are the row. A
closed statement: no term in it is made from public files. -/
theorem k2_written : (asks.all fun a =>
    (IM.prepW.bind fun P => P1K2.numsAt P a).map numsT == litAt a) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one number changed, at link 7: refused. -/
theorem k2_written_no : (asks.all fun a =>
    (IM.prepW.bind fun P => P1K2.numsAt P a).map numsT ==
      if a == some 7 then (litAt a).map fun t => (t.1, t.2.1 + 1, t.2.2) else litAt a) = false := by
  decide +kernel

/-- BY THE KERNEL: each of the 25 places has a row: so k2_written does not pass by comparing nothing
with nothing. -/
theorem k2_there : (asks.all fun a => (litAt a).isSome) = true := by decide +kernel

/-- What IM.prepW holds has the written sizes. -/
theorem prepW_z {P : P1K2.Prep} (h : IM.prepW = some P) : P.z = proofSizedFull := by
  unfold IM.prepW IM.prepOn at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- **K2's NUMBERS AT THE WRITTEN ARGUMENTS ARE NUMERALS, AT EVERY X**, at each of the 25 places. -/
theorem k2n_lit (X : Verify.Public) {a : Option Nat} (ha : a ∈ asks) :
    ((P1K2.prepareAt proofSizedFull X qFull codesFull2 proofSizedFull.request
      proofSizedFull.request.answers).bind fun P => P1K2.numsAt P a) = k2nL a := by
  have e := eq_of_beq (List.all_eq_true.1 k2_written a ha)
  rw [prep_free]
  unfold k2nL
  rw [← e]
  cases hP : IM.prepW with
  | none => rfl
  | some P =>
    show P1K2.numsAt P a = ((P1K2.numsAt P a).map numsT).map ofT
    cases hn : P1K2.numsAt P a with
    | none => rfl
    | some n =>
      show some n = some (ofT (numsT n))
      rw [ofT_numsT n ((P1K2.numsAt_codes hn).trans (congrArg (·.codes) (prepW_z hP)))]

/-- Each link from 1 to 24 is among asks. -/
theorem asks_link {l : Nat} (h0 : 0 < l) (hl : l < 25) : some l ∈ asks :=
  List.mem_cons_of_mem _ (List.mem_map.2 ⟨l - 1, List.mem_range.2 (by omega), by
    show some (l - 1 + 1) = some l
    rw [Nat.sub_add_cancel h0]⟩)

/-- The finish is among asks. -/
theorem asks_none : (none : Option Nat) ∈ asks := List.mem_cons_self

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tiedW
#print axioms Johnson.AtFull.Shape.prep_free
#print axioms Johnson.AtFull.Shape.ofT_numsT
#print axioms Johnson.AtFull.Shape.k2_written
#print axioms Johnson.AtFull.Shape.k2_written_no
#print axioms Johnson.AtFull.Shape.k2_there
#print axioms Johnson.AtFull.Shape.prepW_z
#print axioms Johnson.AtFull.Shape.k2n_lit
#print axioms Johnson.AtFull.Shape.asks_link
#print axioms Johnson.AtFull.Shape.asks_none
