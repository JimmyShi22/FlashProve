-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/TieIs.lean: CONDITIONAL in its last statement. One definition;
five statements with their proofs, by unfolding and two inductions.

What is here. THE TWO LISTS OF COINS THAT Law/Script.lean TYPES (`runsE`, `spentOf`) ARE THOSE OF
Honest/Law/Rule/Spent.lean; AND THE HYPOTHESIS `K4MaskTie` (Law/Script.lean) IS THE COMMON FORM
`MaskTie` (Honest/Law/Rule/Ties.lean) AT K4's PARAMETERS; so the form of the book and the coins
alone, `MaskTieBook`, gives it. K4: the sub-protocol of the feed-forward layers' own rounds.

  `runs_same`, `spent_same`   the two lists of coins that Law/Script.lean types are those of
      Honest/Law/Rule/Spent.lean, at every list and all its coins: one text, typed twice. No
      hypothesis.
  `k4Entry own rdOf`   the reader of the member's j-th mask entry: entry number (the ledger's next
      free slot in front) + j of the segment's mask row, off the witness's tables. A definition.
  `k4MaskTie_iff_own`   K4MaskTie is MaskTie at these parameters and Law/Script.lean's own list of
      coins: by unfolding.
  `k4MaskTie_iff`   and at Honest/Law/Rule/Spent.lean's list.
  `k4MaskTie_of_book`   MaskTieBook at these parameters gives K4MaskTie.

Limits. `k4MaskTie_of_book` is CONDITIONAL: `MaskTieBook` is its hypothesis; IT GOES ONE WAY:
`MaskTieBook` has no premise that the book's lending returns: it asks its equation wherever
`rowSpent` has coins enough; `K4MaskTie` asks only where `lendRow` returns; no way back is shown.
The other four have no hypothesis: two equations and two equivalences between texts. All five at all
coins: no value of a coin is cut off, nothing is counted. Nothing on the last coin that the row
spends: the fence is j + 1 < n, as in `K4MaskTie` itself (why: Law/Script.lean's head, at
`K4MaskTie`: the last coin is no entry of the mask row).
The three on `K4MaskTie` speak of the tie bound at the thread's sentence Thr T b; a statement that
wants the tie at one stand asks `K4MaskTieAt`: `k4MaskTie_iff_at` ties the two (Law/ScriptAt.lean;
it, and so every statement that asks `K4MaskTieAt`, is no part of the library yet).

Not shown here. THAT `K4MaskTie`, `MaskTie` OR `MaskTieBook` HOLDS AT ANY THREAD, SCRIPT OR BOOK.
Nothing on soundness, on completeness, on hiding or on any other property.

Kin. `runsE` and `spentOf` stand thrice in the library, one text but for comments and one binder:
Honest/Law/Rule/Spent.lean (of other writers; its head says that it took the two over from the kinds
K5 and K4), Law/Script.lean and Honest/K5/Law/Script.lean (of other writers). For the third,
Honest/K5/Law/TiesFit.lean has the like of this file: `runs_same`, `spent_same` under the same short
names; `entry5` for `k4Entry`; `mask_iff` for `k4MaskTie_iff_own`; `mask_frame` for `k4MaskTie_iff`,
one way alone, from that kind's whole script; `mask_of_book` for `k4MaskTie_of_book`, ending at
`MaskTie` and not at that kind's own tie; there the fence is j < n. A third `runs_same`
(Johnson/IMR/LinkRest.lean, in another namespace) speaks of blocks, not of coins: no kin. The
writers of Spent.lean mean to lay the two in a light file of their own; once that is part of the
library Law/Script.lean can take them from there, and `runs_same`, `spent_same` and
`k4MaskTie_iff_own` fall.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Script
import Johnson.Desc.ProofFile.Honest.Law.Rule.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ)

/-- The coins of a list of runs: one text, typed twice. -/
theorem runs_same : ∀ (ds : List (String × Due)) (c : CsAll ds), runsE ds c = ProofFile.Honest.runsE ds c
  | [], _ => rfl
  | d :: ds, c => by
    show coinsE _ ++ runsE ds _ = coinsE _ ++ ProofFile.Honest.runsE ds _
    rw [runs_same ds]

/-- The coins that the parts of a row spend: one text, typed twice. -/
theorem spent_same {V W X : Type} : ∀ (ps : List (Part V W X)) (c : RowCoins ps),
    spentOf ps c = ProofFile.Honest.spentOf ps c
  | [], _ => rfl
  | p :: ps, c => by
    show runsE p.spends _ ++ spentOf ps _ = ProofFile.Honest.runsE p.spends _ ++ ProofFile.Honest.spentOf ps _
    rw [runs_same, spent_same ps]

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- The reader of the member's j-th mask entry. -/
def k4Entry {Wt In : Type} (own : List (Nat × Nat)) (rdOf : Wt → Nat × Nat → MsgQ)
    (a : VerifiableInference.Desc.K9.Part) (_ : First.S) (_ : In) (v : Wt) (j : Nat) : GQ :=
  (dataQ own a (rdOf v)).mask (a.F.next + j)

section
variable (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
  (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
  (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ)

/-- K4's tie is the common form, at Law/Script.lean's own list of coins. -/
theorem k4MaskTie_iff_own :
    K4MaskTie T b cells weights tokens look Q own rdOf ↔
      MaskTie T b (k4Place Q) (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts segAt?
        (k4Entry own rdOf) Reading.gl.val (spentOf _) (fun n j => j + 1 < n) :=
  Iff.rfl

/-- K4's tie is the common form, at the common list of coins. -/
theorem k4MaskTie_iff :
    K4MaskTie T b cells weights tokens look Q own rdOf ↔
      MaskTie T b (k4Place Q) (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts segAt?
        (k4Entry own rdOf) Reading.gl.val (ProofFile.Honest.spentOf _) (fun n j => j + 1 < n) := by
  rw [k4MaskTie_iff_own]
  have e : (spentOf (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts) =
      ProofFile.Honest.spentOf _ := funext (spent_same _)
  rw [e]

/-- **The form of the book and the coins alone gives K4's tie.** -/
theorem k4MaskTie_of_book
    (h : MaskTieBook T b (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts.length segAt?
      (k4Entry own rdOf) Reading.gl.val (fun n j => j + 1 < n)) :
    K4MaskTie T b cells weights tokens look Q own rdOf :=
  (k4MaskTie_iff T b cells weights tokens look Q own rdOf).2 (maskTie_of_book h)

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.runs_same
#print axioms ProofFile.Honest.K4.spent_same
#print axioms ProofFile.Honest.K4.k4Entry
#print axioms ProofFile.Honest.K4.k4MaskTie_iff_own
#print axioms ProofFile.Honest.K4.k4MaskTie_iff
#print axioms ProofFile.Honest.K4.k4MaskTie_of_book
