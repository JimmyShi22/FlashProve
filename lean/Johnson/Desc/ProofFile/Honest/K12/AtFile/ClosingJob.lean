-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingJob.lean: what the job of the first chain's closing
proximity test (`jobL`, K12/AtProof/JobL.lean) reads: facts on its text, general in its letters, for
the premises of the laws on the test. No run, no thread.

  `rowsOfHeard_jobL`   of a front its rows read the challenges heard alone
  `carryRows_congr`, `rowsL_congr`, `rows_members_jobL`   its rows read of the stretches those of
                       its members alone
  `fresh_jobL`         its fresh table has come earlier
  `door_jobL`          its state on entry, with the door filled, is `doorL` at the chain's list

By what. The texts of `carryRows`, `rowsL`, `heardL`, `membersL`, `freshL`, `jobL`, `doorAtL`.

Limits.
- Equations on texts. Where the sender's text refuses the rows are zeros, at both sides alike.
- `door_jobL` names the list of blocks and the place by premises: that `flatL` is a thread's list is
  the caller's.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import Johnson.Desc.ProofFile.Honest.K12.TablesAtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.K12.Blind (doorL)

variable {W₀ Rc Xi Tr X : Type}

theorem length_membersL (p : K2.SwitchPlace) : (membersL p).length = p.front.length + 1 := by
  simp [membersL]

/-- **The rows read of the stretches those of the members alone.** -/
theorem carryRows_congr (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    {mem mem' : ℕ → Stretch} (h : ∀ t, t < (membersL p).length → mem t = mem' t) :
    carryRows D readers closing p w heard mem = carryRows D readers closing p w heard mem' := by
  have hl := length_membersL p
  have e0 : mem p.front.length = mem' p.front.length := h _ (by omega)
  unfold carryRows
  refine congrArg₂ (fun a f => Except.bind a f)
    (congrArg (closing p (D w.x) (readers w) heard) (funext fun n => ?_)) (funext fun Wl => ?_)
  · cases hn : p.front[n]? with
    | none => rfl
    | some x =>
      have hlt : n < p.front.length := (List.getElem?_eq_some_iff.1 hn).1
      show (Except.ok (asK2 x.2.2 (mem n)) : Except String K2.Stretch) =
        Except.ok (asK2 x.2.2 (mem' n))
      rw [h n (by omega)]
  · show K2.messageRows K2.freshTable p.sizes.codes (shapeL p) none _
        (asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (mem p.front.length)) =
      K2.messageRows K2.freshTable p.sizes.codes (shapeL p) none _
        (asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (mem' p.front.length))
    rw [e0]

theorem rowsL_congr (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (fr : Front X)
    {mem mem' : ℕ → Stretch} (h : ∀ t, t < (membersL p).length → mem t = mem' t) :
    rowsL D readers closing p w fr mem = rowsL D readers closing p w fr mem' := by
  unfold rowsL
  rw [carryRows_congr D readers closing p w (heardL fr) h]

/-- Of a front the job's rows read the challenges heard alone. -/
theorem rowsOfHeard_jobL (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    RowsOfHeard (jobL q door D readers closing p) := by
  intro w fr fr' mem h
  show rowsL D readers closing p w fr mem = rowsL D readers closing p w fr' mem
  unfold rowsL heardL
  rw [h]

/-- The fresh table has come earlier. -/
theorem fresh_jobL (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    (jobL q door D readers closing p).fresh = some (⟨p.place, 0⟩, (sentL p).size - 1) := rfl

/-- **The state on entry, with the door filled.** bs: a chain's list that is the public part's. a: a
place that is the test's. -/
theorem door_jobL (Z : ProofFile.Pub) (q : P12) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (bs : List (Block S ProofFile.Cl)) (a : Place) (hb : bs = flatL Z) (ha : a = placeL) :
    (jobL q (doorAtL Z) D readers closing p : TestJob (Local W₀ Rc ProofFile.Inst Tr) X).rec₀ =
      doorL bs (startL Z) a idleT12 := by
  show doorAtL Z = _
  unfold doorAtL
  rw [hb, ha]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.length_membersL
#print axioms ProofFile.Honest.K12.AtProof.carryRows_congr
#print axioms ProofFile.Honest.K12.AtProof.rowsL_congr
#print axioms ProofFile.Honest.K12.AtProof.rowsOfHeard_jobL
#print axioms ProofFile.Honest.K12.AtProof.fresh_jobL
#print axioms ProofFile.Honest.K12.AtProof.door_jobL
