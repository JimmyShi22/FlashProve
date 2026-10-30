-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/DoorTermsAlike.lean: the sum of an equation's terms, at two lists of terms that differ
only in the weights that are written out on the arrays' columns: `AddTermsAlike`
(OnBytes/Flat/DoorAlike.lean). Statements and proofs.



A link's check ends in one equation, and `ReqRows.addTerms` (OnBytes/Iop/ReqRows.lean) turns its
terms into forms on oracle messages. It can refuse. Here it is shown that whether it refuses does
not hang on the entries of a written-out vector of weights on the columns, only on their number.
By the program's text: `LaidDraft.pushBit` lays the pair (1, 1) for a bit of a written-out vector
and reads no entry; `IndexWeights.above` returns 1 for such a vector; `laidTensor` takes one entry
by its index, or lays the whole vector into the tensor; `Tensor.ok` (OnBytes/Iop/Tensor.lean) reads
the vector's length and not the scalar.

Main theorems:
  `pushBit_written`, `pushBits_written`   the drafts at two such vectors are equal.
  `ok_scale`, `ok_setValues`             what `Tensor.ok` does not read.
  `laidTensor_alike`, `laidForm_alike`    one block, all blocks of an array: at two vectors of one
                                         length both refuse or both return.
  `addTerms_alike`                        `AddTermsAlike`.
Limits: nothing on what is returned but that the row's kind is kept. The weights on the rows and the
factor before both weights are the same in both terms. Nothing on a block of a protocol: all here
are plain functions. For proofs only; no module of the program imports this file.
-/
import OnBytes.Flat.DoorAlike

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Params (LaidBlock)

/-- One variable more: the written-out weights on the columns are not read. -/
theorem pushBit_written (d : LaidDraft) (b : LaidBlock) (onI : IndexWeights) (L L' : Array E)
    (x : Nat) :
    d.pushBit b onI { values := some L } x = d.pushBit b onI { values := some L' } x := by
  unfold LaidDraft.pushBit
  dsimp only
  by_cases h : (decide (x < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
  · simp only [h, if_true]
  · simp only [h, Bool.false_eq_true, if_false]
    rfl

/-- Several variables more. -/
theorem pushBits_written (b : LaidBlock) (onI : IndexWeights) (L L' : Array E) :
    ∀ (xs : List Nat) (d : LaidDraft),
      d.pushBits b onI { values := some L } xs = d.pushBits b onI { values := some L' } xs
  | [], _ => rfl
  | x :: xs, d => by
    unfold LaidDraft.pushBits
    rw [pushBit_written d b onI L L' x]
    exact congrArg _ (funext fun e => pushBits_written b onI L L' xs e)

/-- `Tensor.ok` does not read the scalar. -/
theorem ok_scale (t : Tensor) (x : E) : (t.scale x).ok = t.ok := by
  unfold Tensor.ok Tensor.scale Tensor.vars
  rfl

/-- Of the written-out vector `Tensor.ok` reads the length alone. -/
theorem ok_setValues (t : Tensor) {L L' : Array E} (h : L.size = L'.size) (first : Nat) :
    (t.setValues L first).ok = (t.setValues L' first).ok := by
  unfold Tensor.ok Tensor.setValues Tensor.vars
  dsimp only
  rw [h]

/-- **One block**: both refuse, or both return. -/
theorem laidTensor_alike (b : LaidBlock) (r p : Nat) (onI : IndexWeights) {L L' : Array E}
    (h : L.size = L'.size) (s : E) :
    OptRel (fun _ _ => True) (laidTensor b r p onI { values := some L } s)
      (laidTensor b r p onI { values := some L' } s) := by
  have w : ∀ M : Array E, ({ values := some M } : IndexWeights).writtenOut = true := fun _ => rfl
  have k : ∀ M : Array E, ({ values := some M } : IndexWeights).ok = true := fun _ => rfl
  have a : ∀ (M : Array E) (x y : Nat),
      ({ values := some M } : IndexWeights).above x y = some oneE := fun _ _ _ => rfl
  unfold laidTensor
  simp only [pushBits_written b onI L L', w, k, a]
  split
  · trivial
  · rename_i hg
    have hw : onI.writtenOut = false := by
      cases hq : onI.writtenOut with
      | false => rfl
      | true => simp [hq] at hg
    simp only [hw, Bool.false_eq_true, if_false]
    refine optRel_bind_same fun _ => ?_
    refine optRel_bind_same fun _ => ?_
    refine optRel_bind_same fun d => ?_
    refine optRel_bind_same fun _ => ?_
    refine optRel_bind_same fun _ => ?_
    split
    · refine optRel_bind (S := fun y y' => y.ok = y'.ok) ?_ fun y y' e => ?_
      · have e : L[b.firstC]?.isSome = L'[b.firstC]?.isSome := by
          by_cases hl : b.firstC < L.size
          · rw [getElem?_pos L b.firstC hl, getElem?_pos L' b.firstC (h ▸ hl)]
            rfl
          · rw [getElem?_neg L b.firstC hl, getElem?_neg L' b.firstC (h ▸ hl)]
        revert e
        cases L[b.firstC]? <;> cases L'[b.firstC]? <;> intro e
        · trivial
        · cases e
        · cases e
        · show Tensor.ok _ = Tensor.ok _
          simp only [ok_scale]
      · rw [e]
        split <;> trivial
    · refine optRel_bind (S := fun y y' => y.ok = y'.ok) ?_ fun y y' e => ?_
      · show Tensor.ok _ = Tensor.ok _
        exact ok_setValues _ h _
      rw [e]
      split <;> trivial

/-- **All blocks of an array.** -/
theorem laidForm_alike (r p : Nat) (onI : IndexWeights) {L L' : Array E} (h : L.size = L'.size)
    (s : E) : ∀ (blocks : List LaidBlock) (f f' : Form),
      OptRel (fun _ _ => True)
        (blocks.foldlM (fun (f : Form) b =>
          (laidTensor b r p onI { values := some L } s).map f.add) f)
        (blocks.foldlM (fun (f : Form) b =>
          (laidTensor b r p onI { values := some L' } s).map f.add) f')
  | [], _, _ => trivial
  | b :: bs, f, f' => by
    rw [List.foldlM_cons, List.foldlM_cons]
    refine optRel_bind (S := fun _ _ => True) ?_ fun g g' _ => laidForm_alike r p onI h s bs g g'
    have h0 := laidTensor_alike b r p onI h s
    revert h0
    cases laidTensor b r p onI { values := some L } s <;>
      cases laidTensor b r p onI { values := some L' } s <;> intro h0
    · trivial
    · exact h0.elim
    · exact h0.elim
    · trivial

/-- **The sum of an equation's terms, at two lists of terms that are alike.** -/
theorem addTerms_alike : AddTermsAlike := by
  intro R f S ts ts' row row' hts
  induction hts generalizing row row' with
  | nil => exact fun hk => hk
  | @cons t t' ts ts' ht _ ih =>
    intro hk
    obtain ⟨e, L, L', e1, e2, hs⟩ := ht
    unfold ReqRows.addTerms
    rw [e]
    dsimp only
    rw [e1, e2]
    refine optRel_bind_same fun a => ?_
    refine optRel_bind_same fun o => ?_
    refine optRel_bind (S := fun _ _ => True) (laidForm_alike _ _ _ hs _ _ _ _) fun c c' _ => ?_
    exact ih _ _ hk

end OnBytes.Flat
