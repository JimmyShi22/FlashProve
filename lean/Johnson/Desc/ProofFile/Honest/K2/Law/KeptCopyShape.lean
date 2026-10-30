-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeptCopyShape.lean: the kind "the code switch" (K2): THE SHAPE
OF A KEPT COPY, AS THE SENDING HAS IT: message 1 + i of a switch's sending has the shape of the
target's kept entry number i; and where the public test `keptCopiesOk`
(Honest/K2/Law/KeptCopiesWritten.lean) accepts a list of places, at each of its places that shape is
the kept member's, has no mask row, lies over the base field and has one answer. PUBLIC DATA ALONE.
Two statements with their proofs; no definition.

  `copy_shape`      message 1 + i has the shape of target number i
  `copy_shape_ok`   where the test accepts: four facts on that shape

By: the sealed `notices_kept` (Johnson/Top/H0/K2Hands/AtYes.lean): the first · the test's own text,
read at one place and one target: the second. WHAT IT IS FOR: the four facts are premises of laws on
a kept copy's text: h3 of `copy_txt_is_senders_f` (Honest/K2/Law/CopyIsSendersF.lean), hb of
`msgTxt_mask_bare` (Honest/K2/Law/TxtBeyond.lean), ha of `padInMain_iff_padB`
(Honest/K2/Law/PadPlaces.lean). None of these is called here.

Limits. hok IS A PREMISE: that the test accepts is `keptCopies_written` and `keptCopies_at_head`'s,
in the sister file. hi counts by the target's entries; under the test that is the number of kept
shapes too: not said apart. Of the shape of the message that the copy repeats, at the switch in
front, nothing is said. Nothing on a prover, a coin or a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptCopiesWritten
import Johnson.Top.H0.K2Hands.AtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Sizes)

/-- **Message 1 + i of a switch's sending has the shape of the target's kept entry number i.** -/
theorem copy_shape (Z : Sizes) (others : Array OnBytes.OracleNotice) {i : Nat}
    (hi : i < Z.target.kept.size) :
    ((switchSent Z others).getD (1 + i) default).shape = Z.target.kept[i].shape := by
  have h := VerifiableInference.Desc.First.K2.notices_kept Z.target others i hi
  show ((Tw.K2.switchNotices Z.target others).getD (1 + i) default).shape = _
  cases e : (Tw.K2.switchNotices Z.target others)[1 + i]? with
  | none =>
    rw [e] at h
    cases h
  | some x =>
    rw [e] at h
    rw [Array.getD_eq_getD_getElem?, e]
    exact Option.some.inj h

/-- **Where the test accepts**: the copy's shape is the kept member's; it has no mask row; it lies
over the base field; it has one answer. -/
theorem copy_shape_ok {ps : List SwitchPlace} (hok : keptCopiesOk ps = true) {p : SwitchPlace}
    (hp : p ∈ ps) {i : Nat} (hi : i < p.sizes.target.kept.size) :
    ((switchSent p.sizes p.others).getD (1 + i) default).shape = p.sizes.kept.getD i {} ∧
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.maskRows = 0 ∧
      (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = false ∧
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.answers = 1 := by
  have h1 := List.all_eq_true.1 hok p hp
  rw [Bool.and_eq_true] at h1
  obtain ⟨hk, ha⟩ := h1
  have hk' : p.sizes.kept = p.sizes.target.kept.toList.map (·.shape) := eq_of_beq hk
  have ht := Array.all_eq_true.1 ha i hi
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨m0, d1⟩, a1⟩ := ht
  rw [copy_shape p.sizes p.others hi]
  refine ⟨?_, m0, ?_, a1⟩
  · rw [hk']
    simp [hi]
  · rw [d1]
    rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copy_shape
#print axioms ProofFile.Honest.K2.Law.copy_shape_ok
