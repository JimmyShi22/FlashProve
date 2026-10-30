-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SegmentLeftInv.lean: A LIGHT FILE: WHAT `segmentLeft`
(Honest/K2/Closing.lean) RETURNS, WHERE IT RETURNS. One statement with its proof, by unfolding. It
imports Closing.lean alone, so that laws on the closing's texts can call it without the files on
claims and layouts beneath them.

  `segmentLeft_inv` `segmentLeft … = .ok (W, kept)` ⊢ there is R with `segmentGroupRows … true = .ok R`;
                    kept is the kept members' shapes; W is what `foldEnd` leaves of R's rows at the
                    challenges heard, kept in arrays (`frozenLeft`)

It stood in Honest/K2/Law/ClaimAtClosing.lean, which imports this file now: the same name, namespace
and statement. The step that opens a bind is typed inside the proof, so that no second file is
imported.

Limits. It drops what `segmentLeft`'s two tests say (the count of challenges; that the group's
shapes fit a fold). Nothing on whether it returns. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes
open VerifiableInference.Desc.K2.Honest (Left foldEnd)

/-- **What `segmentLeft` returns, where it returns**: the group's rows were made; what it hands on
is what `foldEnd` leaves of them, kept in arrays, with the kept members' shapes. -/
theorem segmentLeft_inv {table : FreshTable} {Sg : SegmentPub} {prev : Option Left}
    {prevKept : List OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {base : Nat} {W : Left} {kept : List OracleShape}
    (h : segmentLeft table Sg prev prevKept own heard k base = .ok (W, kept)) :
    ∃ R, segmentGroupRows table Sg prev prevKept own k base true = .ok R ∧
      kept = (R.members.filter (·.kept)).map (·.shape) ∧
      W = frozenLeft (Sg.sizes.codes.base.getD Sg.sizes.code default)
        (Sg.sizes.codes.mask.getD Sg.sizes.maskCode default) kept
        (foldEnd Sg.sizes.codes Sg.sizes.code Sg.sizes.maskCode R.members
          (R.rows.getD · zeroMessage) (R.fresh.getD zeroMessage)
          (challengesOr0 heard Sg.gamma)) := by
  unfold segmentLeft at h
  dsimp only at h
  have bo : ∀ {α β : Type} {x : Except String α} {f : α → Except String β} {b : β},
      (x >>= f) = .ok b → ∃ a, x = .ok a ∧ f a = .ok b := by
    intro α β x f b hb
    cases x with
    | error e => cases hb
    | ok a => exact ⟨a, rfl, hb⟩
  obtain ⟨R, hR, h⟩ := bo h
  split at h
  · cases h
  · simp only [pure_bind] at h
    split at h
    · cases h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact ⟨R, hR, rfl, rfl⟩

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.segmentLeft_inv
