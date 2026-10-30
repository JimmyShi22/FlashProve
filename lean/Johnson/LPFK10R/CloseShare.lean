-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/CloseShare.lean: K10's THIRD OF THE SHARE «close» OF THE JOIN s1_of_shares (Johnson/IMR/GrownJoin.lean: in scope, «each block's yes hands the growth on» over all 358 blocks of the first chain, from ten shares):
AT THAT JOIN's OWN LETTERS, WRITTEN OUT. Statements and proofs.
  LW · PW · nA      IM.linksW := (List.range 25).map subW · IM.placesW := flatPlacesOf linksW true ·
                    IM.nAt l := if l = 24 then 9 else 7 (Johnson/IMR/WrittenList.lean), WRITTEN OUT,
                    with IM.subAt where that file has subW: that file is not imported here: so their
                    right-hand sides are typed here again, as abbreviations.
  sorts_are_w       sortsOf 25 (PromiseBehind.lean) = LW: by the kernel, AT THE subAt OF Johnson/IMR/LinkSeat.lean.
  fit_w · next_w    the two tests on the table say yes at LW, PW.
  k10_place_w       at each l < 25 the place number 14 l + nA l + 5 of PW is of the kind K10: by the kernel.
  close_k10         ∀ l < 25, ∀ Q: IM.Hands N LW PW E ft (14 * l + nA l + 4 + 1) (K9.closing Q : Block S Unit).retype: under the table's test on its numbers (bookFit N PW told), «the block at that number tells nothing», and «more» along a
                    K10Step.
  close_k10_field   the same in the field's own form at j = 1: (K9.closeOf p Q)[1]? = some x → IM.Hands … x.retype.
LIMITS. The field «close» runs over j = 0, 1, 2: THIS IS j = 1 ALONE. bookFit's yes, told's 25 entries and hE are premises. That LW, PW, nA are
IM's linksW, placesW, nAt is held by reading of two files.
These are not the versions of Johnson/IMR/PlacesScope.lean and GrownJoin.lean in this library, where
the three stand in Johnson/IMR/WrittenList.lean; no theorem here ties LW, PW, nA to them.
Nothing on soundness.

-/
import Johnson.IMR.LinkSeat
import Johnson.LPFK10R.HandsAtK10

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Place Oracle KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers start closersFit closersNext bookFit sortsOf
  flatPlacesOf closersFit_real closersNext_real)
open VerifiableInference.Desc.First.Close (Par K10Step)
open ProofFile (Cl)

abbrev LW : List ModelPart := (List.range 25).map IM.subAt
abbrev PW : List Place := flatPlacesOf LW true
abbrev nA (l : Nat) : Nat := if l = 24 then 9 else 7

theorem sorts_are_w : sortsOf 25 = LW := by decide +kernel

theorem fit_w : closersFit LW PW (start LW) = true := by
  have h := (closersFit_real true).1
  rw [sorts_are_w] at h
  exact h

theorem next_w : closersNext LW PW = true := by
  have h := (closersNext_real true).1
  rw [sorts_are_w] at h
  exact h

set_option maxRecDepth 1000000 in
theorem k10_places_w : (List.range 25).all (fun l =>
    (PW[14 * l + nA l + 5]?).any fun p => p.kind == KindName.K10) = true := by decide +kernel

theorem k10_place_w {l : Nat} (hl : l < 25) :
    ∃ p, PW[14 * l + nA l + 5]? = some p ∧ p.kind = KindName.K10 := by
  have h := List.all_eq_true.1 k10_places_w l (List.mem_range.2 hl)
  cases hp : PW[14 * l + nA l + 5]? with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    exact ⟨p, rfl, by simpa using h⟩

/-- **K10's third of the share «close».** -/
theorem close_k10 (N : Numbers) (E : Nat → S → Bool) (ft : Nat) (told : List (List Oracle))
    (hB : bookFit N PW told = true) (hn : ∀ l < 25, told[14 * l + nA l + 5]? = some [])
    (hE : ∀ l < 25, ∀ s s', K10Step s s' → s.failed = none →
      IM.XK N LW PW E (14 * l + nA l + 5) s = true → E (14 * l + nA l + 5 + 1) s' = true) :
    ∀ l < 25, ∀ Q : Par, IM.Hands N LW PW E ft (14 * l + nA l + 4 + 1)
      (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype := by
  intro l hl Q
  obtain ⟨p, hp, hk⟩ := k10_place_w hl
  exact hands_k10_lot N LW PW E ft (14 * l + nA l + 5) p Q fit_w next_w hp hk told hB (hn l hl)
    (hE l hl)

/-- **The same in the field's own form, at j = 1**: x the second member of what closes the segment. -/
theorem close_k10_field (N : Numbers) (E : Nat → S → Bool) (ft : Nat) (told : List (List Oracle))
    (hB : bookFit N PW told = true) (hn : ∀ l < 25, told[14 * l + nA l + 5]? = some [])
    (hE : ∀ l < 25, ∀ s s', K10Step s s' → s.failed = none →
      IM.XK N LW PW E (14 * l + nA l + 5) s = true → E (14 * l + nA l + 5 + 1) s' = true) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      IM.Hands N LW PW E ft (14 * l + nA l + 4 + 1) x.retype := by
  intro l hl p Q x hx
  obtain rfl : (VerifiableInference.Desc.K9.closing Q : Block S Unit) = x := Option.some.inj hx
  exact close_k10 N E ft told hB hn hE l hl Q

end LPFK10

#print axioms LPFK10.close_k10_field
#print axioms LPFK10.sorts_are_w
#print axioms LPFK10.fit_w
#print axioms LPFK10.next_w
#print axioms LPFK10.k10_places_w
#print axioms LPFK10.close_k10
