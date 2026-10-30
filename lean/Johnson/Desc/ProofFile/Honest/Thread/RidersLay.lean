-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RidersLay.lean: A FACT ON A LAYERS' SEGMENT's OWN PART OF THE
STATE, AS A CLAUSE OF THE RIDER. The sister of `riderHead` (Honest/Thread/Riders.lean) and
`riderAtt` (Honest/Thread/RidersAtt.lean) at a layers' segment, with the two forms of its staying;
and the clause that the kind K4's lemmas ask of the list: "the
state's reading own? returns something": it is `riderLay` at the sentence "own is laid". One
definition. Three conditional lemmas on our own definitions.

  `riderLay`          the clause
  `staysBy_lay_of`    it stays where the member's clause of `keeps` hands the sentence on
  `staysBy_lay_read`  the same for a sentence on a reading f of the part that the member leaves
  `lay_own_iff`       ∃ a, s.here = .lay a ∧ a.own.isSome  ⇔  s.own?.isSome

Limits. Who lays the clause and at which borders is not said here. None is one of the library's
goals. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S LayOwn)

/-- **A FACT ON A LAYERS' SEGMENT's OWN PART OF THE STATE**: the chain stands in a layers' segment,
and P holds of that part. -/
def riderLay {W : Type} (lo hi : Nat) (P : LayOwn → Prop) : RiderCl W S :=
  ⟨lo, hi, fun _ _ s => ∃ a, s.here = .lay a ∧ P a⟩

/-- "Own is laid", in the state's own reading. -/
theorem lay_own_iff (s : S) :
    (∃ a, s.here = .lay a ∧ a.own.isSome = true) ↔ s.own?.isSome = true := by
  unfold S.own?
  constructor
  · rintro ⟨a, ha, h⟩
    rw [ha]
    exact h
  · intro h
    cases hh : s.here with
    | lay a =>
      rw [hh] at h
      exact ⟨a, rfl, h⟩
    | between => rw [hh] at h; cases h
    | att a => rw [hh] at h; cases h
    | head a => rw [hh] at h; cases h
    | fin a => rw [hh] at h; cases h
    | mem a => rw [hh] at h; cases h

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE GENERAL FORM.** -/
theorem staysBy_lay_of {b lo hi : Nat} {P : LayOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .lay a →
      ∃ a', s'.here = .lay a' ∧ (P a → P a')) : StaysBy T b (riderLay lo hi P) :=
  fun _ s s' hK ⟨a, ha, hP⟩ =>
    let ⟨a', ha', hPP⟩ := hk s s' hK a ha
    ⟨a', ha', hPP hP⟩

/-- **A SENTENCE ON ONE READING OF THE PART**, where the member leaves that reading. -/
theorem staysBy_lay_read {α : Type} {b lo hi : Nat} (f : LayOwn → α) {R : α → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .lay a →
      ∃ a', s'.here = .lay a' ∧ f a' = f a) : StaysBy T b (riderLay lo hi fun a => R (f a)) :=
  staysBy_lay_of T fun s s' hK a ha =>
    let ⟨a', ha', e⟩ := hk s s' hK a ha
    ⟨a', ha', fun hR => e ▸ hR⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.lay_own_iff
#print axioms ProofFile.Honest.staysBy_lay_of
#print axioms ProofFile.Honest.staysBy_lay_read
