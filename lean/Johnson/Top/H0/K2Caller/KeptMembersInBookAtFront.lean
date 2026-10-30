-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptMembersInBookAtFront.lean: THE TWO PREMISES INTO WHICH hBook OF THE CODE SWITCH's
FIRST AND FOURTH TIES PARTS: hBook with
its three tests on the book alone; and hOld, behind the front.

  hBook3_of_fold   the three tests at what the way in lets in: from the three facts along the fold
                   at border k and `DoorKeepsBook` (BookAtDoor.lean); the promise is not spent
  hOld_of_front    **hOld**: ∀ a, the promise → reached → no mark → ∀ t, enter a.1 = .ok t → ∀ fx,
                   K2.frontAt p t = some fx → ∀ κ, old κ < t.book.place.size: from `DoorKeepsBook`
                   and, at every such front: "the state's oracle messages are the front's" (the last
                   clause of the ties' premise hT1) and "the front's statement has the message
                   old κ" (what `hx_of` gives from the test `storedB`: G/SwitchSampleTop.lean)

The end is hOld to the letter at p := pAt m, old := fun κ => (keptK2 r H (placeFrame W n0 olds)
κ).old.

Limits. Both clauses at the front are premises: `hx_of`'s file is not imported. Shown at no real
state. No soundness statement.

-/
import Johnson.Top.H0.K2Caller.BookAtDoor
import Johnson.Top.H0.K2Hears.Long

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)
open VerifiableInference.Desc.K12.Door (Laid atFirstBook atFirstSeats atFirstFits)

variable {P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (k : ℕ) (z : P)

/-- **hBook with its three tests alone.** -/
theorem hBook3_of_fold (Rch : ℕ → First.S × F.E.Str → Prop) (ft : ℕ) (L : Laid)
    (enter : First.S → Except String First.S)
    (hb : ∀ a, Rch k a → a.1.failed = none → atFirstBook ft a.1 = true)
    (hs : ∀ a, Rch k a → a.1.failed = none → atFirstSeats L a.1 = true)
    (hf : ∀ a, Rch k a → a.1.failed = none → atFirstFits a.1 = true)
    (hE : DoorKeepsBook enter) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t →
        atFirstBook ft t = true ∧ atFirstSeats L t = true ∧ atFirstFits t = true := by
  intro a _ hr hm t ht
  obtain ⟨eb, er⟩ := hE _ _ ht
  obtain ⟨e1, e2, e3⟩ := tests_same ft L eb er
  have h0 : a.1.failed = none := not_not.1 hm
  exact ⟨e1.trans (hb a hr h0), e2.trans (hs a hr h0), e3.trans (hf a hr h0)⟩

/-- **hOld, behind the front.** -/
theorem hOld_of_front {K : Type} (old : K → ℕ) (Rch : ℕ → First.S × F.E.Str → Prop) (p : K2.P2)
    (enter : First.S → Except String First.S) (hE : DoorKeepsBook enter)
    (hAt : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        a.1.st.oracles = fx.st.oracles ∧ ∀ κ, ∃ xo, fx.st.oracles[old κ]? = some xo) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ κ, old κ < t.book.place.size := by
  intro a ha hr hm t ht fx hfx κ
  obtain ⟨hor, hx⟩ := hAt a ha hr hm t ht fx hfx
  obtain ⟨xo, hxo⟩ := hx κ
  exact old_of_front N Mg links ps k z enter hE a ha hm ht hor hxo

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hBook3_of_fold
#print axioms VerifiableInference.Desc.First.K2Caller.hOld_of_front
