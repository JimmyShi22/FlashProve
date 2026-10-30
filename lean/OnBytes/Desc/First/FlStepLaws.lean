-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/FlStepLaws.lean: what the strict reading of a stretch
(OnBytes/Desc/First/FlStep.lean: `plainStretchWith`) gives, as small theorems for all entries and
all rounds: as many rounds as entries; every item of every round is an element of the extension
field; and what a plain round says of its draws. The first two are MEANT FOR the two premises of
a law on `paired` (`Paired.Holds`, declared nowhere in this library, as a text of this project that
is not in this repository words them); that law's file has not been seen here, so the last step onto
its premises' own shape is still to be typed.

Main names (namespace `OnBytes.Desc.First.Kit`): `isElem`; `plainRoundWith_elems`,
`plainRoundWith_draws`; `plainStretchWith_length`, `plainStretchWith_elems`. No axiom beyond Lean's
own. NO SOUNDNESS IS CLAIMED: these say what a test that has said yes has tested.
-/
import OnBytes.Desc.First.FlStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.Kit
open OnBytes

/-- An item of a message that is an element of the extension field. -/
def isElem : Fmt.ItemValue → Bool
  | .e _ => true
  | _ => false

variable (how : Fmt.Entry → RowsHow)

/-- A plain round's items are all elements of the extension field. -/
theorem plainRoundWith_elems {last : Bool} {e : Fmt.Entry} {r : Fmt.RoundView}
    (h : plainRoundWith how last e r = true) : r.vals.all isElem = true := by
  unfold plainRoundWith at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  rw [List.all_eq_true] at h2 ⊢
  intro x hx
  have h3 := h2 x hx
  cases x <;> first | rfl | simp at h3

/-- A plain round drew as many elements as its entry says, no position and no matrix entry. -/
theorem plainRoundWith_draws {last : Bool} {e : Fmt.Entry} {r : Fmt.RoundView}
    (h : plainRoundWith how last e r = true) :
    r.drawn.elems.length = e.drawE ∧ r.drawn.poss.length = 0 ∧ r.drawn.trits.length = 0 := by
  unfold plainRoundWith at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩ := h
  exact ⟨h3, h4.trans h1, h5.trans h2⟩

/-- A plain stretch has as many entries as rounds. -/
theorem plainStretchWith_length : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView),
    plainStretchWith how es rs = true → es.length = rs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [plainStretchWith] at h
  | _ :: _, [], h => by simp [plainStretchWith] at h
  | e :: es, r :: rs, h => by
    simp only [plainStretchWith, Bool.and_eq_true] at h
    simp only [List.length_cons, plainStretchWith_length es rs h.2]

/-- Every item of every round of a plain stretch is an element of the extension field. -/
theorem plainStretchWith_elems : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView),
    plainStretchWith how es rs = true → ∀ r ∈ rs, r.vals.all isElem = true
  | [], [], _ => fun _ hr => by cases hr
  | [], _ :: _, h => by simp [plainStretchWith] at h
  | _ :: _, [], _ => fun _ hr => by cases hr
  | e :: es, r :: rs, h => by
    simp only [plainStretchWith, Bool.and_eq_true] at h
    intro x hx
    cases hx with
    | head => exact plainRoundWith_elems how h.1
    | tail _ hx' => exact plainStretchWith_elems es rs h.2 x hx'

end OnBytes.Desc.First.Kit
