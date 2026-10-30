-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/JReach.lean: K01_law: A CLOSED TERM FOR THE LETTER J OF k01_fifty_paid (what the exchange's arms may ask of the state in front of a link's reads): «s IS THE STATE OF A REACHED STATEMENT IN FRONT OF SOME LINK's READS, INSIDE THE NARROW PROMISE, WITHOUT A MARK».
Why. J stands in the arms' fence (ReadsFence.inv : J x.2) and is owed along «reached» in front of the 25 reads' places alone (armOk_at_rch's hJ). At J := JReach Rch N Mg that debt is paid by the definition (jReach_at), and every premise behind the fence then speaks of REACHED states alone:
no premise of the arms asks anything of a state that no run reaches. Whatever holds along «reached» in front of the reads follows from J (jReach_elim): so each «J s → …» clause is a fact along «reached», no more.
General in Rch, the numbers, the meaning and the frame.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.K01FiftyR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (S Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open IM (k1Ix)

variable {Pp W : Type} {Fr : Frame} (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (N : Numbers)
  (Mg : Meaning Pp W)

/-- The state of a reached statement in front of some link's reads, inside the promise, without a mark. -/
def JReach (s : S) : Prop :=
  ∃ l, l < 25 ∧ ∃ a, Rch (14 * l + k1Ix l false + 2) a ∧
    onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a ∧ a.1.2.failed = none ∧ a.1.2 = s

/-- **What is owed of J along «reached», at JReach: by the definition.** -/
theorem jReach_at : ∀ l, l < 25 → ∀ a, Rch (14 * l + k1Ix l false + 2) a →
    onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a → a.1.2.failed = none →
    JReach Rch N Mg a.1.2 :=
  fun l hl a hr hon hm => ⟨l, hl, a, hr, hon, hm, rfl⟩

/-- **Whatever holds along «reached» in front of the reads follows from JReach.** -/
theorem jReach_elim (Q : S → Prop)
    (h : ∀ l, l < 25 → ∀ a, Rch (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a → a.1.2.failed = none → Q a.1.2) :
    ∀ s, JReach Rch N Mg s → Q s := by
  rintro s ⟨l, hl, a, hr, hon, hm, rfl⟩
  exact h l hl a hr hon hm

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.jReach_at
#print axioms VerifiableInference.Desc.K1.jReach_elim
