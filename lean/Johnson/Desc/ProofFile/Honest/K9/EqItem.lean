-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqItem.lean: FOR THE ITEM "totalB": THE FORM IN WHICH AN ENTRY's TERMS ARE TIED TO
THE TABLE's ITEM: AN EQUATION OF LISTS WITH THE ENTRY's OWN TERMS NAMED; AND FROM IT AND THE TABLE's SENTENCE "forms":
EVERY COEFFICIENT IS 0. A definition, a statement and its proof; no goal is stated.
  `ItemEq`   a definition: at the state s with K9's part b: the link's reader answers R at the entry o, and at every
      first number n the coefficients of tmOf o n, at what is fixed at s and the data that the tables rd hold at b,
      are, in a row, the worths of R's forms in the item's own world
  `fx_self`   the state goes on from what is fixed at it, under the promise at what is fixed (the library lays that
      term in line, four times; it has no name there)
  **`zeros_of_eq`**   `ItemEq` and `Sound.formsQ` at o ⊢ every coefficient of tmOf o n is 0: what `ItemBack`
      (Honest/K9/TotalFront.lean) ends in
WHY. The library's clauses on an item (`ItemAt`, `ItemIn`, Johnson/Desc/First/Link/Law/HitemsStill.lean) say "THERE
ARE runs of the link whose values in a row are (hold) the forms' worths": which runs is not said, so nothing follows
for the entry's own terms. `ItemEq` is concluded, under premises, in Honest/K9/EqK4.lean, EqStill.lean, EqMarks.lean,
EqAt.lean. `zeros_of_eq` is called by Honest/K9/EqCarry.lean and BackAt.lean.
WHAT IS NOT CLAIMED. `ItemEq` or "forms" at any state. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Link.Law.HitemsStill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc

variable {α : Type}

/-- **The equation of lists, with the entry's own terms named.** -/
def ItemEq (φ : S → α) (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (Rd : Desc.K9.Readers) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String) (s : S)
    (b : Desc.K9.Part) : Prop :=
  ∃ R, Rd.forms o.1 o.2 s = some R ∧ ∀ n, (tmOf o n (fixed9 φ s) (dataQ own b rd)).map (·.2) =
    R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b rd))

/-- The state goes on from what is fixed at it, under the promise. -/
theorem fx_self (φ : S → α) (Ok : α × Option Pub9 → Prop) (s : S) (b : Desc.K9.Part)
    (hb : atS.get? s = some b) (hOk : Ok (fixed9 φ s)) : Fx9 φ Ok (fixed9 φ s) s := by
  have hq2 : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  exact ⟨hOk, rfl, pubOf b, b, hq2, hb, goesOn_refl b⟩

/-- **From the equation and the sentence "forms": zeros.** -/
theorem zeros_of_eq (φ : S → α)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)) (Rd : Desc.K9.Readers)
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String) (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hE : ItemEq φ tmOf Rd own rd o s b) (hQ : formsQ Rd own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 φ s) (dataQ own b rd), c.2 = 0 := by
  obtain ⟨R, hR, e⟩ := hE
  obtain ⟨a, R', ha, hR', -, hf⟩ := hQ
  obtain rfl : b = a := Option.some.inj ((Desc.K9.segAt_of_atS s b hb).symm.trans ha)
  obtain rfl : R = R' := Option.some.inj (hR.symm.trans hR')
  intro n c hc
  have hm : c.2 ∈ (tmOf o n (fixed9 φ s) (dataQ own b rd)).map (·.2) := List.mem_map.2 ⟨c, hc, rfl⟩
  rw [e n] at hm
  obtain ⟨g, hg, eg⟩ := List.mem_map.1 hm
  rw [← eg]
  exact (hf g hg).2

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.fx_self
#print axioms ProofFile.Honest.K9.zeros_of_eq
