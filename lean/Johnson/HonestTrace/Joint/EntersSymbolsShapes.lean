-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersSymbolsShapes.lean

Nothing on hiding. No property of the protocol is claimed. Theorems alone, on public data.

"EntryHasTheFillingsShape" (EntersSymbolsFilling.lean) AT EVERY ENTRY OF THE 25 LISTS, in the goals' scope, under ONE premise on public
data: "planesSizes": at the planes' matrix of each link the plan's rows and columns are the filling's. It is typed in the form of the
lookups' premise of that name (their PackedTraceCellsFromLaysFilling.lean), so that their payer (planesSizesAreTheFillingsUnderTheHead)
plugs by a call. Off the planes the library has it ("shapeNo_in_scope").

Main theorems:
* "entry_has_a_name": a number of the plan's list is a number of the filling's list of names.
  (Kin by its name: everyMatrixOfThePlanHasAName, K3/Term/PackedTraceCellsFromLaysFilling.lean:
  the two statements have not been held side by side.)
* "plan_sizes_are_the_fillings": rows and columns, at a matrix of the filling's sizes.
* "entryHasTheFillingsShape_in_scope": the structure, at every entry.

Limits. In scope alone; at "Sz.ref". "planesSizes" is not paid here.
-/
import Johnson.HonestTrace.Joint.EntersSymbolsFilling
import Johnson.HonestTrace.Joint.K3PackedCellsPublic
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.HonestTrace.ShapesAtRefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Meaning (labAt ownerK ownerA sizesOf)
open OnBytes.HonestTrace.PackedCells (number_of_name owner_numbers owner_number_small)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- A segment of a proof with 12 groups has a number below 25. -/
theorem segment_number_below {σ : Seg} (hσ : σ.Below 12) : σ.no 12 < 25 := by
  cases σ with
  | ff g => have : g < 12 := hσ; show 2 * g < 25; omega
  | att g => have : g < 12 := hσ; show 2 * g + 1 < 25; omega
  | head => show 2 * 12 < 25; omega

/-- **A number of the plan's list of matrices is a number of the filling's list of names.** -/
theorem entry_has_a_name (inScope : VerifierAndGoals.InScope Z = true) (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPart : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {m a : ℕ} (hm : m < 25)
    (ha : a < (Meaning.matsAt X m).size) :
    ∃ (σ : Seg) (μ : MatName), σ.Below 12 ∧ σ.no 12 = m ∧ Sz.ref.nameNo σ a = some μ := by
  have C := OnBytes.Road.Hd.core_of_scope inScope filesRead publicPart
  have key : ∀ σ : Seg, σ.Below 12 → σ.no 12 = m → a < Sz.ref.len σ →
      ∃ (σ : Seg) (μ : MatName), σ.Below 12 ∧ σ.no 12 = m ∧ Sz.ref.nameNo σ a = some μ := by
    intro σ hb hn hl
    obtain ⟨μ, hμ⟩ := nameNo_isSome Sz.ref hl
    exact ⟨σ, μ, hb, hn, hμ⟩
  by_cases h24 : m = 24
  · subst h24
    rw [Meaning.size_head publicPart C] at ha
    exact key .head trivial rfl ha
  · by_cases he : m % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, m = 2 * g := ⟨m / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [Meaning.size_even publicPart C hg] at ha
      exact key (.ff g) hg rfl ha
    · obtain ⟨g, rfl⟩ : ∃ g, m = 2 * g + 1 := ⟨m / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [Meaning.size_odd publicPart C hg] at ha
      exact key (.att g) hg rfl ha

/-- **The plan's record has the filling's rows and columns**, at a matrix of the filling's sizes. Off the planes: the library's
"shapeNo_in_scope". At the planes: the premise. -/
theorem plan_sizes_are_the_fillings (inScope : VerifierAndGoals.InScope Z = true)
    (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPart : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {link : ℕ}
    (planesSizes : ∀ number segment, Sz.ref.matAt link number = some (segment, planeOf segment) →
      (sizesOf X link).m number = (Sz.ref.shapeNo link number).1 ∧
        (sizesOf X link).k number = (Sz.ref.shapeNo link number).2)
    {number : ℕ} {σ : Seg} {μ : MatName} (isTheMatrix : Sz.ref.matAt link number = some (σ, μ)) :
    (sizesOf X link).m number = (Sz.ref.shapeNo link number).1 ∧
      (sizesOf X link).k number = (Sz.ref.shapeNo link number).2 := by
  by_cases hp : μ = planeOf σ
  · subst hp
    exact planesSizes number σ isTheMatrix
  · obtain ⟨-, -, hm, hk⟩ := shapeNo_in_scope inScope filesRead publicPart isTheMatrix hp
    rw [planMats_eq] at hm hk
    exact ⟨hm, hk⟩

/-- **Every entry of the 25 lists has the filling's shape**, in scope, where the planes' matrices have. -/
theorem entryHasTheFillingsShape_in_scope (inScope : VerifierAndGoals.InScope Z = true)
    (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPart : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (sizesOf X link).m number = (Sz.ref.shapeNo link number).1 ∧
        (sizesOf X link).k number = (Sz.ref.shapeNo link number).2)
    {m a : ℕ} (hm : m < 25) (ha : a < (sizesOf X m).NM) : EntryHasTheFillingsShape X m a := by
  have C := OnBytes.Road.Hd.core_of_scope inScope filesRead publicPart
  have F := Meaning.follows_sizesOf (Meaning.nmFit_of_core publicPart C)
  have ha' : a < (Meaning.matsAt X m).size := by
    rw [← F.NM m hm]
    exact ha
  obtain ⟨σ, μ, hσ, rfl, hμ⟩ := entry_has_a_name inScope filesRead publicPart hm ha'
  obtain ⟨k1, k2⟩ := owner_numbers inScope filesRead publicPart hσ hμ
  have hmu := number_of_name hσ hμ
  have hb : (Sz.ref.owner σ μ).1.Below 12 := below_of_mu (S := Sz.ref) (by rw [k2]; rfl)
  have hl : ownerK (labAt X (σ.no 12) a) < 25 := by
    rw [k1]
    exact segment_number_below hb
  have hM : Sz.ref.matAt (σ.no 12) a = some (σ, μ) :=
    (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hσ, rfl, hmu⟩
  have hM₀ : Sz.ref.matAt (ownerK (labAt X (σ.no 12) a)) (ownerA (labAt X (σ.no 12) a)) =
      some ((Sz.ref.owner σ μ).1, (Sz.ref.owner σ μ).2) := by
    rw [k1]
    exact (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hb, rfl, k2⟩
  have ho : (Sz.ref.arrayNo (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2).isSome = true :=
    (arrayNo_isSome_iff Sz.ref _ _).2 ⟨by rw [k2]; rfl, owner_owner Sz.ref σ μ⟩
  have eO : Sz.ref.shape (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = Sz.ref.shape σ μ :=
    shape_owner Sz.ref ref_ok.1 σ μ (by rw [hmu]; rfl)
  have eS : Sz.ref.shapeNo (σ.no 12) a = Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [hM]
  have eS₀ : Sz.ref.shapeNo (ownerK (labAt X (σ.no 12) a)) (ownerA (labAt X (σ.no 12) a)) =
      Sz.ref.shape σ μ := by
    unfold Sz.shapeNo
    rw [hM₀]
    exact eO
  obtain ⟨r1, c1⟩ := plan_sizes_are_the_fillings inScope filesRead publicPart (planesSizes _ hm) hM
  obtain ⟨r2, -⟩ := plan_sizes_are_the_fillings inScope filesRead publicPart (planesSizes _ hl) hM₀
  exact ⟨hl, owner_number_small k2, ⟨_, _, hM₀, ho⟩, by rw [r1, eS, eS₀], by rw [c1, eS, eS₀], r2⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.entry_has_a_name
#print axioms OnBytes.HonestTrace.plan_sizes_are_the_fillings
#print axioms OnBytes.HonestTrace.entryHasTheFillingsShape_in_scope
