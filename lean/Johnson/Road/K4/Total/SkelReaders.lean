-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/SkelReaders.lean: WHETHER A READER OF THE ENVIRONMENT RETURNS HANGS ON THREE
FIELDS OF THE ENVIRONMENT ALONE: the layout, the tables' places, the reads' number of columns
(EnvSkel, Johnson/Road/K4/Total/Returns.lean). A kit for the parts NormsSkel to EmbedSkel of the law
"behind K4's hearing its two runs of claims return". Statements and proofs.

The listings of claims (OnBytes/Desc/First/K4/Claims.lean) read the tables through the readers of
OnBytes/Model/LayerForms.lean. Each is an Option. Here: at two environments of one skeleton each
reader returns at both or at neither; the two that return numbers or tensors return the same.

  `tabAt_skel`, `tensorAt_skel`: EQUATIONS: the first entry of a family; a tensor with its
    table.
  `U3at_skel`: an entry of the reads as a form. The number of the array (iU3) goes into the form,
    not into the test.
  `limbs_skel`, `shortA_skel`, `longA_skel`, `xbA_skel`, `shIn_skel`, `shA_skel`: a tensor's
    readers.
  `pure_both`: two values that are there.
  `rowCells_skel`, `row5At_skel`, `rowAt_skel`, `rowR_skel`: a norm's row.
  `digitsAt_skel`: the digits of a norm's row (Claims.lean).
No new argument: walks of the texts over Johnson/Road/K4/Total/IsSomeKit.lean.
**Limits.** One premise throughout: EnvSkel v v₀; its payer is whoever holds Skel (its first
clause). CONGRUENCES: no reader is said to return anywhere. Nothing on what a form is worth, nothing
on soundness. K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no member;
by a run at one honest proof of each of two sizes both runs of claims return at all 2 and 12 layers'
places: that run is the member of the law that these serve.


-/
import Johnson.Road.K4.Total.Returns
import Johnson.Road.K4.Total.IsSomeKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Ten)

variable {v v₀ : Env}

/-- The first entry of a family of tables. -/
theorem tabAt_skel (S : EnvSkel v v₀) (n : String) : v.tabAt n = v₀.tabAt n := by
  unfold Env.tabAt
  rw [S.tab]

/-- An entry of the reads, as a form. -/
theorem U3at_skel (S : EnvSkel v v₀) (t i : ℕ) : (v.U3at t i).isSome = (v₀.U3at t i).isSome := by
  unfold Env.U3at
  rw [S.tab, S.K3]
  cases v₀.tab.find? (fun x => x.first == t) with
  | none => rfl
  | some x =>
    show (if (decide (i < x.len) && v₀.K3 != 0 && decide ((t + i) / v₀.K3 < 2 ^ 32)) = true then
        some (Aff.ent v.iU3 ((t + i) / v₀.K3) ((t + i) % v₀.K3)) else none).isSome =
      (if (decide (i < x.len) && v₀.K3 != 0 && decide ((t + i) / v₀.K3 < 2 ^ 32)) = true then
        some (Aff.ent v₀.iU3 ((t + i) / v₀.K3) ((t + i) % v₀.K3)) else none).isSome
    cases (decide (i < x.len) && v₀.K3 != 0 && decide ((t + i) / v₀.K3 < 2 ^ 32)) <;> rfl

theorem limbs_skel (S : EnvSkel v v₀) (t nl : ℕ) (cell : ℕ → ℕ) :
    (v.limbs t nl cell).isSome = (v₀.limbs t nl cell).isSome := by
  unfold Env.limbs
  refine sumForms_same nl fun l _ => ?_
  rw [Option.isSome_map, Option.isSome_map]
  exact U3at_skel S t (cell l)

theorem shortA_skel (S : EnvSkel v v₀) (t : ℕ) (X : Ten) (i j : ℕ) :
    (v.shortA t X i j).isSome = (v₀.shortA t X i j).isSome :=
  limbs_skel S t X.nl _

theorem longA_skel (S : EnvSkel v v₀) (t : ℕ) (X : Ten) (i jh : ℕ) :
    (v.longA t X i jh).isSome = (v₀.longA t X i jh).isSome := by
  unfold Env.longA
  rw [S.y]
  exact limbs_skel S t X.nl _

theorem xbA_skel (S : EnvSkel v v₀) (t kh : ℕ) : (v.xbA t kh).isSome = (v₀.xbA t kh).isSome := by
  unfold Env.xbA
  rw [S.y]
  exact limbs_skel S t _ _

/-- A tensor with the first entry of its matrix's tables at a point. -/
theorem tensorAt_skel (S : EnvSkel v v₀) (X Z : String) : v.tensorAt X Z = v₀.tensorAt X Z := by
  unfold Env.tensorAt
  rw [S.y]
  simp only [tabAt_skel S]

theorem shIn_skel (S : EnvSkel v v₀) (found : Option (Ten × ℕ)) (i j : ℕ) :
    (v.shIn found i j).isSome = (v₀.shIn found i j).isSome :=
  bind_same found fun x => shortA_skel S x.2 x.1 i j

theorem shA_skel (S : EnvSkel v v₀) (X P : String) (i j : ℕ) :
    (v.shA X P i j).isSome = (v₀.shA X P i j).isSome := by
  unfold Env.shA
  rw [tensorAt_skel S]
  exact shIn_skel S _ i j

/-- The cells of a norm's row. -/
theorem rowCells_skel (S : EnvSkel v v₀) (P : String) (i cells : ℕ) :
    (v.rowCells P i cells).isSome = (v₀.rowCells P i cells).isSome := by
  unfold Env.rowCells
  rw [tabAt_skel S, S.y]
  exact bind_same _ fun t => bind_same _ fun trow => amapM_same _ fun j _ => U3at_skel S t _

/-- Two values that are there. (Stated of variables: Lean does not compare the two values.) -/
theorem pure_both {α β : Type} (a : α) (b : β) :
    (pure a : Option α).isSome = (pure b : Option β).isSome := rfl

theorem row5At_skel (S : EnvSkel v v₀) (P : String) (i : ℕ) :
    (v.row5At P i).isSome = (v₀.row5At P i).isSome := by
  unfold Env.row5At
  exact bind_both (rowCells_skel S P i 99) fun _ _ => pure_both _ _

theorem rowAt_skel (S : EnvSkel v v₀) (P : String) (i : ℕ) :
    (v.rowAt P i).isSome = (v₀.rowAt P i).isSome := by
  unfold Env.rowAt
  exact bind_both (rowCells_skel S P i 74) fun _ _ => pure_both _ _

/-- The reciprocal of a norm's row, in either form of the row. -/
theorem rowR_skel (S : EnvSkel v v₀) (P : String) (i : ℕ) :
    (v.rowR P i).isSome = (v₀.rowR P i).isSome := by
  unfold Env.rowR
  rw [S.y]
  cases (v₀.y.h.xl == 5) with
  | true =>
    show ((v.row5At P i).map (·.R)).isSome = ((v₀.row5At P i).map (·.R)).isSome
    rw [Option.isSome_map, Option.isSome_map]
    exact row5At_skel S P i
  | false =>
    show ((v.rowAt P i).map (·.R)).isSome = ((v₀.rowAt P i).map (·.R)).isSome
    rw [Option.isSome_map, Option.isSome_map]
    exact rowAt_skel S P i

/-- The digits of a norm's row. -/
theorem digitsAt_skel (S : EnvSkel v v₀) (P : String) (i : ℕ) :
    (digitsAt v P i).isSome = (digitsAt v₀ P i).isSome := by
  unfold digitsAt
  rw [Option.isSome_map, Option.isSome_map]
  exact rowCells_skel S P i 99

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.tabAt_skel
#print axioms OnBytes.Desc.First.K4.Total.U3at_skel
#print axioms OnBytes.Desc.First.K4.Total.limbs_skel
#print axioms OnBytes.Desc.First.K4.Total.shortA_skel
#print axioms OnBytes.Desc.First.K4.Total.longA_skel
#print axioms OnBytes.Desc.First.K4.Total.xbA_skel
#print axioms OnBytes.Desc.First.K4.Total.tensorAt_skel
#print axioms OnBytes.Desc.First.K4.Total.shIn_skel
#print axioms OnBytes.Desc.First.K4.Total.shA_skel
#print axioms OnBytes.Desc.First.K4.Total.rowCells_skel
#print axioms OnBytes.Desc.First.K4.Total.pure_both
#print axioms OnBytes.Desc.First.K4.Total.row5At_skel
#print axioms OnBytes.Desc.First.K4.Total.rowAt_skel
#print axioms OnBytes.Desc.First.K4.Total.rowR_skel
#print axioms OnBytes.Desc.First.K4.Total.digitsAt_skel
