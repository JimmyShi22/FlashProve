-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/RowZero.lean: EVERY ENTRY THAT A CLAIM OF K4's NAMES STANDS IN VIRTUAL ROW 0
OF THE ARRAY OF READS, IF THAT ARRAY HAS AT LEAST AS MANY COLUMNS AS THE READS ARE LONG. K4's own
claims name an entry of the reads as (iU3, e / K3, e % K3) (`Env.U3at`,
OnBytes/Model/LayerForms.lean). Statements and proofs, off `InTab` (TermsEnts.lean),
`front_coveredWith_heard` (CoveredWith.lean), `back_covered_bare` (StackEnts.lean), `hear_public`
(OnBytes/Desc/First/K4/HearPublic.lean).

  `layTables_within`: what `layTables` returns: each family ends at or below the first free entry
    that it returns. The script follows `layTables_chain`
    (Johnson/Road/FormsKeysWorld.lean).
  `hear_tab`: where K4's hearing returns o: each family of o.v.tab ends at or below the plan's
    length of the reads, hp.nU[2] (the hearing's own test "internal-W-length").
  `row_zero`: an entry inside a family that ends at or below n, with n ≤ K3, has row 0 and an index
    below n.
  **`front_row0`**, **`back_row0`**: so, behind the hearing, IF hK : hp.nU[2] ≤ o.v.K3: every entry
    that a form of `formsFrontWith rows` | `formsBack` names is (o.v.iU3, 0, i) with i below
    hp.nU[2]; IN FRONT, AT EITHER FORM OF THE RUN (rows = false is the run that rides where the
    lookup's block states its own claims), UNDER hlv (the lookup's leaves' start form names such
    entries alone) and, where rows = true alone, hK3 (so do its own claims); BEHIND UNDER ONE: he:
    the form in which the lookup's key side ends names no entry (`back_covered_bare`,
    StackEnts.lean: the walk of the batched sumcheck's start form and end forms).

Limits. hK IS A PREMISE ON THE PLAN's MAKE (by a run at honest proofs of both sizes the two numbers
are equal at every layers' place; no theorem). hK3, hlv AND he SPEAK OF WHAT THE LOOKUP RETURNED:
PAID NOWHERE HERE. Nothing on what an entry is worth. Nothing on soundness.
-/
import Johnson.Road.K4.Reads.StackEnts
import Johnson.Road.K4.Reads.CoveredWith
import Johnson.Road.FormsKeysWorld
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Pub Own HPlan2 TableAsk TableAt layParts layTables)
open OnBytes.Road (layParts_le map_some)

/-- Each family that `layTables` lays ends at or below the first free entry that it returns. -/
theorem layTables_within (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    p ≤ r.2.2 ∧ ∀ x ∈ r.1, x.first + x.len ≤ r.2.2
  | [], p, r, h => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    exact ⟨Nat.le_refl _, fun x hx => by simp at hx⟩
  | a :: rest, p, r, h => by
    have hle := layParts_le mats a a.parts p
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      obtain ⟨c1, c2⟩ := layTables_within mats rest _ r' h1
      subst h2
      refine ⟨Nat.le_trans hle c1, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · show p + ((layParts mats a a.parts p).2 - p) ≤ r'.2.2
        omega
      · exact c2 x hx

variable {P : Pub} {hpl : HPlan2} {g : ℕ} {fo : Forest.Heard} {F0 G0 : Fork}
  {t u : OnBytes.K.Kc.Tape} {o : Own}

/-- Behind the hearing each family of tables ends at or below the plan's length of the reads. -/
theorem hear_tab (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) :
    ∀ x ∈ o.v.tab, x.first + x.len ≤ hpl.nU.getD 2 0 := by
  obtain ⟨_, _, iU3, tab, laid, nU3, _, _, _, _, _, _, hl, hn, ev, _⟩ := hear_public hh
  intro x hx
  rw [ev] at hx
  rw [← beq_iff_eq.mp hn]
  exact (layTables_within _ _ 0 _ hl).2 x hx

/-- An entry inside a family that ends at or below n ≤ K3 stands in row 0. -/
theorem row_zero {v : Env} {n : ℕ} (ht : ∀ x ∈ v.tab, x.first + x.len ≤ n) (hK : n ≤ v.K3)
    {a r i : ℕ} (h : inTab v a r i) : a = v.iU3 ∧ r = 0 ∧ i < n := by
  obtain ⟨e, x, hx, _, h2⟩ := h
  have hn := ht x hx
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    exact ⟨e, rfl, by omega⟩
  · have := Nat.le_mul_of_pos_left v.K3 hpos
    omega

/-- **The run "front", at either form, behind the hearing**: hK3 is asked where the lookup's own
claims are listed alone. -/
theorem front_row0 {rows : Bool} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (h : formsFrontWith rows P g o F = some (fs, G))
    (hK3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hlv : InTab o.v o.H.fo.leaves.start) :
    ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
      y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < hpl.nU.getD 2 0 :=
  fun f hf y hy => row_zero (hear_tab hh) hK (front_coveredWith_heard hh h hK3 hlv f hf y hy)

/-- **The run "back", behind the hearing**, if the form in which the lookup's key side ends names no
entry. -/
theorem back_row0 {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (h : formsBack o F = some (fs, G)) (he : o.H.fo.cEnd.ents = #[]) :
    ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
      y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < hpl.nU.getD 2 0 :=
  fun f hf y hy => row_zero (hear_tab hh) hK (back_covered_bare hh he h f hf y hy)

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Desc.First.K4.Reads.layTables_within
#print axioms OnBytes.Desc.First.K4.Reads.hear_tab
#print axioms OnBytes.Desc.First.K4.Reads.front_row0
#print axioms OnBytes.Desc.First.K4.Reads.back_row0
