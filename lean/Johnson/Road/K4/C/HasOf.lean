-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/HasOf.lean: CONDITIONAL.

What is here. When does the honest side's valuing of a form return? `valAff?`
(Johnson/Desc/K4/Honest/Cells.lean) returns just where the test `affFits` answers true: each entry
that the form names lies in the array of the reads, in a family whose weights the honest reads hold.
Three general laws towards that yes, from the return of the verifier's own laying of the tables
(`layTables`): the honest reads are made, at every list of points (`readsAt_of_lay`); at every entry
of a table of the verifier's list they hold the family's weights just where the family's own test on
the points' sizes answers true (`has_in_table`); and a form all of whose entries lie in one such
table passes affFits where that test answers true (`affFits_of_inOne`), which holds of each form
that the verifier's reader of one entry returns (`inOne_U3at`). The rules for sums of forms are the
library's (`EntsIn`, Johnson/Road/K4/Reads/EntsIn.lean).

  `readsAt_of_lay`   the honest reads are made.
  `has_in_table`   the reads at an entry of a table.
  `InOne v x f`   each entry that f names lies in the array of the reads, inside the table x.
  `inOne_U3at`   the verifier's reader of one entry.
  `affFits_of_inOne`   the test answers true.

Not shown here. That layTables returns (hl): a hypothesis. That a family's test on the points' sizes
answers true; which family a reader's table is of; that the verifier's readers return: not here. No
example is known. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Road.K4.C.ReadsKit
import Johnson.Road.K4.C.Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env TableAsk TableAt layTables tableAsks)
open OnBytes.Desc.First.K4.Reads (EntsIn entsIn_ent)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads matsOf laidOf famsAt readsAt wtsFit affFits)

variable {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {pt : List (String × Array E)} {R : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **The honest reads are made**, at every input, at whatever the lookup has sampled, at every list
of points. CONDITIONAL: on hl. -/
theorem readsAt_of_lay (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (w : K4In) (fo : Forest.Heard) (pt : List (String × Array E)) :
    ∃ R, readsAt Q w fo pt = some R := by
  unfold readsAt famsAt laidOf
  rw [hl]
  exact ⟨_, rfl⟩

/-- An entry of a family's stretch lies in one of its parts. -/
theorem part_of_entry (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {q : TableAsk × List (ℕ × ℕ)} (hq : q ∈ r.2.1) {e : ℕ} (h1 : famFirst q ≤ e)
    (h2 : e < famFirst q + famLen (matsOf Q) q) :
    ∃ m ∈ q.2, ∃ j, j < wd (matsOf Q) q.1.L m.1 ∧ e = m.2 + j := by
  obtain ⟨L1, _⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨p1, p2⟩ := laid_mem (matsOf Q) r.2.1 0 L1 q hq
  obtain ⟨m, hm, a, b⟩ := parts_cover (matsOf Q) q.1 q.1.parts (famFirst q) e h1
    (by rw [← p2]; exact h2)
  exact ⟨m, by rw [p1]; exact hm, e - m.2, by omega, by omega⟩

/-- **The reads at an entry of a table of the verifier's list.** CONDITIONAL: on hR and hl. -/
theorem has_in_table (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) {x : TableAt}
    (hx : x ∈ r.1) :
    ∃ q ∈ r.2.1, x.name = q.1.name ∧ x.first = famFirst q ∧
      ∀ e, x.first ≤ e → e < x.first + x.len → R.has e = wtsFit Q.P.y fo pt q.1 := by
  obtain ⟨q, hq, e1, e2, e3⟩ := tab_of_lay _ _ _ _ hl x hx
  refine ⟨q, hq, e1, e2, fun e h1 h2 => ?_⟩
  obtain ⟨m, hm, j, hj, rfl⟩ := part_of_entry hl hq (e := e) (by rw [← e2]; exact h1)
    (by rw [← e3]; exact h2)
  exact (fam_at hR hl hq hm hj).2.1

/-- Each entry that the form names lies in the array of the reads, inside the table x. -/
abbrev InOne (v : Env) (x : TableAt) (f : Aff) : Prop :=
  EntsIn (fun t rw i => t = v.iU3 ∧ x.first ≤ rw * v.K3 + i ∧ rw * v.K3 + i < x.first + x.len) f

/-- **The verifier's reader of one entry**: the entry lies in the table that begins at t. -/
theorem inOne_U3at {v : Env} {t i : ℕ} {f : Aff} {x : TableAt}
    (hx : (v.tab.find? fun x => x.first == t) = some x) (h : v.U3at t i = some f) :
    InOne v x f := by
  unfold Env.U3at at h
  rw [hx] at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    have hf : x.first = t := by
      have h1 := List.find?_some hx
      simpa using h1
    have hi : i < x.len := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.1
    have e : (t + i) / v.K3 * v.K3 + (t + i) % v.K3 = t + i := Nat.div_add_mod' _ _
    exact entsIn_ent ⟨rfl, by rw [e]; omega, by rw [e]; omega⟩
  · cases h

/-- **The test answers true.** -/
theorem affFits_of_inOne {v : Env} {x : TableAt} {f : Aff} (I : InOne v x f)
    (hh : ∀ e, x.first ≤ e → e < x.first + x.len → R.has e = true) : affFits v R f = true := by
  unfold affFits
  rw [Array.all_eq_true']
  intro y hy
  obtain ⟨a, b, c⟩ := I y (Array.mem_toList_iff.mpr hy)
  rw [Bool.and_eq_true]
  exact ⟨by rw [a]; exact beq_self_eq_true _, hh _ b c⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.readsAt_of_lay
#print axioms OnBytes.Road.K4.C.part_of_entry
#print axioms OnBytes.Road.K4.C.has_in_table
#print axioms OnBytes.Road.K4.C.inOne_U3at
#print axioms OnBytes.Road.K4.C.affFits_of_inOne
