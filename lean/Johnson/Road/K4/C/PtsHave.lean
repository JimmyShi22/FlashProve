-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PtsHave.lean: CONDITIONAL.

What is here. The hypothesis `PtAt` of Johnson/Road/K4/C/EntsAt.lean, paid at the test «the honest
reads hold the entry's family's weights»: every table that a reader of the verifier picks by a name
prefix@Z has its weights in the honest reads, at all its entries, wherever the point Z stands in the
list of points at which these reads are made, with lt coordinates if Z is a token point and la if it
is a long one (`ptAt_has`). And the three points at which the panels of the batched sumcheck read,
zt, rt and Y, stand so in the honest side's own list (`namedPts`, Johnson/Desc/K4/Honest/Front.lean)
where the lookup's point and the second token sumcheck's end point are whole (`named_three`). By
Johnson/Road/K4/C/HasOf.lean (the reads at a table's entries), AskPoint.lean (the name says the
point, the point the sort), TokReads.lean's fit_found and the library's chain_first and tabAt_mem.

  `PtIn y pt Z`   the point Z stands in the list pt with the number of coordinates of its sort.
  `ptAt_has`   PtAt at the honest reads.
  `find_pass`, `find_stop`, `none_app`, `none_last`, `none_full`   a search through a list laid of
      pieces.
  `named_three`   zt, rt and Y in the honest side's list.

Not shown here. That readsOf and layTables return; that T = 2 ^ lt and ls + lt = la (both follow
from K4Plan; they are asked as they are spent); that the structure's list of tables is the one laid
(ht): hypotheses of ptAt_has. That the lookup's point has at least la coordinates and is not empty,
that its token point and the end point rt have lt coordinates, that lt is not 0: hypotheses of
named_three. No example is known. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Road.K4.C.EntsAt
import Johnson.Road.K4.C.HasOf
import Johnson.Road.K4.C.AskPoint
import Johnson.Road.K4.C.TokReads
import Johnson.Road.K4.C.NamedPart
import Johnson.Road.K4.C.TermsAtOf
import Johnson.Road.FormsKeysWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay TableAsk TableAt layTables tableAsks readsOf)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts matsOf readsAt wtsFit namedPts ztOf)

/-- The point Z stands in the list with the number of coordinates of its sort. This defines a
hypothesis; the definition claims nothing. -/
def PtIn (y : Lay) (pt : List (String × Array E)) (Z : String) : Prop :=
  (Z ∈ ["zt", "P_V", "r_tV", "rt"] ∧
      ∃ p, (pt.find? fun q => q.1 == Z) = some p ∧ p.2.size = y.h.lt) ∨
    (Z ∈ ["Z", "Z_V", "Y", "Z_a", "Z_b", "Z_E"] ∧
      ∃ p, (pt.find? fun q => q.1 == Z) = some p ∧ p.2.size = y.h.la)

variable {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {pt : List (String × Array E)}
  {R : OnBytes.Desc.First.K4.Honest.Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **PtAt AT THE HONEST READS.** CONDITIONAL: on every hypothesis named. -/
theorem ptAt_has (hrd : readsOf Q.P.y = .ok Q.P.rd)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hR : readsAt Q w fo pt = some R) (hT : Q.P.y.T = 2 ^ Q.P.y.h.lt)
    (hla : Q.P.y.ls + Q.P.y.h.lt = Q.P.y.h.la) {v : Env} (ht : v.tab = r.1) :
    PtAt v (fun e => R.has e = true) (PtIn Q.P.y pt) := by
  intro mn hmn Z t hZ htb x hx e h1 h2
  have hm : '@' ∉ mn.toList := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmn
    rcases hmn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨x0, hx0, hn0, hf0⟩ := tabAt_mem htb
  obtain ⟨hc, _⟩ := layTables_chain _ _ 0 r hl
  have e0 := chain_first r.1 0 hc x0 (by rw [← ht]; exact hx0)
  rw [hf0, ← ht, hx] at e0
  obtain rfl := Option.some.inj e0
  obtain ⟨q, hq, n1, _, H⟩ := has_in_table hR hl (by rw [← ht]; exact hx0)
  obtain ⟨_, L2⟩ := laid_of_layTables _ _ _ _ hl
  have hqa : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map_of_mem hq
  have hp : q.1.point = Z := point_of_name hqa hm (n1.symm.trans hn0)
  show R.has e = true
  rw [H e h1 h2]
  rcases hZ with ⟨hs, p, hf, hsz⟩ | ⟨hs, p, hf, hsz⟩
  · obtain ⟨a1, a2⟩ := short_of_point hrd hqa (by rw [hp]; exact hs)
    have he : q.1.point.isEmpty = false := by
      rw [hp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> rfl
    rw [fit_found he (p := p) (by rw [hp]; exact hf), a1, a2, hsz, hT]
    simp
  · obtain ⟨a1, a2⟩ := long_of_point hrd hqa (by rw [hp]; exact hs)
    have he : q.1.point.isEmpty = false := by
      rw [hp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [fit_found he (p := p) (by rw [hp]; exact hf), a1, a2, hsz, hla]
    simp

/-! ## The honest side's own list of points -/

/-- A search passes a piece in which nothing is found. -/
theorem find_pass {α : Type} {f : α → Bool} {l1 l2 : List α} (h : l1.find? f = none) :
    (l1 ++ l2).find? f = l2.find? f := by
  rw [List.find?_append, h]
  rfl

/-- It stops in a piece in which something is found. -/
theorem find_stop {α : Type} {f : α → Bool} {l1 : List α} (l2 : List α) {a : α}
    (h : l1.find? f = some a) : (l1 ++ l2).find? f = some a := by
  rw [List.find?_append, h]
  rfl

/-- Nothing is found in two pieces in neither of which something is found. -/
theorem none_app {α : Type} {f : α → Bool} {l1 l2 : List α} (h1 : l1.find? f = none)
    (h2 : l2.find? f = none) : (l1 ++ l2).find? f = none := by
  rw [List.find?_append, h1, h2]
  rfl

/-- A piece that holds at most the last coordinates of a point, under another name. -/
theorem none_last {la : ℕ} {n tg : String} (z : Array E) (hne : (n == tg) = false) :
    ((match (lastOf z la).toOption with
      | some x => if z.isEmpty then [] else [(n, x)]
      | none => []) : List (String × Array E)).find? (fun q => q.1 == tg) = none :=
  List.find?_eq_none.mpr fun q hq => by
    obtain ⟨_, x, _, rfl⟩ := mem_last hq
    simp [hne]

/-- A piece that holds at most a whole point, under another name. -/
theorem none_full {n tg : String} (k : ℕ) (z : Array E) (hne : (n == tg) = false) :
    ((if (z.size == k && k != 0) = true then [(n, z)] else []) :
      List (String × Array E)).find? (fun q => q.1 == tg) = none :=
  List.find?_eq_none.mpr fun q hq => by
    obtain ⟨_, _, rfl⟩ := mem_full hq
    simp [hne]

/-- **zt, rt AND Y STAND IN THE HONEST SIDE's LIST.** CONDITIONAL: on every hypothesis named. -/
theorem named_three {p : Pts} {z : Array E} (hz : (lastOf p.fo.zx Q.P.y.h.la).toOption = some z)
    (h0 : p.fo.zx.isEmpty = false) (hzt : (ztOf Q p).size = Q.P.y.h.lt)
    (hrt : p.rt.size = Q.P.y.h.lt) (hlt : Q.P.y.h.lt ≠ 0)
    (hla : Q.P.y.ls + Q.P.y.h.lt = Q.P.y.h.la) :
    PtIn Q.P.y (namedPts Q p) "zt" ∧ PtIn Q.P.y (namedPts Q p) "rt" ∧
      PtIn Q.P.y (namedPts Q p) "Y" := by
  have hzs : z.size = Q.P.y.h.la := lastOf_size hz
  have c1 : ((ztOf Q p).size == Q.P.y.h.lt && Q.P.y.h.lt != 0) = true := by simp [hzt, hlt]
  have c2 : (p.rt.size == Q.P.y.h.lt) = true := by simp [hrt]
  refine ⟨Or.inl ⟨by decide, ("zt", ztOf Q p), ?_, hzt⟩, Or.inl ⟨by decide, ("rt", p.rt), ?_, hrt⟩,
    Or.inr ⟨by decide, ("Y", longPoint (z.extract 0 Q.P.y.ls) p.rt), ?_, ?_⟩⟩
  · unfold namedPts
    dsimp only
    rw [hz]
    simp only [h0, c1, c2, Bool.false_eq_true, if_false, if_true]
    exact find_stop _ (find_stop _ (find_stop _ (find_stop _ (find_stop _ (find_stop _
      (find_stop _ (by simp)))))))
  · unfold namedPts
    dsimp only
    rw [hz]
    simp only [h0, c1, c2, Bool.false_eq_true, if_false, if_true]
    exact find_stop _ ((find_pass (none_app (none_app (none_app (none_app (none_app (by simp)
      (none_last _ (by decide))) (none_full _ _ (by decide))) (none_full _ _ (by decide)))
      (none_full _ _ (by decide))) (none_last _ (by decide)))).trans (by simp))
  · unfold namedPts
    dsimp only
    rw [hz]
    simp only [h0, c1, c2, Bool.false_eq_true, if_false, if_true]
    exact find_stop _ ((find_pass (none_app (none_app (none_app (none_app (none_app (by simp)
      (none_last _ (by decide))) (none_full _ _ (by decide))) (none_full _ _ (by decide)))
      (none_full _ _ (by decide))) (none_last _ (by decide)))).trans (by simp))
  · unfold longPoint
    rw [Array.size_append, Array.size_extract, hrt, hzs]
    omega

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ptAt_has
#print axioms OnBytes.Road.K4.C.find_pass
#print axioms OnBytes.Road.K4.C.find_stop
#print axioms OnBytes.Road.K4.C.none_app
#print axioms OnBytes.Road.K4.C.none_last
#print axioms OnBytes.Road.K4.C.none_full
#print axioms OnBytes.Road.K4.C.named_three
