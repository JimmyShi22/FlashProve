-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TermsPubKit.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the second token
sumcheck: seven public facts on what the two jobs share (Sides, Johnson/Desc/K4/Honest/Sides.lean),
from the return of Sides.of and the plan's public facts: the seven clauses laid, asks, y, low, T,
Tc, rowsOfT of the hypothesis TermsPub (Johnson/Desc/ProofFile/Honest/K4/Law/TermsAll.lean), each
in that clause's own text. Statements and proofs.

  `sides_more`     what Sides.of lays besides: the structure that the rotation factor reads; the
                   gated products' table.
  `sides_laid`     layTables returns.
  `sides_low`      the first coordinates of the long tables' point are ls in number.
  **`sides_seven`**  the seven together.

Not shown here. That a plan with the public facts K4Plan exists, or that the honest side's function
Sides.of returns anywhere: no example is known. K4Plan can hold only at shapes with routed experts,
under the library's eleven switches (its field sw). Public numbers and sizes alone.
No property is claimed.
-/
import Johnson.Road.K4.C.TermsAtOf
import Johnson.Road.K4.C.StackIs
import Johnson.Road.K4.C.TokAsksOf
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.PlanClauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (layTables tableAsks)
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides}

/-- **What Sides.of lays besides**: the structure that the rotation factor reads holds the forms'
own structure; the gated products' table has 2 ^ muH entries. -/
theorem sides_more (h : Sides.of Q w p = some S) :
    S.ce.v = S.v ∧ S.hh.size = 2 ^ Q.P.rd.muH := by
  unfold Sides.of at h
  obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨TS, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Z, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cls, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨x, lfc⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨opens, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨gl, gr⟩, hg, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ends, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  refine ⟨rfl, ?_⟩
  show ((Array.range gl.size).map _).size = _
  rw [Array.size_map, Array.size_range]
  unfold gatedTabs at hg
  obtain ⟨ts, _, hg⟩ := Option.bind_eq_some_iff.1 hg
  obtain ⟨tu, _, hg⟩ := Option.bind_eq_some_iff.1 hg
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hg)
  unfold layerTab
  exact Array.size_ofFn

/-- layTables returns: Sides.of has called it. -/
theorem sides_laid (h : Sides.of Q w p = some S) :
    ∃ r, layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r := by
  obtain ⟨_, _, _, hv, _⟩ := sides_fields h
  unfold envOf at hv
  obtain ⟨iU3, _, hv⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨r, hr, _⟩ := Option.bind_eq_some_iff.mp hv
  exact ⟨r, hr⟩

/-- The first coordinates of the long tables' point are ls in number. -/
theorem sides_low (h : Sides.of Q w p = some S) (hls : Q.P.y.ls ≤ Q.P.y.h.la) :
    S.zlow.size = Q.P.y.ls := by
  obtain ⟨_, _, _, _, ⟨Z, hZ, e⟩, _⟩ := sides_fields h
  rw [e, Array.size_extract, lastOf_size hZ]
  omega

/-- **THE SEVEN PUBLIC CLAUSES**, each in TermsPub's own text. CONDITIONAL: on A and h. -/
theorem sides_seven {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}
    (A : K4Plan hS pc Q.P Q.g tl D) (h : Sides.of Q w p = some S) :
    (∃ r, layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r) ∧ TokAsks S.Q ∧
      S.v.y = S.Q.P.y ∧ S.zlow.size = S.v.y.ls ∧ S.v.y.T = 2 ^ S.v.y.h.lt ∧
      S.ce.v.y.T ≤ 2 ^ S.v.y.h.lt ∧ S.hh.size % S.v.y.T = 0 := by
  obtain ⟨hQ, _, _, hv, _⟩ := sides_fields h
  obtain ⟨hce, hhh⟩ := sides_more h
  have hy : S.v.y = Q.P.y := envOf_y hv
  have Ad := admitted_of_layout A.lay A.sw.p3
  have L2 := laid2_of_layout A.lay
  have hla : Q.P.y.ls ≤ Q.P.y.h.la := by
    rw [Ad.shape, Ad.la]
    exact Nat.le_add_right _ _
  obtain ⟨_, m2, _⟩ := Fo.readsOf_mu A.reads
  rw [hQ, hce, hy]
  refine ⟨sides_laid h, tokAsks_of_readsOf A.reads, rfl, sides_low h hla, L2.T,
    Nat.le_of_eq L2.T, ?_⟩
  rw [hhh, m2, L2.T, Nat.pow_add]
  exact Nat.mul_mod_left _ _

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sides_more
#print axioms OnBytes.Road.K4.C.sides_laid
#print axioms OnBytes.Road.K4.C.sides_low
#print axioms OnBytes.Road.K4.C.sides_seven
