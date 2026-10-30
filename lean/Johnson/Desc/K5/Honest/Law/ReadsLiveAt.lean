-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsLiveAt.lean: CONDITIONAL: AT AN ATTENTION SEGMENT, BEHIND THE QUIET
STEP THAT CLOSES THE LIST OF TABLES: A TEST WITH CODE ON WHAT THE SEGMENT's OWN ROUNDS HEARD, under
which the closed list holds, on matrix number NAs and on matrix number NAs + 3, ONE TABLE EACH, LAID
IN VECTOR NUMBER 2, NO ENTRY OF WHOSE WEIGHTS IS THE WORD 0. On the verifier's own functions and
state; no prover in it.

Why. A test of the smallness test's kind asks, for each column of its reads' row, that some table
that is read there has a weight that is not the word 0. Four kinds of tables of an attention segment
have weights that are 0 at every draw (said here without a theorem). On these two matrices a table
of equality weights, and a product of two, of challenges that the segment's own rounds draw, stand
beside them.

The two tables, in the library's written list (`K5Law.laidBy`,
Johnson/Desc/First/Att/Claims/ReadsOfIs.lean):
  on NAs: `eqTab` of the coordinates [lgk, lgk + lt) of the division's sumcheck's challenges;
  on NAs + 3: `blockRows` of `eqTab` of the last ls of the coordinates from lt + lgk on, and of
    `eqTab` of the coordinates [0, lt), of the challenges of the sumcheck "at the index".

Main names:
  `ptE`, `ptFi`, `ptFc`: the three points, off the structure of what was heard.
  `heardReads`: **the test**: the three points have lt, lt and ls coordinates, and each coordinate
    passes `nz01` (Johnson/Desc/K5/Honest/Law/EqTabNz.lean).
  `tables_live`: under it no entry of the two written weights is the word 0.
  `mem_layFrom`: a table of a list is laid in vector number 2.
  `funs_live`: **behind a yes of the quiet step, in the state's closed list.**

The entries are counted to the tables' own lengths T and 2 ^ la: where the function of the tables
returns, its own tests say that these two weights have so many entries (the library's `forced`,
Johnson/Desc/First/Att/Claims/ReadsReturn.lean), and the test's three lengths say how many they
have.

Limits. `funs_live` does not say that the list is closed. Of the segment's other matrices nothing is
said here. The test is sufficient, not necessary. No count of the draws at which it fails. That the
three points have their lengths where the hearing returns is shown in
Johnson/Desc/K5/Honest/Law/ReadRounds.lean (`reads_fit`, `heardReads_of_draws`), not here: the test
asks it.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.EqTabNz
import Johnson.Desc.K5.Honest.Law.ReadsStep
import Johnson.Desc.First.Att.Claims.ReadsApart
import Johnson.Desc.First.Att.Claims.ReadsReturn
import Johnson.Desc.First.Att.Claims.PointsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE isZeroE)
open OnBytes.Model (Reading HTailF2 HFun)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts eqTab blockRows lastCoords chal)
open K5Law (Table layFrom laidBy)

/-- The coordinates [lgk, lgk + lt) of the division's sumcheck's challenges. -/
def ptE (g : Geo) (hh : Heard) : Array E := (chal hh.division).extract g.lgk (g.lgk + g.lt)

/-- The coordinates [0, lt) of the challenges of the sumcheck "at the index". -/
def ptFi (g : Geo) (hh : Heard) : Array E := (chal hh.atIndex).extract 0 g.lt

/-- The last ls of the coordinates from lt + lgk on of the same challenges. -/
def ptFc (g : Geo) (hh : Heard) : Array E :=
  lastCoords ((chal hh.atIndex).extract (g.lt + g.lgk) (chal hh.atIndex).size) g.ls

/-- **The test on what the segment's own rounds heard.** -/
def heardReads (g : Geo) (hh : Heard) : Bool :=
  (ptE g hh).size == g.lt && (ptFi g hh).size == g.lt && (ptFc g hh).size == g.ls &&
    (ptE g hh).all nz01 && (ptFi g hh).all nz01 && (ptFc g hh).all nz01

/-- A point all of whose coordinates pass the test reads 0 or 1 at none. -/
theorem pt_of_all {z : Array E} (h : z.all nz01 = true) :
    ∀ j < z.size, pt Reading.gl z j ≠ 0 ∧ pt Reading.gl z j ≠ 1 := by
  intro j hj
  have h1 := (Array.all_eq_true.1 h) j hj
  unfold pt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
  exact nz01_val h1

/-- **Under the test no entry of the two written weights is the word 0**; and how many entries they
have. Conditional: hp: the function of the points returns; hR: the test. -/
theorem tables_live {g : Geo} {zk : Array (Array E)} {hh : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk hh L = some p) (hR : heardReads g hh = true) :
    (∀ c < 2 ^ g.lt,
      isZeroE ((eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))).getD c zeroE) = false) ∧
    (∀ x < 2 ^ g.ls * 2 ^ g.lt,
      isZeroE ((blockRows (eqTab (lastCoords (p.x.rc g) g.ls)) (eqTab (p.x.ri g))).getD x zeroE) =
        false) ∧
    (eqTab (p.d.scE.r.extract g.lgk (g.lgk + g.lt))).size = 2 ^ g.lt ∧
    (blockRows (eqTab (lastCoords (p.x.rc g) g.ls)) (eqTab (p.x.ri g))).size =
      2 ^ g.ls * 2 ^ g.lt := by
  have PA := K5Law.points_are hp
  unfold heardReads at hR
  simp only [Bool.and_eq_true, beq_iff_eq] at hR
  obtain ⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, a1⟩, a2⟩, a3⟩ := hR
  have e1 : p.d.scE.r.extract g.lgk (g.lgk + g.lt) = ptE g hh := by
    rw [PA.scE]
    rfl
  have e2 : p.x.ri g = ptFi g hh := by
    unfold P.MaxP.ri
    rw [PA.scF]
    rfl
  have e3 : lastCoords (p.x.rc g) g.ls = ptFc g hh := by
    unfold P.MaxP.rc
    rw [PA.scF]
    rfl
  rw [e1, e2, e3]
  refine ⟨fun c hc => eqTab_nz Reading.gl (pt_of_all a1) (by rw [s1]; exact hc), fun x hx =>
    blockRows_eq_nz Reading.gl (pt_of_all a3) (pt_of_all a2) (by rw [s3, s2]; exact hx), ?_, ?_⟩
  · rw [size_eqTab, s1]
  · rw [K5Law.blockRows_size, size_eqTab, size_eqTab, s3, s2]

/-- A table of a list is laid in vector number 2, with its matrix, its length and its weights. -/
theorem mem_layFrom {t : Table} : ∀ (L : List Table) (first : ℕ), t ∈ L →
    ∃ st, (⟨t.mat, t.len, t.phi, 2, st⟩ : P.Fun1) ∈ layFrom first L
  | [], _, h => nomatch h
  | u :: L, first, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨first, List.mem_cons_self⟩
    · obtain ⟨st, hs⟩ := mem_layFrom L (first + u.entries) h
      exact ⟨st, List.mem_cons_of_mem _ hs⟩

/-- **BEHIND A YES OF THE QUIET STEP THE CLOSED LIST HOLDS, ON THE MATRICES NAs AND NAs + 3, A TABLE
IN VECTOR NUMBER 2 NO ENTRY OF WHOSE WEIGHTS, BELOW THE TABLE's OWN LENGTH, IS THE WORD 0.**
Conditional: h: the yes; h5: what the
segment's own rounds heard, in the state in front; hR: the test on it. -/
theorem funs_live (A : OnBytes.Attention.Plan) {m s : S} (h : readsAtSO A m = .ok s) {hh : Heard}
    (h5 : m.heard5? = some hh) (hR : heardReads (P.parCOf A).geo hh = true) :
    ∃ tl, s.tl? = some tl ∧
      (∃ Fn ∈ tl.funs.toList, Fn.mat = (P.parCOf A).geo.NAs ∧ Fn.len = (P.parCOf A).geo.T ∧
        Fn.tree = 2 ∧ ∀ c < Fn.len, isZeroE (Fn.phi.getD c zeroE) = false) ∧
      ∃ Fn ∈ tl.funs.toList, Fn.mat = (P.parCOf A).geo.NAs + 3 ∧
        Fn.len = 2 ^ (P.parCOf A).geo.la ∧ Fn.tree = 2 ∧
        ∀ x < Fn.len, isZeroE (Fn.phi.getD x zeroE) = false := by
  obtain ⟨a, hh', g, p, t, _, e5, _, _, hp, ht, _, _, rfl⟩ := (readsAtSO_iff A m s).1 h
  obtain rfl : hh' = hh := Option.some.inj (e5.symm.trans h5)
  unfold P.ptsFrom at hp
  obtain ⟨Lf, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨l1, l2, z1, z2⟩ := tables_live hp' hR
  have hl := K5Law.tablesP_laid ht
  have hok : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = true := by
    rw [← K5Law.tablesP_isSome, ht]
    rfl
  have f1 : (eqTab (p.d.scE.r.extract (P.parCOf A).geo.lgk
      ((P.parCOf A).geo.lgk + (P.parCOf A).geo.lt))).size = (P.parCOf A).geo.T :=
    K5Law.forced hok .rowsAtProduct (by simp [P.reads]) (by simp [K5Law.theTen])
  have f2 : (blockRows (eqTab (lastCoords (p.x.rc (P.parCOf A).geo) (P.parCOf A).geo.ls))
      (eqTab (p.x.ri (P.parCOf A).geo))).size = 2 ^ (P.parCOf A).geo.la :=
    K5Law.forced hok .queriesAtIndex (by simp [P.reads]) (by simp [K5Law.theTen])
  have back : ∀ f : P.Fun1, f ∈ t.funs.toList → funBack f ∈ ((tabsBack t).funs).toList := by
    intro f hf
    show funBack f ∈ (t.funs.map funBack).toList
    rw [Array.toList_map]
    exact List.mem_map_of_mem hf
  have mr : ∀ {x : Table} {X Y : List Table}, x ∈ Y → x ∈ X ++ Y := fun h =>
    List.mem_append_right _ h
  have ml : ∀ {x : Table} {Y : List Table}, x ∈ [x] ++ Y := List.mem_append_left _
    (List.mem_singleton.2 rfl)
  refine ⟨_, rfl, ?_, ?_⟩
  · obtain ⟨st, hs⟩ := mem_layFrom (t := ⟨(P.parCOf A).geo.NAs, (P.parCOf A).geo.T,
      eqTab (p.d.scE.r.extract (P.parCOf A).geo.lgk ((P.parCOf A).geo.lgk + (P.parCOf A).geo.lt)),
      (P.parCOf A).geo.fillH⟩) (laidBy (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb g) p) 0
      (by
        unfold laidBy
        exact mr (mr (mr (mr (mr (mr ml))))))
    rw [← hl] at hs
    exact ⟨_, back _ hs, rfl, rfl, rfl, fun c hc => l1 c (by rw [← z1, f1]; exact hc)⟩
  · obtain ⟨st, hs⟩ := mem_layFrom (t := ⟨(P.parCOf A).geo.NAs + 3, 2 ^ (P.parCOf A).geo.la,
      blockRows (eqTab (lastCoords (p.x.rc (P.parCOf A).geo) (P.parCOf A).geo.ls))
        (eqTab (p.x.ri (P.parCOf A).geo)),
      (P.parCOf A).geo.fillQ * (P.parCOf A).geo.T / 2 ^ (P.parCOf A).geo.la⟩)
      (laidBy (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb g) p) 0
      (by
        unfold laidBy
        exact mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr (mr ml)))))))))))))))
    rw [← hl] at hs
    exact ⟨_, back _ hs, rfl, rfl, rfl, fun x hx => l2 x (by rw [← z2, f2]; exact hx)⟩

end H2K5.Honest

#print axioms H2K5.Honest.pt_of_all
#print axioms H2K5.Honest.tables_live
#print axioms H2K5.Honest.mem_layFrom
#print axioms H2K5.Honest.funs_live
