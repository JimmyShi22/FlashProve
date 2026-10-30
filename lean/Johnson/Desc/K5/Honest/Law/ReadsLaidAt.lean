-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsLaidAt.lean: CONDITIONAL: AT AN ATTENTION SEGMENT, BEHIND THE QUIET
STEP THAT CLOSES THE LIST OF TABLES: EVERY TABLE OF THE LIBRARY's WRITTEN LIST STANDS IN THE STATE's
LIST, IN VECTOR NUMBER 2, WITH ITS MATRIX, ITS LENGTH AND ITS WEIGHTS; its length is not 0
and divides the number of rows of the plan's matrix. On the verifier's own functions and state; no
prover in it.

Why. Johnson/Desc/K5/Honest/Law/ReadsLiveAt.lean and LiveValAt.lean show this of two tables of the
written list (`K5Law.laidBy`, Johnson/Desc/First/Att/Claims/ReadsOfIs.lean). Their proofs name the
table in two places alone: where it stands in the list, and that its weights do not read 0. Here the
table is a letter, so that whoever wants a third table shows these two facts and no more.

Main names:
  `LaidIn`: a table of the written list as the state's list holds it.
  `funs_of_laid`: **behind a yes of the quiet step**: the open segment, what its own rounds heard,
    what the lookup on the calls left, the points, the yes of the library's test on the placing, and
    `LaidIn` at every table of the written list at these.
  `out_size`: how many entries the table on the matrix NAs + 1 has.
  `mats_of_plan`: the plan's list has just NAs + 4 matrices.

How. `readsAtSO_iff` (Johnson/Desc/K5/Honest/Law/ReadsStep.lean) opens the yes; the library's
`tablesP_laid` and `tablesP_fits` (Johnson/Desc/First/Att/Claims/ReadsApart.lean) say what the
function of the tables lays and that each table passes its test; `mem_layFrom` and `fits_at` are the
two files' own.

Limits. It does not say that the list is closed. THE MATRIX IS THE PLAN's (A.mats), NOT THE STATE's
(tl.mats), as in LiveValAt.lean. Nothing is said of any weight.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.LiveValAt
import Johnson.Desc.First.Att.ArmAttPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Reading HTailF2 HFun TMat)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Pts)
open K5Law (Table layFrom laidBy)

/-- **A table of the written list as the state's list holds it**: in vector number 2, with the
table's matrix, length and weights; the length is not 0 and divides the number of rows of that
matrix in the list mats (taken as 0 if mats has no such matrix). -/
def LaidIn (mats : Array TMat) (tl : HTailF2) (t : Table) : Prop :=
  ∃ Fn ∈ tl.funs.toList, Fn.mat = t.mat ∧ Fn.len = t.len ∧ Fn.phi = t.phi ∧ Fn.tree = 2 ∧
    0 < Fn.len ∧ (mats.getD t.mat {}).m % Fn.len = 0

/-- **BEHIND A YES OF THE QUIET STEP EVERY TABLE OF THE WRITTEN LIST STANDS IN THE STATE's LIST.**
Conditional: h: the yes. a: the open segment in front; hh: what its own rounds heard; g: what the
lookup on the calls left; p: the points. -/
theorem funs_of_laid (A : OnBytes.Attention.Plan) {m s : S} (h : readsAtSO A m = .ok s) :
    ∃ a hh g p tl, m.here = .att a ∧ m.heard5? = some hh ∧ a.g = some g ∧
      P.ptsFrom (P.parCOf A).geo g.zk hh a.F = some p ∧
      K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
        (P.lookOfO (P.parCOf A).geo.lmb g) p = true ∧
      s.tl? = some tl ∧
      ∀ t ∈ laidBy (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb g) p, LaidIn A.mats tl t := by
  obtain ⟨a, hh, g, p, t, ea, e5, eg, _, hp, ht, _, _, rfl⟩ := (readsAtSO_iff A m s).1 h
  have hl := K5Law.tablesP_laid ht
  have hfit := List.all_eq_true.1 (K5Law.tablesP_fits ht)
  have hok : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = true := by
    rw [← K5Law.tablesP_isSome, ht]
    rfl
  refine ⟨a, hh, g, p, _, ea, e5, eg, hp, hok, rfl, fun u hu => ?_⟩
  obtain ⟨p1, q1⟩ := fits_at (mats := A.mats) (hfit u hu)
  obtain ⟨st, hs⟩ := mem_layFrom _ 0 hu
  rw [← hl] at hs
  refine ⟨funBack ⟨u.mat, u.len, u.phi, 2, st⟩, ?_, rfl, rfl, rfl, rfl, p1, q1⟩
  show funBack _ ∈ (t.funs.map funBack).toList
  rw [Array.toList_map]
  exact List.mem_map_of_mem hs

/-- Where the library's test on the placing says yes, the table on the matrix NAs + 1 has 2 ^ la
entries: the library's `forced` (Johnson/Desc/First/Att/Claims/ReadsReturn.lean), called.
Conditional: hok. -/
theorem out_size {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : P.LookIn} {p : Pts}
    (hok : K5Law.placeOk g mats nW lk p = true) :
    (P.blockRows (P.eqTab (P.lastCoords p.d.zcW g.ls)) (P.eqTab p.d.ziW)).size = 2 ^ g.la :=
  K5Law.forced hok .outAtDivide (by simp [P.reads]) (by simp [K5Law.theTen])

/-- **The plan's list has just NAs + 4 matrices**: the library's `ofPlan_size`
(Johnson/Desc/First/Att/ArmAttPublic.lean) and `ofPlan_nm`
(Johnson/Desc/First/Att/Claims/OfPlan.lean), called. Conditional: hP: the plan is a planner's
return, but for the readers' records of shared matrices. -/
theorem mats_of_plan {A : OnBytes.Attention.Plan} (hP : K5Law.OfPlan A) :
    A.mats.size = (P.parCOf A).geo.NAs + 4 := by
  show A.seam.tl.mats.size = A.S.cf.NAs + 4
  rw [← K5Law.ofPlan_size hP, K5Law.ofPlan_nm hP]

end H2K5.Honest

#print axioms H2K5.Honest.mats_of_plan
#print axioms H2K5.Honest.funs_of_laid
#print axioms H2K5.Honest.out_size
