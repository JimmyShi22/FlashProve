-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsNumberAtBatch.lean: THE NUMBER THAT "THE ROWS FIT" BOUNDS
(`rowsFit`,
Johnson/Desc/First/Batch/Law/RowsNumber.lean: v.F.planClaimsF + top8 tlb funs ≤ rows) IS, AT EVERY
STATE
REACHED IN FRONT OF THE BATCHING OF A LAYERS' SEGMENT OR OF THE HEAD, A TERM OFF THE PUBLIC
PARAMETERS. So
"the rows fit" is there ONE CLOSED INEQUALITY A SEGMENT. In the goals' scope. Definitions,
statements
and proofs: the join of three readings.

  `rowsRead tl`: (NM, mats, tau, shp): the four fields of the structure that `top8` reads;
    `planned_rows`: a `Planned` reading (PlannedAtDraw.lean: no sub-protocol between the plan and
    the batching turns it); `top8_congr`: `top8` reads the structure through these four alone.
  `rowsTerm tl n sh`: n + (firstOf tl tl.NM + readsLenOf tl.NM tl.mats sh * tl.stepF).
  `rowsNumber_layers`: **g < 12: reached at 28 g + 9 ⊢ there are the ledger G, the list funs, the
built
    segment Xl and the plan's number n of claims, and AT EVERY STRUCTURE tl' THAT READS AS THE
    STATE's: G.planClaimsF + top8 tl' funs = rowsTerm Xl.tl n (layShapes Bs.G₀.W.layers g).**
  `rowsNumber_head`: **the like at 347: = rowsTerm Xl.tl Bs.G₀.W.H.nLin (shapesOf t0.funs), t0 :=
    tabsOfPlan's.**
THE THREE READINGS: the planned claims (PlanClaimsAtBatch.lean); the structure's four fields
(`planned_at_batch`); the number of reads (ReadsLenOfSkel.lean, HeadSkel.lean).
Limits. THE 12 ATTENTION SEGMENTS ARE NOT HERE: the skeleton of their list of tables is owed. The
closed inequality itself is shown nowhere here. "Reads as the state's": rowsRead tl' = rowsRead of
the state's structure: that the fixed (blanked) structure reads so is the caller's. At the start
`ProofFile.startS Z`. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.HeadSkel
import Johnson.Desc.First.Link.Law.PlanClaimsAtBatch
import Johnson.Desc.First.Link.Law.PlannedAtDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf firstOf)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (readTl)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The four fields of the structure that `top8` reads. -/
def rowsRead (tl : HTailF2) : ℕ × Array TMat × ℕ × Array ShP := (tl.NM, tl.mats, tl.tau, tl.shp)

theorem planned_rows : Planned rowsRead :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- `top8` reads the structure through these four alone. -/
theorem top8_congr {tl tl' : HTailF2} (h : rowsRead tl' = rowsRead tl) (funs : Array HFun) :
    K9L.top8 tl' funs = K9L.top8 tl funs := by
  have h1 : tl'.NM = tl.NM := congrArg (·.1) h
  have h2 : tl'.mats = tl.mats := congrArg (·.2.1) h
  have h3 : tl'.tau = tl.tau := congrArg (·.2.2.1) h
  have h4 : tl'.shp = tl.shp := congrArg (·.2.2.2) h
  unfold K9L.top8 firstOf readsList segsOf HTailF2.stepF
  rw [h1, h2, h3, h4]

/-- The number, off the plan. -/
def rowsTerm (tl : HTailF2) (n : ℕ) (sh : List Tab) : ℕ :=
  n + (firstOf tl tl.NM + readsLenOf tl.NM tl.mats sh * tl.stepF)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE LAYERS' SEGMENTS.** -/
theorem rowsNumber_layers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s')) :
    ∃ G funs Xl n tl, s'.fork? = some G ∧ s'.funs? = some funs ∧ s'.tl? = some tl ∧
      Bs.G₀.built[2 * g]? = some Xl ∧ planClaimsAt Bs.G₀.W (2 * g) = some n ∧
      ∀ tl', rowsRead tl' = rowsRead tl →
        G.planClaimsF + K9L.top8 tl' funs = rowsTerm Xl.tl n (layShapes Bs.G₀.W.layers g) := by
  obtain ⟨funs, f1, f2, f3⟩ := funsSkel_at_batch hS hR O hg h
  have e9 : 28 * g + 9 = 14 * (2 * g) + 9 := by omega
  obtain ⟨G, n, g1, g2, g3⟩ := planClaims_at_batch hS hR O (l := 2 * g) (by omega) (e9 ▸ h)
  obtain ⟨Xl, -, hX, -⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches := by
    unfold P1K8S.stretches
    refine List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), ?_⟩
    have n24 : 2 * g ≠ 24 := by omega
    simp [n24]
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s')
    (by
      show Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 4 + 3 + 2) (z, s')
      have e : 14 * (2 * g) + 4 + 3 + 2 = 28 * g + 9 := by omega
      rw [e]
      exact h)
  obtain ⟨tl, t1, t2⟩ := Option.map_eq_some_iff.1 hr
  refine ⟨G, funs, Xl, n, tl, g1, f1, t1, hX, g2, fun tl' ht => ?_⟩
  rw [top8_congr (ht.trans t2) funs, top8_of_skel Xl.tl funs f3, f2, g3]
  rfl

/-- **AT THE HEAD.** -/
theorem rowsNumber_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s')) :
    ∃ G funs Xl t0 tl, s'.fork? = some G ∧ s'.funs? = some funs ∧ s'.tl? = some tl ∧
      Bs.G₀.built[24]? = some Xl ∧ tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 ∧
      ∀ tl', rowsRead tl' = rowsRead tl →
        G.planClaimsF + K9L.top8 tl' funs =
          rowsTerm Xl.tl Bs.G₀.W.H.nLin (shapesOf t0.funs) := by
  obtain ⟨funs, t0, f1, f0, f2, f3⟩ := headSkel_at_batch hS hR O h
  obtain ⟨G, g1, g3⟩ := planClaims_at_head hS hR O h
  obtain ⟨Xl, hX, -⟩ := (IM.ground_named hS hR O.pub O.blank).2
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches := by
    unfold P1K8S.stretches
    exact List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') h
  obtain ⟨tl, t1, t2⟩ := Option.map_eq_some_iff.1 hr
  refine ⟨G, funs, Xl, t0, tl, g1, f1, t1, hX, f0, fun tl' ht => ?_⟩
  rw [top8_congr (ht.trans t2) funs, top8_of_skel Xl.tl funs f3, f2, g3]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planned_rows
#print axioms VerifiableInference.Desc.LinkJoin.top8_congr
#print axioms VerifiableInference.Desc.LinkJoin.rowsNumber_layers
#print axioms VerifiableInference.Desc.LinkJoin.rowsNumber_head
