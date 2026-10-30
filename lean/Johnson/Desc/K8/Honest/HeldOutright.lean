-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/HeldOutright.lean: THE SMALLNESS TEST: THE PUBLIC TEST `heldPubB`
(Johnson/Desc/K8/Honest/HeldPublic.lean) SAYS YES AT THE DATA OF EACH OF THE 25 BUILT SEGMENTS,
OUTRIGHT: IN THE GOALS' SCOPE, UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN, WITH NO
STATE. Johnson/Desc/K8/Honest/HeldInScope.lean had it where a state is reached: the state served for
one thing, that the digits' array has a column; here that is read off the plan. Lemmas; none of the
library's goals.

  `made_count` at every record that is made as the three plans make it: NM = mats.size
  `cols_at_built` at each built segment the matrices lie one behind the other (the library's
                   DgP.colsTest)
  **`matrix_at_built`** there is a matrix: the draw's block's own test on the plan asks that the
                   lot's list of columns is not empty
  `column_at_built` so the digits' array has a column: 0 < Xl.tl.mz
  **`heldPub_at_built`** heldPubB Xl.tl = true
By: `heldPub_of_made` (HeldInScope.lean) · `made_at_built` (Johnson/P1K8R/SecondLaidAtBatch.lean),
`made_sizes` (MadeAtPlans.lean), `mz_pos` (WantAtBatch.lean) · the library's `public_cols`
(Johnson/Desc/First/Look/ColsAt.lean), IM.ground_tails, IM.k8_tau_128, `sitsAt_open`
(Johnson/P1K8R/OrderAtSeat.lean), `planOk_iff` (Johnson/Desc/First/K8/HearMeans.lean),
Keeps.planOk_blocks, `shapeF_size`, `addTreesF_fits`.
WRITTEN A FURTHER TIME: the lines of `matrix_at_built` that reach the draw's block's test are those
of `matrix_there` (Johnson/P1K8R/WantAtBatch.lean), which goes on to a state; the cases of
`cols_at_built` are those of `made_at_built`.
Limits. UNDER THE DESCRIPTION's TEST ON ITS PLAN: without it nothing says that there is a matrix. IN
SCOPE ALONE: the full size's 25 segments; under an opening of the description. On the plan alone: no
state, no run. No prover stands in it. Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.HeldInScope
import Johnson.Desc.First.Look.ColsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 (planOk_iff atS)
open _root_.P1K8 (Made)

/-- At every record that is made as the three plans make it the number of matrices is the list's
length. -/
theorem made_count {tlc : HTailF2} (M : Made tlc) : tlc.NM = tlc.mats.size := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩ := M
  obtain ⟨-, -, hE⟩ := OnBytes.Tie.Pv.Tail.Port.addTreesF_fits tl tl' F G T T' nU aTX hb hbLine ha
  have a1 : tl'.NM = tl.NM := by rw [hE]
  have a2 : tl'.mats = tl.mats := by rw [hE]
  have b1 : tlc.NM = tl'.NM := congrArg (·.NM) hr
  have b2 : tlc.mats = tl'.mats := congrArg (·.mats) hr
  rw [b1, b2, a1, a2]
  exact (_root_.Fo.shapeF_size hs).1

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At each built segment the matrices lie one behind the other. -/
theorem cols_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : DgP.colsTest Xl.tl = true := by
  obtain ⟨cG, cA, cH⟩ := _root_.Fo.ZPlan.public_cols O.public
  obtain ⟨tails, l24, e24, t24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [t24]
    exact cH
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', -⟩ := tails g hg12
    rcases hg with rfl | rfl
    · obtain rfl : x = Xl := Option.some.inj (ex.symm.trans e3)
      rw [etl]
      exact cG g hp ehp
    · obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans e3)
      rw [etl']
      exact cA g a ea

/-- **At each built segment there is a matrix**, where the description passes its test on its plan:
the draw's block's own test on the plan asks that the lot's list of columns is not empty. -/
theorem matrix_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : 0 < Xl.tl.NM := by
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨Lk, b8, X', -, -, hf8, e3', -, -, hLike, -⟩ := P1K8S.sitsAt_open hS hR O _ hp
  obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
  have hq : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have e := O.desc
    subst e
    exact (Keeps.planOk_blocks _ hOk).1
  have h8 := hq b8 (List.mem_of_getElem? hf8)
  rw [hLike.planOk] at h8
  have hks := ((planOk_iff atS _).1 h8).1
  rw [made_count (_root_.P1K8.made_at_built hS hR O hl e3)]
  have hne : X'.tl.mats.toList.map (·.k) ≠ [] := hks
  have hlen : 0 < (X'.tl.mats.toList.map (·.k)).length := List.length_pos_of_ne_nil hne
  simpa using hlen

/-- **So the digits' array has a column there.** -/
theorem column_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : 0 < Xl.tl.mz :=
  _root_.P1K8.mz_pos (matrix_at_built hS hR O hOk hl e3) (cols_at_built hS hR O hl e3)
    (_root_.P1K8.made_sizes (_root_.P1K8.made_at_built hS hR O hl e3))

/-- **THE PUBLIC TEST SAYS YES AT EACH OF THE 25 BUILT SEGMENTS' DATA, OUTRIGHT.** -/
theorem heldPub_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    heldPubB Xl.tl = true :=
  heldPub_of_made (_root_.P1K8.made_at_built hS hR O hl e3)
    (IM.k8_tau_128 hS hR O (by omega) e3) (column_at_built hS hR O hOk hl e3)

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.made_count
#print axioms VerifiableInference.Desc.First.K8.Honest.cols_at_built
#print axioms VerifiableInference.Desc.First.K8.Honest.matrix_at_built
#print axioms VerifiableInference.Desc.First.K8.Honest.column_at_built
#print axioms VerifiableInference.Desc.First.K8.Honest.heldPub_at_built
