-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/SecondLaidAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, AT ALL 25 SEGMENTS: TWO OF THE THREE CLAUSES OF
`SecondLaid` (Johnson/Desc/K8/Honest/SecondFew.lean): EVERY MATRIX HAS A SHAPE; THE MATRICES' ARRAYS
DIFFER. UNDER THE SCOPE, THE FILES READ AND IM.Open. Lemmas; none of the library's goals. No prover
stands in them; nothing on completeness, soundness or hiding.

  `made_shapes`   `Made tlc` (Johnson/P1K8R/MadeAtPlans.lean) gives "as many shapes as matrices":
      addTreesF_fits (OnBytes/Tie/Pv/Tail/EndSame.lean). Its first lines are those of the proof of
      `made_sizes`
  **`made_at_built`**   `Made Xl.tl` at each of the 25 built segments: IM.ground_tails
      (Johnson/IMR/K8Seat.lean), `public_made` (MadeAtPlans.lean). The cut into the three sorts is
      that of the proof of IM.k8_tau_128 (Johnson/K8Q14R/TauAt.lean)
  `shapes_at_batch`   carried to the state: LinkJoin.planned_at_batch at the planned reading
      rowsRead (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean, RowsNumberAtBatch.lean)
  **`secondLaid_at_batch`**   `SecondLaid tl G` from "each matrix's array has a virtual row 0":
      the third clause by `oneEach_at_batch` (Johnson/P1K8R/SymbolsAtBatch.lean)
Limits. The second clause of `SecondLaid` (each matrix's array has a virtual row 0) is a premise.
Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.SymbolsAtBatch
import Johnson.Desc.K8.Honest.SecondFew
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.RowsNumberAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- At a record that is made so there are as many shapes as matrices. -/
theorem made_shapes {tlc : HTailF2} (M : Made tlc) : tlc.shp.size = tlc.NM := by
  obtain ⟨tl₀, tl, tl', m, txOf, f, hasU, tau, F, G, T, T', nU, aTX, hb, hbLine, hs, ha, hr⟩ := M
  obtain ⟨-, hz, -⟩ := OnBytes.Tie.Pv.Tail.Port.addTreesF_fits tl tl' F G T T' nU aTX hb hbLine ha
  have cS : tlc.shp = tl'.shp := congrArg (·.shp) hr
  have cN : tlc.NM = tl'.NM := congrArg (·.NM) hr
  rw [cS, cN]
  exact hz

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The data of each built segment are made so.** -/
theorem made_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : Made Xl.tl := by
  obtain ⟨tails, l24, e24, t24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [t24]
    exact (public_made O.public).2.2
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', -⟩ := tails g hg12
    rcases hg with rfl | rfl
    · obtain rfl : x = Xl := Option.some.inj (ex.symm.trans e3)
      rw [etl]
      exact (public_made O.public).1 g hp ehp
    · obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans e3)
      rw [etl']
      exact (public_made O.public).2.1 g a ea

/-- At every state reached in front of a segment's batching there are as many shapes as
matrices. -/
theorem shapes_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : tl.shp.size = tl.NM := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have v : LinkJoin.rowsRead tl = LinkJoin.rowsRead Xl.tl :=
    LinkJoin.of_readTl
      (LinkJoin.planned_at_batch LinkJoin.planned_rows hS hR O hx e3 (z, s) h') tl ht
  have v1 : tl.NM = Xl.tl.NM := congrArg (·.1) v
  have v4 : tl.shp = Xl.tl.shp := congrArg (·.2.2.2) v
  rw [v1, v4]
  exact made_shapes (made_at_built hS hR O hl e3)

/-- **`SecondLaid` AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING, FROM ITS SECOND
CLAUSE.** -/
theorem secondLaid_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) {G : Fork}
    (hr : ∀ mu, mu < tl.NM → Fo.HasRow G (tl.gtTree.getD mu 0) 0) : SecondLaid tl G := by
  obtain ⟨t, a, h1⟩ := oneEach_at_batch hS hR O hl h
  rw [Option.some.inj (a.symm.trans ht)] at h1
  unfold oneEachB at h1
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h1
  refine ⟨Nat.le_of_eq (shapes_at_batch hS hR O hl e3 h ht).symm, hr, fun x hx y hy e => ?_⟩
  rcases h1 y hy x hx with q | q
  · exact q
  · exact absurd e q

end

end P1K8

#print axioms P1K8.made_shapes
#print axioms P1K8.made_at_built
#print axioms P1K8.shapes_at_batch
#print axioms P1K8.secondLaid_at_batch
