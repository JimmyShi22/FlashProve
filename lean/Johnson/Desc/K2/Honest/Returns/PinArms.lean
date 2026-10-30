-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/PinArms.lean: THE EIGHT CLAUSES OF Returns/PinReached.lean
(`ShapeFits`) AND THE TWO THAT FOLLOW, AT THE TWO OTHER PLACES OF A SWITCH, IN THE GOALS' SCOPE AND
UNDER THE SAME THREE NAMED TESTS ON THE PUBLIC PART: AT THE HEAD's FRONT AT A STATE REACHED IN FRONT
OF THE OUTPUT HEAD's SWITCH (NUMBER 339), AND AT THE FINISH's FRONT BEHIND THE WAY IN AT A STATE
REACHED IN FRONT OF THE FINISH's SWITCH (NUMBER 353). Statements with their proofs: calls.

  `head_pinned_reached`, `fin_pinned_reached` the library's test `frontB2` accepts the front, at the
                    written front of the place (entries 23 and 24 of the table) and its frame; and
                    the front's statement has `SampleGoodS`
  `head_shape_reached`, `fin_shape_reached` `ShapeFits` at the front
  `head_reads_paid`, `fin_reads_paid` `FrontCore.reads` there
  `head_tables_paid`, `fin_tables_paid` `TablesFit.stored` there, where each copy has a main row

The fronts are the library's own terms `headFrontOf s a Q.target` and `finFrontOf t a Q`
(Johnson/Top/H0/Tw/K2C/Closed.lean), at which `HeadBehind` and `FinBehind` (Returns/ArmsBehind.lean)
ask these clauses. The premises `here`, `group` and `laid` are fields of these two structures, in
their letters; `he` is `FinBehind.quiet`.

AT WHICH TERMS THE LIBRARY's STATEMENTS ARE TAKEN: "reached" is the walk over the wrapped list
itself · the way in: at the head it lets the state in as it is, at the finish it is `finishFrontQ` ·
the place's numbers are `placeQ .head` and `placeQ .finish` · the second component is `Unit`.

By, all the library's: `hT1_head_plain`, `hT1_fin_plain` (Johnson/P1K2R/HT1Plain.lean) ·
`front_tests_full` (Johnson/G/SwitchFrontTests.lean) · `frontAt_of`
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean).

Limits. As in Returns/PinReached.lean: THE THREE TESTS hy · hcut · hB READ THE PUBLIC PART ALONE;
Johnson/P1K2R/HT1Plain.lean's HEAD SAYS THAT THE SEALED VERIFIER ASKS NEITHER hy NOR hcut, THAT
WHETHER IT ASKS hB WAS NOT READ, AND THAT THE THREE ARE NOT SHOWN MET TOGETHER WITH THE PREMISES
IN FRONT. NOR IS THAT SHOWN HERE: NO MEMBER. `here` at the head is paid at a reached state, under
"there is an a", by `head_here_reached` (Returns/LinkReached.lean); `here` and `laid` at the finish
follow from `he`, under "there are a and Q", by the library's `finishFrontQ_fr`
(Johnson/Top/H0/Tw/K2C/FinFront.lean): neither is called here. `group` at the head, `he` at the
finish, and "each copy has a main row" at both places are premises here. The full size alone. This
file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.PinReached
import Johnson.Top.H0.Tw.K2C.HeldAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (SampleGoodS frameAt n0At oldsAt headFrontOf finFrontOf
  finishFrontQ frontAt_of)
open VerifiableInference.Desc.First.K2Hands (frontB2)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (fxAt front_tests_full)
open P1K2 (hT1_head_plain hT1_fin_plain)
open _root_.Tw.K2 (readsMainOf)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-! ## In front of the output head's switch -/

theorem head_pinned_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {r : SwRow} (hrw : tableFullLit[23]? = some r) :
    ∃ W, frameAt (fxAt r) = some W ∧
      frontB2 (fxAt r) W 24 0 (n0At 24) (oldsAt 24) (headFrontOf s a Q.target) = true ∧
      SampleGoodS (headFrontOf s a Q.target).st := by
  obtain ⟨W, hW, -⟩ := front_tests_full (List.mem_of_getElem? hrw)
  have hfx : First.K2.frontAt (placeQ .head) s = some (headFrontOf s a Q.target) :=
    frontAt_of (Or.inr (Or.inl ⟨rfl, a, Q, here, group, rfl⟩))
  have H := hT1_head_plain (Str := Unit)
    (Rch := fun k y => Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k y.1) hS hR O hF hpl hy hcut hB
    (fun _ _ h => h) (enter := fun u => .ok u) (fun _ _ h => (Except.ok.inj h).symm)
    (q := placeQ .head) rfl hrw hW z (s, ()) hr s rfl _ hfx
  exact ⟨W, hW, H.1, H.2.2.1⟩

/-- **THE EIGHT at the head's front.** -/
theorem head_shape_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    ShapeFits (headFrontOf s a Q.target) := by
  obtain ⟨r, hrw⟩ := row_at (m := 23) (by omega)
  obtain ⟨W, hW, hb, -⟩ := head_pinned_reached hS hR O hF hpl hy hcut hB hr here group hrw
  exact shape_of_test (List.mem_of_getElem? hrw) hW (olds_once (by omega) (by omega)) hb

theorem head_reads_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    ∀ o ∈ (switchKept (headFrontOf s a Q.target).f.rows).toList,
      ∀ r ∈ ((headFrontOf s a Q.target).st.oracles.getD o default).sampleRows.toList,
        readsMainOf o r = true := by
  obtain ⟨r, hrw⟩ := row_at (m := 23) (by omega)
  obtain ⟨-, -, -, hG⟩ := head_pinned_reached hS hR O hF hpl hy hcut hB hr here group hrw
  exact (head_shape_reached hS hR O hF hpl hy hcut hB hr here group).reads hG

theorem head_tables_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    (keptPos : ∀ k ∈ (headFrontOf s a Q.target).T.kept.toList, 0 < k.shape.mainRows) :
    ∀ o ∈ (switchKept (headFrontOf s a Q.target).f.rows).toList,
      ∀ r ∈ ((headFrontOf s a Q.target).st.oracles.getD o default).sampleRows.toList,
        (∀ v ∈ r.terms.toList,
          v.v.pairs.length = (headFrontOf s a Q.target).st.tableBits o .main ∧ Own.InOrder v.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (headFrontOf s a Q.target).st.tableBits o .main := by
  obtain ⟨r, hrw⟩ := row_at (m := 23) (by omega)
  obtain ⟨-, -, -, hG⟩ := head_pinned_reached hS hR O hF hpl hy hcut hB hr here group hrw
  exact (head_shape_reached hS hR O hF hpl hy hcut hB hr here group).tables hG keptPos

/-! ## Behind the finish's way in -/

theorem fin_pinned_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a)
    (laid : a.G = some Q)
    {r : SwRow} (hrw : tableFullLit[24]? = some r) :
    ∃ W, frameAt (fxAt r) = some W ∧
      frontB2 (fxAt r) W 25 0 (n0At 25) (oldsAt 25) (finFrontOf t a Q) = true ∧
      SampleGoodS (finFrontOf t a Q).st := by
  obtain ⟨W, hW, -⟩ := front_tests_full (List.mem_of_getElem? hrw)
  have hfx : First.K2.frontAt (placeQ .finish) t = some (finFrontOf t a Q) :=
    frontAt_of (Or.inr (Or.inr ⟨rfl, a, Q, here, laid, rfl⟩))
  have H := hT1_fin_plain (Str := Unit)
    (Rch := fun k y => Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k y.1) hS hR O hF hpl hy hcut hB
    (fun _ _ h => h) (enter := finishFrontQ) (fun _ _ h => h)
    (q := placeQ .finish) rfl hrw hW z (s, ()) hr t he _ hfx
  exact ⟨W, hW, H.1, H.2.2.1⟩

/-- **THE EIGHT at the finish's front.** -/
theorem fin_shape_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a)
    (laid : a.G = some Q) :
    ShapeFits (finFrontOf t a Q) := by
  obtain ⟨r, hrw⟩ := row_at (m := 24) (by omega)
  obtain ⟨W, hW, hb, -⟩ := fin_pinned_reached hS hR O hF hpl hy hcut hB hr he here laid hrw
  exact shape_of_test (List.mem_of_getElem? hrw) hW (olds_once (by omega) (by omega)) hb

theorem fin_reads_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a)
    (laid : a.G = some Q) :
    ∀ o ∈ (switchKept (finFrontOf t a Q).f.rows).toList,
      ∀ r ∈ ((finFrontOf t a Q).st.oracles.getD o default).sampleRows.toList,
        readsMainOf o r = true := by
  obtain ⟨r, hrw⟩ := row_at (m := 24) (by omega)
  obtain ⟨-, -, -, hG⟩ := fin_pinned_reached hS hR O hF hpl hy hcut hB hr he here laid hrw
  exact (fin_shape_reached hS hR O hF hpl hy hcut hB hr he here laid).reads hG

theorem fin_tables_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a)
    (laid : a.G = some Q)
    (keptPos : ∀ k ∈ (finFrontOf t a Q).T.kept.toList, 0 < k.shape.mainRows) :
    ∀ o ∈ (switchKept (finFrontOf t a Q).f.rows).toList,
      ∀ r ∈ ((finFrontOf t a Q).st.oracles.getD o default).sampleRows.toList,
        (∀ v ∈ r.terms.toList,
          v.v.pairs.length = (finFrontOf t a Q).st.tableBits o .main ∧ Own.InOrder v.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (finFrontOf t a Q).st.tableBits o .main := by
  obtain ⟨r, hrw⟩ := row_at (m := 24) (by omega)
  obtain ⟨-, -, -, hG⟩ := fin_pinned_reached hS hR O hF hpl hy hcut hB hr he here laid hrw
  exact (fin_shape_reached hS hR O hF hpl hy hcut hB hr he here laid).tables hG keptPos

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_pinned_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_shape_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_reads_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_tables_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_pinned_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_shape_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_reads_paid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_tables_paid
