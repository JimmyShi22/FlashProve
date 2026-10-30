-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/PinPublic.lean: SIX MORE CLAUSES OF `FrontCore` AND `TablesFit` THAT
READ THE CODES AND THE TARGET ALONE (restMain · keptAnswers · lengths · logC · logZ ·
`TablesFit.bitsG`), AT THE FRONT OF EACH OF THE THREE SORTS OF PLACE OF A SWITCH, AT A REACHED
STATE, IN THE GOALS' SCOPE AND UNDER THE THREE NAMED TESTS ON THE PUBLIC PART OF
Returns/PinReached.lean. The road is that file's: the six hold at the 25 written fronts by Lean's
kernel, and pass to every front with the same public side. Statements with their proofs: rewriting,
and calls.

  `PublicFits x` the six at a front x, each field in the letters of the structure that asks it
  `publicB x`, `publicB_says` the six as a test; what its yes says
  `publicFits_pin` they pass from a front x₀ to every front x that has x₀'s public side, by place
                    (`Pinned`)
  `publicB_full` yes at all 25 written fronts of the full size
  `publicB_can_fail` it says no at the first written front with the rest laid into mask rows
  `public_of_test` `PublicFits x` wherever the library's test `frontB2` accepts x at a written front
                    of the table: no state, no plan
  `link_public_reached`, `head_public_reached`, `fin_public_reached` at the three sorts of place

THE DEVICE. `publicB_full` and `publicB_can_fail` are closed by `decide +kernel`, six times in all,
under `set_option maxRecDepth 1000000`, as in Returns/WrittenFronts.lean.

By, all the library's: `pin_facts` (Johnson/Top/H0/K2Hands/FrameOne.lean) · `rowBits_bare`
(Johnson/Top/H0/K2Hands/FrameRenumbered.lean) · `full_all` (Johnson/Top/H0/K2Caller/LitRows.lean).
This folder's: `link_pinned_reached`, `row_at` (Returns/PinReached.lean) · `head_pinned_reached`,
`fin_pinned_reached` (Returns/PinArms.lean).

Limits. As in Returns/PinReached.lean and Returns/PinArms.lean: the three tests hy · hcut · hB read
the public part alone and are premises; the opening stands at the public files' own layout file; at
the link the statement speaks at a front that the text returns; at the head `here` and `group`, at
the finish `he`, `here` and `laid` are premises. THE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY
NOBODY HERE: NO MEMBER. `publicB_can_fail` bites the clause on the rest; the other five are shown no
failing case. `FrontCore.groupCode`, `copiesCode`, `inRange`: not reached. The full size alone. This
file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.PinArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (frameAt headFrontOf finFrontOf finishFrontQ)
open VerifiableInference.Desc.First.K2Hands (Pinned frontB2 pin_facts rowBits_bare)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit full_all full0)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (fxAt)
open _root_.Tw.K2 (Front firstFront)
open ProofFile (Cl)

/-- **The six**, at a front: `bitsG` is `TablesFit`'s; the five in front of it are `FrontCore`'s. No
field of `LinkPlain`, but a bundle. -/
structure PublicFits (x : Front) : Prop where
  restMain : x.T.rest.part = .main
  keptAnswers : ∀ k ∈ x.T.kept.toList, k.shape.answers ≠ 0
  lengths : x.st.codes.lengthsOk = true
  logC : (x.st.codes.base.getD x.f.rows.code default).logN ≤ 32
  logZ : (x.st.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32
  bitsG : switchRowBits x.T .main + (x.st.codes.base.getD x.T.shape.code default).logEll ≤ 63

/-- The six as a test. -/
def publicB (x : Front) : Bool :=
  decide (x.T.rest.part = .main) && (x.T.kept.toList.all fun k => decide (k.shape.answers ≠ 0)) &&
    x.st.codes.lengthsOk && decide ((x.st.codes.base.getD x.f.rows.code default).logN ≤ 32) &&
    decide ((x.st.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32) &&
    decide (switchRowBits x.T .main + (x.st.codes.base.getD x.T.shape.code default).logEll ≤ 63)

theorem publicB_says {x : Front} (h : publicB x = true) : PublicFits x := by
  unfold publicB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The six pass from one pinned front to the other.** -/
theorem publicFits_pin {x₀ x : Front} (P : Pinned x₀ x) (H : PublicFits x₀) : PublicFits x where
  restMain := by rw [P.rest]; exact H.restMain
  keptAnswers := by
    intro k hk
    have hm : k.shape ∈ x.T.kept.toList.map (·.shape) := List.mem_map.2 ⟨k, hk, rfl⟩
    rw [P.kept] at hm
    obtain ⟨k₀, hk₀, e⟩ := List.mem_map.1 hm
    rw [← e]
    exact H.keptAnswers k₀ hk₀
  lengths := by rw [P.codes]; exact H.lengths
  logC := by rw [P.codes, P.code]; exact H.logC
  logZ := by rw [P.codes, P.maskCode]; exact H.logZ
  bitsG := by rw [rowBits_bare P.shape, P.codes, P.shape]; exact H.bitsG

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at all 25 entries of the full table.** -/
theorem publicB_full : (tableFullLit.all fun r => publicB (fxAt r)) = true :=
  full_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- **The test can fail.** -/
theorem publicB_can_fail :
    publicB { fxAt full0 with
      T := { (fxAt full0).T with rest := { (fxAt full0).T.rest with part := .mask } } } =
      false := by
  decide +kernel

/-- **The six, wherever the library's test accepts a front at a written front of the table.** -/
theorem public_of_test {r : SwRow} (hr : r ∈ tableFullLit) {W : SwitchFrame} {grp n0 : Nat}
    {olds : List Nat} {x : Front} (hb : frontB2 (fxAt r) W grp 0 n0 olds x = true) :
    PublicFits x := by
  simp only [frontB2, Bool.and_eq_true] at hb
  exact publicFits_pin (pin_facts hb.1.1) (publicB_says (List.all_eq_true.1 publicB_full r hr))

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

theorem link_public_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    {x : Front} (hx : firstFront s.st s.check.frame = .ok x) : PublicFits x := by
  obtain ⟨r, hrw⟩ := row_at (m := m) (by omega)
  obtain ⟨W, -, hb, -⟩ := link_pinned_reached hS hR O hF hpl hy hcut hB h23 hr hx hrw
  exact public_of_test (List.mem_of_getElem? hrw) hb

theorem head_public_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q) :
    PublicFits (headFrontOf s a Q.target) := by
  obtain ⟨r, hrw⟩ := row_at (m := 23) (by omega)
  obtain ⟨W, -, hb, -⟩ := head_pinned_reached hS hR O hF hpl hy hcut hB hr here group hrw
  exact public_of_test (List.mem_of_getElem? hrw) hb

theorem fin_public_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a)
    (laid : a.G = some Q) : PublicFits (finFrontOf t a Q) := by
  obtain ⟨r, hrw⟩ := row_at (m := 24) (by omega)
  obtain ⟨W, -, hb, -⟩ := fin_pinned_reached hS hR O hF hpl hy hcut hB hr he here laid hrw
  exact public_of_test (List.mem_of_getElem? hrw) hb

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.publicB_says
#print axioms VerifiableInference.Desc.K2.Honest.Returns.publicFits_pin
#print axioms VerifiableInference.Desc.K2.Honest.Returns.publicB_full
#print axioms VerifiableInference.Desc.K2.Honest.Returns.publicB_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.public_of_test
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_public_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_public_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_public_reached
