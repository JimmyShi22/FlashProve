-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.NineTenAtLaid
import Johnson.Loose.H2K12.ShapesAtSeats
import Johnson.Desc.K12.Coin.MembersLaid
import OnBytes.Plan.PlanListsProof
/-
H2K12/SeamPlanAtSeats.lean: at the proof file's two shared proximity tests (the shared
chain's sub-protocols 9 and 10: on G_u and on G_omega), seven premises of the seam's joined call as
facts in the goals' scope and at the return of `LPFD.Full.proofDataAndDecisionOfPublicFiles`. Definitions, statements and
proofs.

Why. `tupleNine_sh`, `tupleTen_sh` and their later forms `tupleNine_shQ`, `tupleTen_shQ`
(Johnson/Desc/Sound/SeamAtSh.lean, SeamAtShQ.lean [not in the base; not imported here]) join all
that is typed of the seam at these two tests. Seven of their premises read nothing but the shared
chain's public parameters P : `Desc.K14.P14`. In that call's own letters:
  hU : withU P.S = some sentU · hsU : sentU.size = 2 · hsO : (withOmega P.S).size = 2 ·
  hlU : layTrees P.codes sentU = some layU · hlO : layTrees P.codes (withOmega P.S) = some layO ·
  hS : P.S.sharedSplitNeeded = true · hm : P.S.masksAhead = true.
Main names.
  `SeamPlan P sentU layU layO`: a Lean structure with the seven as its fields, under these letters.
  `lays_of_linSizeOf`: general. Where the planner's `linSizeOf` (OnBytes/Params/DeriveLin.lean)
    returns, what goes out with o_u can be said and the trees of both sendings can be laid: its own
    text asks the three.
  `lays_of_configure`: the same off configure's yes, at the proof's codes and the shared chain's
    shape, by `configure_proofPlans` (OnBytes/Plan/PlanListsProof.lean) and `sharedPlan_is`
    (OnBytes/Params/PlanListsChains.lean).
  `seamPlan_of_configure`: configure's yes, a split is needed, the masks go ahead: then there are
    sentU, layU, layO with `SeamPlan` at EVERY P whose codes and shape are the made ones. The two
    sizes are `withU_size`, `withOmega_size` (Johnson/Desc/K12/Coin/MembersLaid.lean).
  `seamPlan_of_plain`: the same from two premises: the files are in scope; `ProofFile.Plain.planned`
    returns.
  `seamPlan_in_scope_at`: the same at `ProofFile.pubPlain`'s return Z, at every P with P.codes =
    Z.p.chains.made.sized.proof.codes and P.S = Z.p.chains.made.sized.proof.batch.shape.
  `seamPlan_in_scope`: the same two premises: there are sentU, layU, layO such that AT EVERY N
    `SeamPlan (p14N Z N) sentU layU layO`. `p14N Z N` (H2K12/LaterSeatsN.lean) is what the proof
    file's IOP as written in Lean has as the shared chain's parameters; N enters its field
    beforePoint alone, which none of the seven reads.
  `seamPlan_laid`: the files are in scope; proofDataAndDecisionOfPublicFiles … = .ok (D, r): then there are Z, N, nO, c with
    four returns and sentU, layU, layO with `SeamPlan (p14N Z N) sentU layU layO`. No test is left
    in front.
  `nine_ten_plan_laid`: the same two premises: there are Z, N, nO, c with the seven returns of
    `ten_facts_laid`, with `NineAtGu` and `TenAtGomega` (H2K12/NineTenAtLaid.lean) and with sentU,
    layU, layO as above: all under one «there are», so that the three speak of the same Z, N, nO, c
    is held by Lean.
Whence each. hS: `ShapesFull.split` (Johnson/Desc/K12/Law/Sizes/ShapesAtScope.lean). hm:
`AtFull.ahead` (Law/Sizes/StageSizesAtScope.lean). hU, hlU, hlO: `lays_of_configure` at the
configure's yes that `plain_parts` (H2K12/PlainParts.lean) hands. hsU, hsO: the two lemmas on sizes.
Nearest kin. `Second.Seam.Facts` (Johnson/Second/Seam/PlanFacts.lean [not in the base; not imported
here]) is a Lean structure with these seven fields, under the same letters, and three more: `K1.Tie`
at the three oracle messages' shapes. `nine_takes`, `ten_takes` (PlanFactsCall.lean beside it) call
`tupleNine_sh`, `tupleTen_sh` with the ten. There the structure is had from one test with code that
is evaluated at stored files, on the landed planner's road: an evaluation at a value, no theorem.
Here the seven are theorems in scope, on the plain road; the three on `K1.Tie` are not here.
`facts_of_plan` (H2K12/SeamPlanFits.lean) makes that structure of this one and the three.
`can_of_back` (Johnson/Desc/Book/ToldShared.lean) has hU, hlU, hlO off the kind's own tests on the
plan: it asks that the eight sub-protocols pass them. Here the planner's yes is spent instead, so
that test is no premise.
What it is not. THAT THE SEVEN TEXTS ARE THE CALL's BINDERS IS HELD BY NO LINE OF THIS FILE: the
call is not imported here; a sheet that is not in this library is for that. The call is not typed
at these values. What sentU, layU, layO are is not said: they stand under «there are», and each is
pinned as the one return of a function (hU, hlU, hlO). Every other premise of the call is untouched:
on the piece and the test's own list of rounds (four of them are fields of `NineFacts`, `TenFacts`;
their fit to the call is by reading), on the IOP as written in Lean, on the promise, on the numbers,
on a member. Facts on public values: it pays no law and closes no row.
NO EXAMPLE: at no files does Lean show that they are in scope and that pubPlain or proofDataAndDecisionOfPublicFiles returns:
whether the premises can be met together is not said here.
No soundness and no level is claimed. Nothing on hiding. No sorry, no axiom of ours;
what each theorem rests on is printed at the file's end.

-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K14 (P14 withU withOmega)
open Johnson.G (writtenPFull)

/-- **The seven premises of the seam's joined call that read the shared chain's public parameters
alone**, under that call's letters. -/
structure SeamPlan (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) : Prop where
  /-- what goes out with o_u can be said -/
  hU : withU P.S = some sentU
  /-- o_u and the first mask -/
  hsU : sentU.size = 2
  /-- o_omega and o_sp -/
  hsO : (withOmega P.S).size = 2
  /-- the trees of the first sending can be laid -/
  hlU : layTrees P.codes sentU = some layU
  /-- so can those of the second -/
  hlO : layTrees P.codes (withOmega P.S) = some layO
  /-- G_u and Omega differ in code -/
  hS : P.S.sharedSplitNeeded = true
  /-- the first fold's mask is sent ahead -/
  hm : P.S.masksAhead = true

/-- General: linSizeOf's own text asks that what goes out with o_u can be said and that the trees of
both sendings can be laid. -/
theorem lays_of_linSizeOf {codes : Codes} {x : LinSized} {L : LinSize}
    (h : linSizeOf codes x = some L) :
    ∃ sentU layU layO, withU x.shape = some sentU ∧ layTrees codes sentU = some layU ∧
      layTrees codes (withOmega x.shape) = some layO := by
  unfold linSizeOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, treesOf, Option.map_eq_some_iff] at h
  obtain ⟨_, _, _, _, sentU, hU, _, ⟨layU, hlU, _⟩, _, ⟨layO, hlO, _⟩, _⟩ := h
  exact ⟨sentU, layU, layO, hU, hlU, hlO⟩

/-- The same off configure's yes, at the proof's codes and the shared chain's shape. -/
theorem lays_of_configure {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    ∃ sentU layU layO, withU made.sized.proof.batch.shape = some sentU ∧
      layTrees made.sized.proof.codes sentU = some layU ∧
      layTrees made.sized.proof.codes (withOmega made.sized.proof.batch.shape) = some layO := by
  obtain ⟨_, _, _, _, _, hS2, _⟩ := configure_proofPlans h
  obtain ⟨_, hL, _⟩ := sharedPlan_is hS2
  exact lays_of_linSizeOf hL

/-- ★ At every P whose codes and shape are the made ones. -/
theorem seamPlan_of_configure {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made)
    (hS : made.sized.proof.batch.shape.sharedSplitNeeded = true)
    (hm : made.sized.proof.batch.shape.masksAhead = true) :
    ∃ sentU layU layO, ∀ P : P14, P.codes = made.sized.proof.codes →
      P.S = made.sized.proof.batch.shape → SeamPlan P sentU layU layO := by
  obtain ⟨sentU, layU, layO, hU, hlU, hlO⟩ := lays_of_configure h
  refine ⟨sentU, layU, layO, fun P hc hs => ?_⟩
  rw [← hs] at hU hlO hS hm
  rw [← hc] at hlU hlO
  exact ⟨hU, Coin.withU_size P.S sentU hm hU, Coin.withOmega_size P.S hS, hlU, hlO, hS, hm⟩

/-- ★ On the plain road, in the goals' scope, at every o. -/
theorem seamPlan_of_plain {o : Nat → ByteArray → ByteArray} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) {lay : Option ByteArray} {p : Model.Verify.Planned}
    (hp : ProofFile.Plain.planned o S.pol S.KL lay = .ok p) :
    ∃ sentU layU layO, ∀ P : P14, P.codes = p.chains.made.sized.proof.codes →
      P.S = p.chains.made.sized.proof.batch.shape → SeamPlan P sentU layU layO := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _, _, _, _⟩ := H2K.Made.plain_parts hp
  exact seamPlan_of_configure hc (H2K.Sizes.shapes_of_plain hS hp).split
    (H2K.Sizes.atFull_of_plain hS hp).ahead

/-- ★★ In the goals' scope, at the plain road's public part: at every P whose codes and shape are
those of its «made». -/
theorem seamPlan_in_scope_at {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    {Z : ProofFile.Pub} (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) :
    ∃ sentU layU layO, ∀ P : P14, P.codes = Z.p.chains.made.sized.proof.codes →
      P.S = Z.p.chains.made.sized.proof.batch.shape → SeamPlan P sentU layU layO :=
  seamPlan_of_plain hS (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts S.pol S.lay S.KL = .ok Z from hZ)))

/-- ★★ In the goals' scope, at the seated description's own parameters of the shared chain, at every
N. -/
theorem seamPlan_in_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    {Z : ProofFile.Pub} (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) :
    ∃ sentU layU layO, ∀ N : H2U.Places4, SeamPlan (p14N Z N) sentU layU layO := by
  obtain ⟨sentU, layU, layO, h⟩ := seamPlan_in_scope_at hS hZ
  exact ⟨sentU, layU, layO, fun N => h (p14N Z N) rfl rfl⟩

/-- ★★★ At proofDataAndDecisionOfPublicFiles's return: the letters and the first four returns are ten_facts_laid's. -/
theorem seamPlan_laid (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) (o : ProofFile.SecondHashFunctionArgument)
    (D : WholeD) (r : LPFD.Full.RunPF)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      ∃ sentU layU layO, SeamPlan (p14N Z N) sentU layU layO := by
  obtain ⟨F, hF, hp, _, hs, _⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  obtain ⟨sentU, layU, layO, h⟩ := seamPlan_in_scope hS hZ
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, sentU, layU, layO, h N⟩

/-- ★★★ At proofDataAndDecisionOfPublicFiles's return: what the shared chain's ledger asks of the list of rounds and of the
piece at the two tests, and the seven, under one «there are». -/
theorem nine_ten_plan_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : LPFD.Full.RunPF)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      NineAtGu W o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord ∧
      TenAtGomega W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord ∧
      ∃ sentU layU layO, SeamPlan (p14N Z N) sentU layU layO := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  obtain ⟨sentU, layU, layO, h⟩ := seamPlan_in_scope hS hZ
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    nine_facts_at_Gu W o S hS Z hZ _ N c hN hp hpin _,
    ten_facts_at_Gomega W o S hS Z hZ _ N nO hO c hN hp hpin _, sentU, layU, layO, h N⟩

end H2K.JointK

#print axioms H2K.JointK.lays_of_linSizeOf
#print axioms H2K.JointK.lays_of_configure
#print axioms H2K.JointK.seamPlan_of_configure
#print axioms H2K.JointK.seamPlan_of_plain
#print axioms H2K.JointK.seamPlan_in_scope_at
#print axioms H2K.JointK.seamPlan_in_scope
#print axioms H2K.JointK.seamPlan_laid
#print axioms H2K.JointK.nine_ten_plan_laid
