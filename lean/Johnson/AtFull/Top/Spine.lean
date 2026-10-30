-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/Spine.lean: the proof file's description (`ProofFile.onlineDescription`,
Johnson/Desc/ProofFile/OnlineDescription.lean) returns at `VerifierAndGoals.storedPublicFiles`, and its first chain's skeletons and
declared rounds are the written ones.

Main names.
* `spine_zFull`: one call of `ProofFile.Sk.Full.decl_first_at_rows`
  (Johnson/Desc/ProofFile/Law/Skel/Full/FirstRows.lean). Of its 46 premises: three are theorems on
  the goals' scope and on the public part; the blank ground is returned by `LPFK9.blank_of_pub`
  (Johnson/LPFK9R/BaseOfPubWhole.lean); 28 are the fields of `Struck`
  (Johnson/AtFull/Entry/Makers/AtZFull.lean); nine the fields of `SpineMine`
  (Johnson/AtFull/Top/SpineMine.lean); two follow from the later seats' returns
  (Johnson/AtFull/Entry/Makers/LaterNames.lean). THREE STAY PREMISES: r₆, r₇: the two later seats
  return; R3: what the lookups' lot reads of the public part is the written value.
* `first_of_skel`: from the skeletons: the first chain's cut is the written one, and every block's
  test on the plan accepts.

Limits. An implication: the size of the layout file, the two makers' returns, two facts on the
planner's answer, r₆, r₇ and R3 are premises. Five of the 46 (cW, e9, t3, t4, g9) are projections of
terms that `ZqM` spells as written values: by themselves they say nothing of what a maker returns,
and count only together with the return of the public part at `ZqM` (`pubPlain_zFull`,
Johnson/AtFull/Entry/Makers/AtZFull.lean). The first chain alone. At the second hash function.
`VerifierAndGoals.storedPublicFiles` is a term; no Lean ties it to files in a folder. Nothing on soundness.

-/
import Johnson.AtFull.Top.SpineMine
import Johnson.AtFull.Entry.Makers.LaterNames
import Johnson.AtFull.Desc.Lots.K3RowX
import Johnson.Desc.ProofFile.Law.Skel.SkelCut
import Johnson.Desc.ProofFile.Law.Skel.Full.FlatOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile ProofFile.Sk ProofFile.Sk.Full
open VerifiableInference VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Joined (writtenSized writtenMade)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open Johnson.AtFull.Pub (DW)

/-- **The proof file's description returns at `VerifierAndGoals.storedPublicFiles`**, with the first chain's skeletons and
declared rounds the written ones. Left as premises: the two later seats' returns, and what the
lookups' lot reads of the public part. -/
theorem spine_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : OnBytes.Model.Verify.Public}
    {m : Made}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (e1 : MadeFree.freeOf m.p.chains.made = writtenMade)
    {A : SharedSeat} {B : SecondSeat}
    (r₆ : onlineSharedChain (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = some A)
    (r₇ : onlineLastChain (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = some B)
    (R3 : Johnson.AtFull.Lots.K3.ReadsLeft (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m)) :
    ∃ c, onlineDescription OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL =
        .ok (FW OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m A B c) ∧
      c.blocksInOrder.map skel = flatW ∧
      (FW OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m A B c).roundsDeclaredByBlocks.1 = DW.1 := by
  have hS := VerifierAndGoals.inScope_full
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  have hZ := Johnson.AtFull.Entry.pubPlain_zFull hX hm hF e1
  obtain ⟨G, hG⟩ := LPFK9.blank_of_pub hS hR hZ
  have T := Johnson.AtFull.Entry.struck_zFull hsz hX hm hF e1 hG
  have M := spineMine_zFull hsz hX hm hF e1 hG
  exact decl_first_at_rows hS hR hZ hG T.cW T.e9 T.l0 T.g0 T.a0 T.p0 T.d0 T.m0 T.c1 T.s1 T.l1 T.g1
    T.z2 T.u1 T.u2 T.t3 T.t4 T.t5 T.b2 R3 M.n4 M.q5 T.m5 M.k8 T.n8 T.g9 T.t9 M.v12 T.r13 T.c13
    T.l13 T.g11 M.w5 M.a5 T.t8 M.w13 M.n6 M.h₄ (Johnson.AtFull.Entry.shared_named r₆)
    (Johnson.AtFull.Entry.second_named r₇) r₆ r₇

/-- What the skeletons give: the first chain's cut is the written one and every block's test on the
plan accepts. -/
theorem first_of_skel {c : Chain S Cl} (h : c.blocksInOrder.map skel = flatW) :
    cutOf c.blocksInOrder = cutFirstFull ∧ ∀ b ∈ c.blocksInOrder, b.planOk = true :=
  ⟨(cutOf_skel c.blocksInOrder).trans (by rw [h]; exact flat_cut), first_planOk h⟩

end AtFull.Top

#print axioms AtFull.Top.spine_zFull
#print axioms AtFull.Top.first_of_skel
