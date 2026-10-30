-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/SpineMine.lean: nine of the premises of `ProofFile.Sk.Full.decl_first_at_rows`
(Johnson/Desc/ProofFile/Law/Skel/Full/FirstRows.lean) hold at `VerifierAndGoals.storedPublicFiles`.

That theorem says that the proof file's description returns, with the first chain's skeletons and
declared rounds as written, under 46 premises. Twenty-eight are paid in
Johnson/AtFull/Entry/Makers/AtZFull.lean. This file pays nine more. Each is a call of a theorem in
another file.

Main names.
* `SpineMine Z G`: the nine, to the letter, under one name; each field bears the name of the premise
  that it pays. A helper: it states no goal.
* `spineMine_zFull`: they hold at the written public part `ZqM` of `VerifierAndGoals.storedPublicFiles` and at every blank
  ground G that `blankBy` returns there. n4: `n4_zFull` (Johnson/AtFull/Rounds/K4NumsAtFull.lean).
  q5: `k5Q_zFull_of_rest` (Johnson/AtFull/K5/AtFull.lean). v12: `v12_of`
  (Johnson/Loose/H2K12/K12HVOfWritten.lean). w5: `work_at_blank`
  (Johnson/LPFK9R/WorkFieldRequest.lean). a5: `k5_hA`
  (Johnson/Desc/First/Att/Row/K5OwnAtPlacesW.lean). k8: `kinds_in_scope`
  (Johnson/AtFull/Desc/Lots/LinksInScope.lean). w13: `works_of_pub`
  (Johnson/AtFull/Rounds/K13.lean). n6: `k6_nameW` (Johnson/AtFull/Rounds/K6Name.lean). h₄:
  `subs_written_of_pub` (Johnson/LPFK9R/SubsWrittenOfPub.lean).

Limits. The size of the layout file, the two makers' returns and two facts on the planner's answer
are premises. Calls alone: what each called theorem rests on is said in its own file; some rest on
evaluations in Lean's kernel at written values. `VerifierAndGoals.storedPublicFiles` is a term; no Lean ties it to files
in a folder. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.FirstRows
import Johnson.AtFull.Rounds.SecondRowsAtFull
import Johnson.AtFull.Rounds.K4NumsAtFull
import Johnson.AtFull.K5.AtFull
import Johnson.LPFK9R.BaseOfPubWhole
import Johnson.LPFK9R.SubsWrittenOfPub
import Johnson.AtFull.Entry.Makers.AtZFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Joined (writtenSized writtenMade)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (madeAt fixedDigest fixedDigest_size)
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Pub (DW toldW decl_of_made told_of_made u2_of_first u5_of_sized u6_of_plans
  u7_of_plan given_of_plans)

/-- Nine of the premises of `ProofFile.Sk.Full.decl_first_at_rows`, to the letter, under one name. A list
of premises: no goal. -/
structure SpineMine (Z : Pub) (G : Ground) : Prop where
  n4 : ∀ g < 12, ∀ hp, G.W.G[g]? = some hp →
    Johnson.AtFull.Rounds.numsOf G.W.layers hp = Johnson.AtFull.Rounds.numsW g
  q5 : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a →
    VerifiableInference.Desc.First.Att.P.claimsOkAtQ a = true
  v12 : H2U.p12OfMade Z.made = H2K.Member.piLFull
  w5 : Johnson.AtFull.Rounds.k5Work G.W = 0
  a5 : ∀ x ∈ H2K5.k5Places G, ∀ a, G.W.A[x.2.2]? = some a →
    a.own = Johnson.AtFull.Rounds.k5OwnW a.own.rows
  k8 : G.built.toList.map (fun X => (X.kind, X.name)) = P1K8L.k8KindsW
  w13 : Johnson.AtFull.Rounds.K13.worksM3 Z.cuts Z.plans.1 = (0, 0, 0)
  n6 : ProofFile.Sk.Full.nameW ⟨1, some 24, 4, .K6⟩ = "H:4"
  h₄ : subsOf Z = ProofFile.Sk.Full.subsW

/-- **The nine hold at `VerifierAndGoals.storedPublicFiles`.** -/
theorem spineMine_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : OnBytes.Model.Verify.Public}
    {m : Made}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (e1 : MadeFree.freeOf m.p.chains.made = writtenMade) {G : Ground}
    (hG : blankBy pureRoad.links (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = some G) :
    SpineMine (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) G := by
  have hS := VerifierAndGoals.inScope_full
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  have hZ := Johnson.AtFull.Entry.pubPlain_zFull hX hm hF e1
  have hx : m.p.X = X₀ := VerifiableInference.Desc.Key.madeAt_public hm
  have hz : m.p.chains.made.sized = writtenSized := congrArg (·.sized) e1
  have hpl : m.p.chains.made.proof =
      [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] := congrArg (·.proof) e1
  have hs : m.proof = proofSendsFull := proof_of_free hm e1
  have e9 : (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m).D.1.map (·.entry) =
      Johnson.AtFull.Desc.Lots.esW :=
    Johnson.AtFull.Rounds.entries_at rfl
  refine ⟨Johnson.AtFull.Rounds.n4_zFull hsz hZ hG, ?_,
    H2K12.v12_of hX hm hF hz hpl (decl_of_made hX hm hz hpl hs) (told_of_made hX hm hz hpl hs) hZ
      hs,
    Johnson.AtFull.Rounds.k5Work_of (LPFK9.work_at_blank hS hZ hG),
    H2K5.Row.k5_hA hS hR hZ hG,
    Johnson.AtFull.Lots.LinksScope.kinds_in_scope hS hR hZ hG,
    Johnson.AtFull.Rounds.K13.works_of_pub hZ rfl e9,
    Johnson.AtFull.Rounds.k6_nameW,
    (LPFK9.subs_written_of_pub hS hR hZ).trans ProofFile.Sk.Full.subs_tie.symm⟩
  intro g hg a ha
  obtain ⟨W, hW, H⟩ := Johnson.AtFull.K5.k5Q_zFull_of_rest hsz
  obtain rfl : W = X₀ := Except.ok.inj (hW.symm.trans hX)
  obtain ⟨a', ha', -, -, hq⟩ := H g hg
  have ha2 : W.A[g]? = some a := by
    rw [← hx]
    exact ha
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha2)
  exact hq

end AtFull.Top

#print axioms AtFull.Top.spineMine_zFull
