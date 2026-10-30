-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/AtZFull.lean: THE TWENTY-EIGHT HYPOTHESES OF
Johnson/AtFull/Entry/Makers/Binders.lean AT THE LEAN LIBRARY'S WRITTEN COPY OF THE FULL-SIZE PUBLIC
FILES (`VerifierAndGoals.storedPublicFiles`, as Ladder/Stored.lean spells it). Calls alone.

  `pubPlain_zFull`: the public part of the proof file's description returns there, and its value is
    `ZqM` (Johnson/AtFull/Top/ProofLaidOfMade.lean) over the planner's answer m.
  **`struck_zFull`**: at that value and at the blank ground G: `Struck (ZqM …) G`.
What both still take: hX hm (the public values X₀ and the planner's answer m are what their
makers return there) · hF (the first chain's parameters are the written ones) · e1 (the planner's
four free parts are the written ones). The second besides: hsz (the stored layout file has 224975
bytes) · hG (the blank ground returns).
How. The seven facts on X₀ that `struck` asks: five are conjuncts of `publicOfO_zFull_all`
(Johnson/AtFull/Public/AtX0All.lean); `k8AsksWB_zFull`
(Johnson/AtFull/Entry/Makers/K8AsksAtX0.lean); `hK_of_rest` (Johnson/AtFull/Head/OwnerK.lean). A
maker is a function, so they speak of X₀.

Limits. EVERY PREMISE NAMED ABOVE IS A PREMISE HERE. `ZqM` lays the table of stretches, the declared
rounds and the first state as written terms, so five fields (cW e9 t3 t4 g9) are projections of a
written term: what makes them speak of the maker's value is `pubPlain_zFull`: THE TWO COUNT
TOGETHER, NEVER `Struck` ALONE. `VerifierAndGoals.storedPublicFiles` is three terms written in
Ladder/Stored.lean: no Lean code ties them to the repository's folder of examples; the example's
weights are synthetic. At the second hash function. Nothing on soundness.

-/
import Johnson.AtFull.Entry.Makers.Binders
import Johnson.AtFull.Entry.Makers.K8AsksAtX0
import Johnson.AtFull.Public.AtX0All
import Johnson.AtFull.Head.OwnerK
import Johnson.AtFull.Top.ProofLaidOfMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (publicOfO FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized writtenMade)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G.OfPlan (Made)
open _root_.AtFull.Top (ZqM proof_of_free)

variable {X₀ : Verify.Public} {m : Made}

/-- The public part of the proof file's description returns at the stored full-size files, under hX
hm hF e1. -/
theorem pubPlain_zFull
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (e1 : Johnson.G.MadeFree.freeOf m.p.chains.made = writtenMade) :
    ProofFile.pubPlain OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL =
      .ok (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) :=
  Johnson.AtFull.Pub.pubPlain_of_made hX hm hF (congrArg (·.sized) e1) (congrArg (·.proof) e1)
    (proof_of_free hm e1)

/-- **The twenty-eight hypotheses at the stored full-size files.** -/
theorem struck_zFull {G : ProofFile.Ground}
    (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (e1 : Johnson.G.MadeFree.freeOf m.p.chains.made = writtenMade)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = some G) :
    Struck (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) G := by
  obtain ⟨X₁, hX₁, g0, a0, -, ha, P, -⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  obtain rfl := Except.ok.inj (hX₁.symm.trans hX)
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  have hz : m.p.chains.made.sized = writtenSized := congrArg (·.sized) e1
  have hpl : m.p.chains.made.proof =
      [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] := congrArg (·.proof) e1
  have hs := proof_of_free hm e1
  exact struck VerifierAndGoals.inScope_full hR (pubPlain_zFull hX hm hF e1) hG hX hm hF hz hpl
    (Johnson.AtFull.Pub.decl_of_made hX hm hz hpl hs)
    (Johnson.AtFull.Pub.told_of_made hX hm hz hpl hs) P.p4 P.groups g0 a0 ha
    (k8AsksWB_zFull hsz hX) (_root_.AtFull.Head.hK_of_rest hsz hX).2.2

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.pubPlain_zFull
#print axioms Johnson.AtFull.Entry.struck_zFull
