-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the kind's share at the named family, with nothing left at three of its places.
/-
AtFullSide/K12/ShareK12OfTheObject.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together? NOT KNOWN. O : `TheThreadsHalf` h hr is itself a premise, and a
heavy one: no value of it is laid in this file or beneath it. hRel is a premise here. pays, on₁,
and bud₁ are premises, not discharged here. No K that meets hK₁ to hK₄ is laid here.

What is here. AtFullSide/K12/ShareK12AtTheThreads.lean's gather at the family of invariants of
record, WITH ITS ONE SENTENCE AT THE REQUEST's OWN TEST PAID by
AtFullSide/K12/RowsSayAtTheLetters.lean (which has it from another file's top). One call: no new
content. No definition; one statement.

  `k12_share_of_the_object`   `KindShare` A (`theGOfReturn` made h T K) A.H (`K12Rel` Z Ry)
      (O.threadsAtRelation …) .K12.

THE PREMISES, SORTED. THE MAKER AND THE HEAD: made · h. THE THREADS' HALF: O. THE RELATION: hRel. ON
K: hK₁ to hK₄ (memberships). THE OTHER SHARES: pays (`Good`'s three at all four lists) · on₁ ·
bud₁ (the first chain's test). NOTHING ELSE: at the shared chain's two tests and at the request's
own test no premise on values, on a book, on public numbers or on the family is left.

THE ROW IS NOT PAID: pays, on₁ and bud₁ stand; O, hRel and K have no value.

Limits. All limits of the two files' heads and of what lies beneath. Nothing on completeness,
soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.ShareK12AtTheThreads
import AtFullSide.K12.RowsSayAtTheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins baseFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.TheSides AtPublicFiles.TheG
open VerifierAndGoals (readFiles)
open LPFD.Full (XF)
open AtFullSide.Honest AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp} {Wt : Type}

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **THE KIND K12's THREE SHARES AT THE NAMED FAMILY OF INVARIANTS, WITH
NO PREMISE LEFT AT THE TESTS ON G_u AND ON G_omega AND AT THE REQUEST's OWN TEST** but the
memberships in K. `k12_share_at_the_threads` with its sentence rowsSay paid by
`rowsSay_at_the_letters`. -/
theorem k12_share_of_the_object
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr) (T : ThreadParts A Wt) (K : KindRows (baseFilling Z) A.Z A.G)
    (hK₁ : ∀ r ∈ K.shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G)
    (hK₂ : ∀ g ∈ (baseFilling Z).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.shared, r.place = g.place)
    (hK₃ : ∀ r ∈ K.second, r.place.kind = KindName.K12 →
      r ∈ (lotW Face.own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).rows
        A.Z A.G)
    (hK₄ : ∀ g ∈ (baseFilling Z).second A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.second, r.place = g.place)
    (Ry : FullSizeMatrix → XF → Prop)
    (hRel : ∀ w₀ rc x, K12Rel Z Ry w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x)
    (pays : VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) KindName.K12)
    (on₁ : ∀ w₀ rc x (hrel : K12Rel Z Ry w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R) ρ r,
      ρ.due A.F = true → silentAt A.F ((theGOfReturn made h T K).prover A.H) w₀ rc x ρ = none →
      runC A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k ρ = .ok r →
      ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = KindName.K12 →
        OnAtRun₁ (G := (theGOfReturn made h T K)) (H := A.H)
          (O.threadsAtRelation made (theGOfReturn made h T K) (theGOfReturn_prover made h T K) hRel
              w₀ rc x hrel k R
            hR) ρ r L)
    (bud₁ : ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = KindName.K12 →
      Johnson.M1.BudOwed A.F L) :
    KindShare A (theGOfReturn made h T K) A.H (K12Rel Z Ry)
      (O.threadsAtRelation made (theGOfReturn made h T K) (theGOfReturn_prover made h T K) hRel)
          KindName.K12 :=
  k12_share_at_the_threads made O T K hK₁ hK₂ hK₃ hK₄ Ry hRel pays on₁ bud₁
    (rowsSay_at_the_letters h made O.open₃)

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_share_of_the_object
