-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the kind's share at the named family of invariants.
/-
AtFullSide/K12/ShareK12AtTheThreads.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together? NOT KNOWN. O : `TheThreadsHalf` h hr IS ITSELF A PREMISE, AND A
HEAVY ONE: a structure of two letters and some twenty sockets, of which no value is laid in this
file or beneath it. hRel (the relation lies in the tied requests) is a premise here. rowsSay is a
premise here: it is `rowsSay_at_the_letters` (AtFullSide/K12/RowsSayAtTheLetters.lean), which
AtFullSide/K12/ShareK12OfTheObject.lean lays in. pays, on₁, bud₁: another house's. No K that meets
hK₁ to hK₄ is laid here.

What is here. THE GATHER (AtFullSide/K12/ShareK12.lean) AT THE FAMILY OF INVARIANTS OF RECORD:
`TheThreadsHalf`.threadsAtRelation (AtFullSide/Honest/TheCrossing.lean, another house's): the family
that is meant to fill the top statement's binder. The last chain's need of the family, ONE EQUATION
ON ITS THIRD MEMBER AT BORDER 2, IS PAID THERE. No definition; two statements.

  `k12_left₃_at_the_threads`   the gather's premise left₃ at that family, from rowsSay alone.
  `k12_share_at_the_threads`   the gather at that family.

HOW THE EQUATION IS PAID. At a run's own value (`TheThreadsHalf`.threads) the third family IS ThrS
(`thread₃` …) (`said₃` …) by rfl. The family of record is that value under a cast over the
description, the prover, the input and the coins. `threadsAtRelation_of`
(AtFullSide/Honest/TheCrossingCast.lean) carries over the cast any sentence that is stated general
in these four. `OwnTestDebts` and the sentence of left₃ are general in the description
(AtFullSide/K12/SecondShareK12.lean has F as a letter for this), so no HEq is opened here. The debts
thread and said and the job's equation are paid at the letters' names
(AtFullSide/K12/SecondShareAtTheLetters.lean; `OpenLast`.ownIsTheFilling).

THE PREMISES OF THE SECOND, SORTED. THE MAKER AND THE HEAD: made · h. THE THREADS' HALF: O. THE
RELATION: hRel. ON K: hK₁ to hK₄. ANOTHER HOUSE's SHARES: pays · on₁ (now at the named family) ·
bud₁. AT THE OWN TEST: rowsSay ALONE: `SaysAt` at every stand of `thread₃` with `said₃` at border 2,
at every return R, all coins, and whatever the frame lends the unguarded pair. General in the
threads' parts T and the kinds' rows K of G, and in the clause on the request Ry.

Limits. All limits of the files beneath. THE ROW IS NOT PAID. A sorting and one crossing: nothing on
values is paid here. The two instances [Inhabited …] are binders: `thread₃` reads a default
through them, so two callers with two instances have two objects.
 Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.ShareK12
import AtFullSide.K12.SecondShareAtTheLetters
import AtFullSide.Honest.TheCrossingCast

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

/-- CONDITIONAL: see the head. **WHAT THE GATHER ASKS AT THE REQUEST's OWN TEST (left₃), AT THE
NAMED FAMILY OF INVARIANTS**, from the one sentence rowsSay at the letters' names. The equation on
the family's third member is paid: at the run's value it holds by rfl, and it crosses the cast by
`threadsAtRelation_of`, because the sentence is general in the description. -/
theorem k12_left₃_at_the_threads
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr)
    (G : Sides A.F A.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit) (hP : G.prover A.H = A.H)
    {Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop}
    (hRel : ∀ w₀ rc x, Rel w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x)
    (rowsSay : ∀ (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (k : Coins A.B)
      (st : h.description.S₃) (m₀ : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
      (c : RowCoins [(firstPart O.open₃.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
          (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart O.open₃.ownMany.toRun.toTest]),
      ThrS (thread₃ h O.open₃ R) (said₃ h O.open₃ R) 2 k st m₀ E₀ →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) placeW
        [(firstPart O.open₃.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix
                              IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart O.open₃.ownMany.toRun.toTest] 0 = .ok c →
      SaysAt O.open₃.ownMany m₀.st.input (frontOf m₀)
        (restCoins O.open₃.ownMany.toRun.toTest c.2.1)) :
    ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready A.F A.B (G.prover A.H) w₀ rc x k = .ok R),
      ∃ (Th₃ : Thread A.B A.F.S₃ A.F.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst
                            Cells) Unit ProofFile.Inst)
        (Said : ℕ → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop),
        (O.threadsAtRelation made G hP hRel w₀ rc x hrel k R hR).I₃ 2 = ThrS Th₃ Said 2 ∧
        OwnTestDebts A.F A.Z h.places h.firstChain A.H k O.open₃.ownMany Th₃ Said :=
  fun w₀ rc x hrel k R hR =>
    TheThreadsHalf.threadsAtRelation_of made O G hP hRel w₀ rc x hrel k R hR
      (Q := fun F₀ _ _ _ c T₀ =>
        ∃ (Th₃ : Thread A.B F₀.S₃ F₀.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst
                              Cells) Unit ProofFile.Inst)
          (Said : ℕ → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop),
          T₀.I₃ 2 = ThrS Th₃ Said 2 ∧
          OwnTestDebts F₀ A.Z h.places h.firstChain A.H c O.open₃.ownMany Th₃ Said)
      fun _ _ _ _ _ => ⟨thread₃ h O.open₃ R, said₃ h O.open₃ R, rfl,
        ownTestDebts_at_the_letters h O.open₃ R _ (rowsSay R _)⟩

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **THE KIND K12's THREE SHARES AT THE NAMED FAMILY OF INVARIANTS.** Of
the request's own test rowsSay alone is left. -/
theorem k12_share_at_the_threads
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
      Johnson.M1.BudOwed A.F L)
    (rowsSay : ∀ (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (k : Coins A.B)
      (st : h.description.S₃) (m₀ : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
      (c : RowCoins [(firstPart O.open₃.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
          (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart O.open₃.ownMany.toRun.toTest]),
      ThrS (thread₃ h O.open₃ R) (said₃ h O.open₃ R) 2 k st m₀ E₀ →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) placeW
        [(firstPart O.open₃.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix
                              IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart O.open₃.ownMany.toRun.toTest] 0 = .ok c →
      SaysAt O.open₃.ownMany m₀.st.input (frontOf m₀)
        (restCoins O.open₃.ownMany.toRun.toTest c.2.1)) :
    KindShare A (theGOfReturn made h T K) A.H (K12Rel Z Ry)
      (O.threadsAtRelation made (theGOfReturn made h T K) (theGOfReturn_prover made h T K) hRel)
          KindName.K12 :=
  k12_share_at_theGOfReturn made h T K hK₁ hK₂ hK₃ hK₄ Ry _ pays on₁ bud₁ O.open₃.ownMany
    O.open₃.ownIsTheFilling
    (k12_left₃_at_the_threads made O _ (theGOfReturn_prover made h T K) hRel rowsSay)

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_left₃_at_the_threads
#print axioms AtFullSide.K12.k12_share_at_the_threads
