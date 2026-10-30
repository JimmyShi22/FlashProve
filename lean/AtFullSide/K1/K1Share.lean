-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1Share.lean: the shared "sending" (the kind K1): **K1's SHARE OF THE ROWS OF ZERO KNOWLEDGE's ONE THEOREM**: one term of ProofFile.Honest.KindShare
(Honest/Law/RowDebtsByKind.lean: pays · bud · on) at G := theGOfReturn made h T K (E2E/TheG.lean), H := A.H, at the base filling, in scope, where the gate
accepts: GENERAL in the threads' parts T, the kinds' rows K, the relation Rel and THE FAMILY OF INVARIANTS Th (a binder of the theorem that takes the share).

  Premises: the three memberships on K (our two lots among K.lots; the shared chain's two sendings' rows among K.shared), and ONE NAMED DEBT:
  SendingsOnAtRun   at every run of the premise's prefix: OnAtRun₂ at the lists of G.shared at places of the kind K1. These two rows' On is
                    pointApart ⟨qAt …, 0⟩ m.st.heard, that is 0 ≠ m.st.heard.length: "a challenge has been heard". It is had from a thread's invariant
                    (another house's on₂_row, six_on_at_head: at I₂ := ThrS T₂ S₂); at a family Th whose invariants are letters it must come off the
                    run itself (the state that midSharedAtW returns at the address): NOT TYPED: a premise here, named, not begged

  bud_any           BudOwed at a job's laid row, at any description equal to the return's, any thread's letters (handIn_at_return's fourth clause)
  budOwed₂_congr    what a shared list owes reads its place, its row and its bound alone
  kindBud_K1_headG, kindBud_K1_ofReturn   **bud**: Johnson.M1.KindBud G .K1: the 52 by bud_any; the two by another house's sendings_budOwed₂; none in the last chain
  k1_on_first       the 52 lists' On holds always
  k1_stands         THE ROWS STAND: each list of G.first at a place of the kind K1 has a side (with k1_lists_first: there are 52)
  **k1Share_ofReturn**   KindShare A (theGOfReturn made h T K) A.H Rel Th .K1

Limits. SendingsOnAtRun is owed. pays: all limits of KindPaysK1AtTheG.lean (Good at predicates that never hold; clause 2 called). That the two
shared lists have sides: six_at_atPure, not restated. The base filling alone. No property of the protocol is claimed.
-/
import AtFullSide.K1.K1LaidOfMembers
import AtFullSide.K1.K1ListsAtTheG
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import Johnson.M1.BudSendings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open VerifiableInference.Compilation (KindPays)
open OnBytes (TableKey)
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim ProofFile.Honest.Term
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG
open Johnson.M1 (KindBud BudOwed BudOwed₂ budOwed_congr sendings_budOwed₂)

variable {Z : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **BudOwed at a job's laid row**, at any description equal to the return's. -/
theorem bud_any (hS : VerifierAndGoals.InScope Z = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) {F' : FileDescription Inst} (e : A.F = F')
    (T' : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Thread A.B F'.S₁ F'.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst)
    (Sd' : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit → Prop) :
    ∀ r ∈ rowsOfLots A.Z A.G [baseLotS, baseWS], BudOwed F' (r.lay T' Sd' F'.first.blocksInOrder) := by
  subst e
  intro r hr
  rw [rows_eq] at hr
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
  exact (handIn_at_return (pre₀ := []) hS hL matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest made
    .own A.B [] 0 0 T' Sd' [] J hJ _ rfl).2.2.2.1

/-- What a shared list owes reads its place, its row and its bound alone. -/
theorem budOwed₂_congr {Xi V W Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {L L' : Lettered Bk F.S₂ F.Cl V W Y Pb} (hp : L.place = L'.place) (hr : L.row = L'.row)
    (hb : ∀ a b c, L'.bud a b c → L.bud a b c) (h : BudOwed₂ F L') : BudOwed₂ F L := by
  intro σ hσ u hu pre t n hc hn ρ hρ
  have hσ' : L'.side F.shared.blocksInOrder = some σ := by
    unfold Lettered.side at hσ ⊢
    rw [← hp, ← hr]
    exact hσ
  exact hb _ _ _ (h σ hσ' u hu pre t n hc hn ρ hρ)

/-- **bud, at the head's description.** -/
theorem kindBud_K1_headG (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (made : baseMaker Z = .ok A)
    (h : HeadAtReturn Z A) (T : ThreadParts A Wt) (K : KindRows (baseFilling Z) A.Z A.G)
    (hK : K1Laid h K) : KindBud (theG h T K) .K1 := by
  refine ⟨fun L hL' hk => ?_, fun L hL' hk => ?_, fun L hL' hk => absurd hk (none₃_at_theG h T K L hL')⟩
  · obtain ⟨r, hr, c1, c2, -, c4⟩ := rows₁_at_theG h T K hK L hL' hk
    exact budOwed_congr (L' := r.lay (ProofFile.Honest.FirstThread.firstThread h T.first) (fun _ => SaidOk)
        h.description.first.blocksInOrder) c1 c2 (fun a b c hb => by rw [c4]; exact hb)
      (bud_any hS hL made (ProofFile.Honest.atPure_at_laid h.head.laid made).2 _ _ r hr)
  · obtain ⟨r, hr, c1, c2, -, c4⟩ := rows₂_at_theG h T K hK L hL' hk
    exact budOwed₂_congr (L' := r.lay (ProofFile.Honest.FirstThread.sharedThread h T.reads T.shared)
        (fun _ => SaidOk) h.description.shared.blocksInOrder) c1 c2 (fun a b c hb => by rw [c4]; exact hb)
      (sendings_budOwed₂ hS hL (P5J.dpZ_live hL ▸ h.head.laid) 0 _ _ _ _ r hr)

/-- **bud, at the description that the return holds.** -/
theorem kindBud_K1_ofReturn (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (made : baseMaker Z = .ok A)
    (h : HeadAtReturn Z A) (T : ThreadParts A Wt) (K : KindRows (baseFilling Z) A.Z A.G)
    (hK : K1Laid h K) : KindBud (theGOfReturn made h T K) .K1 :=
  castSides_of (Q := fun _ G₀ => KindBud G₀ .K1) _ (kindBud_K1_headG hS hL made h T K hK)

/-- The lists of the first chain at places of the kind K1 bear our rows, at the description that the return holds. -/
theorem rows₁_ofReturn (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hK : K1Laid h K) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [baseLotS, baseWS],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud :=
  castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [baseLotS, baseWS],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) _ (rows₁_at_theG h T K hK)

/-- **The 52 lists' On holds always.** -/
theorem k1_on_first (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hK : K1Laid h K) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K1 → ∀ u ca m front, L.On u ca m front := by
  intro L hL' hk u ca m front
  obtain ⟨r, hr, -, -, c3, -⟩ := rows₁_ofReturn made h T K hK L hL' hk
  rw [rows_eq] at hr
  obtain ⟨J, -, rfl⟩ := List.mem_map.1 hr
  rw [c3]
  trivial

/-- **THE ROWS STAND: each list of the first chain at a place of the kind K1 has a side.** -/
theorem k1_stands (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hK : K1Laid h K) :
    ∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K1 →
      ∃ σ, L.side A.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ := by
  intro L hL' hk
  obtain ⟨r, hr, c1, c2, -, -⟩ := rows₁_ofReturn made h T K hK L hL' hk
  rw [rows_eq] at hr
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
  obtain ⟨σ, hσ, -⟩ := side_at_return matrixInput id id OnBytes.HonestTrace.Sz.ref openHonest made
    (theGOfReturn made h T K).falls₁ J hJ
  refine ⟨σ, ?_⟩
  unfold Lettered.side
  rw [c1, c2]
  exact hσ

/-- **THE NAMED DEBT: On at the run at the shared chain's two sendings' lists.** -/
def SendingsOnAtRun (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k R) : Prop :=
  ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
    (hR : ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R) ρ r,
    ρ.due A.F = true → silentAt A.F ((theGOfReturn made h T K).prover A.H) w₀ rc x ρ = none →
    runC A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k ρ = .ok r →
    ∀ L ∈ (theGOfReturn made h T K).shared, L.place.kind = .K1 →
      OnAtRun₂ (G := theGOfReturn made h T K) (H := A.H) (Th w₀ rc x hrel k R hR) ρ r L

/-- **K1's SHARE.** -/
theorem k1Share_ofReturn (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (made : baseMaker Z = .ok A)
    (h : HeadAtReturn Z A) (T : ThreadParts A Wt) (K : KindRows (baseFilling Z) A.Z A.G)
    (h1 : baseLotS ∈ K.lots) (h2 : baseWS ∈ K.lots) (h3 : ∀ r ∈ baseSendings h, r ∈ K.shared)
    (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k R)
    (on₂ : SendingsOnAtRun made h T K Rel Th) :
    KindShare A (theGOfReturn made h T K) A.H Rel Th .K1 where
  pays := kindPays_K1_of_mem hS hL made h T K h1 h2 h3
  bud := kindBud_K1_ofReturn hS hL made h T K (k1Laid_of_mem h K h1 h2 h3)
  on := fun w₀ rc x hrel k R hR ρ r due silent run =>
    ⟨fun L hL' hk => onAtRun₁_of_always _ ρ r (k1_on_first made h T K (k1Laid_of_mem h K h1 h2 h3) L hL' hk),
      on₂ w₀ rc x hrel k R hR ρ r due silent run,
      fun L hL' hk => absurd hk (castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.second, L.place.kind ≠ .K1) _
        (none₃_at_theG h T K) L hL')⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.bud_any
#print axioms AtFullSide.K1.budOwed₂_congr
#print axioms AtFullSide.K1.kindBud_K1_headG
#print axioms AtFullSide.K1.kindBud_K1_ofReturn
#print axioms AtFullSide.K1.k1_on_first
#print axioms AtFullSide.K1.k1_stands
#print axioms AtFullSide.K1.k1Share_ofReturn
