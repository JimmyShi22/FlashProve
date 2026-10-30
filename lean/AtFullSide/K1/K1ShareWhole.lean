-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1ShareWhole.lean: the shared "sending" (the kind K1): THE NAMED DEBT OF K1Share.lean, SendingsOnAtRun, PAID OFF THE RUN ITSELF, and so K1's SHARE WITH NO DEBT LEFT
BUT THE THREE MEMBERSHIPS ON K. The shared chain's two sendings' rows have On := pointApart ⟨qAt …, 0⟩ m.st.heard, that is 0 ≠ m.st.heard.length. OnAtRun₂ hands the
state m as what midSharedAtW returns at the part's address, at challenges that are due. Another file's law (point_at_walk, AtFullSide/K14/RowIsWholeAtServedRuns.lean)
says: under the head, at such a state at an address that stands neither at the chain's front nor at "LIN point", the shared point is heard: so the list heard is not
empty. No invariant of a thread is read: so it holds at EVERY family of invariants.

  on₂_of_walk       OnAtRun₂ at a list at one of the two sendings' places whose On is a sending's row's, at a description that equals the head's, at any ThreadsP
  sendingsOn_paid   SendingsOnAtRun made h T K Rel Th, at every Rel and Th
  k1_bears          "bear": every list of the kind K1 in G is one of the kind's own rows (52 | 2 | none)
  **k1Share_whole**     KindShare A (theGOfReturn made h T K) A.H Rel Th .K1 from the three memberships alone

Limits. All limits of K1Share.lean but the debt. point_at_walk is another house's law, called. No property of the protocol is claimed.
-/
import AtFullSide.K1.K1Share
import AtFullSide.K14.RowIsWholeAtServedRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open OnBytes (TableKey)
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.Term
open ProofFile.Honest.K14 (sendingRows simPub pointApart sendPlace place)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG

/-- **On at the run, off the run.** -/
theorem on₂_of_walk {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
    (hd : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type} {F : FileDescription Inst}
    (e : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF) {Bk : ProverCoinCounts} {H : Prover W₀ Rc Inst TableKey Tr X₀ X}
    {G : Sides F Bk W₀ Rc TableKey Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Inst} {k : Coins Bk}
    {R : Ready W₀ Rc Inst TableKey Tr X₀ X} (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws)
    (r : RunC F) (due : ρ.due F = true) (L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (hk : L.place.kind = .K1)
    (hOn : ∀ u ca m front, 0 ≠ m.st.heard.length → L.On u ca m front) :
    OnAtRun₂ (G := G) (H := H) T ρ r L := by
  subst e
  intro σ _ u _ pre t _ m ca _ _ _ _ hmid _
  refine hOn u ca m _ ?_
  have hm : midSharedAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩ =
      .ok (some m) := by
    unfold orRefused at hmid
    cases hq : midSharedAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ
        ⟨L.place, u.number⟩ with
    | error e' => rw [hq] at hmid; cases hmid
    | ok o =>
      rw [hq] at hmid
      cases o with
      | none => cases hmid
      | some m' => cases hmid; rfl
  have hdue : drawsFit (P5J.F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true := by
    unfold Draws.due at due
    simp only [Bool.and_eq_true] at due
    exact due.1.1.2
  have ha₁ : L.place ≠ ⟨2, none, 0, .frame⟩ := by
    intro e'
    rw [e'] at hk
    cases hk
  have ha₂ : L.place ≠ place 1 := by
    intro e'
    rw [e'] at hk
    cases hk
  obtain ⟨d, -, hh⟩ := AtFullSide.K14.point_at_walk hd hdue (a := ⟨L.place, u.number⟩) ⟨ha₁, ha₂⟩ hm
  intro h0
  unfold heardFrom at hh
  have : m.st.heard = [] := List.length_eq_zero_iff.1 h0.symm
  rw [this] at hh
  cases hh

variable {Z : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **THE DEBT, PAID, at every relation and every family of invariants.** -/
theorem sendingsOn_paid (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hK : K1Laid h K) (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k R) :
    SendingsOnAtRun made h T K Rel Th := by
  intro w₀ rc x hrel k R hR ρ r due _ _ L hL' hk
  have rows := castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.shared, L.place.kind = .K1 →
      ∃ r ∈ baseSendings h, L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud)
    (ProofFile.Honest.atPure_at_laid h.head.laid made).2 (rows₂_at_theG h T K hK)
  obtain ⟨q, hq, -, -, c3, -⟩ := rows L hL' hk
  refine on₂_of_walk h.head (ProofFile.Honest.atPure_at_laid h.head.laid made).2 _ ρ r due L hk ?_
  intro u ca m front h0
  rw [c3]
  simp only [baseSendings, sendingRows, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> exact h0

/-- **"BEAR": every list of the kind in G is one of the kind's own rows**: in the first chain one of our 52, in the shared chain one of the two sendings'; in the
last chain there is none. -/
theorem k1_bears (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hK : K1Laid h K) :
    (∀ L ∈ (theGOfReturn made h T K).first, L.place.kind = .K1 →
      ∃ r ∈ rowsOfLots A.Z A.G [baseLotS, baseWS],
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) ∧
    (∀ L ∈ (theGOfReturn made h T K).shared, L.place.kind = .K1 →
      ∃ r ∈ baseSendings h, L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) ∧
    ∀ L ∈ (theGOfReturn made h T K).second, L.place.kind ≠ .K1 :=
  ⟨rows₁_ofReturn made h T K hK,
    castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.shared, L.place.kind = .K1 →
      ∃ r ∈ baseSendings h, L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) _
      (rows₂_at_theG h T K hK),
    castSides_of (Q := fun _ G₀ => ∀ L ∈ G₀.second, L.place.kind ≠ .K1) _ (none₃_at_theG h T K)⟩

/-- **K1's SHARE, WHOLE.** -/
theorem k1Share_whole (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (made : baseMaker Z = .ok A)
    (h : HeadAtReturn Z A) (T : ThreadParts A Wt) (K : KindRows (baseFilling Z) A.Z A.G)
    (h1 : baseLotS ∈ K.lots) (h2 : baseWS ∈ K.lots) (h3 : ∀ r ∈ baseSendings h, r ∈ K.shared)
    (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T K) A.H Rel Th .K1 :=
  k1Share_ofReturn hS hL made h T K h1 h2 h3 Rel Th
    (sendingsOn_paid made h T K (k1Laid_of_mem h K h1 h2 h3) Rel Th)

end AtFullSide.K1

#print axioms AtFullSide.K1.on₂_of_walk
#print axioms AtFullSide.K1.sendingsOn_paid
#print axioms AtFullSide.K1.k1_bears
#print axioms AtFullSide.K1.k1Share_whole
