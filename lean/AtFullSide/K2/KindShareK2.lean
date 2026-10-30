-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KindShareK2.lean: the share of the kind "the code switch" (K2) of the rule's premises at
G at a return of the maker at the base filling: KindPays, the bound and On at every run, in one term.

  first_rows        a list of the kind at such sides is a row of this kind's lot
  kindShare_k2_cast at any letters that keep a row whole, at a description equal to the return's
  kindShare_k2      at theGOfReturn

By: kindPays_k2_rows, PositionsWithinBound in simulatorAtTheBase, onAtRun₁_of_always. On is True at
this kind, so the run is not read.

Limits. K is a letter; that baseSimLot stands in it is the premise hmine. H, Rel and the invariants Th
are letters and nothing is read of them. All limits of simulatorAtTheBase hold.
-/
import AtFullSide.K2.KindPaysAtTheG
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.Term ProofFile.Honest.K2 ProofFile.Honest.FirstFill
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtPublicFiles.TheSides
open AtPublicFiles.TheG (ThreadParts theLetters theGOfReturn)
open VerifiableInference.Desc (KindName FileDescription)

variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **A list of the kind at such sides is a row of this kind's lot.** -/
theorem first_rows (Ls : Letters A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (K : KindRows (baseFilling Z) A.Z A.G)
    (f₁ : List (Fall A.F.S₁)) (f₂ : List (Fall A.F.S₂)) (f₃ : List (Fall A.F.S₃))
    (hmine : baseSimLot ∈ K.lots) :
    ∀ L ∈ (theSides A.F Ls K.slots.rows f₁ f₂ f₃).first, L.place.kind = .K2 →
      ∃ u ∈ baseSimLot.rows A.Z A.G, L = Ls.first u := by
  intro L hL hk
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
  have hu' : u.place.kind = .K2 := by
    rw [← (Ls.keeps₁ u).1]
    exact hk
  have hr := rows_of_overlay (Z := A.Z) (Gr := A.G) K.apart (ls := [baseSimLot])
    (fun l hl => by obtain rfl := List.mem_singleton.1 hl; exact hmine) K.lots_fit
    (fun M hM => by
      rcases lots_alone matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G M hM
        with e | e
      · exact .inl ⟨baseSimLot, List.Mem.head _, e.symm⟩
      · exact .inr e)
  obtain ⟨l, hl, hul⟩ := hr u hu hu'
  obtain rfl := List.mem_singleton.1 hl
  exact ⟨u, hul, rfl⟩

/-- **The kind's share, at letters that keep a row whole.** -/
theorem kindShare_k2_cast (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) {F : FileDescription ProofFile.Inst} (e : A.F = F)
    (Ls : Letters F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (K : KindRows (baseFilling Z) A.Z A.G)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hmine : baseSimLot ∈ K.lots) (hB : ∀ u, (Ls.first u).bare = u)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((castSides e (theSides F Ls K.slots.rows f₁ f₂ f₃)).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((castSides e (theSides F Ls K.slots.rows f₁ f₂ f₃)).prover H) w₀ rc x k R) :
    KindShare A (castSides e (theSides F Ls K.slots.rows f₁ f₂ f₃)) H Rel Th .K2 := by
  subst e
  obtain ⟨pp, read⟩ := H2K.Sizes.inScope_readFiles scope
  obtain ⟨Zp, Np, cF, x₀, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  obtain ⟨-, -, -, hPos, -⟩ := simulatorAtTheBase.2.2 Z scope live
  obtain ⟨o1, o2⟩ := others_no_kind h made
  obtain ⟨-, -, -, -, -, -, -, -, e2, e3, -⟩ := atPure_ok made
  have n2 : ∀ L ∈ (theSides A.F Ls K.slots.rows f₁ f₂ f₃).shared, L.place.kind ≠ .K2 := by
    intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    have hm : u.half ∈ A.H.shared := by
      rw [e2, ← K.slots.shared_fit]
      exact List.mem_map_of_mem hu
    have hk' : u.place.kind = .K2 := by
      rw [← (Ls.keeps₂ u).1]
      exact hk
    exact List.filter_eq_nil_iff.1 o1 _ hm (beq_iff_eq.2 hk')
  have n3 : ∀ L ∈ (theSides A.F Ls K.slots.rows f₁ f₂ f₃).second, L.place.kind ≠ .K2 := by
    intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    have hm : u.half ∈ A.H.second := by
      rw [e3, ← K.slots.second_fit]
      exact List.mem_map_of_mem hu
    have hk' : u.place.kind = .K2 := by
      rw [← (Ls.keeps₃ u).1]
      exact hk
    exact List.filter_eq_nil_iff.1 o2 _ hm (beq_iff_eq.2 hk')
  refine ⟨kindPays_k2_rows scope live made rfl Ls K f₁ f₂ f₃ hmine
      fun u _ => narrows_of_bare (hB u), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro L hL hk σ hσ v hv pre t n hc hn ρ hρ
    obtain ⟨u, hu, rfl⟩ := first_rows Ls K f₁ f₂ f₃ hmine L hL hk
    have eb : (Ls.first u).bud = u.bud := congrArg (·.bud) (hB u)
    rw [eb]
    have hσ' : Side.seated A.F.first.blocksInOrder u.place u.row = some σ := by
      rw [← (Ls.keeps₁ u).1, ← (Ls.keeps₁ u).2]
      exact hσ
    exact hPos FullSizeMatrix IndexCommitterCoins Unit Unit _ A made matrixInput.weights id u hu σ hσ' v hv pre t n hc hn ρ hρ
  · exact fun L hL hk => absurd hk (n2 L hL)
  · exact fun L hL hk => absurd hk (n3 L hL)
  · intro w₀ rc x hrel k R hR ρ r _ _ _
    refine ⟨fun L hL hk => ?_, fun L hL hk => absurd hk (n2 L hL), fun L hL hk => absurd hk (n3 L hL)⟩
    obtain ⟨u, hu, rfl⟩ := first_rows Ls K f₁ f₂ f₃ hmine L hL hk
    refine onAtRun₁_of_always _ ρ r fun v ca m front => ?_
    have eo : (Ls.first u).On = u.On := congrArg (·.On) (hB u)
    obtain ⟨p, -, -, e4, -, -⟩ := row_at_place hu
    rw [eo, e4]
    trivial

/-- **The kind's share at G at the return.** -/
theorem kindShare_k2 {Wt : Type} (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hmine : baseSimLot ∈ K.lots)
    (H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindShare A (theGOfReturn made h T K) H Rel Th .K2 :=
  kindShare_k2_cast scope live made (atPure_at_laid h.head.laid made).2 (theLetters h T) K _ _ _
    hmine (fun u => by cases u; rfl) H Rel Th

end AtFullSide.K2

#print axioms AtFullSide.K2.first_rows
#print axioms AtFullSide.K2.kindShare_k2_cast
#print axioms AtFullSide.K2.kindShare_k2
