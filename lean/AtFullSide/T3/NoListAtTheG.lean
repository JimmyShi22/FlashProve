-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/NoListAtTheG.lean: THE KINDS WITH NO LIST. K9, K15 and frame have no side at the base prover, in any of its
three chains; so at any sides whose prover is the return's they have no list, and the share of each holds with nothing to show.
This file proves zero knowledge of nothing.
-/
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsByKind
import Johnson.P1K8R.PinAtFill
import AtFullSide.K12.ReturnsAtFillW
import AtFullSide.K14.Sim.RestKinds

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section

namespace VerifiableInference.Compilation
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription KindName Place)

section General
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **No prover's side of a kind, no list of it**, at sides whose prover is H. -/
theorem noList_of_prover (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (hP : G.prover H = H) {κ : KindName} (h₁ : ∀ g ∈ H.first, g.place.kind ≠ κ)
    (h₂ : ∀ g ∈ H.shared, g.place.kind ≠ κ) (h₃ : ∀ g ∈ H.second, g.place.kind ≠ κ) :
    (∀ L ∈ G.first, L.place.kind ≠ κ) ∧ (∀ L ∈ G.shared, L.place.kind ≠ κ) ∧
      ∀ L ∈ G.second, L.place.kind ≠ κ := by
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩
  · have hm : (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _) ∈ (G.prover H).first :=
      List.mem_map.2 ⟨L, hL, rfl⟩
    rw [hP] at hm
    exact h₁ _ hm
  · have hm : (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _) ∈ (G.prover H).shared :=
      List.mem_map.2 ⟨L, hL, rfl⟩
    rw [hP] at hm
    exact h₂ _ hm
  · have hm : (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _) ∈ (G.prover H).second :=
      List.mem_map.2 ⟨L, hL, rfl⟩
    rw [hP] at hm
    exact h₃ _ hm

end General

section Share
variable {W₀ Rc Tr X₀ X : Type}

/-- **A kind with no list has a share**, with nothing to show. -/
theorem kindShare_of_noList {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X}
    {H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X} {Rel : W₀ → Rc → ProofFile.Inst → Prop}
    {T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B (G.prover H) w₀ rc x k R} {κ : KindName}
    (h₁ : ∀ L ∈ G.first, L.place.kind ≠ κ) (h₂ : ∀ L ∈ G.shared, L.place.kind ≠ κ)
    (h₃ : ∀ L ∈ G.second, L.place.kind ≠ κ) : KindShare A G H Rel T κ where
  pays := ⟨fun L hL e => absurd e (h₁ L hL), fun L hL e => absurd e (h₂ L hL),
    fun L hL e => absurd e (h₃ L hL)⟩
  bud := Johnson.M1.kindBud_none h₁ h₂ h₃
  on := fun _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun L hL e => absurd e (h₁ L hL), fun L hL e => absurd e (h₂ L hL),
      fun L hL e => absurd e (h₃ L hL)⟩

end Share

section Base
variable {W₀ : Type}

/-- The kinds with no side at the base prover. -/
abbrev Unlaid (κ : KindName) : Prop := κ = .K9 ∨ κ = .K15 ∨ κ = .frame

/-- **No side of the filling's lots stands at a kind that is unlaid.** -/
theorem lots_unlaid (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {κ : KindName} (hκ : Unlaid κ) :
    ∀ L ∈ (onlineProverPartsInUse I o S O).lots, ∀ Z G, ∀ x ∈ L.halves Z G, x.place.kind ≠ κ := by
  intro L hL Z G x hx
  have e : (onlineProverPartsInUse I o S O).lots =
      (ownPairsCP (LongLots.plain o S O) I S O).map (·.1) ++ [wLotAt I o O] := rfl
  rw [e] at hL
  rcases List.mem_append.1 hL with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    rw [ownPairsCP_kinds S O (FirstFill.longKinds_plain I o S O Z G) r hr x hx]
    simp only [ownPairsCP, ownPairsC, FirstFill.ownPairs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hκ with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain rfl := List.mem_singleton.1 h
    rw [P1K8.wLot_kind I o O Z G x hx]
    rcases hκ with rfl | rfl | rfl <;> decide

/-- The six sides of the shared chain stand at places of the kinds K14 and K1. -/
theorem six_kinds {S Cl Wa Rca Ky X' : Type} {P : Desc.K14.P14}
    {bs : List (VerifiableInference.Desc.Block S Cl)} {weights : Wa → Weights}
    {rand : Rca → TableRand}
    {six : List (Placed Empty (Common Wa Rca Ky) X')}
    (h : K14.sixOf P bs weights rand = .ok six) {κ : KindName} (hκ : Unlaid κ) :
    ∀ g ∈ six, g.place.kind ≠ κ := by
  unfold K14.sixOf at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl : _ = six := Except.ok.inj h
      intro g hg
      simp only [K14.proverSidesOfSharedRounds, K14.proverSidesOfSharedSendings, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hg
      rcases hκ with rfl | rfl | rfl <;>
        rcases hg with ((rfl | rfl | rfl) | hg) | rfl | rfl
      all_goals first
        | (simp [K14.place, K14.sendPlace]; done)
        | (split at hg
           · obtain rfl := List.mem_singleton.1 hg
             simp [K14.place]
           · cases hg)

/-- Where the six sides are made they stand at no kind that is unlaid. -/
theorem nowShared_unlaid {weights : W₀ → Weights} {Z : ProofFile.Pub}
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    (h : nowSharedBy weights Z = .ok six) {κ : KindName} (hκ : Unlaid κ) :
    ∀ g ∈ six, g.place.kind ≠ κ := by
  unfold nowSharedBy at h
  cases hp : p14At Z with
  | none =>
    rw [hp] at h
    cases h
  | some P =>
    rw [hp] at h
    cases hs : ProofFile.onlineSharedChain Z with
    | none =>
      rw [hs] at h
      cases h
    | some s =>
      rw [hs] at h
      exact six_kinds h hκ

/-- **At what the maker returns at the base filling no side stands at a kind that is unlaid.** -/
theorem base_unlaid (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {o' : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (made : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) {κ : KindName}
    (hκ : Unlaid κ) :
    (∀ g ∈ A.H.first, g.place.kind ≠ κ) ∧ (∀ g ∈ A.H.shared, g.place.kind ≠ κ) ∧
      ∀ g ∈ A.H.second, g.place.kind ≠ κ := by
  obtain ⟨-, -, -, -, -, -, -, h₁, h₂, h₃, -⟩ := atPure_ok made
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · rw [h₁] at hg
    obtain ⟨M, hM, hx⟩ := List.mem_flatMap.1 hg
    exact lots_unlaid I o S O hκ M hM _ _ g hx
  · rw [h₂] at hg
    have hg' : g ∈ K12.AtProof.sharedWithUO I A.Z := hg
    unfold K12.AtProof.sharedWithUO at hg'
    split at hg'
    · rename_i six e
      have hr := K12.AtProof.rest_kind (I.weights A.Z)
        (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z
      have hk : g ∈ six ∨ g.place.kind = KindName.K12 := by
        rcases List.mem_append.1 hg' with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · exact Or.inr (hr g (List.mem_append_left _ h))
        · exact Or.inr (hr g (List.mem_append_right _ h))
      rcases hk with h | h
      · exact nowShared_unlaid e hκ g h
      · rw [h]
        rcases hκ with rfl | rfl | rfl <;> decide
    · cases hg'
  · rw [h₃] at hg
    have hg' : g ∈ secondW I o S O A.Z A.G := hg
    unfold secondW at hg'
    split at hg'
    · rw [AtFullSide.K12.halfW_place _ _ _ _ _ _ _ _ A.Z A.G _ hg']
      rcases hκ with rfl | rfl | rfl <;> decide
    · cases hg'

end Base

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.noList_of_prover
#print axioms VerifiableInference.Compilation.kindShare_of_noList
#print axioms VerifiableInference.Compilation.lots_unlaid
#print axioms VerifiableInference.Compilation.six_kinds
#print axioms VerifiableInference.Compilation.nowShared_unlaid
#print axioms VerifiableInference.Compilation.base_unlaid
