-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionRunDebtsAtTheG.lean: the lists of the attention segments' own rounds (kind K5: the label of
that sub-protocol in the description) at G as E2E/TheG.lean lays it at a return of the base maker: each
is a row of the lot, there is none in the two other chains, On holds at all arguments, and the clause on
positions holds.

  AttentionListsAt              those five statements, at any sides
  attention_lists_at_rows       CONDITIONAL: made; e; hl; hAlone; hk; hb: at the rows that KindRows lays
  attention_lists_at_theG       CONDITIONAL: made; h; hk: at theGAtBase

What the law says and does not say is in the head of Honest/K5/Law/AttentionAtAFilling.lean.
No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.AttentionAtTheG
import E2E.AttentionRunDebts

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (baseMaker baseFilling theGAtBase)
open VerifiableInference.Desc (FileDescription KindName)

variable {W₀ Rc X₀ X : Type}

/-- **The five statements on the lists of this kind.** -/
structure AttentionListsAt {F : FileDescription ProofFile.Inst} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc OnBytes.TableKey Cells X₀ X)
    (rows : List (Unlettered (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst)) :
    Prop where
  /-- each list of this kind in the first chain is a row -/
  first : ∀ L ∈ G.first, L.place.kind = KindName.K5 → L.bare ∈ rows
  /-- the shared chain has no list of this kind -/
  noneShared : ∀ L ∈ G.shared, L.place.kind ≠ KindName.K5
  /-- the last chain has no list of this kind -/
  noneSecond : ∀ L ∈ G.second, L.place.kind ≠ KindName.K5
  /-- On holds at all arguments -/
  on : ∀ L ∈ G.first, L.place.kind = KindName.K5 → ∀ v ca m front, L.On v ca m front
  /-- the clause on positions, at every number of rounds and trees in front and all draws -/
  bud : ∀ L ∈ G.first, L.place.kind = KindName.K5 → ∀ σ, L.side F.first.blocksInOrder = some σ →
    ∀ u ∈ σ.members, ∀ (n N : Nat) (ρ : Draws),
      L.bud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length)) N)

/-- **At the rows that the kinds lay, at a description equal to the return's.** CONDITIONAL: made; e; hl;
hAlone; hk; hb: the letters leave a first-chain row whole. -/
theorem attention_lists_at_rows {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} (made : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {F : FileDescription ProofFile.Inst} (e : F = A.F) (hl : AttentionLawAt A) (K : KindRows P A.Z A.G)
    (Ls : Letters F A.B W₀ Rc OnBytes.TableKey Cells X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hAlone : ∀ M ∈ P.lots, M = k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 ∨
      ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K5)
    (hk : k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3 ∈ K.lots)
    (hb : ∀ u, (Ls.first u).bare = u) :
    AttentionListsAt (theSides F Ls K.slots.rows f₁ f₂ f₃) (rowsOfReturn A) := by
  subst e
  obtain ⟨-, -, -, -, -, -, -, -, eS, eT, -⟩ := atPure_ok made
  refine ⟨attention_list_is_row hAlone hk hb, fun L hL hkind => ?_, fun L hL hkind => ?_,
    attention_list_on hl hAlone hk hb, attention_list_bud hl hAlone hk hb⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hu
    have eh := overlayRow_half (K.shared_fit h hh)
    have ep : (Ls.shared (overlayRow K.shared h)).place = h.place := by
      rw [(Ls.keeps₂ _).1]
      exact congrArg Placed.place eh
    rw [ep] at hkind
    exact hl.kindPlaces.2.2.2.1 h (by rw [eS]; exact hh) hkind
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hu
    have eh := overlayRow_half (K.second_fit h hh)
    have ep : (Ls.second (overlayRow K.second h)).place = h.place := by
      rw [(Ls.keeps₃ _).1]
      exact congrArg Placed.place eh
    rw [ep] at hkind
    exact hl.kindPlaces.2.2.2.2 h (by rw [eT]; exact hh) hkind

/-- **At G at a return of the base maker.** CONDITIONAL: made; h; hk: this kind's lot is among the lots
that K lays. -/
theorem attention_lists_at_theG {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}
    (made : baseMaker files = .ok A) (h : ProofFile.Honest.FirstThread.HeadAtReturn files A)
    (T : AtPublicFiles.TheG.ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hk : k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3 ∈
      K.lots) :
    AttentionListsAt (theGAtBase h T K) (rowsOfReturn A) :=
  attention_lists_at_rows made (ProofFile.Honest.atPure_at_laid h.head.laid made).2.symm
    (AtPublicFiles.AtFiles.HonestTerm.Attention.attention_law_at_base made h.head) K _ _ _ _
    (lot_alone _ _ _ _ (k5_pair_only _ _ _ _) A.Z A.G) hk fun _ => rfl

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.AttentionListsAt
#print axioms AtPublicFiles.TheSides.attention_lists_at_rows
#print axioms AtPublicFiles.TheSides.attention_lists_at_theG
