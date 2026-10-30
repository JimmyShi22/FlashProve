--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/KindPaysAtTheBase.lean: THE KIND K6 ("the output head's own rounds") PAYS, AT
THE SIDES THAT `theSides` BUILDS OVER THE ONE BASE MAKER's RETURN: `VerifiableInference.Compilation.KindPays G .K6`
(Johnson/T3/OwedOfKinds.lean: the fields fits, exact and fresh of `Good` at every list of the kind, in all
three chains; NOT `ProofFile.Honest.KindPays` of Honest/Law/ReadyOfSides.lean, which says that the book lends a
kind's sides their runs), and K6's two
conditions of use (Honest/K6/Term/ConditionsOfUse.lean), where G is `theSides returned.F Ls (overlaySlots
(baseFilling files) … mine …).rows f₁ f₂ f₃` (E2E/TheSides.lean) at ANY list `mine` of kinds' lots that holds
K6's lot, any rows of the two other chains that fit the filling, and any falls. A call of other authors'
`kindPays_of_lot` and `rows_of_overlay` (E2E/KindPaysOfALot.lean) at K6's hand-in.

WHAT IS ASKED OF THE LETTERS Ls. For `KindPays`: that at K6's row they narrow On and bud and no more
(`Narrows`). For the conditions of use: that at K6's row they leave On and bud AS THEY ARE
(`(Ls.first u).bare = u`): at an On that is narrower than the row's, "On at the run" would be a debt again.
`Letters.bare` and `Letters.ofThreads` leave them as they are (`bareLettersLeaveARowWhole`,
`threadsLettersLeaveARowWhole`). LETTERS THAT NARROW On OR bud TO "NEVER" MEET `Narrows`, AND THEN `exact` AND `fresh` ASK
NOTHING AT K6: `KindPays` alone does not bite; what bites is "On at the run" and `BudDebts` at the same
letters. The statements to count on stand under "whole", all at one G: Honest/K6/Term/PaysAtTheG.lean.

WHAT IT IS NOT.
  * NOT zero knowledge and NOT hiding of anything. THE SPENDER's HALF: fits, exact and an empty fresh at simulators
    that read their own coins alone. That K6's 173 spent coins are fresh is owed with the owner's kind, K2:
    here it FOLLOWS from `KindPays G .K2`, which stays a premise.
  * NOT "the one G" by name: mine, the two other chains' rows, the letters and the falls are arguments.
  * `plays` and `acc` of `Good` are left unasked by `KindPays`' own form (they are met here at A := False), and
    the rule that takes `KindPays` ends in `Owed` at the muted lists. The equation of views needs neither
    field. BUT `acc` was the one field that could show that a run ever CALLS K6's parts: so that what is said
    here is not idle at K6 hangs on acceptance at the same description, book, prover and lists, which no
    file states.
  * In the shared and the second chain K6 pays for want of a member of the kind in the description.
  * At the base prover, which is not the prover that plays. In scope, where the library's test passes.

  `bareLettersLeaveARowWhole`, `threadsLettersLeaveARowWhole`   the two ways of setting letters that
        E2E/TheSides.lean has leave a row's On and bud as they are
  `otherLotsLayNoSideOfTheKind`   of the base filling's thirteen lots, each but the head's lays no side of the kind
  `headKindPays_at_the_base_prover`   **`KindPays G .K6`**
  `headListsBear_at_the_base_prover`   `ListsOfTheKindBear G .K6 rows`: the one premise of the conditions of use
  `headConditionsOfUse_at_theSides`   so both conditions of use at that G
  `noEntryBeyondTheEight`   the maker's book has no spending entry for a part of number 8 or more at K6's place
  `ownerFreshK6_of_the_owners_kind`   **`OwnerFreshK6 G` (Honest/K6/Term/OwedBeside.lean) FROM `KindPays G .K2`**:
        that K6's 173 spent coins are fresh is one projection of what the owner's kind pays. `KindPays G .K2`
        is a premise
  `ownerFreshK6_at_the_base_prover`   the same at the base maker's return, at every G there
-/
import E2E.KindPaysOfALot
import Johnson.Desc.ProofFile.Honest.K6.Term.BookLends
import Johnson.Desc.ProofFile.Honest.K6.Term.OwedBeside
import Johnson.Desc.ProofFile.Honest.K6.Term.SideAsAList
import Johnson.Desc.ProofFile.Honest.K6.Term.SlotAtTheFilling
import Johnson.Desc.ProofFile.Honest.K6.Term.ConditionsOfUse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain KindName)
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.TheSides (Letters theSides overlaySlots Narrows narrows_of_bare kindPays_of_lot rows_of_overlay
  block_of_seated)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- The letters that say nothing leave a row of the first chain as it is. -/
theorem bareLettersLeaveARowWhole {Xi W₀ Rc Ky Tr X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi)
    (Bk : ProverCoinCounts) (u : Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) :
    ((Letters.bare (Ky := Ky) (X₀ := X₀) F Bk).first u).bare = u := rfl

/-- The letters of the threads leave a row of the first chain as it is. -/
theorem threadsLettersLeaveARowWhole {Xi W₀ Rc Ky Tr X₀ X : Type}
    (F : VerifiableInference.Desc.FileDescription Xi) {Bk : ProverCoinCounts}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (u : Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) :
    ((Letters.ofThreads F T₁ T₂ T₃ S₁ S₂ S₃).first u).bare = u := rfl

/-- **Of the base filling's thirteen lots, each either bears the name of the head's lot or lays no side of
the kind K6.** No premise. -/
theorem otherLotsLayNoSideOfTheKind {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      M.name = "the output head's own rounds (K6)" ∨ ∀ x ∈ M.halves Zq G, x.place.kind ≠ .K6 := by
  intro M hM
  rw [fillPairs_lots] at hM
  obtain ⟨pair, isPair, rfl⟩ := List.mem_map.1 hM
  by_cases same : pair.2 = KindName.K6
  · left
    have among : pair.1 ∈ ((fillPairs I o S O).filter fun p => p.2 == KindName.K6).map (·.1) :=
      List.mem_map_of_mem (List.mem_filter.2 ⟨isPair, beq_iff_eq.2 same⟩)
    rw [Term.headPairAlone] at among
    rw [List.mem_singleton.1 among]
    rfl
  · right
    intro x hx e
    exact same ((fillPairs_kinds I o S O Zq G pair isPair x hx).symm.trans e)

section
variable (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned)
    (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (named : ∀ s ∈ mine, (ProofFile.Honest.Term.baseFilling files).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (ProofFile.Honest.Term.baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (ProofFile.Honest.Term.baseFilling files).shared returned.Z returned.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst))
    (h₃ : second.map (·.half) = (ProofFile.Honest.Term.baseFilling files).second returned.Z returned.G)
    (Ls : Letters returned.F returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall returned.F.S₁)) (f₂ : List (Fall returned.F.S₂)) (f₃ : List (Fall returned.F.S₃))
    (laid : headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights ∈ mine)
include scope live made laid

/-- CONDITIONAL: in scope; the library's test passes; this is the base maker's return; K6's lot is among the
lots laid over the filling's; the letters narrow On and bud at K6's row (letters that narrow them to
"never" do, and then `exact` and `fresh` ask nothing). **`KindPays G .K6`.** -/
theorem headKindPays_at_the_base_prover
    (narrows : ∀ u ∈ (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G, Narrows (Ls.first u) u) :
    VerifiableInference.Compilation.KindPays (theSides returned.F Ls
      (overlaySlots (ProofFile.Honest.Term.baseFilling files) returned.Z returned.G mine named apart hm shared hs
        second h₃).rows f₁ f₂ f₃) .K6 := by
  obtain ⟨places, firstChain, row, s⟩ := simulatorShare_at_the_base_prover files scope live made
  have stands := s.sideAndBook.stands
  rw [← s.description] at stands
  refine kindPays_of_lot mine named apart hm shared hs second h₃ Ls f₁ f₂ f₃ .K6
    [headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights]
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact laid) ?_ ?_ ?_ ?_
  · intro M hM
    rcases otherLotsLayNoSideOfTheKind matrixInput _ _ _ returned.Z returned.G M hM with name | none
    · exact Or.inl ⟨_, List.mem_singleton.2 rfl, name.symm⟩
    · exact Or.inr none
  · intro l hl u hu _ σ hσ
    obtain rfl := List.mem_singleton.1 hl
    exact ⟨narrows u hu, _, _, s.share.good u hu f₁ σ hσ _ fun _ _ _ _ => False⟩
  · intro u _ hk σ hσ
    obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (by rw [e]; exact hk) (stands.2.2.1 b hb)
  · intro u _ hk σ hσ
    obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (by rw [e]; exact hk) (stands.2.2.2 b hb)

/-- CONDITIONAL: as above, and the letters leave K6's row as it is. **The lists of the kind at that G are the
lot's rows, in the first chain alone.** -/
theorem headListsBear_at_the_base_prover
    (whole : ∀ u ∈ (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G, (Ls.first u).bare = u) :
    ListsOfTheKindBear (theSides returned.F Ls
      (overlaySlots (ProofFile.Honest.Term.baseFilling files) returned.Z returned.G mine named apart hm shared hs
        second h₃).rows f₁ f₂ f₃) .K6
      ((headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z returned.G) := by
  obtain ⟨places, firstChain, row, s⟩ := simulatorShare_at_the_base_prover files scope live made
  obtain ⟨-, -, -, -, -, -, -, -, e₂, e₃, -⟩ := atPure_ok made
  refine ⟨?_, ?_, ?_⟩
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₁ u).1] at hk
    obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit)
      matrixInput.weights]) apart (fun l hl => by rw [List.mem_singleton.1 hl]; exact laid) hm
      (fun M hM => by
        rcases otherLotsLayNoSideOfTheKind matrixInput _ _ _ returned.Z returned.G M hM with
          name | none
        · exact Or.inl ⟨_, List.mem_singleton.2 rfl, name.symm⟩
        · exact Or.inr none) u hu hk
    obtain rfl := List.mem_singleton.1 hl
    rw [whole u hul]
    exact hul
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₂ u).1] at hk
    have side : u.half ∈ returned.H.shared := by
      rw [e₂, ← hs]
      exact List.mem_map_of_mem hu
    exact s.sideAndBook.noneShared _ side hk
  · intro L hL hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
    rw [(Ls.keeps₃ u).1] at hk
    have side : u.half ∈ returned.H.second := by
      rw [e₃, ← h₃]
      exact List.mem_map_of_mem hu
    exact s.sideAndBook.noneLast _ side hk

/-- CONDITIONAL: as above. **K6's two conditions of use at that G**: its share of `BudDebts` and of "On at the
run, list by list". -/
theorem headConditionsOfUse_at_theSides
    (whole : ∀ u ∈ (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).rows returned.Z
      returned.G, (Ls.first u).bare = u) :
    HeadConditionsOfUse returned (theSides returned.F Ls
      (overlaySlots (ProofFile.Honest.Term.baseFilling files) returned.Z returned.G mine named apart hm shared hs
        second h₃).rows f₁ f₂ f₃) :=
  headConditionsOfUse_at_the_base_prover files scope live made
    (headListsBear_at_the_base_prover files scope live made mine named apart hm shared hs second h₃ Ls f₁
      f₂ f₃ laid whole)

end

/-! ## The owner's debt, from the owner's kind -/

section
variable {W₀ Rc X₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the library's hypothesis; the maker returns. **The maker's book has no spending entry for
a part of number 8 or more at K6's place.** reader: any; it is not read. -/
theorem noEntryBeyondTheEight (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {P : OnlineProverParts W₀ Rc Cells X₀ Unit} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (reader : Local W₀ Rc Inst Cells → HeadAsk) :
    ∀ o i, 8 ≤ i → A.B.spentBy o ⟨IM.k6Place, i⟩ = [] := by
  obtain ⟨member, isMember, atPlace⟩ := k6_member_there h
  have none := (Term.sixTestsAtTheMember h hA reader isMember atPlace).2.2.2.2.1
  intro o i hi
  refine List.filter_eq_nil_iff.2 fun e he hf => ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  refine List.any_eq_false.1 none e he ?_
  rw [hf.1.2, atPlace]
  simp only [beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
  exact hi

end

/-- A list's side stands at the list's place. -/
theorem side_stands_at_the_place {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} {L : Lettered Bk S Cl V W Y Pb}
    {bs : List (VerifiableInference.Desc.Block S Cl)} {fs : List (Fall S)} {σ : Side S Cl V W Y Pb}
    (h : L.side bs fs = some σ) : σ.block.place = L.place := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact eq_of_beq (List.find?_some (p := fun b : VerifiableInference.Desc.Block S Cl =>
    b.place == L.place) hb)

/-- CONDITIONAL: book: what the returned book says of K6's row; beyond: it has no spending entry for a part
of number 8 or more; THE OWNER's KIND PAYS. **`OwnerFreshK6 G`: the coins that K6's parts spend are fresh**, in
the sense of the field `fresh` of `Good` at their owner. One projection: every part of which a part of
K6's spends a coin is `headOwner`, which stands at a place of the kind K2. -/
theorem ownerFreshK6_of_the_owners_kind {W₀ Rc X₀ X : Type} {returned : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    {reader : Local W₀ Rc Inst Cells → HeadAsk}
    {numbers : VerifiableInference.Desc.Kinds.Head.Par}
    (book : BookAtTheHead returned reader numbers)
    (beyond : ∀ o i, 8 ≤ i → returned.B.spentBy o ⟨IM.k6Place, i⟩ = [])
    {G : Sides returned.F returned.B W₀ Rc OnBytes.TableKey Cells X₀ X}
    (ownersKindPays : VerifiableInference.Compilation.KindPays G .K2) : OwnerFreshK6 G := by
  intro L hL σ hσ u hu i spends
  have inside : i < 8 := by
    by_contra notInside
    exact spends (beyond _ i (by omega))
  have owner := owner_of_the_heads_coins book _ i inside spends
  have place : σ.block.place = headOwner.place := congrArg Addr.place owner
  have kind : L.place.kind = .K2 := by
    rw [← side_stands_at_the_place hσ, place]
    rfl
  obtain ⟨A', B', good⟩ := ownersKindPays.1 L hL kind σ hσ
  exact ownerFresh_of_good good hu _

/-- **The same at the one base maker's return**, in scope and live, at every G there at which the owner's
kind pays. -/
theorem ownerFreshK6_at_the_base_prover (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : ProofFile.Honest.Term.baseMaker files = .ok returned)
    {G : Sides returned.F returned.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (ownersKindPays : VerifiableInference.Compilation.KindPays G .K2) : OwnerFreshK6 G := by
  obtain ⟨places, firstChain, row, s⟩ := simulatorShare_at_the_base_prover files scope live made
  obtain ⟨Zp, Np, cF, x, h⟩ := head_of_the_two_tests files scope live
  exact ownerFreshK6_of_the_owners_kind s.book
    (noEntryBeyondTheEight h made
      (headWit' id (matrixInput.weights returned.Z) returned.Z returned.G)) ownersKindPays

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.bareLettersLeaveARowWhole
#print axioms ProofFile.Honest.K6.threadsLettersLeaveARowWhole
#print axioms ProofFile.Honest.K6.otherLotsLayNoSideOfTheKind
#print axioms ProofFile.Honest.K6.headKindPays_at_the_base_prover
#print axioms ProofFile.Honest.K6.headListsBear_at_the_base_prover
#print axioms ProofFile.Honest.K6.headConditionsOfUse_at_theSides
#print axioms ProofFile.Honest.K6.noEntryBeyondTheEight
#print axioms ProofFile.Honest.K6.side_stands_at_the_place
#print axioms ProofFile.Honest.K6.ownerFreshK6_of_the_owners_kind
#print axioms ProofFile.Honest.K6.ownerFreshK6_at_the_base_prover
