-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/KindPaysAtTheG.lean: `KindPays … .K4` by its name at
IOP's `theGAtBase` (E2E/TheG.lean), at a filling whose authors' three warnings are being checked, for
every K that holds K4's slot.

  `k4_alone_at_base`   a lot of the base filling either bears K4's name or lays no half of the kind.
  `kindPays_K4_at_theG`   **at `baseMaker`'s return, at the head at that return, for all threads' parts
      and every K with K4's slot: KindPays (theGAtBase h T K) .K4.**
  `kindPays_K4_at_theGOfReturn`   **the same at `theGOfReturn`.**
  `headAtReturn_of_live`   the head at the return, from scope, read and live.
  `k4_rows_in_theG`   at a K with K4's slot each of K4's rows stands in the first list of `theGAtBase`.
  `onlyTheSeventhLotBearsK4sName`, `kindRows_with_K4s_slot`   such a K exists.

Limits. Those of Law/ExactFresh/AtFiles.lean, of which nothing is taken back: THE SPENDER's HALF;
fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False. In the shared and the second chain it holds for
want of a block: TRUE AND EMPTY THERE. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.KindPaysAtBase
import E2E.TheG

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open ProofFile.Honest.Term (baseMaker baseFilling matrixInput theGAtBase)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts)
open AtPublicFiles.TheSides (KindRows block_of_seated kindPays_of_rows narrows_of_bare rows_of_overlay)

/-- **A lot of the base filling either bears K4's name or lays no half of the kind K4.** -/
theorem k4_alone_at_base (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (Gr : ProofFile.Ground) :
    ∀ M ∈ (baseFilling files).lots, (∃ l ∈ [k4BaseSlot], l.name = M.name) ∨
      ∀ x ∈ M.halves Zq Gr, x.place.kind ≠ .K4 := by
  intro M hM
  by_cases hx : ∃ y ∈ M.halves Zq Gr, y.place.kind = .K4
  · obtain ⟨y, hy, hk⟩ := hx
    have hL : ((HLot.byPub matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt),
        KindName.K4) ∈ widerPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest :=
      List.mem_of_getElem? (i := 6) rfl
    obtain rfl := pair_only matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest hL
      (by decide) M (lot_of_kind _ _ _ _ Zq Gr M hM y hy hk)
    exact Or.inl ⟨k4BaseSlot, List.mem_singleton.2 rfl, rfl⟩
  · exact Or.inr fun y hy hk => hx ⟨y, hy, hk⟩

/-- **KindPays AT THE KIND K4 AT `theGAtBase`: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW;
A' := B' := False.** The one premise on K: its lots hold K4's slot. -/
theorem kindPays_K4_at_theG {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A) (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) (hslot : k4BaseSlot ∈ K.lots) :
    KindPays (theGAtBase h T K) .K4 := by
  have hin := k4SimulatorHandInAtMaker (W₁ := FullSizeMatrix) (Rc₁ := IndexCommitterCoins) (Tr₁ := Cells) (X₁ := Unit) h.head
    made id (matrixInput.weights A.Z) (fun _ _ => k4LookAt)
  obtain ⟨n2, n3⟩ := noK4PlaceInTheLaterChains h.head.laid.value h.head.laid.planOk
  refine kindPays_of_rows _ _ _ _ _ .K4 ?_ ?_ ?_
  · intro u hu hk σ hσ
    obtain ⟨l, hl, hul⟩ := rows_of_overlay (ls := [k4BaseSlot]) K.apart
      (fun l hl => by rw [List.mem_singleton.1 hl]; exact hslot) K.lots_fit
      (k4_alone_at_base files A.Z A.G) u hu hk
    obtain rfl := List.mem_singleton.1 hl
    exact ⟨narrows_of_bare rfl, _, _, (hin.atEveryRow u hul).good _ σ hσ _ .own _ 0 0⟩
  · intro u _ hk σ hσ
    obtain ⟨b, hbk, e⟩ := block_of_seated hσ
    exact absurd (e ▸ hk) (n2 b hbk)
  · intro u _ hk σ hσ
    obtain ⟨b, hbk, e⟩ := block_of_seated hσ
    exact absurd (e ▸ hk) (n3 b hbk)

/-- **THE SAME AT THE DESCRIPTION THAT THE RETURN HOLDS (`theGOfReturn`), BY `castSides_of`: THE
SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False.** -/
theorem kindPays_K4_at_theGOfReturn {files : VerifierAndGoals.PublicFiles} {Wt : Type}
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) : KindPays (AtPublicFiles.TheG.theGOfReturn made h T K) .K4 :=
  AtPublicFiles.TheSides.castSides_of (Q := fun _ G => KindPays G .K4) _
    (kindPays_K4_at_theG made h T K hslot)

/-- **The head at a return, from scope, read and live.** -/
theorem headAtReturn_of_live (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok A) :
    Nonempty (HeadAtReturn files A) := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_of_live files scope read live
  obtain rfl := atPure_pub_at_laid h.laid made
  exact ⟨⟨⟨_, made⟩, Np, cF, x, h⟩⟩

/-- **Each of K4's rows stands in the first list of `theGAtBase`, with its place, row, On and bud**, at
every K with K4's slot: at such a K the clauses do not pay for want of rows. -/
theorem k4_rows_in_theG {files : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hslot : k4BaseSlot ∈ K.lots) {row : Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst}
    (hr : row ∈ k4BaseSlot.rows A.Z A.G) :
    ∃ L ∈ (theGAtBase h T K).first, L.bare = row := by
  have hL : (HLot.byPub matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt) ∈
      (baseFilling files).lots := List.mem_of_getElem? (i := 6) rfl
  have eo : AtPublicFiles.TheSides.overlayLot K.lots
      (HLot.byPub matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt) = k4BaseSlot := by
    unfold AtPublicFiles.TheSides.overlayLot
    have hf := AtPublicFiles.TheSides.find_name K.apart hslot
    have en : (HLot.byPub (V := Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (W := Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
        (X := Unit) matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt).name =
        k4BaseSlot.name := rfl
    rw [en, hf]
  have hin : row ∈ rowsOfLots A.Z A.G ((baseFilling files).lots.map
      (AtPublicFiles.TheSides.overlayLot K.lots)) :=
    List.mem_flatMap.2 ⟨k4BaseSlot, List.mem_map.2 ⟨_, hL, eo⟩, hr⟩
  exact ⟨_, List.mem_map.2 ⟨row, hin, rfl⟩, rfl⟩

/-- **Of the thirteen lots of the base filling the seventh alone bears K4's name.** An evaluation of
thirteen names. -/
theorem onlyTheSeventhLotBearsK4sName {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ((onlineProverPartsInUse I o S O).lots.map fun L => L.name == "K4") =
      [false, false, false, false, false, false, true, false, false, false, false, false, false] :=
  rfl

/-- In a list whose test says yes at the seventh place alone, an entry that passes is the seventh. -/
theorem entry_at_the_only_true {α : Type} (list : List α) (test : α → Bool)
    (written : list.map test =
      [false, false, false, false, false, false, true, false, false, false, false, false, false])
    (entry : α) (inList : entry ∈ list) (passes : test entry = true) :
    list[6]? = some entry := by
  obtain ⟨number, atNumber⟩ := List.getElem?_of_mem inList
  have tested : (list.map test)[number]? = some true := by
    rw [List.getElem?_map, atNumber]
    exact congrArg some passes
  rw [written] at tested
  match number, tested, atNumber with
  | 6, _, atSix => exact atSix
  | later + 7, testedLater, _ =>
    exact absurd (List.mem_of_getElem?
      (l := [false, false, false, false, false, false]) (i := later) testedLater) (by decide)

/-- **A value of `KindRows` with K4's slot exists**, at every public part and ground: K4's slot
alone, the other lots bare. It shows that the premise `hslot` can be met, not that a value with
thirteen simulators that simulate anything exists. -/
theorem kindRows_with_K4s_slot (files : VerifierAndGoals.PublicFiles) (Zq : ProofFile.Pub) (Gr : ProofFile.Ground) :
    ∃ K : KindRows (baseFilling files) Zq Gr, k4BaseSlot ∈ K.lots := by
  refine ⟨⟨[k4BaseSlot], ?_, List.nodup_singleton _, ?_, [], (fun _ h => nomatch h), List.nodup_nil, ?_,
    [], (fun _ h => nomatch h), List.nodup_nil, ?_⟩, List.mem_singleton.2 rfl⟩
  · intro s hs
    obtain rfl := List.mem_singleton.1 hs
    exact List.any_eq_true.2 ⟨_, List.mem_of_getElem? (i := 6) rfl, by rfl⟩
  · intro L hL s hs
    obtain rfl := List.mem_singleton.1 (List.mem_of_find?_eq_some hs)
    have hn : (L.name == "K4") = true := by
      have h1 : (k4BaseSlot.name == L.name) = true :=
        List.find?_some (p := fun s : SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
          (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst => s.name == L.name) hs
      exact beq_iff_eq.2 (beq_iff_eq.1 h1).symm
    have at6 := entry_at_the_only_true _ _ (onlyTheSeventhLotBearsK4sName matrixInput OnBytes.secondHashFunction
      OnBytes.HonestTrace.Sz.ref openHonest) L hL hn
    obtain rfl : (HLot.byPub matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt) = L :=
      Option.some.inj at6
    exact k4_rows_halves id (matrixInput.weights Zq) _ Zq Gr
  · intro h _ r hr
    cases hr
  · intro h _ r hr
    cases hr

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4_alone_at_base
#print axioms ProofFile.Honest.K4.ExactFresh.kindPays_K4_at_theG
#print axioms ProofFile.Honest.K4.ExactFresh.kindPays_K4_at_theGOfReturn
#print axioms ProofFile.Honest.K4.ExactFresh.headAtReturn_of_live
#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_in_theG
#print axioms ProofFile.Honest.K4.ExactFresh.onlyTheSeventhLotBearsK4sName
#print axioms ProofFile.Honest.K4.ExactFresh.kindRows_with_K4s_slot
