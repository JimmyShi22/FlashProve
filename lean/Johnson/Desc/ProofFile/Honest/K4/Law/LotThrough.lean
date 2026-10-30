-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotThrough.lean: equations of definitions, and what they give
at the term's filling.

What is here. K4's LOT IS NATURAL IN ITS READER OF THE INDEX: at the reader composed with a total
`g` it is the lot read through `g` and `rd` (`Honest/Thru.lean`), as K13's is
(`k13Lot_thru`, Honest/ThruK13.lean). So what holds of a filling's lots at K4 holds of that filling
read through (`OnlineProverParts.through`). And at the filling `onlineProverPartsInUse` (Honest/K1/Law/WSideAtFill.lean),
which the term reads through, K4's lot stands and no other lot has a half of the kind K4.

  `k4Half_thru`                K4's half at the reader composed with `g`: the half read through
  `k4HLot_thru`                the same of the lot
  `k4_lot_at_through`          K4's lot among a filling's lots, and no other lot with a half of the
                               kind K4: read through, the same, at the reader composed
  `k4_lot_at_widerFillAtCPUOWM`  no hypothesis: the two at `onlineProverPartsInUse`
  `k4_lot_at_widerFill_through`  no hypothesis: the two at that filling read through

Limits. Lists of sides alone: nothing on `play`, `ready`, `Good` or `Owed` at what is read through.
`g` and `rd` are total and nothing is asked of them.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LettersFirst
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (KindName)

section
variable {W₀ W₀' Rc Rc' Xi Tr X : Type}

/-- **K4's half at a reader composed with `g`: the half read through.** `g`, `rd`: any. -/
theorem k4Half_thru (g : W₀' → W₀) (rd : Rc' → Rc) (cells : Tr → Cells) (wt : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Q : K4Pub) :
    (k4Half cells (wt ∘ g) tokens look Q :
        Placed (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) =
      (k4Half cells wt tokens look Q).thru (Local.thru g rd) (Local.thru g rd) := by
  show (⟨k4Place Q, (k4RowIn Q).map fun p =>
      p.lift (fun _ => ()) (k4Wit Q cells (wt ∘ g) tokens (look Q)) (fun _ => ()) fun x _ => x⟩ :
        Placed _ _ X) =
    ⟨k4Place Q, ((k4RowIn Q).map fun p =>
      p.lift (fun _ => ()) (k4Wit Q cells wt tokens (look Q)) (fun _ => ()) fun x _ => x).map
        (Part.thru (Local.thru g rd) (Local.thru g rd))⟩
  rw [List.map_map]
  refine congrArg (Placed.mk (k4Place Q)) (List.map_congr_left fun p _ => ?_)
  exact (Part.lift_thru (Local.thru g rd) (Local.thru g rd) (fun _ => ())
    (k4Wit Q cells wt tokens (look Q)) (fun _ => ()) (fun x _ => x) p).symm

variable (g : W₀' → W₀) (rd : Rc' → Rc) (cells : Tr → Cells) (wt : W₀ → Weights)
  (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- **K4's lot is natural in its reader of the index**: at the reader composed with `g` it is the
lot read through. `g`, `rd`: any. -/
theorem k4HLot_thru :
    (k4HLot cells (wt ∘ g) look : HLot (Local W₀' Rc' Inst Tr) (Local W₀' Rc' Inst Tr) X) =
      (k4HLot cells wt look).thru (Local.thru g rd) (Local.thru g rd) := by
  refine HLot.ext' rfl (funext fun Z => funext fun G => ?_)
  show List.filterMap _ _ = List.map _ (List.filterMap _ _)
  rw [List.map_filterMap]
  refine congrArg (fun f => List.filterMap f _) (funext fun x => ?_)
  cases (k4PubOf Z x.2).filter k4TableFits with
  | none => rfl
  | some Q => exact congrArg some (k4Half_thru g rd cells wt k4Tokens (look Z G) Q)

variable {X₀ : Type}

/-- **What holds of a filling's lots at K4 holds of the filling read through**, at the reader
composed with `g`. -/
theorem k4_lot_at_through (d' : W₀') (P : OnlineProverParts W₀ Rc Tr X₀ X) (Zq : Pub) (G : Ground)
    (hM : ∃ M ∈ P.lots, M.halves Zq G = (k4HLot cells wt look).halves Zq G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot cells wt look).halves Zq G) :
    (∃ M ∈ (P.through g rd d').lots,
      M.halves Zq G = (k4HLot cells (wt ∘ g) look).halves Zq G) ∧
    ∀ M' ∈ (P.through g rd d').lots, (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot cells (wt ∘ g) look).halves Zq G := by
  have key : ∀ M : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X,
      M.halves Zq G = (k4HLot cells wt look).halves Zq G →
      (M.thru (Local.thru g rd) (Local.thru g rd)).halves Zq G =
        (k4HLot cells (wt ∘ g) look).halves Zq G := by
    intro M e
    rw [k4HLot_thru g rd cells wt look]
    show (M.halves Zq G).map _ = ((k4HLot cells wt look).halves Zq G).map _
    rw [e]
  obtain ⟨M, hm, e⟩ := hM
  refine ⟨⟨_, List.mem_map.2 ⟨M, hm, rfl⟩, key M e⟩, fun M' hM' => ?_⟩
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM'
  rcases ho M₀ hM₀ with h1 | h2
  · refine .inl fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact h1 z hz
  · exact .inr (key M₀ h2)

end

variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  (Zq : ProofFile.Pub) (G : ProofFile.Ground)

/-- NO HYPOTHESIS. **K4's lot among the lots of `onlineProverPartsInUse`, and no other lot with a half of
the kind K4.** -/
theorem k4_lot_at_widerFillAtCPUOWM :
    (∃ M ∈ (onlineProverPartsInUse I o S O).lots,
      M.halves Zq G = (k4HLot id (I.weights Zq) (fun _ _ => k4LookAt)).halves Zq G) ∧
    ∀ M' ∈ (onlineProverPartsInUse I o S O).lots, (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot id (I.weights Zq) (fun _ _ => k4LookAt)).halves Zq G := by
  obtain ⟨M, hM, hE⟩ := widerFillOwn_k4 () (LongLots.plain o S O) I o S O
  have ho := ho_widerAt (FirstFill.widerKinds I o S O Zq G)
  refine ⟨⟨M, ?_, hE Zq G⟩, fun M' hM' => ?_⟩
  · rw [widerFillAtCPUOWM_lots]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hM))
  rw [widerFillAtCPUOWM_lots] at hM'
  simp only [List.mem_append, List.mem_singleton] at hM'
  rcases hM' with ((h | rfl) | rfl) | rfl
  · exact ho M' h
  · refine .inl fun y hy => ?_
    rw [closeLotAt_kinds I S Zq G y hy]
    decide
  · refine .inl fun y hy => ?_
    rw [proxLotAt_kinds I S Zq G y hy]
    decide
  · refine .inl fun y hy => ?_
    rw [K12.AtProof.wLot_place I o O Zq G y hy]
    decide

/-- NO HYPOTHESIS. **The same at that filling read through**, at the reader composed with `g`. -/
theorem k4_lot_at_widerFill_through {W₀' Rc' : Type} (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') :
    (∃ M ∈ ((onlineProverPartsInUse I o S O).through g rd d').lots,
      M.halves Zq G = (k4HLot id (I.weights Zq ∘ g) (fun _ _ => k4LookAt)).halves Zq G) ∧
    ∀ M' ∈ ((onlineProverPartsInUse I o S O).through g rd d').lots,
      (∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) ∨
      M'.halves Zq G = (k4HLot id (I.weights Zq ∘ g) (fun _ _ => k4LookAt)).halves Zq G :=
  k4_lot_at_through g rd id (I.weights Zq) (fun _ _ => k4LookAt) d' _ Zq G
    (k4_lot_at_widerFillAtCPUOWM I o S O Zq G).1 (k4_lot_at_widerFillAtCPUOWM I o S O Zq G).2

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Half_thru
#print axioms ProofFile.Honest.K4.k4HLot_thru
#print axioms ProofFile.Honest.K4.k4_lot_at_through
#print axioms ProofFile.Honest.K4.k4_lot_at_widerFillAtCPUOWM
#print axioms ProofFile.Honest.K4.k4_lot_at_widerFill_through
