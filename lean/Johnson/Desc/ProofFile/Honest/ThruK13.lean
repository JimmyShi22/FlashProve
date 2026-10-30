-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/ThruK13.lean: ONE lot of `widerFillOwn` (Honest/AtPureWiderAt.lean) is
natural in its reader of the index: K13's (`K13.k13Lot`, Honest/K13/Part.lean): at the reader
composed with a total `g` it is the lot read through `g` (`k13Lot_thru`); and so as it lies in the
filling's list, inside `HLot.byPub`, at `WiderIn.comap` (`k13_byPub_thru`).

  1  `WiderIn.comap`, `OnlineProverParts.through`   definitions
  2  `quietPart_thru`, `k13Ask_thru`, `k13Half_thru`, `k13Lot_thru`   the lot
  3  `byPub_thru`, `k13_byPub_thru`   as it lies in the filling

By what. `Part.lift_thru` (Honest/Thru.lean); the texts of `K13.k13Ask`, `K13.k13Row`,
`K13.proverSideOfClaimCombination`, `K13.k13Lot`, `quietPart` (Honest/ForKinds.lean) and `HLot.byPub`.

Limits.
  * ONE lot of ten. Of the other nine nothing is said.
  * `OnlineProverParts.through` is a definition alone: that `widerFillOwn` at `I.comap g d'` is `widerFillOwn` at
    `I` read through is not stated, nor anything of `onlineProverFromPublicFiles` at a filling read through.
  * `d'` is free: nothing ties it to `I.dummy`.
  * The laws are equations of definitions. They prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ W₀' Rc Rc' Xi Tr X₀ X : Type}

/-! ## 1 The definitions over a filling -/

/-- **What depends on the type of the index, read through `g`.** `d'`: the named member: an element,
which no function into W₀ carries. -/
def WiderIn.comap (g : W₀' → W₀) (d' : W₀') (I : WiderIn W₀) : WiderIn W₀' :=
  ⟨fun Z w => I.weights Z (g w), fun Z w => I.trace Z (g w), fun w => I.inRange (g w), d'⟩

/-- **A filling read through.** Field by field. A definition: no law on it is stated here. -/
def OnlineProverParts.through (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀') (P : OnlineProverParts W₀ Rc Tr X₀ X) :
    OnlineProverParts W₀' Rc' Tr X₀ X :=
  { trace := fun Z w => P.trace Z (g w)
    readers := fun Z w rc => P.readers Z (g w) (rd rc)
    rows := P.rows
    inRange := fun w => P.inRange (g w), dummy := d'
    enc := fun Z w rc => P.enc Z (g w) (rd rc)
    own₀ := P.own₀, ownShared₀ := P.ownShared₀
    meet := fun x t => P.meet x (t.narrow (Common.thru g rd) id)
    lots := P.lots.map (HLot.thru (Local.thru g rd) (Local.thru g rd))
    shared := fun Z G => (P.shared Z G).map (Placed.thru id (Common.thru g rd))
    second := fun Z G => (P.second Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) }

/-! ## 2 One lot -/

/-- The part that sends nothing, read through, is itself. -/
theorem quietPart_thru {V V' W W' : Type} (see : V' → V) (wit : W' → W) (n : Nat) :
    (quietPart n : Part V W X).thru see wit = quietPart n := by
  unfold Part.thru Part.lift quietPart
  simp only [List.map_replicate]
  rfl

/-- The small input of K13's parts at a reader composed with `g`. -/
theorem k13Ask_thru (g : W₀' → W₀) (rd : Rc' → Rc) (wt : W₀ → Weights) (pile : K13.PileOf Xi) :
    (K13.k13Ask (Rc := Rc') (Tr := Tr) (wt ∘ g) pile) =
      K13.k13Ask wt pile ∘ Local.thru g rd := rfl

/-- K13's half at a reader composed with `g`: the half read through. -/
theorem k13Half_thru (g : W₀' → W₀) (rd : Rc' → Rc) (wt : W₀ → Weights) (pile : K13.PileOf Xi)
    (p : VerifiableInference.Desc.K13.Where) :
    (K13.proverSideOfClaimCombination (wt ∘ g) pile p : Placed (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) =
      (K13.proverSideOfClaimCombination wt pile p).thru (Local.thru g rd) (Local.thru g rd) := by
  show (⟨K13.k13Place p, [quietPart, (K13.k13Sum p).lift (fun _ => ())
      (K13.k13Ask (wt ∘ g) pile) (fun _ => ()) fun x _ => x]⟩ : Placed _ _ X) =
    ⟨K13.k13Place p, [Part.thru (Local.thru g rd) (Local.thru g rd) quietPart,
      Part.thru (Local.thru g rd) (Local.thru g rd) ((K13.k13Sum p).lift (fun _ => ())
        (K13.k13Ask wt pile) (fun _ => ()) fun x _ => x)]⟩
  rw [quietPart_thru, Part.lift_thru]
  rfl

/-- **K13's lot is natural in its reader of the index**: at the reader composed with `g` it is the
lot read through. `g`, `rd`: any. -/
theorem k13Lot_thru (g : W₀' → W₀) (rd : Rc' → Rc) (wt : W₀ → Weights)
    (pile : Pub → Ground → K13.PileOf Xi) :
    (K13.k13Lot (wt ∘ g) pile : HLot (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) =
      (K13.k13Lot wt pile).thru (Local.thru g rd) (Local.thru g rd) :=
  HLot.ext' rfl (funext fun Z => funext fun G =>
    congrArg (fun h => [h]) (k13Half_thru g rd wt (pile Z G) _))

/-! ## 3 As it lies in `widerFillOwn` -/

/-- **A list that is natural in its reader, inside `HLot.byPub`.** -/
theorem byPub_thru {V V' W W' : Type} (g : W₀' → W₀) (d' : W₀') (I : WiderIn W₀) (see : V' → V)
    (wit : W' → W) (L : (W₀ → Weights) → HLot V W X) (L' : (W₀' → Weights) → HLot V' W' X)
    (h : ∀ wt, L' (wt ∘ g) = (L wt).thru see wit) :
    HLot.byPub (I.comap g d').weights L' = (HLot.byPub I.weights L).thru see wit := by
  have hz := congrArg HLot.name (h fun _ => ⟨fun _ _ => OnBytes.Slice.toF 0⟩)
  refine HLot.ext' ?_ ?_
  · exact hz
  · funext Z G
    exact congrFun (congrFun (congrArg HLot.halves (h (I.weights Z))) Z) G

/-- K13's entry of `widerFillOwn`'s list of lots, at `I.comap g d'`: the entry at `I`, read through.
The stored tables' pads and encoding randomness stay (`rd := id`). -/
theorem k13_byPub_thru (g : W₀' → W₀) (d' : W₀') (I : WiderIn W₀)
    (pile : Pub → Ground → K13.PileOf Inst) :
    (HLot.byPub (I.comap g d').weights fun wt => K13.k13Lot wt pile :
        HLot (Local W₀' IndexCommitterCoins Inst Cells) (Local W₀' IndexCommitterCoins Inst Cells) X) =
      (HLot.byPub I.weights fun wt => K13.k13Lot wt pile).thru (Local.thru g id)
        (Local.thru g id) :=
  byPub_thru g d' I _ _ _ _ fun wt => k13Lot_thru g id wt pile

end ProofFile.Honest

#print axioms ProofFile.Honest.WiderIn.comap
#print axioms ProofFile.Honest.OnlineProverParts.through
#print axioms ProofFile.Honest.quietPart_thru
#print axioms ProofFile.Honest.k13Ask_thru
#print axioms ProofFile.Honest.k13Half_thru
#print axioms ProofFile.Honest.k13Lot_thru
#print axioms ProofFile.Honest.byPub_thru
#print axioms ProofFile.Honest.k13_byPub_thru
