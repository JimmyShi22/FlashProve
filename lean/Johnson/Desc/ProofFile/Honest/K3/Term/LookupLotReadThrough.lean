-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupLotReadThrough.lean: AT ANY FILLING. The kind "lookup"
(K3): the lot's honest side, read through readers of the input (`HLot.thru`, Honest/Thru.lean), is
the lot's honest side at the filling whose reader is composed with them. Two definitions; equations
between definitions. General in the lookup's filling (`K3.Fill`, Honest/K3/LotRow.lean). No premise
in any of them.

  `lookupFillingReadThrough`      a lookup's filling with its reader composed with a reader
  `lookupSeatReadThrough`         the seated row at one place, read through
  `lookupLotReadThrough`          the lot at a filling that may read the public part, read through
  `lookupFillingAtWeights`        the filling that `theLotInst id` has at a reader of the index that
                                  depends on the public part
  `lookupLotByPublicPart`         `HLot.byPub` of `theLotInst id` is `rowLotAt` at that filling
  `lookupFillingThrough`          that filling read through `Local.thru g rd`
  `lookupLotByPublicPartReadThrough`   the two equations joined
  `lookupHalvesReadThrough`       the same, side by side: at each site the seat `proverSideOfLookupInChainAtOneOwner`
  `lookupLotIsTheSixthLot`, `lookupLotIsTheSixthLotReadThrough`   the lot is the sixth of the lots
      of
                                  `onlineProverPartsInUse`; read through, of that filling read through
  `lookupLotIsAmongTheLots`       the lot is one of the lots of `onlineProverPartsInUse`
  `lookupLotIsAmongTheLotsReadThrough`   read through, it is one of the lots of that filling read
                                  through (`OnlineProverParts.through`): by that definition's field `lots`

Limits. Equations between definitions: nothing on what a side sends, on whether it plays or is
accepted. Nothing of `onlineProverFromPublicFiles` at a filling read through. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K3.LotInst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term

section
variable {V V' W W' Wj X : Type}

/-- **A lookup's filling, its reader composed with a reader of a wider input.** The summands stay.
-/
def lookupFillingReadThrough (reader : W' → W) (A : Fill W) : Fill W' :=
  { jobs := A.jobs, wit := fun s => A.wit s ∘ reader }

/-- **The seated row at one place, read through, is the seated row at the reader composed.** -/
theorem lookupSeatReadThrough (R : Reads) (J : LookJobs Wj) (wit : W → Wj) (a : At)
    (see : V' → V) (reader : W' → W) :
    (proverSideOfLookupInChainAtOneOwner R J wit a : Placed V W X).thru see reader = proverSideOfLookupInChainAtOneOwner R J (wit ∘ reader) a := by
  show (⟨a.place, ((lookRow (V := Unit) R J a).map
      (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)).map (Part.thru see reader)⟩ :
      Placed V' W' X) =
    ⟨a.place, (lookRow (V := Unit) R J a).map
      (Part.lift (fun _ => ()) (wit ∘ reader) (fun _ => ()) fun x _ => x)⟩
  rw [List.map_map]
  exact congrArg (Placed.mk a.place) (List.map_congr_left fun p _ =>
    Part.lift_thru see reader (fun _ => ()) wit (fun _ => ()) (fun x _ => x) p)

/-- **The lot's honest side, read through, is the lot's honest side at the filling read through.**
-/
theorem lookupLotReadThrough (F : Pub → Fill W) (see : V' → V) (reader : W' → W) :
    (rowLotAt F : HLot V W X).thru see reader =
      rowLotAt fun Z => lookupFillingReadThrough reader (F Z) := by
  refine HLot.ext' rfl (funext fun Z => funext fun _ => ?_)
  show ((lookSites Z).map fun s => (⟨s.at_.place,
      (proverSideOfLookupInChainAtOneOwner theReads ((F Z).jobs s).asked ((F Z).wit s) s.at_).parts⟩ : Placed V W X)).map
      (Placed.thru see reader) =
    (lookSites Z).map fun s => ⟨s.at_.place,
      (proverSideOfLookupInChainAtOneOwner theReads ((F Z).jobs s).asked ((F Z).wit s ∘ reader) s.at_).parts⟩
  rw [List.map_map]
  exact List.map_congr_left fun s _ =>
    lookupSeatReadThrough theReads ((F Z).jobs s).asked ((F Z).wit s) s.at_ see reader

end

section
variable {W₀ W₀' Rc Rc' X : Type}

/-- **The filling of `theLotInst id`, at a reader of the index that depends on the public part.** -/
def lookupFillingAtWeights (weights : Pub → W₀ → Weights) :
    Pub → Fill (Local W₀ Rc Inst Cells) :=
  fun Z => fastFill (sourcesAt id (weights Z) (reqAt Z) Z)

/-- **The lot as the online prover's fillings lay it is `rowLotAt` at that filling.** -/
theorem lookupLotByPublicPart (weights : Pub → W₀ → Weights) :
    (HLot.byPub weights fun wt => theLotInst id wt :
        HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X) =
      rowLotAt (lookupFillingAtWeights weights) :=
  HLot.ext' rfl rfl

/-- **That filling, read through**: the index by `g`, the stored tables' pads and encoding
randomness by `rd`. -/
def lookupFillingThrough (weights : Pub → W₀ → Weights) (g : W₀' → W₀) (rd : Rc' → Rc) :
    Pub → Fill (Local W₀' Rc' Inst Cells) :=
  fun Z => lookupFillingReadThrough (Local.thru g rd) (lookupFillingAtWeights weights Z)

/-- **THE EQUATION: the lot as the fillings lay it, read through, is the lookups' own lot at the
filling read through.** -/
theorem lookupLotByPublicPartReadThrough (weights : Pub → W₀ → Weights) (g : W₀' → W₀)
    (rd : Rc' → Rc) :
    (HLot.byPub weights fun wt => theLotInst id wt :
        HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X).thru
        (Local.thru g rd) (Local.thru g rd) =
      rowLotAt (lookupFillingThrough weights g rd) := by
  rw [lookupLotByPublicPart]
  exact lookupLotReadThrough (lookupFillingAtWeights weights) (Local.thru g rd) (Local.thru g rd)

/-- **The same, side by side**: at each site of the public part the seat `proverSideOfLookupInChainAtOneOwner`, at the filling
read through. -/
theorem lookupHalvesReadThrough (weights : Pub → W₀ → Weights) (g : W₀' → W₀) (rd : Rc' → Rc)
    (publicPart : Pub) (ground : Ground) :
    ((HLot.byPub weights fun wt => theLotInst id wt :
        HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X).thru
        (Local.thru g rd) (Local.thru g rd)).halves publicPart ground =
      (lookSites publicPart).map fun s =>
        proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ ((lookupFillingThrough weights g rd publicPart).jobs s).asked
          ((lookupFillingThrough weights g rd publicPart).wit s) s.at_ := by
  rw [lookupLotByPublicPartReadThrough]
  rfl

end

section
variable {W₀ W₀' Rc' : Type}

/-- **The lookups' lot is the sixth of the lots of `onlineProverPartsInUse`.** -/
theorem lookupLotIsTheSixthLot (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    (onlineProverPartsInUse I o S O).lots[5]? = some (HLot.byPub I.weights fun wt => theLotInst id wt) :=
  rfl

/-- **Read through, it is the sixth of the lots of that filling read through**, in the lookups' own
form. -/
theorem lookupLotIsTheSixthLotReadThrough (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') :
    (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots[5]? =
      some (rowLotAt (lookupFillingThrough I.weights g rd)) := by
  show ((onlineProverPartsInUse I o S O).lots.map
    (HLot.thru (Local.thru g rd) (Local.thru g rd)))[5]? = _
  rw [List.getElem?_map, lookupLotIsTheSixthLot, ← lookupLotByPublicPartReadThrough]
  rfl

/-- **The lookups' lot is one of the lots of `onlineProverPartsInUse`.** -/
theorem lookupLotIsAmongTheLots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    (HLot.byPub I.weights fun wt => theLotInst id wt) ∈ (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- **Read through, it is one of the lots of that filling read through**, in the lookups' own form.
-/
theorem lookupLotIsAmongTheLotsReadThrough (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') :
    rowLotAt (lookupFillingThrough I.weights g rd) ∈
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots := by
  rw [← lookupLotByPublicPartReadThrough]
  exact List.mem_map_of_mem (lookupLotIsAmongTheLots I o S O)

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupFillingReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupSeatReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupLotReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupFillingAtWeights
#print axioms ProofFile.Honest.K3.Term.lookupLotByPublicPart
#print axioms ProofFile.Honest.K3.Term.lookupFillingThrough
#print axioms ProofFile.Honest.K3.Term.lookupLotByPublicPartReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupHalvesReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupLotIsTheSixthLot
#print axioms ProofFile.Honest.K3.Term.lookupLotIsTheSixthLotReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupLotIsAmongTheLots
#print axioms ProofFile.Honest.K3.Term.lookupLotIsAmongTheLotsReadThrough
