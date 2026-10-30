-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ClosingStage.lean: the closing of a segment as one stage.

The closing (Blocks/ClosingBlock.lean) as one stage (Blocks/Stage.lean), `Blocks.Closing.stage`,
with all its properties if every masked scalar has its own pad (`props_stage`), its tracking data
(`track`: no vector is sent; tracking data: Blocks/StageTrack.lean), a common bound for its errors
(`below_stage`) and its counts (`rounds_stage`, `sum_track`). The protocol runs in the order of the
messages (Blocks/ClosingBlock.lean, (1) to (4)). Only the proof of masked form takes the pads in the
other order, those of the opened elements first, because the auxiliary scalars depend on them
(Blocks/ClosingBlock.lean, the head's paragraph on the honest prover).

Notation: from Blocks/Stage.lean: `Sorts`: the types between two stages: the explicit part X and the
implicit part Y of a statement, and the state I of the honest prover; `Cut P E a`: the relations
between two stages: `R`: the relation for soundness; `Hn`: the relation of the honest run; `V`:
validity of the honest state; from Blocks/StageTrack.lean: `Reads F E a`: a structure with the
fields `N : Type`, `rd : a.Y → N → E`, `mat : a.Y → ℕ → ℕ → F`; `Core.Track`: the tracking data: how
a protocol sends its vectors (`d`), and where the exposed entries come from (`src`); `Stage.Below`
(Blocks/StageNums.lean): every error of the stage, as a probability, is at most κ.
-/
import Blocks.StageLib
import Blocks.StageSide
import Blocks.StageNums
import Blocks.StageCount
import Blocks.ClosingBlock
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks.Closing

open Iop Prob Blocks

section Stage

variable {N E P : Type} [Fintype N] [DecidableEq N] [Field E] [Fintype E] [DecidableEq E]
  {nO nR : ℕ} (nL : ℕ) (pl : Places N (Fin nR) nO) (pp : Places P (Fin nR) nO)

variable (N E nO nR) in
/-- The types before the closing. -/
abbrev sIn : Sorts := ⟨Ledger N E, N → E, HClose E (Fin nR) nO⟩

variable (N E nO nR) in
/-- The types after it: the form of the linear claim, the entries, the honest prover's state. -/
abbrev sOut : Sorts := ⟨Form N E, N → E, HClose E (Fin nR) nO⟩

/-- The protocol of the closing. -/
def core : Blocks.Core P E (sIn N E nO nR) (sOut N E nO nR) where
  B := closing E nL pl
  H := honClosing E nL pl pp

/-- The closing as one stage. -/
def stage : Blocks.Stage P E (sIn N E nO nR) (sOut N E nO nR) where
  toCore := core nL pl pp
  ε := closeErr E (Fin nL) (Fin nR) nO
  U := Set.range pp.aux ∪ Set.range pp.opn
  D := Set.range pp.aux ∪ Set.range pp.opn
  Sim := Hon.simSeq (s := []) (fun _ => PMF.pure ())
    (Hon.simSeq (Hon.simOne (r := rAux E (Fin nR)) (K := Fin nR × Bool) E id)
      (Hon.simOne (r := rOpen E (Fin nL) (Fin nR) nO) (K := Fin nO) E id))
  pBad := 0
  pWin := 0

/-- Before the closing: all deferred claims are true. -/
def cutIn : Cut P E (sIn N E nO nR) := ⟨Ledger.True, HonLedger nL pl pp, fun _ => True⟩

variable (N E P nO nR) in
/-- After the closing: the linear claim is true. -/
def cutOut : Cut P E (sOut N E nO nR) :=
  ⟨fun g y => Form.val y g = 0, fun _ _ g y => Form.val y g = 0, fun _ => True⟩

variable [Fintype P] [DecidableEq P]

/-- All properties of the closing (`Stage.Props`, Blocks/Stage.lean: `clean`, `acc`, `masked`,
`keeps`, `prBad`, `prWin`; between `cutIn` and `cutOut`), if every scalar has its own pad (`haux`,
`hopn`, `hd`). The withheld set (`Hon.withheld`) is empty. -/
theorem props_stage (haux : Function.Injective pp.aux) (hopn : Function.Injective pp.opn)
    (hd : Disjoint (Set.range pp.opn) (Set.range pp.aux)) :
    (stage (E := E) nL pl pp).Props (cutIn nL pl pp) (cutOut N E P nO nR) :=
  Blocks.Stage.Props.of_empty (S := stage (E := E) nL pl pp)
    (ca := cutIn nL pl pp) (cb := cutOut N E P nO nR) (clean_closing E nL pl)
    (accOn_honClosing nL pl pp) (masked_honClosing nL pl pp haux hopn hd) (fun _ _ _ => trivial)
    (Set.eq_empty_iff_forall_notMem.mpr fun ρ h => by
      rcases h with h | h | h
      · exact h
      · exact h
      · exact h)
    (fun s => Set.eq_empty_iff_forall_notMem.mpr fun ρ h => by
      rcases h with h | h | h
      · exact h
      · exact h
      · exact h)

variable (F : Type) [Field F] [Algebra F E]

variable (N E nO nR) in
/-- What is exposed before the closing: the entries. (No matrix of weights is among its types.) -/
def readsIn : Reads F E (sIn N E nO nR) := ⟨N, fun y => y, fun _ _ _ => 0⟩

variable (N E nO nR) in
/-- After the closing the same entries are exposed. -/
def readsOut : Reads F E (sOut N E nO nR) := ⟨N, fun y => y, fun _ _ _ => 0⟩

/-- The closing sends no vector: every exposed entry was exposed before. -/
def track :
    (core (E := E) nL pl pp).Track (readsIn N E nO nR F) (readsOut N E nO nR F) where
  d := EncData.app (s := []) (t := [rAux E (Fin nR)] ++ [rOpen E (Fin nL) (Fin nR) nO]) PUnit.unit
    (EncData.app (s := [rAux E (Fin nR)]) (t := [rOpen E (Fin nL) (Fin nR) nO])
      (REnc.none E F (Fin nR × Bool) E, PUnit.unit)
      (REnc.none E F (Fin nO) (Fin nL ⊕ Fin nO ⊕ Fin nR → E), PUnit.unit))
  src := srcSeq (s := []) PUnit.unit _ (fun n : N => (Sum.inl n : Src N [] PUnit.unit))
    (srcSeq (s := [rAux E (Fin nR)]) _ _ (srcSame (REnc.none E F (Fin nR × Bool) E) N)
      (srcSame (REnc.none E F (Fin nO) (Fin nL ⊕ Fin nO ⊕ Fin nR → E)) N))

omit [Fintype N] [DecidableEq E] [Fintype P] [DecidableEq P] in
/-- Every exposed entry has the same value after the closing as before. -/
theorem track_ok : (track (E := E) nL pl pp F).OK :=
  ⟨Block.Tracks.comp (B₁ := Block.pure (toRecorded nL nO nR) id) (B₂ := closeCore E (Fin nL) pl)
      (r₁ := fun y : N → E => y) (r₂ := fun y : N → E => y) (r₃ := fun y : N → E => y)
      (Block.tracks_pure (F := F) (fun n : N => n) fun _ _ => rfl)
      (Block.Tracks.comp (B₁ := closeA N E (Fin nL) (Fin nR) nO)
        (B₂ := closeB E (Fin nL) pl) (r₂ := fun y : N → E => y)
        (Block.tracks_one (REnc.none E F (Fin nR × Bool) E)
          (fun n : N => Sum.inl n) fun _ _ _ _ => rfl)
        (Block.tracks_one (REnc.none E F (Fin nO) (Fin nL ⊕ Fin nO ⊕ Fin nR → E))
          (fun n : N => Sum.inl n) fun _ _ _ _ => rfl)),
    fun _ _ => rfl⟩

omit [Fintype N] [DecidableEq E] [Fintype P] [DecidableEq P] in
/-- No vector is sent, so every condition on the vectors that are sent holds. -/
theorem all_track {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} : (track (E := E) nL pl pp F).All Q :=
  EncData.All.app (s := []) (d := PUnit.unit) trivial
    (EncData.All.app (s := [rAux E (Fin nR)]) (t := [rOpen E (Fin nL) (Fin nR) nO])
      (d := (REnc.none E F (Fin nR × Bool) E, PUnit.unit))
      (d' := (REnc.none E F (Fin nO) (Fin nL ⊕ Fin nO ⊕ Fin nR → E), PUnit.unit))
      ⟨fun e => Empty.elim e, trivial⟩ ⟨fun e => Empty.elim e, trivial⟩)

open scoped ENNReal in
omit [Fintype N] [DecidableEq E] [Fintype P] [DecidableEq P] in
/-- If 2 / |E| ≤ κ and anything is deferred or opened (hn), the errors of the closing, as
probabilities, are at most κ: 2 / |E| at ς and 1 / |E| at the coefficients. -/
theorem below_stage {κ : ℝ≥0∞} (h2 : (2 : ℝ≥0∞) / Fintype.card E ≤ κ) (hn : 0 < nL + (nO + nR)) :
    (stage (E := E) nL pl pp).Below κ := by
  have hq0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2' : (2 : ℝ≥0∞) ≤ κ * Fintype.card E := (ENNReal.div_le_iff hq0 hqt).1 h2
  have h1' : (1 : ℝ≥0∞) ≤ κ * Fintype.card E := le_trans (by norm_num) h2'
  show (((2 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)) ∧
    (((Fintype.card E ^ (Fintype.card (Fin nL ⊕ Fin nO ⊕ Fin nR) - 1) : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card (Fin nL ⊕ Fin nO ⊕ Fin nR → E) : ℝ≥0∞)) ∧
    True
  refine ⟨by exact_mod_cast h2', ?_, trivial⟩
  have hc : Fintype.card (Fin nL ⊕ Fin nO ⊕ Fin nR) = nL + (nO + nR) := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  rw [Fintype.card_fun, hc]
  have h3 : Fintype.card E ^ (nL + (nO + nR)) =
      Fintype.card E ^ (nL + (nO + nR) - 1) * Fintype.card E := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [h3]
  push_cast
  calc
    (Fintype.card E : ℝ≥0∞) ^ (nL + (nO + nR) - 1) =
        (Fintype.card E : ℝ≥0∞) ^ (nL + (nO + nR) - 1) * 1 := (mul_one _).symm
    _ ≤ (Fintype.card E : ℝ≥0∞) ^ (nL + (nO + nR) - 1) * (κ * Fintype.card E) := by gcongr
    _ = κ * ((Fintype.card E : ℝ≥0∞) ^ (nL + (nO + nR) - 1) * Fintype.card E) := by ring

omit [Fintype N] [DecidableEq E] [Fintype P] [DecidableEq P] in
/-- The closing has two rounds. -/
theorem rounds_stage : (stage (E := E) nL pl pp).rounds = 2 := rfl

omit [Fintype N] [DecidableEq E] [Fintype P] [DecidableEq P] in
/-- No vector is sent, so every sum over the vectors that are sent is 0. -/
theorem sum_track (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) : (track (E := E) nL pl pp F).sum f = 0 :=
  rfl

end Stage

end Blocks.Closing
