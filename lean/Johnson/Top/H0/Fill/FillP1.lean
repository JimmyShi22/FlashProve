-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Fill/FillP1.lean: one layer of the filling of the table of joints: "tie", "wo",
"carry", and the public item of PubP1.lean; with the sentence for "weights" at the head.
Definitions, and theorems by rfl.

Main names:
  `woAt d rw`: "wo m": the row that the frame's reader gives at the verifier's state (`rowAt`,
    Johnson/Top/H0/Walk/FrameRow.lean), if it gives one, holds in the pile's sense (`Holds`,
    Johnson/Desc/K13/Law/Means.lean). rw IS THE PILE's OWN READER, of what was handed to the chain,
    the verifier's state and the witness: one letter for "pile" and "wo".
  `wtAt`, `wtP1`, `wtP1_iff`: "weights" at the head, the claim's unit and the slot of its value read
    off the verifier's state. `wtP1` has no proof among its letters; where the layout is no return
    of the planner's it is false.
  `fillP1 d rw A cr Mg`: THE LAYER: tie := `K8.tieK8Rec A`
    (Johnson/Desc/First/K8/TieAtSegment.lean); wo := `woAt d rw`; carry := cr; pub := `pubP1 d
    Mg.pub`; pubP := true at the layer's own item. The door's filling is handed on as it is.
  `fillP1_pub` ... `fillP1_fields`: what it lays, and that it leaves all else.

Limits. rw, A, cr, cellOf and maskOf are letters: the terms that are meant stand in other authors'
files. Nothing says that a sub-protocol's law meets a sentence. Nothing on soundness.

-/
import Johnson.Top.H0.Fill.PubP1
import Johnson.Top.H0.MergeLaw.OffRecord
import Johnson.Desc.First.K8.TieAtSegment

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.FillP1
open OnBytes (TensorRow)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading WsShape wsLayOf)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K13.Law (Holds)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.Walk.Law (rowAt)

/-- The witness as the pile of pending rows reads it: a matrix and mask entries. nR, kC: the
matrix's number of rows, and of bits that name a column. -/
abbrev PileWit (nR kC : ℕ) : Type := VerifiableInference.Desc.K13.Law.Wit GE nR kC

/-- **"wo", at every segment that bears it**: the row that the frame's reader gives at the
verifier's state, if it gives one, holds, in the pile's sense, of the witness's matrix. rw: THE
PILE's OWN READER: of what was handed to the chain, the verifier's state (it finds a mask entry's
place through that state's own book) and the witness: one letter for "pile" and "wo". -/
def woAt {P W : Type} {nR kC : ℕ} (d : PubData) (rw : P × S → W → PileWit nR kC) :
    ℕ → P × S → Strs → W → Prop :=
  fun m a _ w => ∀ r : TensorRow, rowAt d.lay (d.ncl m) d.lin a.2 = some r →
    Holds Reading.gl (rw a w) r

/-- **"weights" at the head**, the claim's unit and the slot of its value read off the verifier's
state: for the letter of the layer that fills "forms" and "formsT". -/
def wtAt {P W : Type} (Pm : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ}
    (h : wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni : ℕ)
    (cellOf : W → ℕ → ℕ → GE) (maskOf : P × S → W → ℕ → GE) : P × S → Strs → W → Prop :=
  fun a _ w => ∃ (ui : Fin Pm.lay.U.size) (sv : ℕ) (hsv : sv < Pm.nMsg) (c : ℕ) (hc : c < ni),
    ReadsAt a.2 ui.val sv ∧
      WeightsHere (recNums Pm h hn ni ui sv hsv c hc) (cellOf w) (maskOf a w) a.2

/-- **The same with no proof among its letters**: "there are" the planner's three numbers of which
the layout is a return. Where the layout is no return of the planner's, or the plan has too few
slots, the sentence is FALSE: it fails shut. -/
def wtP1 {P W : Type} (Pm : HeadMergeP) (ni : ℕ) (cellOf : W → ℕ → ℕ → GE)
    (maskOf : P × S → W → ℕ → GE) : P × S → Strs → W → Prop :=
  fun a y w => ∃ (s₀ : WsShape) (p3 : Bool) (lkW : ℕ) (h : wsLayOf s₀ p3 lkW = .ok Pm.lay)
    (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg), wtAt Pm h hn ni cellOf maskOf a y w

/-- Which three numbers are named does not matter: they stand in a proof alone. -/
theorem wtP1_iff {P W : Type} (Pm : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ}
    (h : wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni : ℕ)
    (cellOf : W → ℕ → ℕ → GE) (maskOf : P × S → W → ℕ → GE) (a : P × S) (y : Strs) (w : W) :
    wtP1 Pm ni cellOf maskOf a y w ↔ wtAt Pm h hn ni cellOf maskOf a y w :=
  ⟨fun ⟨_, _, _, _, _, x⟩ => x, fun x => ⟨_, _, _, h, hn, x⟩⟩

/-- **THE LAYER.** d: the plan's numbers. rw: the pile's own reader. A: segment m's table of cells,
as the equations of the reads read it, at the verifier's state (which array a number names is the
open segment's own table's to say). cr: "carry"'s sentence, by segment: the switch's authors' own.
-/
def fillP1 {P W : Type} {nR kC : ℕ} (d : PubData) (rw : P × S → W → PileWit nR kC)
    (A : ℕ → P × S → W → ℕ → ℕ → ℕ → Cb.Gl.E) (cr : ℕ → P × S → Strs → W → Prop)
    (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    tie := K8.tieK8Rec A
    wo := woAt d rw
    carry := cr
    pub := pubP1 d Mg.pub
    pubP := fun q a => if p1Item q = true then True else Mg.pubP q a }

section
variable {P W : Type} {nR kC : ℕ} (d : PubData) (rw : P × S → W → PileWit nR kC)
  (A : ℕ → P × S → W → ℕ → ℕ → ℕ → Cb.Gl.E) (cr : ℕ → P × S → Strs → W → Prop)
  (Mg : Meaning P W)

/-- (i) The layer's `pub` is its half with code, by the make. -/
theorem fillP1_pub : (fillP1 d rw A cr Mg).pub = pubP1 d Mg.pub := rfl

/-- (ii) What it lays, at every `Meaning`. -/
theorem fillP1_tie : (fillP1 d rw A cr Mg).tie = K8.tieK8Rec A := rfl
theorem fillP1_wo : (fillP1 d rw A cr Mg).wo = woAt d rw := rfl
theorem fillP1_carry : (fillP1 d rw A cr Mg).carry = cr := rfl
theorem fillP1_hasRow (m : ℕ) (a : P × S) :
    (fillP1 d rw A cr Mg).pub (.hasRow m) a =
      Johnson.Desc.First.Walk.Law.hasRow d.lay (d.ncl m) d.lin a.2 := rfl

/-- The layer's public items say nothing beside their Bools. -/
theorem fillP1_pubP_own (q : Pub) (h : p1Item q = true) (a : P × S) :
    (fillP1 d rw A cr Mg).pubP q a := by
  show if p1Item q = true then True else Mg.pubP q a
  rw [if_pos h]
  trivial

theorem fillP1_pubP_else (q : Pub) (h : p1Item q = false) (a : P × S) :
    (fillP1 d rw A cr Mg).pubP q a = Mg.pubP q a := by
  show (if p1Item q = true then True else Mg.pubP q a) = _
  rw [if_neg (by rw [h]; simp)]

/-- (iii) It leaves every other public item, and every other field. -/
theorem fillP1_else (q : Pub) (h : p1Item q = false) (a : P × S) :
    (fillP1 d rw A cr Mg).pub q a = Mg.pub q a := pubP1_else d Mg.pub q h a

theorem fillP1_fields :
    (fillP1 d rw A cr Mg).pin = Mg.pin ∧ (fillP1 d rw A cr Mg).noColl = Mg.noColl ∧
    (fillP1 d rw A cr Mg).shown = Mg.shown ∧ (fillP1 d rw A cr Mg).held = Mg.held ∧
    (fillP1 d rw A cr Mg).pinW = Mg.pinW ∧ (fillP1 d rw A cr Mg).decodes = Mg.decodes ∧
    (fillP1 d rw A cr Mg).inOrder = Mg.inOrder ∧
    (fillP1 d rw A cr Mg).constr = Mg.constr ∧ (fillP1 d rw A cr Mg).forms = Mg.forms ∧
    (fillP1 d rw A cr Mg).formsT = Mg.formsT ∧ (fillP1 d rw A cr Mg).worth = Mg.worth ∧
    (fillP1 d rw A cr Mg).totalB = Mg.totalB ∧ (fillP1 d rw A cr Mg).total = Mg.total ∧
    (fillP1 d rw A cr Mg).row = Mg.row ∧ (fillP1 d rw A cr Mg).pile = Mg.pile ∧
    (fillP1 d rw A cr Mg).pileOne = Mg.pileOne ∧ (fillP1 d rw A cr Mg).wrow = Mg.wrow ∧
    (fillP1 d rw A cr Mg).more = Mg.more :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end VerifiableInference.Desc.First.FillP1
