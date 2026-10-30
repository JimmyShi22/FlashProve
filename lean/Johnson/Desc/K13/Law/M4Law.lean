-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M4Law.lean: the law of kind K13's block behind W's commitment: its form, and
tries of the form. Definitions, and statements as definitions of propositions; the proofs are in
Johnson/Desc/K13/Law/M4Tries.lean and Johnson/Desc/K13/Law/M4Proof.lean.

The block has no round and draws nothing: so the law has no error. It stands at the border between
W's commitment, which is another kind's block, and `rowsB`.
Main names:
  `linAt`; `Behind`: the witness is pinned; ALL that the statement claims holds of the witness's
    words (`OnBytes.Means.Holds`); W's message holds g^T M (`WIs`).
  `FrontOk`: what is promised of the record in front.
  `pieceQuiet`: a block without a round as a piece.
  `BackAt`: the form of the law, of any block in the place of `rowsB atS P`.
  `lazyB`, `falseClaim`, `Spec.not_back_lazy`; `Spec.back_no`; `Spec.some_matrix_fails`: the tries.
  `Spec.rowsB_back`: the law.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/M4.lean names.

What is not claimed. With "(Eval) says its claim" in the relation behind, in the place of all that
the statement claims, a block that lays no row would meet the form: so the law has to find (Eval)
among the own group's open rows. `WIs` is part of what stands behind: see
Johnson/Desc/K13/Law/Eval.lean on who is to give it. `FrontOk` is a promise that the blocks in front
have to keep: the batching's block lays a claim that is made of a row; that W's vector fits its
table is not shown here. The joined block of the description holds W's commitment too: no rule for
such a joining is given here. `WIs` is given by no law yet. The number nR of the matrix's rows is a
free letter: that it is the plan's is said nowhere but in Johnson/Desc/K13/Law/Caller.lean.

-/
import Johnson.Desc.K13.Law.M4
import Johnson.Desc.K13.Law.Pin
import Johnson.Desc.Means.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Maker
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- What goes on to the third chain, at the chain's end. -/
def linAt (s : S) : Option LinFirst :=
  match s.here with
  | .mem a => a.lin
  | _ => none

/-- **What stands behind the block**: the witness is pinned; all that the statement claims holds of
the witness's words; and W's message, read through its layout, holds g^T M. -/
def Behind {F : Frame} (P : Where) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (Pin : F.E.Str → W → Prop) (b : S × F.E.Str) (w : W) : Prop :=
  Pin b.2 w ∧ OnBytes.Means.Holds ρg b.1.st (rwW w) ∧
    ∀ l, linAt b.1 = some l →
      WIs (rwM w) (rwW w) l.claim.g l.w (linLayW b.1.st.codes P.lin)

/-- What is promised of the record in front: the claim is made of a row, and W's vector fits its
table. Both read the public record alone. -/
def FrontOk {F : Frame} (P : Where) (a : S × F.E.Str) : Prop :=
  ∀ l, linAt a.1 = some l → (∃ row, l.claim = memberClaim row) ∧
    P.lin.kCol ≤ (linLayW a.1.st.codes P.lin).bits

/-- A block without a round, as a piece: no error; the extractor is the identity. -/
def pieceQuiet (F : Frame) (B : Block S Cl) (base : ℕ) : Piece (ckP .two) F S Cl W where
  b := B
  base := base
  ds := []
  back := []
  ext := fun _ _ w => w
  err := ()

/-- **The form of the law**, of any block B in the place of `rowsB atS P`: from what stands behind
to: all rows on the table are true of the matrix and of the words' mask entries. -/
def BackAt (F : Frame) (P : Where) (B : Block S Cl) (base : ℕ)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : F.E.Str → W → Prop) : Prop :=
  (pieceQuiet (W := W) F B base).GoodIn (FrontOk P) (fun _ => True)
    (RowsHold (fun w => witOf (rwM w) (rwW w)) Pin) (Behind P rwM rwW Pin)

/-! ## Tries -/

/-- A block that says yes to all and lays no row: it leaves the record as it is. -/
def lazyB : Block S Cl where
  name := "lazy"
  place := ⟨1, none, 0, .K13⟩
  planOk := true
  rounds := []
  oracles := []
  before := []
  decide := fun s _ _ => .ok s
  claims := []
  after := []

/-- A record at the chain's end whose claim is made of a row that is false of everything; its
statement claims nothing. -/
def falseClaim : S :=
  { S.blank with here := .mem ⟨#[], #[], some { claim := memberClaim ⟨[], [], [], oneE⟩ }⟩ }

/-- **The block that lays no row does not meet the form.** -/
def Spec.not_back_lazy : Prop :=
  ∀ (Cl : Type) (nR : ℕ) (F : Frame) (P : Where) (base : ℕ) (_ : F.E.Str),
    P.lin.kCol ≤ (linLayW S.blank.st.codes P.lin).bits →
    ¬ BackAt (Cl := Cl) (W := Unit) (nR := nR) F P lazyB base (fun _ _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ _ => True)

/-- A block that refuses all meets the form. -/
def Spec.back_no : Prop :=
  ∀ (Cl W : Type) (nR : ℕ) (F : Frame) (P : Where) (base : ℕ)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : F.E.Str → W → Prop),
    BackAt (Cl := Cl) F P { lazyB with decide := fun _ _ _ => .error "no" } base rwM rwW Pin

/-- **Without "W's message holds g^T M" nothing goes back**: what a statement claims of words does
not name the matrix: whatever the words, a row with a weight that is not 0 is false of some matrix.
-/
def Spec.some_matrix_fails : Prop :=
  ∀ (nR k : ℕ) (row : TensorRow) (m : Words GE), (∃ i, weights ρg nR row.g i ≠ 0) →
    ∃ mat : Fin nR → (Fin k → Bool) → GE, ¬ Holds ρg (witOf mat m) row

/-- **The law.** -/
def Spec.rowsB_back : Prop :=
  ∀ (Cl W : Type) (nR : ℕ) (F : Frame) (P : Where) (base : ℕ)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : F.E.Str → W → Prop),
    (∀ a τ b w, (pieceQuiet (Cl := Cl) (W := W) F (rowsB atS P) base).ior.red.out a τ = some b →
      Pin b.2 w → Pin a.2 w) →
    BackAt (Cl := Cl) F P (rowsB atS P) base rwM rwW Pin

end VerifiableInference.Desc.K13.Law
