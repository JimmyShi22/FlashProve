-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/GatedShare.lean: the late entries that the claims on the gated products read, as forms
on the early entries, and what the pull-back of the ledger of these claims pays of what the chain of
a layers' sub-proof's own rounds owes at its end.

The link of a sub-proof takes the late entries through forms on the early entries
(Cb/Sub/Late.lean: pullL). This file writes these forms for the four tables that the claims on the
gated products read, in the names and tools of Cb/Pv/Lay/End/NormsA.lean (LateLay, lateA, extF,
toAff), and shows that with each late entry at the value of its form the tables are true
(GatedTables in Cb/Pv/Lay/End/GatedCl.lean). The claims that the two sumchecks leave are the forms
of Cb/Pv/Lay/End/RowForm.lean. So the ledger enters by its pull-back alone.

Main definitions: GatedNm (the late entries' names), GatedNm.InR (the names in range), readFm,
gatedFm (their forms), gReadsAt,
gatedLedOf (the ledger of the six claims, off the two sumchecks' outputs).
Main theorems.
  val_readFm: the form of a read is worth readAt on the cells that the entries hold.
  gated_tables: GatedTables at the values of the forms.
  gated_pull: the pull-back of the ledger gives all output claims of the two sumchecks.

Limits. hfm and the premises on good names: the late entries' names and forms, as in
Cb/Pv/Lay/End/NormsA.lean. The forms are asked at the names in range alone (GatedNm.InR). Sizes: at
least two layers (1 ≤ lL); the number of hidden units of an expert is a power of two; a block is no
longer than the hidden units of a layer or of an expert. That the ledger is a program's is not said
here.


-/
import Cb.Pv.Lay.End.NormsA
import Cb.Pv.Lay.End.GatedPay
import Cb.Pv.Lay.End.RowForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model.FFSeg (Dim Cell Arr lF lFe)
open Blocks (ext eqN Form)

/-- The names of the late entries that the claims on the gated products read: limb l of block b of
layer i, of the tensors s and u, at the last coordinates of the first layer's point and of the
second's. -/
inductive GatedNm
  | s5 (l i b : ℕ)
  | u5 (l i b : ℕ)
  | s6 (l i b : ℕ)
  | u6 (l i b : ℕ)

/-- The names in range: those that the four claims read at the sizes D, with 2^s features in a
block. In the second layer the claims read the layers with routed experts (odd numbers) and the
blocks behind the shared expert's. -/
def GatedNm.InR (D : Dim) (s : ℕ) : GatedNm → Prop
  | .s5 l i b | .u5 l i b => l < 2 ∧ i < 2 ^ D.lL ∧ b < 2 ^ (lF D - s)
  | .s6 l j c | .u6 l j c => l < 2 ∧ ∃ i, i < 2 ^ (D.lL - 1) ∧ j = 2 * i + 1 ∧
      ∃ b, b < 2 ^ (lFe D - s) ∧ c = 2 ^ (lFe D - s) + b

section Fm

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J] (rd : (J → E) → Cell → E)

/-- The form of the read of limb l of block kh of layer lam of the array A: see readAt. -/
def readFm (D : Dim) (A : Arr) (r : ℕ → E) (g s l lam kh : ℕ) : Form J E :=
  ∑ q ∈ range (2 ^ s), eqN s g r q •
    extF rd D.lT (fun p => ⟨A, l, lam, kh * 2 ^ s + q, p⟩) (fun j => r (g + s + j))

theorem val_readFm
    (hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
      rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c)
    (D : Dim) (A : Arr) (r : ℕ → E) (g s l lam kh : ℕ) (m : J → E) :
    Form.val m (readFm rd D A r g s l lam kh) = readAt D (rd m) A r g s l lam kh := by
  unfold readFm readAt
  rw [map_sum]
  exact sum_congr rfl fun q _ => by rw [map_smul, val_extF rd hrd, smul_eq_mul]

/-- What the late entry of a name is meant to be. -/
def gatedFm (D : Dim) (e : GatedE E) (s : ℕ) : GatedNm → Form J E
  | .s5 l i b => readFm rd D .sl e.r5 (D.lL + lF D - s) s l i b
  | .u5 l i b => readFm rd D .up e.r5 (D.lL + lF D - s) s l i b
  | .s6 l i b => readFm rd D .sl e.r6 (D.lL - 1 + lFe D - s) s l i b
  | .u6 l i b => readFm rd D .up e.r6 (D.lL - 1 + lFe D - s) s l i b

end Fm

/-- The late entries that the claims read. -/
def gReadsAt {Nm J₂ : Type} (Y : LateLay Nm J₂) (ι : GatedNm → Nm) : GatedReads J₂ where
  uS5 l i b := Y.at' (ι (.s5 l i b))
  uU5 l i b := Y.at' (ι (.u5 l i b))
  uS6 l i b := Y.at' (ι (.s6 l i b))
  uU6 l i b := Y.at' (ι (.u6 l i b))

/-- The names that the four claims read are names of late entries. -/
structure GoodNm {Nm J₂ : Type} (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (D : Dim) (s : ℕ) :
    Prop where
  s5 : ∀ l, l < 2 → ∀ i, i < 2 ^ D.lL → ∀ b, b < 2 ^ (lF D - s) → Y.good (ι (.s5 l i b))
  u5 : ∀ l, l < 2 → ∀ i, i < 2 ^ D.lL → ∀ b, b < 2 ^ (lF D - s) → Y.good (ι (.u5 l i b))
  s6 : ∀ l, l < 2 → ∀ i, i < 2 ^ (D.lL - 1) → ∀ b, b < 2 ^ (lFe D - s) →
    Y.good (ι (.s6 l (2 * i + 1) (2 ^ (lFe D - s) + b)))
  u6 : ∀ l, l < 2 → ∀ i, i < 2 ^ (D.lL - 1) → ∀ b, b < 2 ^ (lFe D - s) →
    Y.good (ι (.u6 l (2 * i + 1) (2 ^ (lFe D - s) + b)))

section Pull

variable {E : Type} [Field E] [Fintype E] (P : FootPar0 E) {Nm J₂ : Type} [Fintype J₂]
  [DecidableEq P.J] [DecidableEq J₂]

omit [Fintype J₂] [DecidableEq J₂] in
/-- With each late entry at the value of its form, the tables are true. -/
theorem gated_tables
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J) (e : GatedE E) (s : ℕ)
    (hfm : ∀ x : GatedNm, x.InR P.D s →
      fm (ι x) = toAff (gatedFm P.rd P.D e s x)) (hY : GoodNm Y ι P.D s)
    (m : P.J → E) :
    GatedTables (gNamesAt P (gReadsAt Y ι)) e P.D (P.rd m) s
      (Sum.elim m fun j => (lateA Y fm j).val m) := by
  have key : ∀ x : GatedNm, x.InR P.D s → Y.good (ι x) → (lateA Y fm (Y.at' (ι x))).val m =
      Form.val m (gatedFm P.rd P.D e s x) := fun x hr hx => by
    unfold lateA
    rw [Y.ok _ hx, hfm _ hr, toAff_val]
  refine ⟨fun l hl i hi b hb => ?_, fun l hl i hi b hb => ?_, fun l hl i hi b hb => ?_,
    fun l hl i hi b hb => ?_⟩
  · show (lateA Y fm (Y.at' (ι (.s5 l i b)))).val m = _
    rw [key (.s5 l i b) ⟨hl, hi, hb⟩ (hY.s5 l hl i hi b hb)]
    exact val_readFm P.rd hrd P.D .sl _ _ s l i b m
  · show (lateA Y fm (Y.at' (ι (.u5 l i b)))).val m = _
    rw [key (.u5 l i b) ⟨hl, hi, hb⟩ (hY.u5 l hl i hi b hb)]
    exact val_readFm P.rd hrd P.D .up _ _ s l i b m
  · show (lateA Y fm (Y.at' (ι (.s6 l (2 * i + 1) (2 ^ (lFe P.D - s) + b))))).val m = _
    rw [key (.s6 l (2 * i + 1) (2 ^ (lFe P.D - s) + b)) ⟨hl, i, hi, rfl, b, hb, rfl⟩
      (hY.s6 l hl i hi b hb)]
    exact val_readFm P.rd hrd P.D .sl _ _ s l _ _ m
  · show (lateA Y fm (Y.at' (ι (.u6 l (2 * i + 1) (2 ^ (lFe P.D - s) + b))))).val m = _
    rw [key (.u6 l (2 * i + 1) (2 ^ (lFe P.D - s) + b)) ⟨hl, i, hi, rfl, b, hb, rfl⟩
      (hY.u6 l hl i hi b hb)]
    exact val_readFm P.rd hrd P.D .up _ _ s l _ _ m

/-- The ledger of the six claims on the gated products, off the outputs of the two sumchecks. -/
noncomputable def gatedLedOf (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (o5 : P.gp.toSum.T.par.Out)
    (o6 : P.rt.L.toSum.T.par.Out) (s : ℕ) : TWhole.Ledger E (P.J ⊕ J₂) :=
  gatedLed P (gNamesAt P (gReadsAt Y ι)) (gatedEAt P o5 o6) (prodU P.gp o5) (prodU P.rt.L o6) s

/-- All output claims of the two product layers' sumchecks, from the pull-back of the ledger to the
early entries. -/
theorem gated_pull
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (o5 : P.gp.toSum.T.par.Out) (o6 : P.rt.L.toSum.T.par.Out) (m : P.J → E) (s : ℕ)
    (h1 : 1 ≤ P.D.lL) (hs1 : s ≤ lF P.D) (hs2 : s ≤ lFe P.D) (hfe : P.D.fe = 2 ^ lFe P.D)
    (hfm : ∀ x : GatedNm, x.InR P.D s → fm (ι x) = toAff (gatedFm P.rd P.D (gatedEAt P o5 o6) s x))
    (hY : GoodNm Y ι P.D s)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (gatedLedOf P Y ι o5 o6 s)) m) :
    P.gp.toSum.T.par.OutHolds o5 m ∧ P.rt.L.toSum.T.par.OutHolds o6 m :=
  gated_pay P (gReadsAt Y ι) o5 o6 _ _ m _ s h1 hs1 hs2 hfe
    (gated_tables P hrd Y ι fm _ s hfm hY m) ((Cb.Sub.pullL_holds _ _ m).1 h)
    (prodU_iff P.gp o5 m _).1 (prodU_iff P.rt.L o6 m _).1

end Pull

end Cb.Pv.Lay.End.Gated
