-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsA.lean: the late entries that the claims on the norms read, as forms on the early
entries; the tables are true of them; and what the pull-back of the ledger then pays.

The link of a sub-proof takes the late entries through forms on the early entries: late entry j is
meant to be the value of a form a j (Cb/Sub/Late.lean: pullL, Agree). This file writes these forms
for the four kinds of late entries that the claims on the norms read, and shows that, with each late
entry at the value of its form, the tables are true in the sense of Cb/Pv/Lay/End/NormsCl.lean. So
that premise of Cb/Pv/Lay/End/NormsRows.lean falls away, and the ledger enters by its pull-back.

How cells are read. rd reads the cells off the early entries. It is asked to be linear (hrd). Then a
cell is a form on the entries (cellF, val_cellF).

Which late entry is which. LateLay Nm J₂: each late entry has a name in Nm; at' finds the entry of a
name and is right on the good names. The names of all parts of a layers' sub-proof are a letter Nm,
into which the norms' names NormsNm are laid by a map ι; fm gives each name its form, and at the
norms' names in range (InRange) it is asked to be normsFm (hfm). Of a name out of range nothing is
asked: so ι may send such names wherever it likes. Two names in range whose forms differ must go to
two members of Nm, or hfm cannot hold.

Main definitions: cellF, extF, toAff, NormsNm, InRange, normsFm, LateLay, lateA, readsAt.
Main theorems: rd_eq, val_cellF, val_extF, tables_true, norms_pull.

Limits. That the programs' late message has these entries at these places is not said here, nor that
the smallness test gives agreement with these forms. hst (the state that the first sumcheck's output
carries holds the drawn element) stays a premise. Sizes as in Cb/Pv/Lay/End/NormsPay.lean.


-/
import Cb.Sub.Late
import Cb.Pv.Lay.End.NormsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr led bS val streamAt lDd)
open Blocks (ext eqN Form)

/-! ### Cells as forms -/

section Lin

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J] (rd : (J → E) → Cell → E)
  (hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
    rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c)

omit [Fintype J] [DecidableEq J] in
include hrd in
theorem rd_zero (c : Cell) : rd (fun _ => 0) c = 0 := by
  have h := hrd 0 0 (fun _ => 0) (fun _ => 0) c
  simpa using h

omit [Fintype J] in
include hrd in
theorem rd_part (s : Finset J) (m : J → E) (c : Cell) :
    rd (fun j => if j ∈ s then m j else 0) c = ∑ i ∈ s, m i * rd (Pi.single i 1) c := by
  refine Finset.induction_on s ?_ ?_
  · simpa using rd_zero rd hrd c
  · intro i s hi ih
    have e : (fun j => if j ∈ insert i s then m j else 0) =
        fun j => m i * (Pi.single i 1 : J → E) j + 1 * (if j ∈ s then m j else 0) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hi]
      · simp [hj]
    rw [e, hrd, ih, sum_insert hi, one_mul]

include hrd in
/-- A cell is a linear combination of the entries. -/
theorem rd_eq (m : J → E) (c : Cell) : rd m c = ∑ j, rd (Pi.single j 1) c * m j := by
  have h := rd_part rd hrd Finset.univ m c
  simp only [mem_univ, if_true] at h
  rw [h]
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- A cell as a form on the entries. -/
def cellF (c : Cell) : Form J E := fun o => o.elim 0 fun j => rd (Pi.single j 1) c

include hrd in
theorem val_cellF (m : J → E) (c : Cell) : Form.val m (cellF rd c) = rd m c := by
  rw [Form.val_apply, rd_eq rd hrd m c]
  simp [cellF]

/-- The extension over 2^g places of a family of cells, at a point, as a form. -/
def extF (g : ℕ) (c : ℕ → Cell) (z : ℕ → E) : Form J E :=
  ∑ p ∈ range (2 ^ g), eqN g 0 z p • cellF rd (c p)

include hrd in
theorem val_extF (m : J → E) (g : ℕ) (c : ℕ → Cell) (z : ℕ → E) :
    Form.val m (extF rd g c z) = ext g (fun p => rd m (c p)) z := by
  unfold extF Blocks.ext
  rw [map_sum]
  exact sum_congr rfl fun p _ => by rw [map_smul, val_cellF rd hrd, smul_eq_mul]

omit [DecidableEq J] in
/-- A form of Blocks/Form.lean as an affine form of Cb/G6/Led.lean. -/
def toAff (f : Form J E) : TWhole.Aff E J := ⟨fun j => f (some j), f none⟩

omit [DecidableEq J] in
theorem toAff_val (f : Form J E) (m : J → E) : (toAff f).val m = Form.val m f := by
  unfold toAff TWhole.Aff.val
  rw [Form.val_apply, add_comm]

end Lin

/-! ### The norms' late entries -/

/-- The names of the late entries that the claims on the norms read: limb l of block kh of the
stream at place ν; cell n of the ledger of norm ν at the norms' token point and at the end point of
the token sumcheck; the selector's entry x of routed layer l. -/
inductive NormsNm
  | xi (ν l kh : ℕ)
  | atP (ν n : ℕ)
  | atR (ν n : ℕ)
  | sel (l x : ℕ)

/-- The names in range. n: the number of norms; B: the number of blocks of the stream; ne: the
number of layers with routed experts; nx: the number of experts. -/
def InRange (n B ne nx : ℕ) : NormsNm → Prop
  | .xi ν l kh => ν < n ∧ l < 5 ∧ kh < B
  | .atP ν k => ν < n ∧ k < 99
  | .atR ν k => ν < n ∧ k < 99
  | .sel l x => l < ne ∧ x < nx

/-- What the late entry of a name is meant to be. -/
def normsFm {E J : Type} [Field E] [DecidableEq J] (rd : (J → E) → Cell → E) (D : Dim)
    (e : NormsE E) (lNI b s : ℕ) : NormsNm → Form J E
  | .xi ν l kh => ∑ r ∈ range (2 ^ s), eqN s (lNI + b) e.r1 r •
      extF rd D.lT (fun p => ⟨(streamAt D ν).1, l, (streamAt D ν).2, kh * 2 ^ s + r, p⟩)
        (fun j => e.r1 (lNI + (b + s) + j))
  | .atP ν n => extF rd D.lT (fun p => ⟨.D, 0, ν, n, p⟩) e.pV
  | .atR ν n => extF rd D.lT (fun p => ⟨.D, 0, ν, n, p⟩) e.r2
  | .sel l x => extF rd D.lT (fun p => ⟨.sel, 0, l, x, p⟩) e.zt

/-- Which late entry has which name. -/
structure LateLay (Nm J₂ : Type) where
  /-- the name of a late entry -/
  nm : J₂ → Nm
  /-- the late entry of a name -/
  at' : Nm → J₂
  /-- the names that late entries have -/
  good : Nm → Prop
  /-- on these, at' is right -/
  ok : ∀ x, good x → nm (at' x) = x

/-- The forms of all late entries, from a form for each name. -/
def lateA {E J₁ Nm J₂ : Type} (Y : LateLay Nm J₂) (fm : Nm → TWhole.Aff E J₁) (j : J₂) :
    TWhole.Aff E J₁ := fm (Y.nm j)

/-- The late entries that the claims on the norms read. -/
def readsAt {Nm J₂ : Type} (Y : LateLay Nm J₂) (ι : NormsNm → Nm) : NormsReads J₂ where
  uXi ν l kh := Y.at' (ι (.xi ν l kh))
  uP ν n := Y.at' (ι (.atP ν n))
  uR ν n := Y.at' (ι (.atR ν n))
  uSel l x := Y.at' (ι (.sel l x))

/-- A byte of a ledger is its cell plus 128. -/
theorem led_cell {E : Type} [Field E] (t : Cell → E) (ν i n : ℕ) :
    led t ν i n = t ⟨.D, 0, ν, n, i⟩ + 128 := by
  unfold Inst.Model.FFSeg.led Inst.Model.FFSeg.val
  simp [Arr.nCell, Arr.off]

/-- A selector's entry is its cell. -/
theorem sel_cell {E : Type} [Field E] (t : Cell → E) (l x i : ℕ) :
    val t .sel l x i = t ⟨.sel, 0, l, x, i⟩ := by
  unfold Inst.Model.FFSeg.val
  simp [Arr.nCell, Arr.off]

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) {Nm J₂ : Type}
  [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

omit [Fintype J₂] [DecidableEq J₂] in
/-- With each late entry at the value of its form, the tables are true. -/
theorem tables_true
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J) (e : NormsE E)
    (lNI b s B : ℕ)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
      fm (ι x) = toAff (normsFm P.rd P.D e lNI b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x))) (m : P.J → E) :
    TablesTrue (namesAt P (readsAt Y ι)) e P.D (P.rd m) lNI b s B
      (Sum.elim m fun j => (lateA Y fm j).val m) := by
  have key : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x → Y.good (ι x) →
      (lateA Y fm (Y.at' (ι x))).val m = Form.val m (normsFm P.rd P.D e lNI b s x) :=
    fun x hr hx => by
      unfold lateA
      rw [Y.ok _ hx, hfm _ hr, toAff_val]
  refine ⟨fun ν l kh h1 h2 h3 => ?_, fun ν n h1 h2 => ?_, fun ν n h1 h2 => ?_,
    fun l x h1 h2 => ?_⟩
  · show (lateA Y fm (Y.at' (ι (.xi ν l kh)))).val m = _
    rw [key (.xi ν l kh) ⟨h1, h2, h3⟩ (gXi ν l kh h1 h2 h3)]
    show Form.val m (∑ r ∈ range (2 ^ s), _ • _) = _
    rw [map_sum]
    exact sum_congr rfl fun r _ => by
      rw [map_smul, val_extF P.rd hrd, smul_eq_mul]
      rfl
  · show (lateA Y fm (Y.at' (ι (.atP ν n)))).val m + 128 = _
    rw [key (.atP ν n) ⟨h1, h2⟩ (gP ν n h1 h2)]
    show Form.val m (extF P.rd P.D.lT _ e.pV) + 128 = _
    rw [val_extF P.rd hrd]
    simp only [led_cell]
    rw [Blocks.ext_add, Blocks.ext_const]
  · show (lateA Y fm (Y.at' (ι (.atR ν n)))).val m + 128 = _
    rw [key (.atR ν n) ⟨h1, h2⟩ (gR ν n h1 h2)]
    show Form.val m (extF P.rd P.D.lT _ e.r2) + 128 = _
    rw [val_extF P.rd hrd]
    simp only [led_cell]
    rw [Blocks.ext_add, Blocks.ext_const]
  · show (lateA Y fm (Y.at' (ι (.sel l x)))).val m = _
    rw [key (.sel l x) ⟨h1, h2⟩ (gS l x h1 h2)]
    show Form.val m (extF P.rd P.D.lT _ e.zt) = _
    rw [val_extF P.rd hrd]
    simp only [sel_cell]

/-- The five clauses that the chain owes at its end for the norms, from the pull-back of the ledger
of the claims on the norms to the early entries. -/
theorem norms_pull
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J) (p : Fin P.D.lT → E)
    (sW : Fin (P.D.nNu * 9) → E) (c : E) (o1 : P.sq.R.L.toSum.T.par.Out)
    (sP : Fin (P.D.nNu * 7) → E) (σ z : E) (o2 : P.rows.tok.toSum.T.par.Out) (zt : ℕ → E)
    (m : P.J → E) (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hst : o1.st.1.2 = c)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x → fm (ι x) =
      toAff (normsFm P.rd P.D (normsEAt P p sW c o1 sP σ z o2 zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (normsLed (namesAt P (readsAt Y ι)) (normsEAt P p sW c o1 sP σ z o2 zt) (u1At P o1)
        (u2At P o2) P.D (P.D.lL + 1) b B)) m) :
    P.sq.B ((p, fun q => sW (finProdFinEquiv q)), c) m ∧
      P.sq.R.L.toSum.T.par.OutHolds o1 m ∧
      (P.rows.led p m fun n => sP n - m (P.mkP n)) ∧ P.rows.tie ((p, sP), σ) z m ∧
      P.rows.tok.toSum.T.par.OutHolds o2 m :=
  norms_pay_rows P (readsAt Y ι) p sW c o1 sP σ z o2 zt m _ b s B hl hd hB hst
    (tables_true P hrd Y ι fm _ (P.D.lL + 1) b s B hfm gXi gP gR gS m)
    ((Cb.Sub.pullL_holds _ _ m).1 h)

end Cb.Pv.Lay.End
