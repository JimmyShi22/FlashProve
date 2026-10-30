-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegHeadLedger.lean: the ledger of a normalisation (Inst/Model/Common/Ledger.lean) as forms and
expressions, generic in where the bytes and the cells of the values that are normalised stand, so
that it serves the head and the two normalisations of every layer (but `ledEx`, `wsEx` are applied
at the head alone: `idnEx`, Cm/TargetSegHead.lean; the layers' normalisations have
forms of their own: `LF.b256` to `LF.rq`, Cm/SegFFCellLed.lean).

A ledger writes the sum of squares, the square root and the reciprocal of a normalisation in bytes
with carries; its identities are equations between these bytes. A form (`CForm`,
Cb/Req/ReqSpec.lean) is an affine form in cells; an expression (`Ex1`, Cm/SegHeadExp.lean) is a sum
of monomials, each a coefficient table times a product of atoms. Here each definition of the ledger
but `Ledger.mu` gets its mirror as a form or an expression, with lemmas on its value and on the
places that it reads, and for the expressions on well-formedness.

Main names:
  `lb256` to `lrq`: the ledger's row values as affine forms in the bytes D (a function from the
    number of a byte to a form).
  `wsEx v w B s`: W_s = Σ_j Σ_{l + l' = s} b_l[j] b_l'[j] as a sum atom over w further variables;
    B l b' is the form of cell l at the inner vertex b' = b · 2^w + j (the constant 0 at dead j).
  `val_wsEx`: its value is `Ledger.Wsum d`, if d ≤ 2^w and the forms at j ≥ d have the value 0.
  `ledEx np Ws D k`: the 17 identities as expressions: a mirror of `Ledger.idn`; D n b is the form
    of byte n at the vertex b.
  `val_ledEx`: see its docstring.
  `wf_wsEx`, `wf_ledEx`: well formed, `ledEx` if every `Ws s` is. `pl_wsEx`, `pl_ledEx`: reads only
    places that the bytes' and cells' forms read, `ledEx` also those that the `Ws s` read.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadExp
import Inst.Model.Common.Ledger

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Seg
open Cb Inst.Model Finset Cm.Seg.Ex

theorem sum_range_dead {M : Type} [AddCommMonoid M] {n d : ℕ} (hd : d ≤ n)
    (f : ℕ → M) (h : ∀ j, d ≤ j → j < n → f j = 0) :
    ∑ j ∈ range n, f j = ∑ j ∈ range d, f j := by
  refine (sum_subset (range_subset_range.2 hd) fun j hj hj' => ?_).symm
  exact h j (not_lt.1 fun hlt => hj' (mem_range.2 hlt)) (mem_range.1 hj)

/-! ## 1. Row values as forms -/

section Rows
variable {E : Type} [Field E] (D : ℕ → CForm E)

def lb256 (a n : ℕ) : CForm E := cSum n fun l => ((256 : E) ^ l) • D (a + l)
def lVlo : CForm E := lb256 D 0 6
def lVhi : CForm E := lb256 D 6 4
def lcs (s : ℕ) : CForm E :=
  if s = 0 then cK 0 else if s = 9 then D 9 else lb256 D (10 + 6 * (s - 1)) 6 - cK (2 ^ 47)
def lsa : CForm E := (2 : E) • D 58 + D 59 + ((2 : E) ^ 8) • D 60 + ((2 : E) ^ 16) • D 61
def ls0 : CForm E := D 59
def lsb : CForm E := D 62 + ((2 : E) ^ 8) • D 63
def lsig : CForm E := lsa D + ((2 : E) ^ 24) • lsb D
def ll1 : CForm E := lb256 D 64 5
def lh1 : CForm E := lb256 D 69 5
def lBlo : CForm E := lb256 D 74 3
def lBhi : CForm E := lb256 D 77 2
def lkc : CForm E := D 79 - cK 4
def lRlo : CForm E := lb256 D 80 3
def lRhi : CForm E := lb256 D 83 3
def lR : CForm E := lRlo D + ((2 : E) ^ 24) • lRhi D
def lq1 : CForm E := lb256 D 86 3
def lrr : CForm E := lb256 D 89 5
def lrq : CForm E := lb256 D 94 5

variable (A : ℕ → ℕ → ℕ → E)

@[simp] theorem val_lb256 (a n : ℕ) :
    (lb256 D a n).val A = Ledger.b256 (fun m => (D m).val A) a n := by
  simp [lb256, Ledger.b256]
@[simp] theorem val_lVlo : (lVlo D).val A = Ledger.Vlo fun m => (D m).val A := by
  simp [lVlo, Ledger.Vlo]
@[simp] theorem val_lVhi : (lVhi D).val A = Ledger.Vhi fun m => (D m).val A := by
  simp [lVhi, Ledger.Vhi]
@[simp] theorem val_lcs (s : ℕ) : (lcs D s).val A = Ledger.cs (fun m => (D m).val A) s := by
  unfold lcs Ledger.cs
  split_ifs <;> simp
@[simp] theorem val_lsa : (lsa D).val A = Ledger.sa fun m => (D m).val A := by simp [lsa, Ledger.sa]
@[simp] theorem val_ls0 : (ls0 D).val A = Ledger.s0 fun m => (D m).val A := rfl
@[simp] theorem val_lsb : (lsb D).val A = Ledger.sb fun m => (D m).val A := by simp [lsb, Ledger.sb]
@[simp] theorem val_lsig : (lsig D).val A = Ledger.sig fun m => (D m).val A := by
  simp [lsig, Ledger.sig]
@[simp] theorem val_ll1 : (ll1 D).val A = Ledger.l1 fun m => (D m).val A := by simp [ll1, Ledger.l1]
@[simp] theorem val_lh1 : (lh1 D).val A = Ledger.h1 fun m => (D m).val A := by simp [lh1, Ledger.h1]
@[simp] theorem val_lBlo : (lBlo D).val A = Ledger.Blo fun m => (D m).val A := by
  simp [lBlo, Ledger.Blo]
@[simp] theorem val_lBhi : (lBhi D).val A = Ledger.Bhi fun m => (D m).val A := by
  simp [lBhi, Ledger.Bhi]
@[simp] theorem val_lkc : (lkc D).val A = Ledger.kc fun m => (D m).val A := by simp [lkc, Ledger.kc]
@[simp] theorem val_lRlo : (lRlo D).val A = Ledger.Rlo fun m => (D m).val A := by
  simp [lRlo, Ledger.Rlo]
@[simp] theorem val_lRhi : (lRhi D).val A = Ledger.Rhi fun m => (D m).val A := by
  simp [lRhi, Ledger.Rhi]
@[simp] theorem val_lR : (lR D).val A = Ledger.R fun m => (D m).val A := by simp [lR, Ledger.R]
@[simp] theorem val_lq1 : (lq1 D).val A = Ledger.q1 fun m => (D m).val A := by simp [lq1, Ledger.q1]
@[simp] theorem val_lrr : (lrr D).val A = Ledger.rr fun m => (D m).val A := by simp [lrr, Ledger.rr]
@[simp] theorem val_lrq : (lrq D).val A = Ledger.rq fun m => (D m).val A := by simp [lrq, Ledger.rq]

/-! places: every row value reads bytes below 99 only (`lb256` for a + n ≤ 99, `lcs` for s ≤ 9) -/

variable {D} {P : Cb.Place → Prop} (h : ∀ n < 99, AllPl P (D n))
include h

theorem pl_lb256 {a n : ℕ} (han : a + n ≤ 99) : AllPl P (lb256 D a n) :=
  AllPl.cSum fun l hl => AllPl.smul _ (h _ (by omega))
theorem pl_lVlo : AllPl P (lVlo D) := pl_lb256 h (by norm_num)
theorem pl_lVhi : AllPl P (lVhi D) := pl_lb256 h (by norm_num)
theorem pl_lcs {s : ℕ} (hs : s ≤ 9) : AllPl P (lcs D s) :=
  AllPl.ite (fun _ => AllPl.cK _) fun _ =>
    AllPl.ite (fun _ => h 9 (by norm_num)) fun _ => AllPl.sub (pl_lb256 h (by omega)) (AllPl.cK _)
theorem pl_lsa : AllPl P (lsa D) :=
  AllPl.add (AllPl.add (AllPl.add (AllPl.smul _ (h 58 (by norm_num))) (h 59 (by norm_num)))
      (AllPl.smul _ (h 60 (by norm_num))))
    (AllPl.smul _ (h 61 (by norm_num)))
theorem pl_ls0 : AllPl P (ls0 D) := h 59 (by norm_num)
theorem pl_lsb : AllPl P (lsb D) :=
  AllPl.add (h 62 (by norm_num)) (AllPl.smul _ (h 63 (by norm_num)))
theorem pl_lsig : AllPl P (lsig D) := AllPl.add (pl_lsa h) (AllPl.smul _ (pl_lsb h))
theorem pl_ll1 : AllPl P (ll1 D) := pl_lb256 h (by norm_num)
theorem pl_lh1 : AllPl P (lh1 D) := pl_lb256 h (by norm_num)
theorem pl_lBlo : AllPl P (lBlo D) := pl_lb256 h (by norm_num)
theorem pl_lBhi : AllPl P (lBhi D) := pl_lb256 h (by norm_num)
theorem pl_lkc : AllPl P (lkc D) := AllPl.sub (h 79 (by norm_num)) (AllPl.cK _)
theorem pl_lRlo : AllPl P (lRlo D) := pl_lb256 h (by norm_num)
theorem pl_lRhi : AllPl P (lRhi D) := pl_lb256 h (by norm_num)
theorem pl_lR : AllPl P (lR D) := AllPl.add (pl_lRlo h) (AllPl.smul _ (pl_lRhi h))
theorem pl_lq1 : AllPl P (lq1 D) := pl_lb256 h (by norm_num)
theorem pl_lrr : AllPl P (lrr D) := pl_lb256 h (by norm_num)
theorem pl_lrq : AllPl P (lrq D) := pl_lb256 h (by norm_num)

end Rows

/-! ## 2. The sums of squares' parts, and the 17 identities -/

section Idn
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- W_s as a sum atom. -/
def wsEx (v w : ℕ) (B : ℕ → ℕ → CForm E) (s : ℕ) : Ex1 X E :=
  sumA v w (Ex.pSum 5 fun l =>
      Ex.pSum 5 fun l' => if l + l' = s then aff0 (B l) * aff0 (B l') else Ex.zero)

/-- a row value at every vertex, as an expression -/
def rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) : Ex1 X E :=
  aff fun b => g fun n => D n b

/-- The 17 identities: the mirror of `Ledger.idn`. -/
def ledEx (np : NormPar) (Ws : ℕ → Ex1 X E) (D : ℕ → ℕ → CForm E) (k : ℕ) : Ex1 X E :=
  if k < 9 then Ws k + rowEx D fun d => lcs d k - d k - (256 : E) • lcs d (k + 1)
  else match k with
    | 9 => rowEx D lsa * rowEx D lsb - rowEx D fun d => lBlo d + ((2 : E) ^ 23) • lBhi d
    | 10 =>
      (rowEx D fun d =>
          lVlo d + cK (np.eps : E) - ((2 : E) ^ 25) • lBlo d - ll1 d + ((2 : E) ^ 48) • lkc d) -
        rowEx D lsa * rowEx D lsa
    | 11 => (rowEx D fun d => lVhi d - lBhi d - lkc d) - rowEx D lsb * rowEx D lsb
    | 12 => rowEx D fun d => ll1 d + lh1 d - (2 : E) • lsig d
    | 13 => rowEx D lRlo * rowEx D lsb + rowEx D lRhi * rowEx D lsa - rowEx D lq1
    | 14 => rowEx D lRhi * rowEx D lsb
    | 15 =>
      (rowEx D fun d =>
          cK (2 ^ (np.M + 1)) + lsig d - ls0 d - ((2 : E) ^ 25) • lq1 d - (2 : E) • lrr d) -
        (2 : E) • (rowEx D lRlo * rowEx D lsa)
    | 16 => rowEx D fun d => lrr d + lrq d - lsig d + cK 1
    | _ => Ex.zero

variable (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem val_wsEx (v w : ℕ) (B : ℕ → ℕ → CForm E) (s b d : ℕ) (hd : d ≤ 2 ^ w)
    (hB : ∀ l, ∀ j, d ≤ j → j < 2 ^ w → (B l (b * 2 ^ w + j)).val A = 0) :
    Ex1.val Φ x W A (wsEx v w B s) v b =
      Ledger.Wsum d (fun l j => (B l (b * 2 ^ w + j)).val A) s := by
  unfold wsEx Ledger.Wsum
  rw [val1_sumA]
  rw [sum_range_dead hd _ fun j h1 h2 => by
    simp only [val0_pSum, val0_ite, val0_mul, val0_aff, val0_zero]
    exact sum_eq_zero fun l _ => sum_eq_zero fun l' _ => by rw [hB l j h1 h2, zero_mul, ite_self]]
  simp

@[simp] theorem val_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) (v b : ℕ) :
    Ex1.val Φ x W A (rowEx D g) v b = (g fun n => D n b).val A := by simp [rowEx]

/-- The value of the expression is `Ledger.idn` at the values of W_s and of the bytes. -/
theorem val_ledEx (np : NormPar) (Ws : ℕ → Ex1 X E) (D : ℕ → ℕ → CForm E) (k v b : ℕ) :
    Ex1.val Φ x W A (ledEx np Ws D k) v b =
      Ledger.idn np (fun s => Ex1.val Φ x W A (Ws s) v b) (fun n => (D n b).val A) k := by
  unfold ledEx Ledger.idn
  split_ifs with hk
  · simp
    ring
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) hk
    | 9 => simp; ring
    | 10 => simp; ring
    | 11 => simp; ring
    | 12 => simp
    | 13 => simp
    | 14 => simp
    | 15 => simp; ring
    | 16 => simp
    | _ + 17 => simp

theorem wf_wsEx (v w : ℕ) (B : ℕ → ℕ → CForm E) (s : ℕ) : WF1 (X := X) Φ v (wsEx v w B s) :=
  WF1.sumA Φ
    (All.pSum fun _ _ =>
      All.pSum fun _ _ =>
        All.ite (fun _ => All.mul (WF0.aff Φ _ _) (WF0.aff Φ _ _)) fun _ => All.zero)

theorem wf_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) (v : ℕ) :
    WF1 (X := X) Φ v (rowEx D g) := WF1.aff Φ _ _

theorem wf_ledEx (np : NormPar) {Ws : ℕ → Ex1 X E} (D : ℕ → ℕ → CForm E)
    (k v : ℕ) (hW : ∀ s, WF1 Φ v (Ws s)) : WF1 Φ v (ledEx np Ws D k) := by
  unfold ledEx
  split_ifs with hk
  · exact All.add (hW k) (wf_rowEx Φ _ _ _)
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) hk
    | 9 => exact All.sub (All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _)) (wf_rowEx Φ _ _ _)
    | 10 => exact All.sub (wf_rowEx Φ _ _ _) (All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _))
    | 11 => exact All.sub (wf_rowEx Φ _ _ _) (All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _))
    | 12 => exact wf_rowEx Φ _ _ _
    | 13 =>
      exact All.sub
        (All.add (All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _))
          (All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _)))
        (wf_rowEx Φ _ _ _)
    | 14 => exact All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _)
    | 15 =>
      exact All.sub (wf_rowEx Φ _ _ _) (All.smul _ (All.mul (wf_rowEx Φ _ _ _) (wf_rowEx Φ _ _ _)))
    | 16 => exact wf_rowEx Φ _ _ _
    | _ + 17 => exact All.zero

variable {P : Cb.Place → Prop}

theorem pl_wsEx {v w : ℕ} {B : ℕ → ℕ → CForm E} (s : ℕ)
    (hB : ∀ l < 5, ∀ b < 2 ^ (v + w), AllPl P (B l b)) :
    Pl1 (X := X) P v (wsEx v w B s) :=
  Pl1.sumA (All.pSum fun l hl =>
    All.pSum fun l' hl' =>
      All.ite (fun _ => All.mul (Pl0.aff (hB l hl)) (Pl0.aff (hB l' hl'))) fun _ => All.zero)

theorem pl_rowEx {D : ℕ → ℕ → CForm E} {g : (ℕ → CForm E) → CForm E} {v : ℕ}
    (h : ∀ b < 2 ^ v, AllPl P (g fun n => D n b)) : Pl1 (X := X) P v (rowEx D g) := Pl1.aff h

/-- all places of a form built from row values by +, -, scalar multiples and constants -/
macro "pl_rows " h:term : tactic => `(tactic| (
  repeat' with_reducible first
    | exact AllPl.cK _
    | exact pl_lVlo $h | exact pl_lVhi $h | exact pl_lsa $h | exact pl_ls0 $h | exact pl_lsb $h | exact pl_lsig $h | exact pl_ll1 $h | exact pl_lh1 $h
    | exact pl_lBlo $h | exact pl_lBhi $h | exact pl_lkc $h | exact pl_lRlo $h | exact pl_lRhi $h | exact pl_lR $h | exact pl_lq1 $h | exact pl_lrr $h | exact pl_lrq $h
    | apply AllPl.smul
    | apply AllPl.sub
    | apply AllPl.add))

theorem pl_ledEx (np : NormPar) {Ws : ℕ → Ex1 X E} {D : ℕ → ℕ → CForm E} {k v : ℕ}
    (hW : ∀ s, Pl1 P v (Ws s)) (hD : ∀ b < 2 ^ v, ∀ n < 99, AllPl P (D n b)) :
    Pl1 P v (ledEx np Ws D k) := by
  have row : ∀ g : (ℕ → CForm E) → CForm E,
      (∀ d : ℕ → CForm E, (∀ n < 99, AllPl P (d n)) → AllPl P (g d)) →
      Pl1 (X := X) P v (rowEx D g) :=
    fun g hg => pl_rowEx fun b hb => hg _ (hD b hb)
  unfold ledEx
  split_ifs with hk
  · exact All.add (hW k)
      (row _ fun d hd =>
        AllPl.sub (AllPl.sub (pl_lcs hd (by omega)) (hd k (by omega)))
          (AllPl.smul _ (pl_lcs hd (by omega))))
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) hk
    | 9 =>
      exact All.sub (All.mul (row _ fun d hd => pl_lsa hd) (row _ fun d hd => pl_lsb hd))
        (row _ fun d hd => by pl_rows hd)
    | 10 =>
      exact All.sub (row _ fun d hd => by pl_rows hd)
        (All.mul (row _ fun d hd => pl_lsa hd) (row _ fun d hd => pl_lsa hd))
    | 11 =>
      exact All.sub (row _ fun d hd => by pl_rows hd)
        (All.mul (row _ fun d hd => pl_lsb hd) (row _ fun d hd => pl_lsb hd))
    | 12 => exact row _ fun d hd => by pl_rows hd
    | 13 =>
      exact All.sub
        (All.add (All.mul (row _ fun d hd => pl_lRlo hd) (row _ fun d hd => pl_lsb hd))
          (All.mul (row _ fun d hd => pl_lRhi hd) (row _ fun d hd => pl_lsa hd)))
        (row _ fun d hd => pl_lq1 hd)
    | 14 => exact All.mul (row _ fun d hd => pl_lRhi hd) (row _ fun d hd => pl_lsb hd)
    | 15 =>
      exact All.sub (row _ fun d hd => by pl_rows hd)
        (All.smul _ (All.mul (row _ fun d hd => pl_lRlo hd) (row _ fun d hd => pl_lsa hd)))
    | 16 => exact row _ fun d hd => by pl_rows hd
    | _ + 17 => exact All.zero

end Idn

end Cm.Seg
