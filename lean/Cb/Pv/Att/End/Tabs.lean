-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Tabs.lean: the tables of an attention sub-proof as forms on the cells, and the forms
that read them, with what they are worth.

Definitions, statements and proofs. The message that an attention sub-proof sends late holds tables.
An entry of a table is meant to be a public combination of cells of one of three kinds: of the cells
of one feature over all positions; of the cells of a block of 2^ls features over all positions; of
2^lmS cells of entries of a region that follow each other. The verifier's claims read the tables
through public combinations of entries. This file writes both in the library's names of cells (Raw
in Inst/Model/Att/Trace.lean) and shows that a reading form, with each entry at its meant value, is
one of the library's reads of the cells (rd2, rd3 in Inst/Model/Att/Sums.lean; Blocks.ext).

Main names:
  Raw.atPos, Raw.addN, Raw.addX: a cell's name at another position, feature, entry. These three are
    declared beside the library's Raw (Inst.Model.AttSeg.Raw), so that r.addN x can be written.
  TabW: the kind of a table with its weights. TabW.form: what an entry is meant to be. An entry is
    named by its table's name and the name of its first cell.
  LateLay Tn J₂: which late entry has which name: nm, at, and ok: at is right on the good names.
  lateA: the forms of all late entries.
  rdRow, rdLong, rdCol: the three reading forms.
  rdRow_val, rdLong_val, rdCol_val: what they are worth at late (lateA ..) m.

Limits: the names of late entries are letters. That the programs' message has these entries at these
places is not said here. Nothing on an honest prover or on hiding.


-/
import Cb.Pv.Att.End.Forms
import Inst.Model.Att.KeyForms
import Blocks.LookupCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

/-! ### Names of cells -/

/-- The cell of the same feature at position i. A cell of an entry of a region has no position. -/
def _root_.Inst.Model.AttSeg.Raw.atPos : Raw → ℕ → Raw
  | .c ρ jj b x, _ => .c ρ jj b x
  | .mx k b g _, i => .mx k b g i
  | .den k b g _, i => .den k b g i
  | .ib k b g _, i => .ib k b g i
  | .qh b g _ n, i => .qh b g i n
  | .qh' b g _ n, i => .qh' b g i n
  | .qry k b g _ n, i => .qry k b g i n
  | .out k b g _ n, i => .out k b g i n
  | .key k lam g _ n, i => .key k lam g i n
  | .val k lam g _ n, i => .val k lam g i n

/-- The cell c features further within the head. -/
def _root_.Inst.Model.AttSeg.Raw.addN : Raw → ℕ → Raw
  | .qh b g i n, c => .qh b g i (n + c)
  | .qh' b g i n, c => .qh' b g i (n + c)
  | .qry k b g i n, c => .qry k b g i (n + c)
  | .out k b g i n, c => .out k b g i (n + c)
  | .key k lam g i n, c => .key k lam g i (n + c)
  | .val k lam g i n, c => .val k lam g i (n + c)
  | r, _ => r

/-- The same cell of the entry y entries further in the region. -/
def _root_.Inst.Model.AttSeg.Raw.addX : Raw → ℕ → Raw
  | .c ρ jj b x, y => .c ρ jj b (x + y)
  | r, _ => r

theorem addN_addN (r : Raw) (a c : ℕ) : (r.addN a).addN c = r.addN (a + c) := by
  cases r <;> simp [Raw.addN, Nat.add_assoc]

theorem addX_addX (r : Raw) (a c : ℕ) : (r.addX a).addX c = r.addX (a + c) := by
  cases r <;> simp [Raw.addX, Nat.add_assoc]

variable {E : Type} [Field E]

/-! ### Tables -/

/-- The kind of a table, with its weights. -/
inductive TabW (E : Type)
  /-- one feature over all positions, under the weights Ψ -/
  | row (Ψ : ℕ → E)
  /-- a block of features over all positions, under the weights low on the features and Ψ -/
  | long (low Ψ : ℕ → E)
  /-- cells of entries that follow each other, under the weights phi -/
  | col (phi : ℕ → E)

section Tab
variable {J₁ : Type} [DecidableEq J₁] (cellJ : Raw → J₁) (D : Dim) (ls lmS : ℕ)

/-- What the entry with the first cell r is meant to be. -/
def TabW.form : TabW E → Raw → Aff E J₁
  | .row Ψ, r => aSum (range D.T) fun i => aSmul (Ψ i) (aEnt (cellJ (r.atPos i)))
  | .long low Ψ, r => aSum (range (2 ^ ls)) fun c => aSum (range D.T) fun i =>
      aSmul (low c * Ψ i) (aEnt (cellJ ((r.addN c).atPos i)))
  | .col phi, r => aSum (range (2 ^ lmS)) fun lo => aSmul (phi lo) (aEnt (cellJ (r.addX lo)))

end Tab

/-- Which late entry has which name. A name: the table's name and the entry's first cell. Tn: the
tables' names. -/
structure LateLay (Tn J₂ : Type) where
  /-- the name of a late entry -/
  nm : J₂ → Tn × Raw
  /-- the late entry of a name -/
  at' : Tn × Raw → J₂
  /-- the names that late entries have -/
  good : Tn × Raw → Prop
  /-- on these, at' is right -/
  ok : ∀ x, good x → nm (at' x) = x

section Read
variable {Tn J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁] [DecidableEq J₂]
  (cellJ : Raw → J₁) (D : Dim) (ls lmS : ℕ) (Y : LateLay Tn J₂) (tb : Tn → TabW E)

/-- The forms of all late entries. -/
def lateA (j : J₂) : Aff E J₁ := (tb (Y.nm j).1).form cellJ D ls lmS (Y.nm j).2

/-- The late entry of a name, as a form. -/
def entF (x : Tn × Raw) : Aff E (J₁ ⊕ J₂) := aEnt (.inr (Y.at' x))

/-- A late entry of a good name, at its meant value. -/
theorem val_entF (m : J₁ → E) {x : Tn × Raw} (hx : Y.good x) :
    (entF (J₁ := J₁) Y x).val (late (lateA cellJ D ls lmS Y tb) m) =
      ((tb x.1).form cellJ D ls lmS x.2).val m := by
  unfold entF
  rw [val_aEnt]
  show (lateA cellJ D ls lmS Y tb (Y.at' x)).val m = _
  unfold lateA
  rw [Y.ok x hx]

/-- Reads table T, on single features: the sum over the heads g of keys and values, under the
equality weights of vg, of the number that the n limbs base 0 g, base 1 g, .. spell. -/
def rdRow (T : Tn) (vg : ℕ → E) (n : ℕ) (base : ℕ → ℕ → Raw) : Aff E (J₁ ⊕ J₂) :=
  aSum (range D.nG) fun g => aSmul (eqN D.lg 0 vg g)
    (aSum (range n) fun k => aSmul (256 ^ k) (entF Y (T, base k g)))

/-- What rdRow is worth: the library's read rd2. -/
theorem rdRow_val (m : J₁ → E) {T : Tn} {Ψ : ℕ → E} (hT : tb T = .row Ψ) (vg : ℕ → E) (n : ℕ)
    (base : ℕ → ℕ → Raw) (hg : ∀ g < D.nG, ∀ k < n, Y.good (T, base k g)) :
    (rdRow (J₁ := J₁) D Y T vg n base).val (late (lateA cellJ D ls lmS Y tb) m) =
      rd2 D vg Ψ fun g i => ∑ k ∈ range n, 256 ^ k * m (cellJ ((base k g).atPos i)) := by
  unfold rdRow rd2
  rw [val_aSum]
  refine sum_congr rfl fun g hg' => ?_
  rw [val_aSmul, val_aSum, mul_sum]
  have e : ∀ k ∈ range n, (aSmul ((256 : E) ^ k) (entF (J₁ := J₁) Y (T, base k g))).val
      (late (lateA cellJ D ls lmS Y tb) m) =
      ∑ i ∈ range D.T, 256 ^ k * (Ψ i * m (cellJ ((base k g).atPos i))) := by
    intro k hk
    rw [val_aSmul, val_entF cellJ D ls lmS Y tb m (hg g (mem_range.mp hg') k (mem_range.mp hk))]
    show _ * ((tb T).form cellJ D ls lmS (base k g)).val m = _
    rw [hT]
    show _ * (aSum (range D.T) fun i => aSmul (Ψ i) (aEnt (cellJ ((base k g).atPos i)))).val m = _
    rw [val_aSum, mul_sum]
    exact sum_congr rfl fun i _ => by rw [val_aSmul, val_aEnt]
  rw [sum_congr rfl fun k hk => congrArg (eqN D.lg 0 vg g * ·) (e k hk)]
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

/-- Reads table T, on cells of entries that follow each other: the cells r, r + 1, .. of 2^l entries
at the point z. -/
def rdCol (T : Tn) (l : ℕ) (z : ℕ → E) (r : Raw) : Aff E (J₁ ⊕ J₂) :=
  aSum (range (2 ^ (l - lmS))) fun hi =>
    aSmul (eqN (l - lmS) 0 z hi) (entF Y (T, r.addX (hi * 2 ^ lmS)))

/-- What rdCol is worth: the extension of the cells at z. -/
theorem rdCol_val (m : J₁ → E) {T : Tn} {l : ℕ} (hl : lmS ≤ l) (z : ℕ → E)
    (hT : tb T = .col (eqN lmS (l - lmS) z)) (r : Raw)
    (hg : ∀ hi < 2 ^ (l - lmS), Y.good (T, r.addX (hi * 2 ^ lmS))) :
    (rdCol (J₁ := J₁) lmS Y T l z r).val (late (lateA cellJ D ls lmS Y tb) m) =
      Blocks.ext l (fun y => m (cellJ (r.addX y))) z := by
  have hsplit : l = l - lmS + lmS := by omega
  unfold rdCol
  rw [val_aSum]
  conv_rhs => rw [hsplit, Blocks.ext_two]
  refine sum_congr rfl fun hi hhi => ?_
  rw [val_aSmul, val_entF cellJ D ls lmS Y tb m (hg hi (mem_range.mp hhi))]
  show _ * ((tb T).form cellJ D ls lmS (r.addX (hi * 2 ^ lmS))).val m = _
  rw [hT]
  show _ * (aSum (range (2 ^ lmS)) fun lo => aSmul (eqN lmS (l - lmS) z lo)
    (aEnt (cellJ ((r.addX (hi * 2 ^ lmS)).addX lo)))).val m = _
  rw [val_aSum, mul_sum]
  refine sum_congr rfl fun lo _ => ?_
  rw [val_aSmul, val_aEnt, addX_addX]
  ring

/-- A fourfold sum with the last index first and the middle two exchanged. -/
theorem end_perm4 (A B C D' : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → E) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D', g a b c d =
      ∑ d ∈ D', ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, g a b c d := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D', g a b c d
      = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D', g a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D', ∑ b ∈ B, g a b c d :=
        sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_comm
    _ = ∑ a ∈ A, ∑ d ∈ D', ∑ c ∈ C, ∑ b ∈ B, g a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ d ∈ D', ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, g a b c d := sum_comm

/-- Reads table T, on blocks of features: the sum over the heads g, under the equality weights of
vg, and over the blocks of a head's features, under the equality weights of the first ln - ls
coordinates of vn, of the number that the n limbs spell. -/
def rdLong (T : Tn) (vg vn : ℕ → E) (n : ℕ) (base : ℕ → ℕ → Raw) : Aff E (J₁ ⊕ J₂) :=
  aSum (range D.nG) fun g => aSmul (eqN D.lg 0 vg g)
    (aSum (range (2 ^ (D.ln - ls))) fun ch => aSmul (eqN (D.ln - ls) 0 vn ch)
      (aSum (range n) fun k => aSmul (256 ^ k) (entF Y (T, (base k g).addN (ch * 2 ^ ls)))))

/-- What rdLong is worth: the library's read rd3. -/
theorem rdLong_val (m : J₁ → E) {T : Tn} {Ψ : ℕ → E} (hls : ls ≤ D.ln) (vg vn : ℕ → E)
    (hT : tb T = .long (eqN ls (D.ln - ls) vn) Ψ) (n : ℕ) (base : ℕ → ℕ → Raw)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < n,
      Y.good (T, (base k g).addN (ch * 2 ^ ls))) :
    (rdLong (J₁ := J₁) D ls Y T vg vn n base).val (late (lateA cellJ D ls lmS Y tb) m) =
      rd3 D vg Ψ vn fun g i x =>
        ∑ k ∈ range n, 256 ^ k * m (cellJ (((base k g).addN x).atPos i)) := by
  have hch : D.ch = 2 ^ (D.ln - ls) * 2 ^ ls := by
    show 2 ^ D.ln = _
    rw [← pow_add]
    congr 1
    omega
  have e2 : D.ln - ls + ls = D.ln := by omega
  unfold rdLong rd3
  rw [val_aSum]
  refine sum_congr rfl fun g hg' => ?_
  rw [val_aSmul, val_aSum]
  have e : ∀ ch ∈ range (2 ^ (D.ln - ls)),
      (aSmul (eqN (D.ln - ls) 0 vn ch) (aSum (range n) fun k =>
        aSmul ((256 : E) ^ k) (entF (J₁ := J₁) Y (T, (base k g).addN (ch * 2 ^ ls))))).val
        (late (lateA cellJ D ls lmS Y tb) m) =
      ∑ k ∈ range n, ∑ c ∈ range (2 ^ ls), ∑ i ∈ range D.T,
        eqN (D.ln - ls) 0 vn ch * (256 ^ k * (eqN ls (D.ln - ls) vn c * Ψ i *
          m (cellJ (((base k g).addN (ch * 2 ^ ls + c)).atPos i)))) := by
    intro ch hch'
    rw [val_aSmul, val_aSum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [val_aSmul, val_entF cellJ D ls lmS Y tb m
      (hg g (mem_range.mp hg') ch (mem_range.mp hch') k (mem_range.mp hk))]
    show _ * (_ * ((tb T).form cellJ D ls lmS ((base k g).addN (ch * 2 ^ ls))).val m) = _
    rw [hT]
    show _ * (_ * (aSum (range (2 ^ ls)) fun c => aSum (range D.T) fun i =>
      aSmul (eqN ls (D.ln - ls) vn c * Ψ i)
        (aEnt (cellJ ((((base k g).addN (ch * 2 ^ ls)).addN c).atPos i)))).val m) = _
    rw [val_aSum, mul_sum, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [val_aSum, mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => by rw [val_aSmul, val_aEnt, addN_addN]
  rw [sum_congr rfl e, end_perm4, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hch, Alg.sum_range_mul_add, mul_sum]
  refine sum_congr rfl fun ch _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  have e1 := Blocks.eqN_append' (D.ln - ls) ls 0 vn ch (mem_range.mp hc)
  rw [e2, Nat.zero_add] at e1
  rw [e1, mul_sum, mul_sum]
  exact sum_congr rfl fun k _ => by ring

end Read

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.rdRow_val
#print axioms Cb.Pv.Att.End.rdCol_val
#print axioms Cb.Pv.Att.End.rdLong_val
