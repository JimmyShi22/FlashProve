-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowB.lean: the B side of the summand of the batched sumcheck at its end values:
the verifier's element of the field (BsAt, Johnson/Road/FormsKeysEnd.lean) against the library's
typed second side (Cb/Pv/Lay/At/Inner.lean: sideB), as far as it is geometry and sums.

The typed sumcheck's summand at end values v is a product of two sums, one for each side: over the
side's pieces, a public coefficient times the piece's end value. The coefficient of a piece is a
public factor times the equality weight of the piece's block among the blocks of its size
(Cb/Pv/Lay/At/Pieces.lean: side). The verifier computes, panel by panel, the weight of the panel's
number (sbK) and of each row (eiK), and adds weight times public factors times shown value.

Main names:
  `zR`: the verifier's challenges, read and turned round.
  `geo_sb`: the weight of a panel's number is the library's equality weight of that number.
  `geo_sbei`: that weight times a row's weight is the equality weight of the row's block.
  `f2_sum`: sums over two lists whose members agree pair by pair.
  `sum_members`, `sum_pieces`: a sum over the members of a list without repeats, as a type, is the
    list's sum; so with some names for each member and one name more.
  `sumIB`: a sum over the names of the second side's pieces.
  `cB_unit`, `cB_three`, `cB_two`: the typed coefficients, written out.
  `bs_typed`: the typed second sum is BsAt, if each placed panel adds what its panel's pieces add.
Limits. bs_typed's premise F2 asks the equation of every pair; nothing here shows it. Identities on
public numbers and given values: nothing on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysEnd
import Cb.Pv.Lay.At.Inner
import Cb.Pv.Lay.End.SigC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World eqIndexOK)
open OnBytes.Model.Layer (SBlk Lay)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (IB cntB InnPar0 kS nP wrow)
open Blocks (eqN)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The verifier's challenges, read and turned round. -/
def zR (rs : Array E) (lam : ℕ) : ℕ → K := fun j => ρ.val (rs.getD (lam - 1 - j) zeroE)

/-- eqR up to the top bit is the library's equality weight at the challenges turned round. -/
theorem eqR_top (rs : Array E) (lo lam c : ℕ) :
    eqR ρ rs lo lam c = eqN (lam - lo) 0 (zR ρ rs lam) c := rfl

/-- The weight of a panel's number. -/
theorem geo_sb {rs : Array E} {lam : ℕ} (hl : lam ≤ rs.size) {b : SBlk}
    (hok : eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) :
    sbK ρ rs lam b = eqN (lam - b.w) 0 (zR ρ rs lam) (b.off / 2 ^ b.w) := by
  unfold sbK
  rw [eqLowAt_value ρ rs hl hok, eqR_top]

/-- The weight of a panel's number times the weight of a row. -/
theorem geo_sbei {rs : Array E} {lam : ℕ} (hl : lam ≤ rs.size) {b : SBlk}
    (hok : eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true) (h1 : b.wy ≤ b.w)
    (h2 : b.w ≤ lam) {i : ℕ} (hi : i < 2 ^ (b.w - b.wy)) :
    sbK ρ rs lam b * eiK ρ rs b i =
      eqN (lam - b.wy) 0 (zR ρ rs lam) (b.off / 2 ^ b.w * 2 ^ (b.w - b.wy) + i) := by
  unfold sbK eiK
  rw [eqLowAt_value ρ rs hl hok, eqLow_value ρ rs (Nat.le_trans h2 hl) hi, ← eqR_top,
    eqR_split ρ rs h1 h2 _ hi]

/-- Sums over two lists whose members agree pair by pair. -/
theorem f2_sum {M α β : Type} [AddMonoid M] {f : α → M} {g : β → M} :
    ∀ {l : List α} {l' : List β},
      List.Forall₂ (fun a b => f a = g b) l l' → (l.map f).sum = (l'.map g).sum
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h, f2_sum t]

/-- A sum over the members of a list without repeats, as a type, is the list's sum. -/
theorem sum_members {M α : Type} [AddCommMonoid M] [DecidableEq α] {l : List α} (hn : l.Nodup)
    (f : α → M) : ∑ p : {p : α // p ∈ l}, f p.1 = (l.map f).sum := by
  rw [← List.sum_toFinset f hn]
  exact (Finset.sum_subtype l.toFinset (fun x => List.mem_toFinset) f).symm

/-- A sum over one name and, for each member of a list without repeats, cnt names. G p: what the
names of p add. -/
theorem sum_pieces {M α : Type} [AddCommMonoid M] [DecidableEq α] {l : List α} (hn : l.Nodup)
    (cnt : α → ℕ) (f : Unit ⊕ (Σ p : {p : α // p ∈ l}, Fin (cnt p.1)) → M) (G : α → M)
    (hG : ∀ p : {p : α // p ∈ l}, ∑ i : Fin (cnt p.1), f (.inr ⟨p, i⟩) = G p.1) :
    ∑ j, f j = f (.inl ()) + (l.map G).sum := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, ← sum_members hn G]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun p _ => hG p

/-- A sum over the names of the second side's pieces. G p: what the pieces of panel p add. -/
theorem sumIB (D : Dim) (f : IB D → K) (G : Pan → K)
    (hG : ∀ p : {p : Pan // p ∈ pans D}, ∑ i : Fin (cntB D p.1), f (.inr ⟨p, i⟩) = G p.1) :
    ∑ j : IB D, f j = f (.inl ()) + ((pans D).map G).sum :=
  sum_pieces (Cb.Pv.Lay.End.Sig.pans_nodup D) (cntB D) f G hG

/-! ## The typed coefficients, written out -/

section Typed

variable {ρ} [Fintype K] [scl : Scl] (P : InnPar0 K) (st : P.St) (z : Fin (kS P.D) → K)

/-- The form part's coefficient is 1. -/
theorem cB_unit : P.sideB.side.c (.inl ()) st z = 1 := by
  show ∑ e ∈ range 1, (1 : K) * eqN (kS P.D - kS P.D) 0 (Blocks.nat z) (0 + e) = 1
  rw [sum_range_one, Nat.sub_self, one_mul]
  rfl

/-- The one piece of a panel with the selector: the weight of the panel's number. -/
theorem cB_three (p : {p : Pan // p ∈ pans P.D}) (h3 : p.1.three = true)
    (i : Fin (cntB P.D p.1)) :
    P.sideB.side.c (.inr ⟨p, i⟩) st z =
      eqN (kS P.D - p.1.wid P.D) 0 (Blocks.nat z) (nP P.D p.1) := by
  show ∑ e ∈ range 1, (if p.1.three then (1 : K) else P.κB st p.1 i) *
      eqN (kS P.D - if p.1.three then p.1.wid P.D else p.1.wcol P.D) 0 (Blocks.nat z)
        ((if p.1.three then nP P.D p.1 else nP P.D p.1 * 2 ^ wrow P.D p.1 + i) + e) = _
  rw [sum_range_one, if_pos h3, if_pos h3, if_pos h3, one_mul, Nat.add_zero]

/-- Piece i of a panel with two factors: the row's public factor times the weight of its block. -/
theorem cB_two (p : {p : Pan // p ∈ pans P.D}) (h3 : p.1.three = false)
    (i : Fin (cntB P.D p.1)) :
    P.sideB.side.c (.inr ⟨p, i⟩) st z = P.κB st p.1 i *
      eqN (kS P.D - p.1.wcol P.D) 0 (Blocks.nat z) (nP P.D p.1 * 2 ^ wrow P.D p.1 + i) := by
  have h3' : ¬ p.1.three = true := by rw [h3]; exact Bool.false_ne_true
  show ∑ e ∈ range 1, (if p.1.three then (1 : K) else P.κB st p.1 i) *
      eqN (kS P.D - if p.1.three then p.1.wid P.D else p.1.wcol P.D) 0 (Blocks.nat z)
        ((if p.1.three then nP P.D p.1 else nP P.D p.1 * 2 ^ wrow P.D p.1 + i) + e) = _
  rw [sum_range_one, if_neg h3', if_neg h3', if_neg h3', Nat.add_zero]

/-- **The typed second sum is BsAt**, if each placed panel adds what its panel's pieces add. v: the
end values, by the pieces' names; G: what a panel's pieces add. -/
theorem bs_typed (W : World K) (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E) (h1 vv : ℕ → K)
    (v : IB P.D → K) (G : Pan → K) {bl : List SBlk}
    (hG : ∀ p : {p : Pan // p ∈ pans P.D},
      ∑ i : Fin (cntB P.D p.1), P.sideB.side.c (.inr ⟨p, i⟩) st z * v (.inr ⟨p, i⟩) = G p.1)
    (F2 : List.Forall₂ (fun b pn => (dEnd ρ W y rs lam om h1 vv b).2.2.2.1 = G pn) bl
      (pans P.D)) :
    ∑ j : IB P.D, P.sideB.side.c j st z * v j =
      BsAt ρ W y rs lam om h1 vv (v (.inl ())) bl := by
  rw [sumIB P.D (fun j => P.sideB.side.c j st z * v j) G hG, cB_unit, one_mul]
  unfold BsAt
  rw [f2_sum F2]

end Typed

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cB_unit
#print axioms OnBytes.Road.K4.cB_three
#print axioms OnBytes.Road.K4.cB_two
#print axioms OnBytes.Road.K4.bs_typed
#print axioms OnBytes.Road.K4.geo_sb
#print axioms OnBytes.Road.K4.geo_sbei
#print axioms OnBytes.Road.K4.sum_pieces
#print axioms OnBytes.Road.K4.sumIB
