-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/CdLink.lean: the codes of the entry's link as codes of the library (`LdCode`), and the two
folded rows' oracle messages: their code, their sample, their seeds, and where a coefficient of a
fold's polynomial stands in them.

Definitions, with the facts on numbers of rows and entries that they and their users need.

Main names:
  `ptOf`, `genOf`: the points and the generator matrix of a code with the sizes C: the coefficient
    number k has the weight z^k at the point z.
  `ldOf C a`: the code, read at the 2^a positions of a tree that may be longer than the code.
  `ldRep C a`: the code repeated to the tree's length: each position has a symbol of its own.
  `Sz`: the link's sizes with three radii and four conditions that the definitions need.
  `Sz.memb`, `Sz.fam`, `Sz.seeds`: a folded row's oracle message (R rows under C, no mask row; a
    standard oracle message `StdM`), the family of two, one seed for both.
  `Sz.entryOf`, `Sz.putAt`: the coefficient k of a fold's polynomial stands at the entry t0 + k if
    k < r (the tail), else at the entry k - r.
  `Sz.rowNo`, `idxOf`, `cell`: a corner's number (lowest digit first); an entry's index in a table.
  `memb_plc_inj`, `seeds_fair`: entries have different corners; the seeds are fair.

Limits: the empty mask part of `Sz.memb` stands under `ldRep`; no row lies there. `putAt` speaks of
coefficients (powers of the point), not of what a configuration calls
message or randomness. Nothing on distances or laws of the codes: CdCodes.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupStdMsg
import Cb.Ent.CdPts

set_option autoImplicit false

namespace Cb.Ent

/-- Two numbers below 2^c with the same c lowest bits are equal. -/
theorem testBit_inj (c : Nat) {x y : Nat} (hx : x < 2 ^ c) (hy : y < 2 ^ c)
    (h : ∀ t : Fin c, x.testBit t.val = y.testBit t.val) : x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < c
  · exact h ⟨i, hi⟩
  · have hc : 2 ^ c ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hc),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hc)]

/-- The map from (row, place) to row + 2^aR * place is injective on rows below 2^aR. -/
theorem idx_inj (aR : Nat) {r r' p p' : Nat} (hr : r < 2 ^ aR) (hr' : r' < 2 ^ aR)
    (h : r + 2 ^ aR * p = r' + 2 ^ aR * p') : r = r' ∧ p = p' := by
  have hrow : r = r' :=
    calc r = (r + 2 ^ aR * p) % 2 ^ aR := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      _ = (r' + 2 ^ aR * p') % 2 ^ aR := by rw [h]
      _ = r' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
  subst hrow
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos aR) (Nat.add_left_cancel h)⟩

end Cb.Ent

namespace Cb.Ent
open Iop Prob Cb Cb.Ood

/-- The point of a position of a code with 2^a positions, in the field. -/
def ptOf (a : ℕ) (x : Fin (2 ^ a)) : GF := pt a x.val

/-- The generator matrix of a code: the coefficient number k of a word's polynomial (the tail's
entries first, then the message's) has the weight z^k at the position with the point z. -/
def genOf (C : RsPar) : Matrix (Fin (2 ^ C.a)) (Fin (C.r + C.l)) GE :=
  fun x k => algebraMap GF GE (ptOf C.a x ^ k.val)

/-- A position of a group with 2^a positions, as a position of the code C: modulo C's length. -/
def posIn (C : RsPar) {a : ℕ} (x : Fin (2 ^ a)) : Fin (2 ^ C.a) :=
  ⟨x.val % 2 ^ C.a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- One row under the code C, read at the 2^a positions of a group. -/
@[reducible] def ldOf (C : RsPar) (a : ℕ) : LdCode GE (Fin (2 ^ a)) where
  NP := Fin (2 ^ C.a)
  NS := fun _ => Unit
  J := Fin C.l
  Q := Fin C.r
  enc := fun m r p _ =>
    (∑ q, genOf C p (Fin.castAdd C.l q) * r q) + ∑ j, genOf C p (Fin.natAdd C.r j) * m j
  Aa := Unit
  T := fun f x _ => f (posIn C x) ()
  src := fun x => {posIn C x}

/-- One row under the code C, repeated to the 2^a positions of a group. A word has a symbol at each
position of the group. The code word's symbol at the position x is C's own at x modulo C's length.
A word that is no code word may have different symbols at two positions that are equal modulo C's
length. This is not the library's `LdCode.rep` (Cb/Ld/LdRel.lean), whose words stand on C's own
positions and are read at x modulo C's length. -/
@[reducible] def ldRep (C : RsPar) (a : ℕ) : LdCode GE (Fin (2 ^ a)) where
  NP := Fin (2 ^ a)
  NS := fun _ => Unit
  J := Fin C.l
  Q := Fin C.r
  enc := fun m r p _ =>
    (∑ q, genOf C (posIn C p) (Fin.castAdd C.l q) * r q) +
      ∑ j, genOf C (posIn C p) (Fin.natAdd C.r j) * m j
  Aa := Unit
  T := fun f x _ => f x ()
  src := fun x => {x}

/-- **The sizes**: the link's numbers, three radii (counts of positions), and what the definitions
below need of the sizes. e0, e1: the radii at which the two folds are tested. eU: the radius of a
folded row's oracle message. -/
structure Sz where
  P : LkPar
  e0 : ℕ
  e1 : ℕ
  eU : ℕ
  hR : 0 < P.R
  hl : 0 < P.C.l
  fitM : P.T.l ≤ P.R * P.C.l
  fitT : P.t0 + P.T.r ≤ P.R * P.C.l

namespace Sz
variable (S : Sz)

/-- the coefficients of a word of the stored tables' code: the tail's r, then the message's l -/
abbrev Co : Type := Fin (S.P.T.r + S.P.T.l)

/-- the number of a row: the vertex's digits, the lowest first -/
def rowNo {v : ℕ} (r : Fin v → Bool) : ℕ := ∑ t, if r t then 2 ^ t.val else 0

/-- the entries of a folded row's oracle message: (row, place), and no mask row -/
abbrev MJ : Type := (Fin S.P.R × Fin S.P.C.l) ⊕ (Empty × Fin S.P.Z.l)

/-- the pad's place: the last place of the last row -/
def padJ : S.MJ :=
  .inl (⟨S.P.R - 1, Nat.sub_lt S.hR Nat.one_pos⟩, ⟨S.P.C.l - 1, Nat.sub_lt S.hl Nat.one_pos⟩)

/-- the index of an entry in the member's table -/
def idxJ : S.MJ → ℕ
  | .inl x => x.1.val + 2 ^ S.P.aR * x.2.val
  | .inr x => x.1.elim

/-- **A folded row's oracle message.** -/
@[reducible] noncomputable def memb : StdM GE (Fin (2 ^ S.P.C.a)) where
  Cm := ((ldOf S.P.C S.P.C.a).il (Fin S.P.R)).pair ((ldRep S.P.Z S.P.C.a).il Empty)
  Dt := {j : S.MJ // j ≠ S.padJ}
  place := (splitAt S.padJ).symm
  μ := Fin (S.P.aR + S.P.aP)
  plc := fun j t => (S.idxJ j.1).testBit t.val
  B := GEˣ
  b := Units.val
  e := S.eU

/-- **The family that is sent in one message**: the first table's folded row (false), the copy's
(true). -/
@[reducible] noncomputable def fam : Sig GE := { O := Bool, om := fun _ => S.memb.om }

/-- the entry of a folded row at which a coefficient of the fold's polynomial stands -/
def entryOf (k : S.Co) : ℕ := if k.val < S.P.T.r then S.P.t0 + k.val else k.val - S.P.T.r

/-- That entry lies in the oracle message. -/
theorem entryOf_lt (k : S.Co) : S.entryOf k < S.P.C.l * S.P.R := by
  have h1 := S.fitM
  have h2 := S.fitT
  have h3 := k.isLt
  rw [Nat.mul_comm]
  unfold entryOf
  split <;> omega

/-- where a coefficient of the fold's polynomial stands in the oracle message -/
def putAt (k : S.Co) : S.MJ :=
  .inl (⟨S.entryOf k / S.P.C.l, Nat.div_lt_of_lt_mul (S.entryOf_lt k)⟩,
    ⟨S.entryOf k % S.P.C.l, Nat.mod_lt _ S.hl⟩)

/-- **The seeds**: one point and one factor for both members. -/
@[reducible] noncomputable def seeds : S.fam.Seeds where
  D := (Fin (S.P.aR + S.P.aP) → GE) × GEˣ
  sd := fun _ s => s
  mult := fun _ => 1

end Sz
end Cb.Ent

namespace Cb.Ent

/-- With one more digit: the number of the k lowest digits, and 2^k more if the top digit is set. -/
theorem rowNo_succ {k : ℕ} (b : Fin (k + 1) → Bool) :
    Sz.rowNo b = Sz.rowNo (fun t : Fin k => b t.castSucc) +
      (if b (Fin.last k) = true then 2 ^ k else 0) := by
  unfold Sz.rowNo
  rw [Fin.sum_univ_castSucc]
  rfl

/-- The number of a vertex with k digits is below 2^k. -/
theorem rowNo_lt {k : ℕ} (b : Fin k → Bool) : Sz.rowNo b < 2 ^ k := by
  induction k with
  | zero =>
    unfold Sz.rowNo
    rw [Fin.sum_univ_zero]
    exact Nat.two_pow_pos 0
  | succ k ih =>
    have h1 : Sz.rowNo (fun t : Fin k => b t.castSucc) < 2 ^ k := ih _
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, Nat.mul_two]
    rw [rowNo_succ, h2]
    by_cases hb : b (Fin.last k) = true
    · rw [if_pos hb]
      omega
    · rw [if_neg hb]
      omega

/-- The bits of the number of a vertex are the vertex's digits. -/
theorem testBit_rowNo {k : ℕ} (b : Fin k → Bool) (t : Fin k) :
    (Sz.rowNo b).testBit t.val = b t := by
  induction k with
  | zero => exact t.elim0
  | succ k ih =>
    have h1 : Sz.rowNo (fun s : Fin k => b s.castSucc) < 2 ^ k := rowNo_lt _
    rw [rowNo_succ]
    by_cases hb : b (Fin.last k) = true
    · rw [if_pos hb, Nat.add_comm]
      induction t using Fin.lastCases with
      | last =>
        show (2 ^ k + Sz.rowNo (fun s : Fin k => b s.castSucc)).testBit k = b (Fin.last k)
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h1, hb, Bool.not_false]
      | cast s =>
        show (2 ^ k + Sz.rowNo (fun s : Fin k => b s.castSucc)).testBit s.val = b s.castSucc
        rw [Nat.testBit_two_pow_add_gt s.isLt]
        exact ih _ s
    · rw [if_neg hb, Nat.add_zero]
      induction t using Fin.lastCases with
      | last =>
        show (Sz.rowNo (fun s : Fin k => b s.castSucc)).testBit k = b (Fin.last k)
        rw [Nat.testBit_lt_two_pow h1, eq_false_of_ne_true hb]
      | cast s => exact ih _ s

/-- Different vertices have different numbers. -/
theorem rowNo_inj {k : ℕ} : Function.Injective (Sz.rowNo (v := k)) := by
  intro b b' h
  funext t
  rw [← testBit_rowNo b t, h, testBit_rowNo]

/-- The vertex of the k lowest bits of i has the number i modulo 2^k. -/
theorem rowNo_testBit (k i : ℕ) : Sz.rowNo (fun t : Fin k => i.testBit t.val) = i % 2 ^ k := by
  refine testBit_inj k (rowNo_lt _) (Nat.mod_lt _ (Nat.two_pow_pos k)) fun t => ?_
  rw [testBit_rowNo, Nat.testBit_mod_two_pow, decide_eq_true t.isLt, Bool.true_and]

/-- The entry with the index i of a table of 2^k rows and l places. -/
def cell (k l i : ℕ) (h : i < 2 ^ k * l) : (Fin k → Bool) × Fin l :=
  (fun t => i.testBit t.val, ⟨i / 2 ^ k, Nat.div_lt_of_lt_mul h⟩)

/-- The index of an entry. -/
def idxOf {k l : ℕ} (x : (Fin k → Bool) × Fin l) : ℕ := Sz.rowNo x.1 + 2 ^ k * x.2.val

/-- The index of an entry is below the number of entries. -/
theorem idxOf_lt {k l : ℕ} (x : (Fin k → Bool) × Fin l) : idxOf x < 2 ^ k * l := by
  have h1 : Sz.rowNo x.1 < 2 ^ k := rowNo_lt x.1
  have h2 : 2 ^ k * (x.2.val + 1) ≤ 2 ^ k * l := Nat.mul_le_mul_left _ x.2.isLt
  rw [Nat.mul_add_one] at h2
  unfold idxOf
  omega

/-- The entry with the index i has the index i. -/
theorem idxOf_cell (k l i : ℕ) (h : i < 2 ^ k * l) : idxOf (cell k l i h) = i := by
  show Sz.rowNo (fun t : Fin k => i.testBit t.val) + 2 ^ k * (i / 2 ^ k) = i
  rw [rowNo_testBit]
  exact Nat.mod_add_div i (2 ^ k)

/-- Different entries have different indices. -/
theorem idxOf_inj {k l : ℕ} : Function.Injective (idxOf (k := k) (l := l)) := by
  intro x y h
  have h1 : Sz.rowNo x.1 = Sz.rowNo y.1 ∧ x.2.val = y.2.val :=
    idx_inj k (rowNo_lt x.1) (rowNo_lt y.1) h
  exact Prod.ext (rowNo_inj h1.1) (Fin.ext h1.2)

end Cb.Ent

namespace Cb.Ent

/-- The index of an entry is below the number of vertices of the cube. -/
theorem idxJ_lt (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) (hl : S.P.C.l ≤ 2 ^ S.P.aP) (j : S.MJ) :
    S.idxJ j < 2 ^ (S.P.aR + S.P.aP) := by
  rcases j with x | x
  · have h1 : x.1.val < 2 ^ S.P.aR := lt_of_lt_of_le x.1.isLt hR
    have h2 : x.2.val + 1 ≤ 2 ^ S.P.aP := le_trans x.2.isLt hl
    calc x.1.val + 2 ^ S.P.aR * x.2.val
        < 2 ^ S.P.aR + 2 ^ S.P.aR * x.2.val := Nat.add_lt_add_right h1 _
      _ = 2 ^ S.P.aR * (x.2.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ S.P.aR * 2 ^ S.P.aP := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (S.P.aR + S.P.aP) := (Nat.pow_add 2 _ _).symm
  · exact x.1.elim

/-- Different entries have different indices. -/
theorem idxJ_inj (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) : Function.Injective S.idxJ := by
  intro j j' h
  rcases j with x | x
  · rcases j' with y | y
    · have hxy : x.1.val = y.1.val ∧ x.2.val = y.2.val :=
        idx_inj S.P.aR (lt_of_lt_of_le x.1.isLt hR) (lt_of_lt_of_le y.1.isLt hR) h
      exact congrArg Sum.inl (Prod.ext (Fin.ext hxy.1) (Fin.ext hxy.2))
    · exact y.1.elim
  · exact x.1.elim

/-- The corners of a folded row's oracle message, the pad left out, are different. -/
theorem memb_plc_inj (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) (hl : S.P.C.l ≤ 2 ^ S.P.aP) :
    Function.Injective S.memb.plc := by
  intro (j : {j : S.MJ // j ≠ S.padJ}) (j' : {j : S.MJ // j ≠ S.padJ}) h
  have hbit : ∀ t : Fin (S.P.aR + S.P.aP),
      (S.idxJ j.1).testBit t.val = (S.idxJ j'.1).testBit t.val := fun t => congrFun h t
  have hidx : S.idxJ j.1 = S.idxJ j'.1 :=
    testBit_inj _ (idxJ_lt S hR hl j.1) (idxJ_lt S hR hl j'.1) hbit
  exact Subtype.ext (idxJ_inj S hR hidx)

end Cb.Ent

namespace Cb.Ent
open Iop Prob Cb

/-- Each member's seed is hit by as many joint seeds as any other: here by one. -/
theorem seeds_fair (S : Sz) : S.seeds.Fair := fun _ ρ => le_of_eq (cnt_eq_const ρ)

end Cb.Ent
