-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyNumLink.lean: the error counts of the link's first rounds are at most 2^-128 as
shares of their rounds' challenge values, from four comparisons of natural numbers. The round that
draws positions may have test bits.

The written link is the link between two stored tables as an interactive protocol in the format's
types (OnBytes/Slice/README.md has the vocabulary). OnBytes/Slice/NoWorkRatesLink.lean bounds the
counts of the round in front and of the link's five rounds at one example's numbers. Here the
numbers are the fields of a record, `LinkNum`, and the record of sizes and the rounds are variables.
All lists have at most one member.

Main definitions.
 `LinkNum`     the numbers: fold variables, bits of a position, tested positions of the two folds,
               elements of the fifth round, the two tests' radii, three numbers of hash blocks.
 `LinkNumSizes`   a record of sizes has these numbers. `LinkRounds`: three written rounds have them.
 `ElemNum`, `SideNum`, `LinkOK`   the comparisons.
Main theorems.
 `link_entry1`, `link_entry4`, `link_entry5`   one round each. The shares of bad typed values are
     (v (e1 + 1) + 2 v) / q, ((2^a - e1 - 1) / 2^a)^nuj and aPhi / q, for q the field's size.
 `link_core_num`   the clause on error counts (`Err.Below`, Iop/InteractiveOracleProof.lean) for the written link at
     2^-128, from the same clause for the rounds after the fifth.

The fourth round is asked to have W test bits (`LinkRounds`): W of its 128 bits are then work. A
bound speaks of one round: it is no bound on the chance of a false proof.

What this file does not claim: any number; that the radii, the count of exceptional fold points and
the bounds on the lists are right for the tables' code; that a description has such sizes or
rounds.

-/
import OnBytes.Slice.ManyNum
import OnBytes.Slice.NoWorkRatesLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch Run Run.PQ Cb Cb.Ood Blocks
open scoped ENNReal

/-- The numbers of the link's five rounds. -/
structure LinkNum where
  /-- The number of fold variables. -/
  v : ℕ
  /-- The tables' code has 2^a positions. -/
  a : ℕ
  /-- The number of positions at which the first fold is tested. -/
  nu0 : ℕ
  /-- The number of positions at which the second fold is tested. -/
  nuj : ℕ
  /-- The number of elements that the fifth round draws. -/
  aPhi : ℕ
  /-- The radius of the first fold's test. -/
  e0 : ℕ
  /-- The radius of the second fold's test. -/
  e1 : ℕ
  /-- The first round's number of hash blocks. -/
  B1 : ℕ
  /-- The fourth round's number of hash blocks. -/
  B4 : ℕ
  /-- The fifth round's number of hash blocks. -/
  B5 : ℕ

/-- The record of sizes S has the numbers x. -/
structure LinkNumSizes (S : Sz) (x : LinkNum) : Prop where
  /-- The fold variables. -/
  v : S.P.v = x.v
  /-- The positions of the tables' code. -/
  a : S.P.T.a = x.a
  /-- The first fold's tested positions. -/
  nu0 : S.P.nu0 = x.nu0
  /-- The second fold's tested positions. -/
  nuj : S.P.nuj = x.nuj
  /-- The fifth round's elements. -/
  aPhi : S.P.aPhi = x.aPhi
  /-- The radius of the first fold's test. -/
  e0 : S.e0 = x.e0
  /-- The radius of the second fold's test. -/
  e1 : S.e1 = x.e1

/-- The link's first, fourth and fifth round have the numbers x: the first draws the fold's point,
the fourth the tested positions, with W test bits, the fifth its elements. -/
structure LinkRounds (W : ℕ) (d1 d4 d5 : PQ.RD) (x : LinkNum) : Prop where
  /-- The first round. -/
  r1 : WkRound d1 (List.replicate x.v Fmt.Draw.elem ++ [.trits 0]) x.B1 0
  /-- The fourth round. -/
  r4 : WkRound d4 (List.replicate (x.nu0 + x.nuj) (Fmt.Draw.pos x.a) ++ [.trits 0]) x.B4 W
  /-- The fifth round. -/
  r5 : WkRound d5 (List.replicate x.aPhi Fmt.Draw.elem ++ [.trits 0]) x.B5 0

/-- The comparison for a share n / q with B hash blocks and no test bit, at the exponent k, with
2^191 in the place of the field's size q. -/
def ElemNum (k B n : ℕ) : Prop :=
  (2 ^ 128 + 1) ^ B * n * 2 ^ k ≤ (2 ^ 128) ^ B * 2 ^ 191 * 2 ^ 0

/-- Of the fourth round's two tests, at the radii e0 and e1 and at nu0 and nuj positions of a bits,
the second has the larger count. -/
def SideNum (a nu0 nuj e0 e1 : ℕ) : Prop :=
  (2 ^ a - e0 - 1) ^ nu0 * (2 ^ a) ^ nuj ≤ (2 ^ a) ^ nu0 * (2 ^ a - e1 - 1) ^ nuj

/-- The comparisons at the numbers x: there is a fold variable; the first and the fifth round's
shares; of the fourth round's two tests the second has the larger count; that count's share. -/
structure LinkOK (W k : ℕ) (x : LinkNum) : Prop where
  /-- There is a fold variable. -/
  pos : 0 < x.v
  /-- The first round. -/
  gam : ElemNum k x.B1 (x.v * (x.e1 + 1) + 2 * x.v)
  /-- Of the two tests the second has the larger count. -/
  side : SideNum x.a x.nu0 x.nuj x.e0 x.e1
  /-- The fourth round. -/
  loc : LastNum W k x.a x.nuj x.B4 x.e1
  /-- The fifth round. -/
  phi : ElemNum k x.B5 x.aPhi

/-- `LinkOK` at numbers that are written out. The numbers are variables here, so that no step
compares two spellings of a large power. -/
theorem LinkOK.of (W k v a nu0 nuj aPhi e0 e1 B1 B4 B5 : ℕ) (pos : 0 < v)
    (gam : ElemNum k B1 (v * (e1 + 1) + 2 * v)) (side : SideNum a nu0 nuj e0 e1)
    (loc : LastNum W k a nuj B4 e1) (phi : ElemNum k B5 aPhi) :
    LinkOK W k ⟨v, a, nu0, nuj, aPhi, e0, e1, B1, B4, B5⟩ :=
  ⟨pos, gam, side, loc, phi⟩

/-! ### Arithmetic, in variables -/

/-- `ElemNum` for every size of the field from 2^191 on. -/
theorem ElemNum.at {k B n : ℕ} (h : ElemNum k B n) (q : ℕ) (hq : 2 ^ 191 ≤ q) :
    (2 ^ 128 + 1) ^ B * n * 2 ^ k ≤ (2 ^ 128) ^ B * q * 2 ^ 0 :=
  _root_.le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq))

/-- The first round's count: (v (r + 1) + 2 v) q^(v - 1) of q^v. -/
theorem gam_num_any (v r q : ℕ) (hv : 0 < v) :
    (0 + (v * (r + 1) * q ^ (v - 1) + 1 * (v * q ^ (v - 1))) + v * q ^ (v - 1)) * q ≤
      (v * (r + 1) + 2 * v) * q ^ v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  rewrite [Nat.add_sub_cancel]
  exact le_of_eq (by ring)

/-- The fifth round's count: l q^(l - 1) of q^l. -/
theorem phi_num_any (l q : ℕ) : l * q ^ (l - 1) * q ≤ l * q ^ l := by
  cases l with
  | zero => exact le_of_eq (by ring)
  | succ w =>
    rewrite [Nat.add_sub_cancel]
    exact le_of_eq (by ring)

/-- The fourth round's count, where the second test has the larger count: X / n^j of the values. -/
theorem loc_num_any (A n X i j : ℕ) (h : A ≤ n ^ i * X) :
    max A (n ^ i * X) * n ^ j ≤ X * n ^ (i + j) :=
  max_mul_le _ _ _ _ h (le_of_eq (by ring))

/-! ### The rounds -/

/-- The first round: the fold's point. The second argument b of the count enters as a variable with
an equation; vv is the number of fold variables and r the radius in the count of exceptional fold
points. -/
theorem link_entry1 (S : Sz) (x : LinkNum) (hS : LinkNumSizes S x) (k : ℕ) (hv : 0 < x.v)
    (hn : ElemNum k x.B1 (x.v * (x.e1 + 1) + 2 * x.v)) (d : PQ.RD)
    (hd : WkRound d (List.replicate x.v Fmt.Draw.elem ++ [.trits 0]) x.B1 0) (vv r b : ℕ)
    (hvv : vv = x.v) (hr : r = x.e1)
    (hb : b = vv * (r + 1) * Fintype.card GE ^ (vv - 1) +
      1 * (S.P.v * Fintype.card GE ^ (S.P.v - 1))) :
    RoundBelow (S.lk.errGam 0 b) d ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  refine entry_pow d hd.log _ (x.v * (x.e1 + 1) + 2 * x.v) (Fintype.card GE) x.B1 0 k hd.blocks
    hd.work card_GE_pos ?_ (hn.at _ card_GE_big)
  rewrite [hd.draws, nVals_elems, hb, errGam_eq]
  generalize Fintype.card GE = q
  rewrite [hS.v, hvv, hr]
  exact gam_num_any x.v x.e1 q hv

/-- The fourth round: the positions at which the two folds are tested. The round is asked to have W
test bits (`WkRound`): W of the k bits are work. -/
theorem link_entry4 (S : Sz) (x : LinkNum) (hS : LinkNumSizes S x) (W k : ℕ)
    (hside : SideNum x.a x.nu0 x.nuj x.e0 x.e1)
    (hn : LastNum W k x.a x.nuj x.B4 x.e1) (d : PQ.RD)
    (hd : WkRound d (List.replicate (x.nu0 + x.nuj) (Fmt.Draw.pos x.a) ++ [.trits 0]) x.B4 W) :
    RoundBelow S.lk.errLoc d ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  refine entry_pow d hd.log _ ((2 ^ x.a - x.e1 - 1) ^ x.nuj) ((2 ^ x.a) ^ x.nuj) x.B4 W k
    hd.blocks hd.work (Nat.pow_pos (Nat.two_pow_pos x.a)) ?_ hn
  rewrite [hd.draws, nVals_rep, nVals_end, mul_one, errLoc_eq, hS.a, hS.e0, hS.e1, hS.nu0, hS.nuj]
  exact loc_num_any _ _ _ _ _ hside

/-- The fifth round: the point at which the compared entries are joined. -/
theorem link_entry5 (S : Sz) (x : LinkNum) (hS : LinkNumSizes S x) (k : ℕ)
    (hn : ElemNum k x.B5 x.aPhi) (d : PQ.RD)
    (hd : WkRound d (List.replicate x.aPhi Fmt.Draw.elem ++ [.trits 0]) x.B5 0) :
    RoundBelow S.lk.errPhi d ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  refine entry_pow d hd.log _ x.aPhi (Fintype.card GE) x.B5 0 k hd.blocks hd.work card_GE_pos ?_
    (hn.at _ card_GE_big)
  rewrite [hd.draws, nVals_elems, errPhi_eq]
  generalize Fintype.card GE = q
  rewrite [hS.aPhi]
  exact phi_num_any x.aPhi q

/-- The clause on error counts of the written link at 2^-128, for sizes and rounds that have the
numbers x, at which the comparisons hold, from the same clause for the rounds after the fifth.
Nothing is asked of the second and the third round: their counts are 0. The fourth round is asked to
have W test bits (`LinkRounds`): W of its 128 bits are work. -/
theorem link_core_num (S : Sz) (x : LinkNum) (W : ℕ) (hS : LinkNumSizes S x) (hx : LinkOK W 128 x)
    (d1 d2 d3 d4 d5 : PQ.RD) (tl : List PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool)
    (hd : LinkRounds W d1 d4 d5 x) (vv r b : ℕ) (hvv : vv = x.v) (hr : r = x.e1)
    (hb : b = vv * (r + 1) * Fintype.card GE ^ (vv - 1) +
      1 * (S.P.v * Fintype.card GE ^ (S.P.v - 1)))
    (εt : Err (PQ.uL (ckP .two) tl)) (ht : Err.Below εt ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    Err.Below (s := (written S d1 d2 d3 d4 d5 tl xs dec).shape)
      (0, coreErr S d1 d2 d3 d4 d5 0 b (fun _ => 1) εt) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  link_below _ _ _ _ _ _ _ _ _ _ _ _ _ _ (core_below _ _ _ _ _ _ _ _ _ _ _
    (link_entry1 S x hS 128 hx.pos hx.gam d1 hd.r1 vv r b hvv hr hb)
    ((le_of_eq (nw_entry2 S d2)).trans (_root_.zero_le _))
    (link_entry4 S x hS W 128 hx.side hx.loc d4 hd.r4) (link_entry5 S x hS 128 hx.phi d5 hd.r5) ht)

end OnBytes.Slice
