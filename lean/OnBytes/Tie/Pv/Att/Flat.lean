-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/Flat.lean: the summands of attention's two kinds of sumcheck, as the port
computes them at the point of the challenges, written as functions on plain data and read in a
field.

The port computes a sumcheck's summand on the scalars that were shown for the end values: sc3Shown
(OnBytes/Model/AttentionSums.lean) for a sumcheck of products, keyTerm and keyAtIndexIn
(OnBytes/Model/AttentionDivide.lean) for the sumcheck by degrees. These routines read the shown
scalars off the state. Here the same arithmetic is written without a state: sh j stands for what was
shown under the slot of end value number j. For every reading of the port's elements in a field
(OnBytes/Model/HideLaws.lean) the result for the sumcheck by degrees is the summand of
Cb/Pv/Att/Scd.lean, and the result for a sumcheck of products is the sum of the readings of W[b],
A_b and B_b multiplied; that this is the summand of Cb/Pv/Att/Sc3.lean, where the caller's weights
are the typed ones, is said in OnBytes/Tie/Pv/Att/Sc3Top.lean.

Main names:
  `weight_sum3`, `weight_nodes`, `weight_nodes_none`: the weight of a round of the form sum3 is
    Weight.plain 4; that of a round of the form nodes and degree d is Weight.plain (d + 1) for d
    from 1 to 64, and there is none for another d.
  `read_prod`, `read_sum`: a fold of products, or of sums, over List.range n, read.
  `eqPts_read`: eqPts, read, is the library's equality polynomial.
  `sc3Flat`, `sc3Flat_succ`, `sc3Flat_read`: the summand of a sumcheck of products.
  `keyTermFlat`, `keyFlat`, `keyFlat_read`: the summand of the sumcheck by degrees, read, is `scdS`.

Limits: arithmetic alone. That the port's routines return these values on a run is not said here.
-/
import Cb.Pv.Att.Sc3
import Cb.Pv.Att.Scd
import OnBytes.Model.HideLaws
import OnBytes.Model.Psc
import OnBytes.Model.AttentionShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Attention Cb.Pv.Att

/-! ## The weights of the rounds -/

theorem weight_sum3 (z : E) (d : Nat) :
    RoundForm.weight .sum3 z d = some (OnBytes.Psc.Weight.plain 4) := rfl

theorem weight_nodes (z : E) (d : Nat) (h1 : 1 ≤ d) (h2 : d ≤ 64) :
    RoundForm.weight .nodes z d = some (OnBytes.Psc.Weight.plain (d + 1)) := by
  simp [RoundForm.weight, RoundForm.degreeOK, RoundForm.equality, roundValues, h1, h2]

theorem weight_nodes_none (z : E) (d : Nat) (h : d = 0 ∨ 64 < d) :
    RoundForm.weight .nodes z d = none := by
  have h' : ¬ (1 ≤ d ∧ d ≤ 64) := by omega
  simp [RoundForm.weight, RoundForm.degreeOK, h']

/-! ## Folds, read -/

section
variable {K : Type} [Field K] (ρ : Reading K)

theorem read_prod (f : Nat → E) (a : E) : ∀ n : Nat,
    ρ.val ((List.range n).foldl (fun p v => mulE p (f v)) a) =
      ρ.val a * ∏ v : Fin n, ρ.val (f v.1)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.mul, read_prod f a n,
      Fin.prod_univ_castSucc, mul_assoc]
    rfl

theorem read_sum (f : Nat → E) (a : E) : ∀ n : Nat,
    ρ.val ((List.range n).foldl (fun s b => addE s (f b)) a) =
      ρ.val a + ∑ b : Fin n, ρ.val (f b.1)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.add, read_sum f a n,
      Fin.sum_univ_castSucc, add_assoc]
    rfl

theorem eqPair_read (x y : E) : ρ.val (eqPair x y) = Alg.eq1 (ρ.val x) (ρ.val y) := by
  simp [eqPair, Alg.eq1, ρ.add, ρ.mul, ρ.sub, ρ.one]

theorem eqPts_read (x y : Array E) (n : Nat) (h : x.size = n) :
    ρ.val (eqPts x y) =
      Alg.eqPt (fun a : Fin n => ρ.val (x.getD a.1 zeroE)) fun a => ρ.val (y.getD a.1 zeroE) := by
  subst h
  unfold eqPts Alg.eqPt
  rw [read_prod ρ (fun v => eqPair (x.getD v zeroE) (y.getD v zeroE)) oneE x.size, ρ.one, one_mul]
  exact Finset.prod_congr rfl fun v _ => eqPair_read ρ _ _

/-! ## The sumcheck of products -/

/-- sc3Shown on plain data: sh j is what was shown for end value number j. The arguments behind sh
are those of sc3Shown: how many pairs of maps are still to be added, the first of them, the sum so
far. -/
def sc3Flat (W : Array E) (sh : Nat → E) (n b : Nat) (s : E) : E :=
  (List.range' b n).foldl
    (fun s b => addE s (mulE (mulE (W.getD b zeroE) (sh (2 * b))) (sh (2 * b + 1)))) s

theorem sc3Flat_zero (W : Array E) (sh : Nat → E) (b : Nat) (s : E) : sc3Flat W sh 0 b s = s := rfl

/-- The step of sc3Shown. -/
theorem sc3Flat_succ (W : Array E) (sh : Nat → E) (n b : Nat) (s : E) :
    sc3Flat W sh (n + 1) b s =
      sc3Flat W sh n (b + 1)
        (addE s (mulE (mulE (W.getD b zeroE) (sh (2 * b))) (sh (2 * b + 1)))) := by
  unfold sc3Flat
  rw [List.range'_succ, List.foldl_cons]

theorem sc3Flat_read (W : Array E) (sh : Nat → E) (nb : Nat) :
    ρ.val (sc3Flat W sh nb 0 zeroE) = ∑ b : Fin nb,
      ρ.val (W.getD b.1 zeroE) * ρ.val (sh (2 * b.1)) * ρ.val (sh (2 * b.1 + 1)) := by
  unfold sc3Flat
  rw [← List.range_eq_range',
    read_sum ρ (fun b => mulE (mulE (W.getD b zeroE) (sh (2 * b))) (sh (2 * b + 1))) zeroE nb,
    ρ.zero, zero_add]
  exact Finset.sum_congr rfl fun b _ => by rw [ρ.mul, ρ.mul]

/-! ## The sumcheck by degrees -/

/-- keyTerm on plain data. -/
def keyTermFlat (lt Lam HA : Nat) (sh : Nat → E) (pj : Array E) (w : E) (b : Nat) : E :=
  (List.range lt).foldl
    (fun t k => mulE t (addE
      (mulE (sh (Lam + b * lt + k))
        (subE (addE (pj.getD (lt - 1 - k) zeroE) (pj.getD (lt - 1 - k) zeroE)) oneE))
      (subE oneE (pj.getD (lt - 1 - k) zeroE))))
    (mulE w (sh (b / HA)))

/-- The argument of scdRow in keyAtIndexIn, on plain data. -/
def keyFlat (lt Lam HA NP : Nat) (ri rg pj pg pi om4 : Array E) (sh : Nat → E) : E :=
  mulE (mulE (eqPts ri pi) (eqPts rg pg))
    ((List.range NP).foldl
      (fun s b => addE s (keyTermFlat lt Lam HA sh pj (om4.getD b zeroE) b)) zeroE)

/-- the number of an end value -/
def scdNum (s : ScdSize) : s.A → Nat
  | .inl l => l.1
  | .inr p => s.Lam + p.1.1 * s.lt + p.2.1

theorem keyFlat_read (s : ScdSize) (ri rg pj pg pi om4 : Array E) (sh : Nat → E)
    (hi : ri.size = s.lt) (hg : rg.size = s.lgk) (z : Fin s.k → K)
    (zj : ∀ a, z (s.jAt a) = ρ.val (pj.getD a.1 zeroE))
    (zg : ∀ a, z (s.gAt a) = ρ.val (pg.getD a.1 zeroE))
    (zi : ∀ a, z (s.iAt a) = ρ.val (pi.getD a.1 zeroE)) :
    ρ.val (keyFlat s.lt s.Lam s.HA s.pairs ri rg pj pg pi om4 sh) =
      scdS s (fun a => ρ.val (ri.getD a.1 zeroE)) (fun a => ρ.val (rg.getD a.1 zeroE))
        (fun b => ρ.val (om4.getD b.1 zeroE)) z fun a => ρ.val (sh (scdNum s a)) := by
  unfold keyFlat scdS
  rw [ρ.mul, ρ.mul, eqPts_read ρ ri pi s.lt hi, eqPts_read ρ rg pg s.lgk hg,
    read_sum ρ (fun b => keyTermFlat s.lt s.Lam s.HA sh pj (om4.getD b zeroE) b) zeroE s.pairs,
    ρ.zero, zero_add]
  simp only [zg, zi]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold keyTermFlat
  rw [read_prod ρ _ _ s.lt, ρ.mul]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  have e : s.lt - 1 - t.1 = t.rev.1 := by rw [Fin.val_rev]; omega
  rw [ρ.add, ρ.mul, ρ.sub, ρ.sub, ρ.add, ρ.one, zj, e]
  rfl

end

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.weight_nodes
#print axioms OnBytes.Tie.Pv.Att.eqPts_read
#print axioms OnBytes.Tie.Pv.Att.sc3Flat_read
#print axioms OnBytes.Tie.Pv.Att.keyFlat_read
