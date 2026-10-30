-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevB2.lean: which variable a round of a level binds, and which point a level hands
on:
in the letters, of every tree with orders.

  `b2_binds`    level l's list of variables, in the order of the rounds: place j is the equality
                weight
                at coordinate sg l j of the level's point.
  `b2_point`    coordinate t of the point at which level l's sumcheck ends is the challenge of the
                round that bound t (round (sg l)⁻¹ t).
  `b2_line`     the next level's point is that point with the line's draw as one more, last
                coordinate: variable g + l.
A variable is a bit of a number:
  `numLE_testBit`  bit t of the number of a Boolean point b is b t.
  `read_corner`, `read_corner_ext`  at every Boolean point b the extension of a table given by
                numbers
                reads entry number numLE b: in the tree's listing of a point, and for `Blocks.ext`
                at
                the point listed top bit first, as a masked claim lists it.
  `key_leaf`    the leaves of a key side at a Boolean point b: lam − key number (numLE b).
  `key_binds_last`, `key_binds_other`  with oK := ordKey first v: at the last level round j binds
                entry
                j of `beginList first l`, at every other level entry j of the list from the highest
                variable down.
Conditions: `BeginOK first (0 + l)` at the last level.
Not claimed: that these lists are the terms of the verifier in OnBytes/Iop/Lkp.lean.
`ppGet`, `hFnOf_get`: PtGet.lean. `pVars_eqsB`: E3Bit.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevSides
import Cb.Pv.KeyLookup.LevOrd
import Cb.Pv.KeyLookup.PtGet
import Cb.Pv.Lookup.Blocks.E3Bit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Iop IOR Hiop Prob

section
variable {E : Type} [Field E] [Fintype E]

theorem b2_binds (D : TreeP E) (l : ℕ) (s : (D.lv l).T.St) :
    (D.lv l).T.vars s =
      List.ofFn fun j : Fin (D.g + l) => (pfCube E 2).var (pdEq E 2 ((D.lv l).pnt s (D.sg l j))) :=
          by
  cases l with
  | zero => exact pVars_eqsB 2 (D.g + 0) (D.z0 s)
  | succ l => exact pVars_eqsB 2 (D.g + l + 1) ((D.cube l).ptS s)

/-- Coordinate sg l j of the point at which level l's sumcheck ends is the challenge of round j. -/
theorem b2_at (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (j : Fin (D.g + l)) :
    (D.lv l).gam o (D.sg l j) = ppGet (D.lv l).T.par.fmt o.pt j := by
  cases l with
  | zero =>
    have e : (D.lv 0).gam o (D.sg 0 j) =
        hFnOf (pfCube E 2) (D.g + 0) (pdEqs E 2 (D.g + 0) (D.z0 o.st))
          (D.T0.ini o.st (D.T0.par.hp o.st o.pt)) ((D.sg 0).symm (D.sg 0 j)) := rfl
    rw [e, Equiv.symm_apply_apply]
    exact hFnOf_get (pfCube E 2) (pDummy E 2) (pDummyD E 2) (D.g + 0) _ o.pt j
  | succ l =>
    have e : (D.lv (l + 1)).gam o (D.sg (l + 1) j) =
        hFnOf (pfCube E 2) (D.g + l + 1) (pdEqs E 2 (D.g + l + 1) ((D.cube l).ptS o.st))
          ((D.cube l).next.ini o.st ((D.cube l).next.par.hp o.st o.pt))
          ((D.sg (l + 1)).symm (D.sg (l + 1) j)) := rfl
    rw [e, Equiv.symm_apply_apply]
    exact hFnOf_get (pfCube E 2) (pDummy E 2) (pDummyD E 2) (D.g + l + 1) _ o.pt j

theorem b2_point (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (t : Fin (D.g + l)) :
    (D.lv l).gam o t = ppGet (D.lv l).T.par.fmt o.pt ((D.sg l).symm t) := by
  have h := b2_at D l o ((D.sg l).symm t)
  rwa [Equiv.apply_symm_apply] at h

theorem b2_line (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (ρ : E) :
    (D.lv (l + 1)).pnt (o, ρ) = (Fin.snoc ((D.lv l).gam o) ρ : Fin (D.g + l + 1) → E) :=
  rfl

end

/-- Bit t of the number of a Boolean point is its coordinate t. -/
theorem numLE_testBit : ∀ (k : ℕ) (b : Fin k → Bool) (t : Fin k), (numLE b).testBit t = b t
  | 0, _, t => t.elim0
  | k + 1, b, t => by
    have hs : b = (Fin.snoc (fun i : Fin k => b i.castSucc) (b (Fin.last k)) : Fin (k + 1) →
        Bool) :=
      (Fin.snoc_init_self b).symm
    have hn : numLE b = numLE (fun i : Fin k => b i.castSucc) + if b (Fin.last k) then 2 ^ k else
        0 := by
      conv_lhs => rw [hs]
      exact ldLkpNum_snoc k _ _
    have hlt : numLE (fun i : Fin k => b i.castSucc) < 2 ^ k := ldLkpNum_lt k _
    rw [hn]
    refine Fin.lastCases ?_ (fun i => ?_) t
    · show (numLE (fun i : Fin k => b i.castSucc) + if b (Fin.last k) then 2 ^ k else 0).testBit k =
        _
      cases hb : b (Fin.last k)
      · simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [if_true]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · show (numLE (fun i : Fin k => b i.castSucc) + if b (Fin.last k) then 2 ^ k else 0).testBit
        i.1 = _
      have ih := numLE_testBit k (fun i : Fin k => b i.castSucc) i
      cases hb : b (Fin.last k)
      · simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        exact ih
      · simp only [if_true]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt i.2]
        exact ih

section
variable {E : Type} [Field E]

/-- At a Boolean point the extension of a table given by numbers reads the entry whose number has
the point's coordinates as its bits. -/
theorem read_corner (k : ℕ) (a : ℕ → E) (b : Fin k → Bool) :
    Alg.mle (fun x : Fin k → Bool => a (numLE x)) (Alg.corner b) = a (numLE b) :=
  Alg.mle_corner _ b

/-- The same in the listing of a masked claim's point: top bit first. -/
theorem read_corner_ext (k : ℕ) (a : ℕ → E) (b : Fin k → Bool) :
    Blocks.ext k a (Blocks.nat fun i : Fin k => (Alg.corner b : Fin k → E) i.rev) = a (numLE b) :=
  (ldLkpNum_ext E k a (Alg.corner b)).symm.trans (read_corner k a b)

end

section
variable {E : Type} [Field E] [Fintype E] {B : KeyBase E}

/-- The leaves of a key side, at a Boolean point. -/
theorem key_leaf (p : KeyPart B) (X : Type) (pr : X → B.X0) (x : X) (m : B.J → E)
    (b : Fin (0 + (p.v' + 1)) → Bool) :
    (p.tree X pr).U x m (p.v' + 1) b = B.lam (pr x) - p.key (B.st (pr x)) m (numLE b) :=
  ldLkpNum_topK E (p.v' + 1) (p.key (B.st (pr x)) m) (B.lam (pr x)) b

/-- With the orders of LevOrd.lean: the last level. -/
theorem key_binds_last (p : KeyPart B) (first : List ℕ) (h : p.oK = ordKey first (p.v' + 1)) (X :
    Type)
    (pr : X → B.X0) (hb : BeginOK first (0 + p.v')) (j : Fin (0 + p.v')) :
    (((p.tree X pr).sg p.v' j : Fin (0 + p.v')) : ℕ) = (beginList first (0 + p.v')).getD j.1 0 := by
  rw [p.side_sg X pr p.v', h, ordKey_last first rfl]
  exact ordOf_val hb j

/-- .. and every other level. -/
theorem key_binds_other (p : KeyPart B) (first : List ℕ) (h : p.oK = ordKey first (p.v' + 1)) (X :
    Type)
    (pr : X → B.X0) (l : ℕ) (hl : l ≠ p.v') (j : Fin (0 + l)) :
    (((p.tree X pr).sg l j : Fin (0 + l)) : ℕ) = ((List.range (0 + l)).reverse).getD j.1 0 := by
  rw [p.side_sg X pr l, h, ordKey_other first (fun e => hl (Nat.succ.inj e))]
  exact rev_val (0 + l) j

end
end Lk6

#print axioms Lk6.b2_binds
#print axioms Lk6.b2_point
#print axioms Lk6.b2_line
#print axioms Lk6.numLE_testBit
#print axioms Lk6.read_corner_ext
#print axioms Lk6.key_leaf
#print axioms Lk6.key_binds_last
#print axioms Lk6.key_binds_other
