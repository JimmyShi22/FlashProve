-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwSet.lean.
At the small lookup `o65A` the orders of binding and the padding reach the builders of the assembled
lookup that (A) lists, and somewhere their values are not the defaults'.

Examples by rfl, statements and proofs.
 (A) At each builder (here: a definition that makes a block's record out of A:
     Cb/Pv/Lookup/Asm/AsmH.lean and the library's files beneath it), at `o65A`, by rfl: the orders
     reach I1, IK, IT, setV, the field sg of both trees, every level's cube, the tree of the planes'
     point, the closing's z, tAt, dg, and the bit test (sg, zc.sg); the padding reaches the head,
     the tie's factor, step 0's summand and the pin. The right sides `E3.o65K`, `o65T`, `o65E`,
     `o65B` are the values of OnBytes/Tie/Pv/Lookup/Order/E3O65.lean; they are the fields of `o65A`
     (`o65A_oK` and its like: rfl) and the fields of `OnBytes.Lkp.o65` under `E3.ordKeyW` and
     `E3.ordDefault` (`tie_E3K` and its like in OnBytes/Tie/Pv/Lookup/Port/TwTies.lean: rfl).
 (B) Lemmas, in five groups. `o65_set_two_ne_one`, `o65_set_last_ne_one`, `o65_set_last_ne_rev`: the
     order at key level 2 is not the identity; at the last key level it is neither the identity nor
     the reversal. `set_table_ne_one`, `set_leaves_ne_one`: the table's level 0 and the closing: not
     the identity. Of the bit test's order no such lemma is here. `fac_eval`, `fac_ne_one`,
     `o65_padPoly_ne_one`: the padding's factor as a polynomial in λ is X − 1, which is not 1.
     `tie_steps`, `tie_shown`: seven steps; 3, 2, .., 2 shown values. `leaves_deg_round`,
     `leaves_deg_var`: degree 2 in the row's variable, 1 in a plane's.
Limits: all at one value, but for `padPoly_eval`, `fac_eval_gen`, tieF_* and `leaves_deg_var_gen`.
The orders stand in the coordinates of the tree's point. That coordinate c of it stands for bit c of
an entry's number: `o65_sigma_keys` (OnBytes/Tie/Pv/Lookup/Value/TwPort.lean), `sigma_keys_by`
(OnBytes/Tie/Pv/Lookup/Port/TwSigma.lean). Neither names a function of OnBytes/Iop/Lkp.lean: that
these coordinates are its variables is stated by neither. That the chain `A.chnK`
(Cb/Pv/Lookup/Know/AsmK.lean), on which `A.baseK` (Cb/Pv/Lookup/Know/AsmKV.lean) stands, runs
through these same builders (A.H, A.R.D, A.IK with setV and DK, A.D, A.En.par, A.Bt.zc) is held by
reading its text; neither file is imported here. Three records of the library keep a default in
place (`LkInst.oK` and `oT`, `TreeP.sg`, the cube's sg): there these examples by rfl are what
guards.

-/
import OnBytes.Tie.Pv.Lookup.Port.TwTies

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Finset
open TwNums (Sizes o65S)

/-! ### (A) every builder, at the small lookup -/
-- the three instances
example : o65A.I1.oK = E3.o65K ∧ o65A.I1.oT = E3.o65T ∧ o65A.IK.oK = E3.o65K ∧ o65A.IK.oT = E3.o65T
    ∧ o65A.IT.oK = E3.o65K ∧ o65A.IT.oT = E3.o65T :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
-- setV keeps them
example : (o65A.IK.setV (o65A.v' + 1)).oK = E3.o65K := rfl
example : (o65A.IK.setV (o65A.v' + 1)).oT = E3.o65T := rfl
-- the trees
example : ((o65A.IK.setV (o65A.v' + 1)).DK).sg = E3.o65K := rfl
example : o65A.D.sg = E3.o65T := rfl
example : (o65A.I1.DT2 (o65A.n + 1)).sg = E3.o65T := rfl
example : o65A.R.D.sg = E3.o65T := rfl
-- each level's cube (the line's block)
example (l : ℕ) : (o65A.D.cube l).sg = E3.o65T (l + 1) := rfl
example (l : ℕ) : ((o65A.IK.setV (o65A.v' + 1)).DK.cube l).sg = E3.o65K (l + 1) := rfl
-- the closing
example : o65A.En.X = (o65A.D.lv o65A.d).T.St := rfl
example (s : o65A.En.X) (i : Fin (o65A.w + o65A.d)) : o65A.En.z s i = (o65A.D.lv o65A.d).pnt s
    (E3.o65E i) := rfl
example (b : Fin (o65A.w + o65A.d) → Bool) : o65A.En.tAt b = o65A.IT.tAt fun v => b (E3.o65E.symm v)
    := rfl
example : o65A.En.dg = dgEnd 3 1 E3.o65E := rfl
-- the bit test
example : o65A.Bt.sg = E3.o65B := rfl
example : o65A.Bt.zc.sg = E3.o65B := rfl
-- the padding: the head, the tie's factor, step 0's summand, the pin
example : o65A.H.pads = [(1, 1)] := rfl
example : o65A.H.tie.a = o65A.H.fac := rfl
example (st : (o65A.H.tie.lv 0).T.St) (pt) (v : Option Bool → K) :
    (o65A.H.tie.lv 0).T.S0 st pt v = v none - o65A.H.fac st * (v (some false) ^ 2 * v (some true))
        := rfl
example : o65A.numRow = o65A.H.numRowF := rfl
theorem pin_target : o65A.numRow.tg = ((o65S.nKeys : ℕ) : K) := rfl
-- the places: the head's, the trees', the closing's are the record's (the bit test's wB, cB: no
-- example)
example : o65A.H.wAt = o65A.wAt ∧ o65A.H.cZ = o65A.cZ ∧ o65A.H.cAt = o65A.cAt := ⟨rfl, rfl, rfl⟩
example : o65A.IK.wK = o65A.wK ∧ o65A.IK.cK = o65A.cK ∧ o65A.IT.wT = o65A.wT ∧ o65A.IT.cT = o65A.cT
    := ⟨rfl, rfl, rfl, rfl⟩
example : o65A.En.wAt = o65A.wE := rfl

/-! ### (B) 1, 2: the orders, at o65A's own tree of keys -/
theorem o65_set_two_ne_one : ((o65A.IK.setV (o65A.v' + 1)).DK).sg 2 ≠ 1 := E3.o65K_two_ne_one
theorem o65_set_last_ne_one : ((o65A.IK.setV (o65A.v' + 1)).DK).sg o65A.v' ≠ 1 :=
    E3.o65K_last_ne_one
theorem o65_set_last_ne_rev : ((o65A.IK.setV (o65A.v' + 1)).DK).sg o65A.v' ≠ Fin.revPerm :=
    E3.o65K_last_ne_rev
theorem set_table_ne_one : o65A.D.sg 0 ≠ 1 := E3.o65T_ne_one
theorem set_leaves_ne_one : o65A.oE ≠ 1 := E3.o65E_ne_one

/-! ### (B) 3: the padding's factor, as a polynomial in λ -/
section Fac
variable {E : Type} [Field E]
open Polynomial

/-- the public factor as a polynomial: the product over the padding of (X − row)^count -/
noncomputable def padPoly (t : ℕ → E) (pads : List (ℕ × ℕ)) : E[X] := (pads.map fun e => (X - C (t
    e.1)) ^ e.2).prod

theorem padPoly_eval (t : ℕ → E) (pads : List (ℕ × ℕ)) (al : E) : (padPoly t pads).eval al = padFac
    t pads al := by
  unfold padPoly padFac
  induction pads with
  | nil => simp
  | cons e l ih => simp [ih]

end Fac

/-- General in A: the head's factor is the polynomial's value at every λ. -/
theorem fac_eval_gen {E : Type} [Field E] [Fintype E] (A : LkAsmH E) (st : A.St) (lam : E) :
    A.H.fac (st, lam) = (padPoly (A.tab st) A.pads).eval lam := (padPoly_eval _ _ _).symm

/-- at the small lookup the polynomial is X − 1 -/
theorem o65_padPoly : padPoly (o65A.tab ()) o65A.pads = (Polynomial.X - Polynomial.C 1 : Polynomial
    K) := by
  show padPoly (fun u : ℕ => (u : K)) [(1, 1)] = _
  simp [padPoly]
theorem fac_eval (lam : K) : o65A.H.fac ((), lam) = (Polynomial.X - Polynomial.C 1 : Polynomial
    K).eval lam := by
  rw [fac_eval_gen, o65_padPoly]
theorem fac_ne_one : (Polynomial.X - Polynomial.C 1 : Polynomial K) ≠ 1 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_one] at this
  exact one_ne_zero this

/-- joined: the factor, as a polynomial in λ, is not 1 -/
theorem o65_padPoly_ne_one : padPoly (o65A.tab ()) o65A.pads ≠ 1 := by
  rw [o65_padPoly]
  exact fac_ne_one

/-! ### (B) 4: the tie: seven steps; 3, 2, …, 2 shown values -/
theorem tie_steps : o65A.n + 1 = 7 := rfl
theorem tie_rows (x : o65A.X2) : (o65A.rows2 x).length = 7 := tieF_rowsAt_len o65A.H.tie (o65A.n +
    1) _
section
variable {E : Type} [Field E] [Fintype E] (D : TieF E)
theorem tieF_A0 : (D.lv 0).T.A = Option Bool := rfl
theorem tieF_AS (j : ℕ) : (D.lv (j + 1)).T.A = Bool := rfl
theorem tieF_card0 : Fintype.card (D.lv 0).T.A = 3 := rfl
theorem tieF_cardS (j : ℕ) : Fintype.card (D.lv (j + 1)).T.A = 2 := rfl
theorem tieF_DY : ∀ l, (D.lv l).T.DY = 3
  | 0 => rfl
  | _ + 1 => rfl
end
theorem tie_shown : (List.range (o65A.n + 1)).map (fun l => Fintype.card (o65A.H.tie.lv l).T.A) =
    [3, 2, 2, 2, 2, 2, 2] := rfl
theorem tie_shown_nums : ∀ l, Fintype.card (o65A.H.tie.lv l).T.A = (o65S.scTie l).shown
  | 0 => rfl
  | _ + 1 => rfl

/-! ### (B) 5: the leaves' degrees -/
theorem leaves_deg_round : List.ofFn o65A.En.dg = [2, 1, 1, 1] := by decide
/-- by variable: coordinate v of the tree's point is bound in round oE⁻¹ v -/
theorem leaves_deg_var_gen {E : Type} [Field E] [Fintype E] (A : LkAsmH E) (v : Fin (A.w + A.d)) :
    A.En.dg (A.oE.symm v) = if (v : ℕ) < A.w then 1 else 2 := by
  show dgEnd A.w A.d A.oE (A.oE.symm v) = _
  unfold dgEnd
  rw [Equiv.apply_symm_apply]
theorem leaves_deg_var : List.ofFn (fun v => o65A.En.dg (o65A.oE.symm v)) = [1, 1, 1, 2] := by
    decide
theorem leaves_deg_nums : List.ofFn o65A.En.dg = o65S.scEnd.degs := by decide

end Cb.Tw
#print axioms Cb.Tw.o65_set_two_ne_one
#print axioms Cb.Tw.o65_set_last_ne_one
#print axioms Cb.Tw.o65_set_last_ne_rev
#print axioms Cb.Tw.fac_eval
#print axioms Cb.Tw.fac_ne_one
#print axioms Cb.Tw.o65_padPoly_ne_one
#print axioms Cb.Tw.tie_shown
#print axioms Cb.Tw.leaves_deg_round
#print axioms Cb.Tw.leaves_deg_var
#print axioms Cb.Tw.leaves_deg_var_gen
