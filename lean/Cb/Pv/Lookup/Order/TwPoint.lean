-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Order/TwPoint.lean.
Which variable each sumcheck of the assembled lookup binds.

A sumcheck's out-statement holds its challenges by round, in its field pt. What comes next reads
them by variable. For each kind of sumcheck of LkAsmH (the tie's steps, the keys' levels, the
table's levels, the closing, the bit test) this file states, for every value of the field pt, that
the next block's weights, or the coefficients of the claim that is left, are made from the
challenges put back at their variables' places by the lookup's own order: coordinate i holds the
challenge of round (order⁻¹ i). In the lemmas' names the closing is "leaves", the bit test "bits".
Main names:
  `point14`: the statements gathered for one A : LkAsmH E, without a premise;
    `point14_bits_row` beside it.
  `round_of`, `round_of_list`: order⁻¹ i is the place of i in the list of the order's values.
  `sigma_table`, `sigma_ext_pt`, `sigma_keys`, `sigma_planes`: which bit of an entry's number a
    coordinate stands for: coordinate c is bit c.
Limits: `keys_reads` (the claim on the keys) and `end_fn` hold whatever the order is. The closing's
own reader LkEndM.fn is by round; by variable it is read through the inverse order, written out in
the statements.
Not claimed: that the field pt holds the transcript's challenges (`takeSc_flat`,
Cb/Pv/Lookup/Out/TwSc.lean, has that for the short sumcheck); that an order is a program's.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Asm.AsmH
import Cb.Pv.Lookup.Blocks.EndMFelt
import Cb.Pv.Lookup.Order.E3Ord
import Cb.Pv.Lookup.Order.TwList
import Cb.Ld.LdLkpNumProofs

set_option autoImplicit false

namespace Cb.Tw
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable {E : Type} [Field E] [Fintype E]

/-! ### The levels (TreeP: sg l j is the coordinate that round j of level l binds) -/

theorem lv_gam (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (i : Fin (D.g + l)) :
    (D.lv l).gam o i = (ppList (D.lv l).T.par.fmt o.pt).getD ((D.sg l).symm i : Fin (D.g + l)) 0 :=
        by
  cases l with
  | zero => exact hFnOf_list (pfCube E 2) (pDummy E 2) (pDummyD E 2) (D.g + 0) _ o.pt ((D.sg 0).symm
      i)
  | succ l => exact hFnOf_list (pfCube E 2) (pDummy E 2) (pDummyD E 2) (D.g + l + 1) _ o.pt ((D.sg
      (l + 1)).symm i)

theorem lv_pnt (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (ρ : E) :
    (D.lv (l + 1)).pnt (o, ρ) = (Fin.snoc ((D.lv l).gam o) ρ : Fin (D.g + l + 1) → E) := rfl

theorem lv_weights (D : TreeP E) (l : ℕ) (s : (D.lv l).T.St) :
    (D.lv l).T.vars s =
      List.ofFn fun j : Fin (D.g + l) => (pfCube E 2).var (pdEq E 2 ((D.lv l).pnt s (D.sg l j))) :=
          by
  cases l with
  | zero => exact pVars_eqsB 2 (D.g + 0) _
  | succ l => exact pVars_eqsB 2 (D.g + l + 1) _

/-- the line's draw hands the sumcheck's out-statement on, whole, with ρ: that is the next level's
state -/
theorem line_state (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (ρ : E) :
    ((D.cube l).toLine.toIn.nxX o ρ).2 = (o, ρ) := rfl

/-- From a level to the next: the next sumcheck's own list of variables (its weights) at the state
(o, ρ), written in o's field pt and ρ, without the readers gam and pnt -/
theorem next_weights (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (ρ : E) :
    (D.lv (l + 1)).T.vars (o, ρ) =
      List.ofFn fun j : Fin (D.g + (l + 1)) => (pfCube E 2).var (pdEq E 2
        ((Fin.snoc (fun i : Fin (D.g + l) => (ppList (D.lv l).T.par.fmt o.pt).getD ((D.sg l).symm i
            : Fin (D.g + l)) 0) ρ :
          Fin (D.g + l + 1) → E) (D.sg (l + 1) j))) := by
  rw [lv_weights D (l + 1) (o, ρ), lv_pnt D l o ρ]
  have e : (D.lv l).gam o = fun i : Fin (D.g + l) => (ppList (D.lv l).T.par.fmt o.pt).getD ((D.sg
      l).symm i : Fin (D.g + l)) 0 :=
    funext fun i => lv_gam D l o i
  rw [e]

/-! ### The last key level → the claim on the keys -/

/-- the library's MCl holds the point top bit first: pnt read backwards -/
theorem next_keys (I : LkInst E) (x : E × (I.DK.lv I.v).T.St) :
    (I.topCl x).pt = Blocks.nat fun i : Fin (0 + I.v) => (I.DK.lv I.v).pnt x.2 i.rev := rfl

/-- Blocks.ext reads the point top bit first too, so the two reversals cancel: what the claim reads
of a vector f of keys is f's multilinear extension, lowest bit first, at pnt. No order is named. -/
theorem keys_reads (I : LkInst E) (x : E × (I.DK.lv I.v).T.St) (f : ℕ → E) :
    Blocks.ext (0 + I.v) f (I.topCl x).pt =
      Alg.mle (fun b : Fin (0 + I.v) → Bool => f (numLE b)) ((I.DK.lv I.v).pnt x.2) :=
  (ldLkpNum_ext E (0 + I.v) f _).symm

/-! ### The last table level → the leaves; the leaves → their end claim (LkEndM at the order σ: its
own coordinates are by round) -/

theorem end_fn_round (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (zz : (I.endM n σ wE).par.Mid) (j :
        Fin (I.w + I.d)) :
    (I.endM n σ wE).fn zz.st ((I.endM n σ wE).par.hp zz.st zz.pt) j =
      (ppList (I.endM n σ wE).par.fmt zz.pt).getD (j : ℕ) 0 :=
  hFnMix_list (I.w + I.d) (dgEnd I.w I.d σ) _ zz.pt j

/-- the same at j := σ⁻¹ v; it does not hang on σ (it holds with any permutation in σ's place) -/
theorem end_fn (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (zz : (I.endM n σ wE).par.Mid) (v :
        Fin (I.w + I.d)) :
    (I.endM n σ wE).fn zz.st ((I.endM n σ wE).par.hp zz.st zz.pt) (σ.symm v) =
      (ppList (I.endM n σ wE).par.fmt zz.pt).getD (σ.symm v : Fin (I.w + I.d)) 0 :=
  end_fn_round I n σ wE zz (σ.symm v)

/-- the closing's weights are made from the last table level's pnt, read through the closing's order
-/
theorem next_leaves (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (s : (I.endM n σ wE).X) :
    (I.endM n σ wE).par.vars s =
      List.ofFn fun j : Fin (I.w + I.d) =>
        (pfCube E (if (σ j : ℕ) < I.w then 1 else 2)).var
          (pdEq E (if (σ j : ℕ) < I.w then 1 else 2) (((I.DT2 n).lv I.d).pnt s (σ j))) :=
  E2H2.endM_vars_at E I n σ wE s

/-- The map that is not revealed: what stays of it in the closing's end claim, at the field pt, is
the extension of the planes' bits at the challenges by variable: coordinate v holds the challenge of
round σ⁻¹ v. -/
theorem leaves_mend (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (zz : (I.endM n σ wE).par.Mid) (m :
        I.J → E) :
    (I.endM n σ wE).par.Gb zz.st m () ((I.endM n σ wE).par.hp zz.st zz.pt) =
      Alg.mle (fun c => m (I.tAt c))
        (fun v => (ppList (I.endM n σ wE).par.fmt zz.pt).getD (σ.symm v : Fin (I.w + I.d)) 0) := by
  have h := E2H5.endM_Y E I n σ wE m ((I.endM n σ wE).fn zz.st ((I.endM n σ wE).par.hp zz.st zz.pt))
  have e : (fun v => (I.endM n σ wE).fn zz.st ((I.endM n σ wE).par.hp zz.st zz.pt) (σ.symm v)) =
      (fun v => (ppList (I.endM n σ wE).par.fmt zz.pt).getD (σ.symm v : Fin (I.w + I.d)) 0) :=
    funext fun v => end_fn_round I n σ wE zz (σ.symm v)
  exact h.trans (congrArg (Alg.mle fun c => m (I.tAt c)) e)

/-- The closing's row: its coefficient at an entry is the sum of the equality weights of the
challenges by variable at the corners that stand at that entry -/
theorem leaves_row (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (zz : (I.endM n σ wE).par.Mid) (j :
        I.J) :
    (I.endM n σ wE).rowB zz.st () ((I.endM n σ wE).par.hp zz.st zz.pt) j =
      ∑ c, if I.tAt c = j then
        Alg.eqk (fun v => (ppList (I.endM n σ wE).par.fmt zz.pt).getD (σ.symm v : Fin (I.w + I.d))
            0) c else 0 := by
  have e : (fun v => (I.endM n σ wE).fn zz.st ((I.endM n σ wE).par.hp zz.st zz.pt) (σ.symm v)) =
      (fun v => (ppList (I.endM n σ wE).par.fmt zz.pt).getD (σ.symm v : Fin (I.w + I.d)) 0) :=
    funext fun v => end_fn_round I n σ wE zz (σ.symm v)
  rw [← e]
  unfold LkEndM.rowB
  refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl Bool)) _ _ fun b => ?_
  have h := Alg.eqk_equiv σ (fun v => (I.endM n σ wE).fn zz.st ((I.endM n σ wE).par.hp zz.st zz.pt)
      (σ.symm v))
    (fun v => b (σ.symm v))
  simp only [Equiv.symm_apply_apply] at h
  exact congrArg (fun t => if I.tAt (fun v => b (σ.symm v)) = j then t else 0) h

/-- The public factor: the extension of cp at the rows' coordinates (the last d) of the challenges
by variable -/
theorem leaves_fac (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (zz : (I.endM n σ wE).par.Mid) (v :
        Empty → E) :
    (I.endM n σ wE).par.S1 zz.st ((I.endM n σ wE).par.hp zz.st zz.pt) v () =
      Alg.mle ((I.endM n σ wE).cp zz.st) fun r : Fin I.d =>
        (ppList (I.endM n σ wE).par.fmt zz.pt).getD (σ.symm (Fin.natAdd I.w r) : Fin (I.w + I.d)) 0
            :=
  congrArg (Alg.mle ((I.endM n σ wE).cp zz.st)) (funext fun r => end_fn_round I n σ wE zz (σ.symm
      (Fin.natAdd I.w r)))

/-! ### The bits (ZeroCubeP, LkBitP: a point is drawn; the sumcheck that follows binds in the order
sg) -/

theorem bit_fn (B : LkBitP E) (o : B.zc.next.par.Out) (i : Fin B.k) :
    B.zc.fn o.st.2.2 (B.zc.next.ini o.st (B.zc.next.par.hp o.st o.pt)) i =
      (ppList B.zc.next.par.fmt o.pt).getD (B.sg.symm i : Fin B.k) 0 :=
  hFnOf_list (pfCube E 2) (pDummy E 2) (pDummyD E 2) B.k _ o.pt (B.sg.symm i)

/-- the bits' own weights: place j weighs at coordinate sg j of the drawn zero point -/
theorem bit_weights (B : LkBitP E) (s : B.zc.next.St) :
    B.zc.next.vars s = List.ofFn fun j : Fin B.k => (pfCube E 2).var (pdEq E 2 (s.2.2 (B.sg j))) :=
  ZeroCubeP.vars_at E B.zc s

open Classical in
/-- The bit test's row: its coefficient at an entry. The equality weights are written in the field
pt; the further variable's challenge stays under the library's reader lst. -/
theorem bits_row (B : LkBitP E) (o : B.zc.next.par.Out) (j : B.J) :
    B.rowA o.st () (B.zc.next.par.hp o.st o.pt) j =
      (∑ b, if B.tAt b = j then
        Alg.eqk (fun i => (ppList B.zc.next.par.fmt o.pt).getD (B.sg.symm i : Fin B.k) 0) b else 0)
            +
      if j = B.cAt then B.zc.next.lst o.st (B.zc.next.par.hp o.st o.pt) else 0 := by
  have e : B.zc.fn o.st.2.2 (B.zc.next.ini o.st (B.zc.next.par.hp o.st o.pt)) =
      fun i => (ppList B.zc.next.par.fmt o.pt).getD (B.sg.symm i : Fin B.k) 0 := funext fun i =>
          bit_fn B o i
  rw [← e]
  rfl

/-! ### The tie: no variable -/

theorem tie_none (D : TieF E) (l : ℕ) : (D.lv l).T.fmt = [] := by cases l <;> rfl

/-! ### An order given as a list: σ⁻¹ i is the place of i in the list -/

theorem round_of (k : ℕ) (L : List ℕ) (h : L.Perm (List.range k)) (i : Fin k) :
    (((E3.permOfList k L h).symm i : Fin k) : ℕ) = L.idxOf i.1 := rfl

/-- for EVERY order: σ⁻¹ i is the place of i in the list of σ's values -/
theorem round_of_list {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    ((σ.symm i : Fin k) : ℕ) = ((List.finRange k).map fun j => ((σ j : Fin k) : ℕ)).idxOf i.1 := by
  have hn : ((List.finRange k).map fun j => ((σ j : Fin k) : ℕ)).Nodup :=
    (List.nodup_finRange k).map fun a b h => σ.injective (Fin.ext h)
  have hl : (σ.symm i).1 < ((List.finRange k).map fun j => ((σ j : Fin k) : ℕ)).length := by simp
  have hg : ((List.finRange k).map fun j => ((σ j : Fin k) : ℕ))[(σ.symm i).1]'hl = i.1 := by simp
  have h := hn.idxOf_getElem (σ.symm i).1 hl
  rw [hg] at h
  exact h.symm

/-! ### Coordinate c stands for bit c -/

omit [Fintype E] in
theorem sigma_table {k : ℕ} (a : ℕ → E) (b : Fin k → Bool) :
    Alg.mle (fun x : Fin k → Bool => a (numLE x)) (Alg.corner b) = a (∑ c : Fin k, if b c then 2 ^
        (c : ℕ) else 0) :=
  Alg.mle_corner _ b

omit [Fintype E] in
/-- the keys' claim as it goes out (MCl.pt, Blocks.ext): where the point is the corner b it reads
key number Σ b_c 2^c -/
theorem sigma_ext_pt (k : ℕ) (a : ℕ → E) (b : Fin k → Bool) :
    Blocks.ext k a (Blocks.nat fun i : Fin k => (Alg.corner b : Fin k → E) i.rev) =
      a (∑ c : Fin k, if b c then 2 ^ (c : ℕ) else 0) := by
  rw [← ldLkpNum_ext E k a (Alg.corner b)]
  exact Alg.mle_corner _ b

/-- the keys' tree's top level -/
theorem sigma_keys (I : LkInst E) (x : I.X) (m : I.J → E) (b : Fin (0 + I.v) → Bool) :
    Alg.mle (I.DK.U x m I.v) (Alg.corner b) =
      I.lam x - I.key (I.st x) m (∑ c : Fin (0 + I.v), if b c then 2 ^ (c : ℕ) else 0) := by
  rw [Alg.mle_corner]
  exact ldLkpNum_topK E I.v (I.key (I.st x) m) (I.lam x) b

/-- the planes: entry (row, plane) = (N / 2^w, N % 2^w) for N = Σ b_c 2^c: the first w coordinates
are the plane's -/
theorem sigma_planes (I : LkInst E) (m : I.J → E) (b : Fin (I.w + I.d) → Bool) :
    Alg.mle (fun c => m (I.tAt c)) (Alg.corner b) =
      m (I.bAt ((∑ c : Fin (I.w + I.d), if b c then 2 ^ (c : ℕ) else 0) / 2 ^ I.w)
        ((∑ c : Fin (I.w + I.d), if b c then 2 ^ (c : ℕ) else 0) % 2 ^ I.w)) :=
  Alg.mle_corner _ b

/-! ### ONE STATEMENT for the assembly -/

/-- For every A and every value of the fields pt: at each kind of sumcheck of LkAsmH, what comes
next is made from that sumcheck's challenges by variable, at A's own order. Twelve clauses. Each
names its order (A.oK, A.oT, A.oE, A.oB) but the first (the tie binds no variable) and the fourth
(the claim on the keys: an equation in the point pnt, which holds whatever the order is). -/
theorem point14 (A : LkAsmH E) :
    -- the tie's steps bind no variable
    (∀ l, (A.H.tie.lv l).T.fmt = []) ∧
    -- the keys' levels, in the order A.oK: the end point; the next level's weights; the claim on
    -- the keys
    (∀ (l : ℕ) (o : (((A.IK.setV (A.v' + 1)).DK).lv l).T.par.Out) (i : Fin (0 + l)),
      (((A.IK.setV (A.v' + 1)).DK).lv l).gam o i =
        (ppList (((A.IK.setV (A.v' + 1)).DK).lv l).T.par.fmt o.pt).getD ((A.oK l).symm i : Fin (0 +
            l)) 0) ∧
    (∀ (l : ℕ) (o : (((A.IK.setV (A.v' + 1)).DK).lv l).T.par.Out) (ρ : E),
      (((A.IK.setV (A.v' + 1)).DK).lv (l + 1)).T.vars (o, ρ) =
        List.ofFn fun j : Fin (0 + (l + 1)) => (pfCube E 2).var (pdEq E 2
          ((Fin.snoc (fun i : Fin (0 + l) =>
              (ppList (((A.IK.setV (A.v' + 1)).DK).lv l).T.par.fmt o.pt).getD ((A.oK l).symm i : Fin
                  (0 + l)) 0) ρ :
            Fin (0 + l + 1) → E) (A.oK (l + 1) j)))) ∧
    (∀ (x : A.X4) (f : ℕ → E),
      Blocks.ext (0 + (A.v' + 1)) f (A.clK x).pt =
        Alg.mle (fun b : Fin (0 + (A.v' + 1)) → Bool => f (numLE b))
          ((((A.IK.setV (A.v' + 1)).DK).lv (A.v' + 1)).pnt x.2)) ∧
    -- the table's levels, in the order A.oT: the end point; the next level's weights; the leaves'
    -- weights
    (∀ (l : ℕ) (o : (A.D.lv l).T.par.Out) (i : Fin (A.w + l)),
      (A.D.lv l).gam o i = (ppList (A.D.lv l).T.par.fmt o.pt).getD ((A.oT l).symm i : Fin (A.w + l))
          0) ∧
    (∀ (l : ℕ) (o : (A.D.lv l).T.par.Out) (ρ : E),
      (A.D.lv (l + 1)).T.vars (o, ρ) =
        List.ofFn fun j : Fin (A.w + (l + 1)) => (pfCube E 2).var (pdEq E 2
          ((Fin.snoc (fun i : Fin (A.w + l) => (ppList (A.D.lv l).T.par.fmt o.pt).getD ((A.oT
              l).symm i : Fin (A.w + l)) 0) ρ :
            Fin (A.w + l + 1) → E) (A.oT (l + 1) j)))) ∧
    (∀ s : A.En.X, A.En.par.vars s =
      List.ofFn fun j : Fin (A.w + A.d) =>
        (pfCube E (if (A.oE j : ℕ) < A.w then 1 else 2)).var
          (pdEq E (if (A.oE j : ℕ) < A.w then 1 else 2) ((A.D.lv A.d).pnt s (A.oE j)))) ∧
    -- the closing, in the order A.oE: the map that is not revealed, the row, the public factor
    (∀ (zz : A.En.par.Mid) (m : A.J → E),
      A.En.par.Gb zz.st m () (A.En.par.hp zz.st zz.pt) =
        Alg.mle (fun c => m (A.IT.tAt c)) (fun v => (ppList A.En.par.fmt zz.pt).getD (A.oE.symm v :
            Fin (A.w + A.d)) 0)) ∧
    (∀ (zz : A.En.par.Mid) (j : A.J),
      A.En.rowB zz.st () (A.En.par.hp zz.st zz.pt) j =
        ∑ c, if A.IT.tAt c = j then
          Alg.eqk (fun v => (ppList A.En.par.fmt zz.pt).getD (A.oE.symm v : Fin (A.w + A.d)) 0) c
              else 0) ∧
    (∀ (zz : A.En.par.Mid) (v : Empty → E),
      A.En.par.S1 zz.st (A.En.par.hp zz.st zz.pt) v () =
        Alg.mle (A.En.cp zz.st) fun r : Fin A.d =>
          (ppList A.En.par.fmt zz.pt).getD (A.oE.symm (Fin.natAdd A.w r) : Fin (A.w + A.d)) 0) ∧
    -- the bits, in the order A.oB: their own weights from the drawn zero point; the end point
    (∀ s : A.Bt.zc.next.St, A.Bt.zc.next.vars s =
      List.ofFn fun j : Fin (A.w + A.d) => (pfCube E 2).var (pdEq E 2 (s.2.2 (A.oB j)))) ∧
    (∀ (o : A.Bt.zc.next.par.Out) (i : Fin (A.w + A.d)),
      A.Bt.zc.fn o.st.2.2 (A.Bt.zc.next.ini o.st (A.Bt.zc.next.par.hp o.st o.pt)) i =
        (ppList A.Bt.zc.next.par.fmt o.pt).getD (A.oB.symm i : Fin (A.w + A.d)) 0) :=
  ⟨tie_none A.H.tie,
    fun l o i => lv_gam ((A.IK.setV (A.v' + 1)).DK) l o i,
    fun l o ρ => next_weights ((A.IK.setV (A.v' + 1)).DK) l o ρ,
    fun x f => keys_reads (A.IK.setV (A.v' + 1)) x f,
    fun l o i => lv_gam A.D l o i,
    fun l o ρ => next_weights A.D l o ρ,
    fun s => next_leaves A.IT (A.n + 1) A.oE A.wE s,
    fun zz m => leaves_mend A.IT (A.n + 1) A.oE A.wE zz m,
    fun zz j => leaves_row A.IT (A.n + 1) A.oE A.wE zz j,
    fun zz v => leaves_fac A.IT (A.n + 1) A.oE A.wE zz v,
    fun s => bit_weights A.Bt s,
    fun o i => bit_fn A.Bt o i⟩

open Classical in
/-- the bit test's row at A. The library's rowA decides its equalities classically, so this clause
stands beside point14, not in it. -/
theorem point14_bits_row (A : LkAsmH E) (o : A.Bt.zc.next.par.Out) (j : A.J) :
    A.Bt.rowA o.st () (A.Bt.zc.next.par.hp o.st o.pt) j =
      (∑ b, if A.Bt.tAt b = j then
        Alg.eqk (fun i => (ppList A.Bt.zc.next.par.fmt o.pt).getD (A.oB.symm i : Fin (A.w + A.d)) 0)
            b else 0) +
      if j = A.Bt.cAt then A.Bt.zc.next.lst o.st (A.Bt.zc.next.par.hp o.st o.pt) else 0 := by
  convert bits_row A.Bt o j

end
end Cb.Tw
