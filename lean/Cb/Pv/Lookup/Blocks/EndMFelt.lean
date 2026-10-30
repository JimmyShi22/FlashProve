-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Blocks/EndMFelt.lean.
Lemmas on the closing of Cb/Pv/Lookup/Blocks/EndM.lean: where the conclusion of `instM_top_iff`
fails, how little it needs, and which variable each round of the closing binds.

One small instance (`I0`, `s0`), statements and proofs.
 (1) `top_iff_fails`: with an idle position (n + 1 < 2^w) the conclusion of `instM_top_iff` can
     fail: it does at `I0` (w = 1, d = 0, n = 0; over ZMod 101; the identity as order; every wE).
 (2) `top_iff_le`: that conclusion from 2^w ≤ n + 1 alone: `instM_top_iff` and `instM_top` ask
     n + 1 = 2^w, more than their proofs take. (The assembly `LkAsmH` has the closing at its own
     n + 1: there the premise reads 2^w ≤ n + 2, and the other half, n + 2 ≤ 2^w, is the first
     clause of `Adm`, Cb/Ld/LdLkp.lean.)
 (3) `pVars_mix`, `endM_vars_at`: place j of the closing's list of variables is a cube variable of
     degree (1 if σ j is a plane's coordinate, else 2) with the equality weight at coordinate σ j of
     the tree's point: the order σ is not idle. Two examples: at the reversal round 1 binds the
     tree's last coordinate, the last round coordinate 0.
 (4) `endM_Y`: the end claim reads the bits at the point `fun v => x (σ.symm v)`: each challenge at
     its own coordinate's place; the public factor at that point's last d places (rfl).
Limits: lemmas on one block; nothing on the assembled lookup.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Blocks.EndM
import Mathlib.Tactic.NormNum.Prime
set_option autoImplicit false
namespace E2H2
open Cb Cb.LdLkp Cb.Lkp Iop Hiop Prob IOR

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩
abbrev K : Type := ZMod 101

noncomputable def I0 : LkInst K where
  X := Unit
  St := Unit
  st := fun _ => ()
  lam := fun _ => 2
  J := Fin 2
  v := 0
  d := 0
  w := 1
  key := fun _ _ _ => 0
  tab := fun _ _ => 0
  bAt := fun _ j => if j = 0 then 0 else 1
  fK := fun _ _ => 0
  formT := fun _ _ _ => 0
  wK := fun _ _ => 0
  cK := fun _ _ => 0
  wT := fun _ _ => 0
  cT := fun _ _ => 0

instance : DecidableEq I0.J := inferInstanceAs (DecidableEq (Fin 2))

noncomputable def s0 : ((I0.DT2 0).lv I0.d).T.St :=
  show Unit × (Fin (1 + 0) → K) from ((), Alg.corner fun _ => true)

/-- At `I0`, n = 0 and the identity as order, for every wE: the equivalence that `instM_top_iff`
concludes does not hold for all x and m. Here n + 1 = 1 < 2 = 2^w. -/
theorem top_iff_fails (wE : PIdx (pfMix K (I0.w + I0.d) (dgEnd I0.w I0.d (Equiv.refl _))) → I0.J) :
    ¬ (∀ (x : K × ((I0.DT2 0).lv I0.d).T.St) (m : I0.J → K),
      ((I0.DT2 0).lv I0.d).T.SumHolds x (fun j => m (((I0.DT2 0).lv I0.d).toJ j)) ↔
      (I0.endM 0 (Equiv.refl _) wE).Holds x m) := by
  intro h
  let wU : PIdx (List.replicate (I0.w + I0.d) (pfCube K 2)) → I0.J := fun _ => (0 : Fin 2)
  let m : I0.J → K := fun _ => 1
  let t : K := Alg.mle (fun b => 1 + m ((I0.endU 0 wU).tAt b) * (I0.endU 0 wU).cp s0 b)
      ((I0.endU 0 wU).z s0) + ∑ j, (I0.endU 0 wU).inc s0 j * m j
  have h1 : (I0.endU 0 wU).Holds (t, s0) m := rfl
  have h2 : (I0.endM 0 (Equiv.refl _) wE).Holds (t, s0) m :=
    (h (t, s0) m).1 ((ldLkpInst2_top_iff K I0 0 wU (t, s0) m).2 h1)
  have h3 : Alg.mle (fun b => 1 + m ((I0.endM 0 (Equiv.refl _) wE).tAt b) *
        (I0.endM 0 (Equiv.refl _) wE).cp s0 fun r => b ((I0.endM 0 (Equiv.refl _) wE).rw r))
        ((I0.endM 0 (Equiv.refl _) wE).z s0) =
      Alg.mle (fun b => 1 + m ((I0.endU 0 wU).tAt b) * (I0.endU 0 wU).cp s0 b) ((I0.endU 0 wU).z s0)
          :=
    add_right_cancel (b := ∑ j, (I0.endU 0 wU).inc s0 j * m j) h2
  have zM : (I0.endM 0 (Equiv.refl _) wE).z s0 = Alg.corner (fun _ => true) := rfl
  have zU : (I0.endU 0 wU).z s0 = Alg.corner (fun _ => true) := rfl
  rw [zM, zU, Alg.mle_corner, Alg.mle_corner] at h3
  have cM : (I0.endM 0 (Equiv.refl _) wE).cp s0
      (fun r => (fun _ : Fin (I0.endM 0 (Equiv.refl _) wE).k => true) ((I0.endM 0 (Equiv.refl _)
          wE).rw r)) = 1 := by
    show (2 : K) - 1 - 0 = 1
    norm_num
  have cU : (I0.endU 0 wU).cp s0 (fun _ => true) = 0 := by
    show (if numLE (fun _ : Fin (1 + 0) => true) % 2 ^ 1 < 0 + 1 then ((2 : K) - 1 - 0) else 0) = 0
    rw [if_neg (by decide)]
  rw [cM, cU] at h3
  have h4 : (1 : K) + 1 * 1 = 1 + 1 * 0 := h3
  exact absurd h4 (by decide)

end E2H2

namespace E2H2
open Cb Cb.LdLkp Cb.Lkp Iop Hiop Prob IOR
variable (E : Type) [Field E] [Fintype E]

/-- The conclusion of `instM_top_iff` from the weaker premise 2^w ≤ n + 1. -/
theorem top_iff_le (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (hn : 2 ^ I.w ≤ n + 1)
    (x : E × ((I.DT2 n).lv I.d).T.St) (m : I.J → E) :
      ((I.DT2 n).lv I.d).T.SumHolds x (fun j => m (((I.DT2 n).lv I.d).toJ j)) ↔
      (I.endM n σ wE).Holds x m := by
  rw [ldLkpP_sum E (I.DT2 n) (ldLkpInst2_step E I n) I.d x m]
  have hU : (I.DT2 n).U (((I.DT2 n).lv I.d).base x.2) m I.d =
      fun c : Fin (I.w + I.d) → Bool =>
        1 + m (I.tAt c) * (I.endM n σ wE).cp x.2 fun r => c (Fin.natAdd I.w r) := by
    funext c
    refine (ldLkpNum_topT E I.w I.d _ _ _ c).trans ?_
    show 1 + (if numLE c % 2 ^ I.w < n + 1 then m (I.bAt (numLE c / 2 ^ I.w) (numLE c % 2 ^ I.w))
            else 0) * _ = _
    rw [if_pos (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos I.w)) hn)]
    have hq : numLE c / 2 ^ I.w = numLE fun r : Fin I.d => c (Fin.natAdd I.w r) :=
      numLE_div I.w I.d c
    exact congrArg (fun u => 1 + m (I.tAt c) *
      (I.lam (((I.DT2 n).lv I.d).base x.2) - 1 - I.tab (I.st (((I.DT2 n).lv I.d).base x.2)) u)) hq
  rw [hU, ← ldLkpP_push E _ _ ((I.DT2 n).lv I.d).toJ (((I.DT2 n).lv I.d).T.slS x.2) m]
  have hm := Alg.mle_equiv σ
    (fun c : Fin (I.w + I.d) → Bool =>
      1 + m (I.tAt c) * (I.endM n σ wE).cp x.2 fun r => c (Fin.natAdd I.w r))
    (((I.DT2 n).lv I.d).pnt x.2)
  exact Iff.of_eq (congrArg (fun t => t +
    ∑ j, pushJ ((I.DT2 n).lv I.d).toJ (((I.DT2 n).lv I.d).T.slS x.2) j * m j = x.1) hm.symm)

/-- place j of the list of variables: degree dg j, equality weight at z j -/
theorem pVars_mix : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    pVars (pfMix E k dg) (pdMix E k dg z) =
      List.ofFn fun j : Fin k => (pfCube E (dg j)).var (pdEq E (dg j) (z j))
  | 0, _, _ => by simp [pfMix, pVars]
  | k + 1, dg, z => by
    rw [List.ofFn_succ]
    exact congrArg (fun t => (pfCube E (dg 0)).var (pdEq E (dg 0) (z 0)) :: t)
      (pVars_mix k (fun i => dg i.succ) fun i => z i.succ)

/-- The order is not idle: round j + 1 of the closing is in a variable of degree (1 if σ j is a
plane's coordinate, else 2) that weighs at coordinate σ j of the tree's point. -/
theorem endM_vars_at (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (s : (I.endM n σ wE).X) :
    (I.endM n σ wE).par.vars s =
      List.ofFn fun j : Fin (I.w + I.d) =>
        (pfCube E (if (σ j : ℕ) < I.w then 1 else 2)).var
          (pdEq E (if (σ j : ℕ) < I.w then 1 else 2) (((I.DT2 n).lv I.d).pnt s (σ j))) :=
  pVars_mix E (I.w + I.d) (dgEnd I.w I.d σ) _

example (I : LkInst E) [DecidableEq I.J] (n : ℕ) σ wE (b : Fin (I.w + I.d) → Bool) :
    (I.endM n σ wE).tAt b = I.tAt fun v => b (σ.symm v) := rfl
/-- at the reversal: round 1 binds the tree's last coordinate (the top bit of the table's row, if
0 < d) -/
example (w d : ℕ) (h : 0 < w + d) : ((Fin.revPerm (⟨0, h⟩ : Fin (w + d)) : Fin (w + d)) : ℕ) = w + d
    - 1 := by
  rw [Fin.revPerm_apply, Fin.val_rev]
example (w d : ℕ) (h : w + d - 1 < w + d) : ((Fin.revPerm (⟨w + d - 1, h⟩ : Fin (w + d)) : Fin (w +
    d)) : ℕ) = 0 := by
  rw [Fin.revPerm_apply, Fin.val_rev]; show w + d - (w + d - 1 + 1) = 0; omega
end E2H2
#print axioms E2H2.top_iff_fails
#print axioms E2H2.top_iff_le
#print axioms E2H2.endM_vars_at

namespace E2H5
open Cb Cb.LdLkp Cb.Lkp Iop Hiop Prob IOR
variable (E : Type) [Field E] [Fintype E]

/-- the bits: the extension of (row, plane) ↦ bit at the point "challenge of the round that bound
coordinate v, at place v" -/
theorem endM_Y (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (m : I.J → E) (x : Fin (I.w + I.d) →
        E) :
    (I.endM n σ wE).Y m x = Alg.mle (fun c => m (I.tAt c)) (fun v => x (σ.symm v)) := by
  have h := Alg.mle_equiv σ (fun c => m (I.tAt c)) (fun v => x (σ.symm v))
  simp only [Equiv.symm_apply_apply] at h
  exact h

/-- the public factor: at the last d places of that same point -/
example (I : LkInst E) [DecidableEq I.J] (n : ℕ) (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) (x : Fin (I.w + I.d) → E) (r : Fin
        I.d) :
    x ((I.endM n σ wE).rw r) = (fun v => x (σ.symm v)) (Fin.natAdd I.w r) := rfl
end E2H5
#print axioms E2H5.endM_Y
