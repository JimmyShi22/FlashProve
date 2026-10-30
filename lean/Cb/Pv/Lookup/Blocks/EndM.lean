-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Blocks/EndM.lean: the closing sumcheck of a lookup's table side, with a degree for each
variable and an order of the variables.

Definitions, statements (in `Cb.Spec`) and proofs. As Cb/Ld/LdLkpEndU.lean and `LkInst.endU`
(Cb/Ld/LdLkpInst2.lean), where every variable has degree 2, the public factor reads all
variables and the order is the tree's.
The closing ties the leaves of the table's tree to the bits of the counts. In the programs its round
polynomials have degree 2 in a variable of the rows and degree 1 in a variable of the planes, and
the variables are bound from the top bit down (OnBytes/Model/Look.lean, `Forest.pad`).

States: part 1: k cube variables under equality weights, each with a degree of its own (pfMix,
pdMix, ppMix, hFnMix and their lemmas). Cb/Part/LdPartVars.lean has the same under other names.
  part 2: the record LkEndM. Under LkEndM.OK (the degrees are high enough): the conditions of the
    sumcheck of Cb/Ld/LdPsc.lean (endM_vars, endM_deg); endM_goodAt, endM_good: the closing is good
    (`GoodAt`, Cb/Ld/LdSigLift.lean; `GoodB`, Ior/Masked.lean) from its claim (LkEndM.Holds) to the
    sumcheck's end claim. endM_row: that end claim is one linear row. endM_errs: the errors.
  part 3: the instance for a lookup (endM), with the order as a permutation. instM_ok: it meets
    LkEndM.OK. instM_top_iff, instM_top: the claim at the top of the table's tree is the closing's
    claim. dgEnd_rev: the degrees in the reversed order.
Limits: instM_top_iff and instM_top ask that all 2^w bit positions (the planes) count
(n + 1 = 2^w): with an idle position the statement is false. Here n + 1 positions count, as in
Cb/Ld/LdLkpInst2.lean; in Cb/Pv/Lookup/Blocks/HeadF.lean n + 2 do.
That the programs have these degrees and this order is read off their text: no statement here says
so.

-/
import Cb.Ld.LdLkpInst2
import Cb.Ld.LdLkpEndUProofs
import Cb.Ld.LdLkpAsm2ErrProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-! ## 1. Cube variables with a degree each -/

section Mix
variable (E : Type) [Field E] [Fintype E]

def pfMix : (k : ℕ) → (Fin k → ℕ) → List (PFmt E)
  | 0, _ => []
  | k + 1, dg => pfCube E (dg 0) :: pfMix k fun i => dg i.succ

def pdMix : (k : ℕ) → (dg : Fin k → ℕ) → (Fin k → E) → PDats (pfMix E k dg)
  | 0, _, _ => ()
  | k + 1, dg, z => (pdEq E (dg 0) (z 0), pdMix k (fun i => dg i.succ) fun i => z i.succ)

def ppMix : (k : ℕ) → (dg : Fin k → ℕ) → (Fin k → E) → PPt (pfMix E k dg)
  | 0, _, _ => ()
  | k + 1, dg, x => (x 0, ppMix k (fun i => dg i.succ) fun i => x i.succ)

def hFnMix : (k : ℕ) → (dg : Fin k → ℕ) → (d : PDats (pfMix E k dg)) →
    HPt (pVars (pfMix E k dg) d) → Fin k → E
  | 0, _, _, _ => Fin.elim0
  | k + 1, dg, d, X => Fin.cons X.1 (hFnMix k (fun i => dg i.succ) d.2 X.2)

theorem mix_ok : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    ∀ v ∈ pVars (pfMix E k dg) (pdMix E k dg z), v.OK := by
  intro k
  induction k with
  | zero => intro _ _ v hv; exact absurd hv (List.not_mem_nil)
  | succ k ih =>
      intro dg z v hv
      rcases List.mem_cons.1 hv with rfl | h
      · exact psv_eq_ok E (dg 0) (z 0)
      · exact ih _ _ v h

theorem mix_val : ∀ (k : ℕ) (dg : Fin k → ℕ), ∀ f ∈ pfMix E k dg, Function.Injective f.val := by
  intro k
  induction k with
  | zero => intro _ f hf; exact absurd hf (List.not_mem_nil)
  | succ k ih =>
      intro dg f hf
      rcases List.mem_cons.1 hf with rfl | h
      · exact (psv_val E).1 (dg 0)
      · exact ih _ f h

theorem mix_fn_pt : ∀ (k : ℕ) (dg : Fin k → ℕ) (d : PDats (pfMix E k dg)) (x : Fin k → E),
    hFnMix E k dg d (pH (pfMix E k dg) d (ppMix E k dg x)) = x := by
  intro k
  induction k with
  | zero => intro _ _ x; exact Subsingleton.elim _ _
  | succ k ih =>
      intro dg d x
      show (Fin.cons (x 0)
          (hFnMix E k (fun i => dg i.succ) d.2
            (pH (pfMix E k fun i => dg i.succ) d.2
              (ppMix E k (fun i => dg i.succ) fun i => x i.succ))) : Fin (k + 1) → E) = x
      rw [ih]
      exact Fin.cons_self_tail x

theorem mix_sum : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E)
    (f : HPt (pVars (pfMix E k dg) (pdMix E k dg z)) → E),
    hSumAll (pVars (pfMix E k dg) (pdMix E k dg z)) f =
      ∑ b : Fin k → Bool,
        Alg.eqk z b * f (pH _ (pdMix E k dg z) (ppMix E k dg (Alg.corner b))) := by
  intro k
  induction k with
  | zero =>
      intro _ z f
      show f () = ∑ b : Fin 0 → Bool, Alg.eqk z b * f ()
      simp [Alg.eqk]
  | succ k ih =>
      intro dg z f
      show ((pfCube E (dg 0)).var (pdEq E (dg 0) (z 0))).sum (fun x =>
          hSumAll (pVars (pfMix E k fun i => dg i.succ)
              (pdMix E k (fun i => dg i.succ) fun i => z i.succ))
            fun xs => f (x, xs)) = _
      rw [psv_eq_sum, ih, ih, Alg.sum_cube_succ, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [eqk_cons_fn, eqk_cons_fn]
      simp only [if_true, Bool.false_eq_true, if_false]
      exact congrArg₂ (· + ·) (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm

theorem mix_hdeg : ∀ (k : ℕ) (dg : Fin k → ℕ) (d : PDats (pfMix E k dg)) (g : (Fin k → E) → E),
    Alg.DegLE dg g → HDeg (pVars (pfMix E k dg) d) fun X => g (hFnMix E k dg d X) := by
  intro k
  induction k with
  | zero => intro _ _ _ _; trivial
  | succ k ih =>
      intro dg d g hg
      refine ⟨fun xs => ?_,
        fun x => ih (fun i => dg i.succ) d.2 (fun z => g (Fin.cons x z)) fun z i => ?_⟩
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons 0 (hFnMix E k (fun i => dg i.succ) d.2 xs)) 0
        refine ⟨fun t => q.coeff t, fun x => ?_⟩
        rw [hev_of_poly E q hq, ← he, Fin.update_cons_zero]
        rfl
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons x z) i.succ
        refine ⟨q, hq, fun t => ?_⟩
        show g (Fin.cons x (Function.update z i t)) = _
        rw [← he, Fin.cons_update]

theorem mix_len : ∀ (k : ℕ) (dg : Fin k → ℕ), (pfMix E k dg).length = k
  | 0, _ => rfl
  | k + 1, dg => congrArg (· + 1) (mix_len k fun i => dg i.succ)

theorem mix_degs : ∀ (k : ℕ) (dg : Fin k → ℕ), (pfMix E k dg).map (fun f => f.n) = List.ofFn dg
  | 0, _ => by simp [pfMix]
  | k + 1, dg => by
    rw [List.ofFn_succ]
    exact congrArg (List.cons (dg 0)) (mix_degs k fun i => dg i.succ)

theorem mix_chals : ∀ (k : ℕ) (dg : Fin k → ℕ),
    (pfMix E k dg).map (fun f => Fintype.card f.Ch) = List.replicate k (Fintype.card E)
  | 0, _ => rfl
  | k + 1, dg => congrArg (List.cons (Fintype.card E)) (mix_chals k fun i => dg i.succ)

end Mix

/-! ## 2. The closing -/

/-- The parameters. -/
structure LkEndM (E : Type) [Field E] [Fintype E] where
  X : Type
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  k : ℕ
  /-- the degree of the round polynomial of each variable -/
  dg : Fin k → ℕ
  tAt : (Fin k → Bool) → J
  z : X → Fin k → E
  /-- the public factor reads kr of the k variables: those that rw names -/
  kr : ℕ
  rw : Fin kr → Fin k
  cp : X → (Fin kr → Bool) → E
  inc : X → J → E
  /-- own masks: the coefficients of the hiding polynomial -/
  wAt : PIdx (pfMix E k dg) → J

attribute [instance] LkEndM.finJ LkEndM.decJ

namespace LkEndM
variable {E : Type} [Field E] [Fintype E] (B : LkEndM E)

/-- The condition: the variables that the public factor reads are different and have degree at least
2; every variable has degree at least 1. -/
structure OK : Prop where
  inj : Function.Injective B.rw
  row : ∀ r, 2 ≤ B.dg (B.rw r)
  one : ∀ i, 1 ≤ B.dg i

/-- The claim; x = (target, state). -/
def Holds (x : E × B.X) (m : B.J → E) : Prop :=
  Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 fun r => b (B.rw r)) (B.z x.2) +
    ∑ j, B.inc x.2 j * m j = x.1

def Y (m : B.J → E) (x : Fin B.k → E) : E := Alg.mle (fun b => m (B.tAt b)) x

abbrev fn (s : B.X) (X : HPt (pVars (pfMix E B.k B.dg) (pdMix E B.k B.dg (B.z s)))) :
    Fin B.k → E :=
  hFnMix E B.k B.dg (pdMix E B.k B.dg (B.z s)) X

/-- The sumcheck: no revealed map; the one map stays as a term of the end claim. -/
def par : PscPar E where
  St := B.X
  J := B.J
  fmt := pfMix E B.k B.dg
  dat := fun s => pdMix E B.k B.dg (B.z s)
  A := Empty
  B := Unit
  G := fun _ _ a _ => a.elim
  Gb := fun s m _ X => B.Y m (B.fn s X)
  S0 := fun _ _ _ => 1
  S1 := fun s X _ _ => Alg.mle (B.cp s) fun r => B.fn s X (B.rw r)
  slS := B.inc
  wAt := B.wAt

/-- the map as a linear form on the entries (as `LkEndU.rowB`, Cb/Ld/LdLkpEndU.lean, with the
record's decidable equality in place of the classical one) -/
def rowB (s : B.par.St) (_ : B.par.B) (X : HPt (B.par.vars s)) (j : B.J) : E :=
  ∑ b, if B.tAt b = j then Alg.eqk (B.fn s X) b else 0

/-- The input joint: A0 rides along. -/
def relsIn {Ex : ExtSpec} {Wt Kc : Type} (A0 : IOR.Rels Kc B.X Ex Wt) (msg : Wt → B.J → E) :
    IOR.Rels Kc (E × B.X) Ex Wt :=
  ⟨fun x y w => A0.rel x.2 y w ∧ B.Holds x (msg w),
    fun a w => A0.relR (a.1.2, a.2) w ∧ B.Holds a.1 (msg w),
    fun a => A0.on (a.1.2, a.2),
    A0.core⟩

/-- the end claim's public part, in the fields of an output claim with no values -/
def outOf (zz : B.par.Mid) : B.par.Out := ⟨zz.st, zz.eps, zz.pt, zz.fin, fun a : Empty => a.elim⟩

end LkEndM

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def endM_sum : Prop :=
  ∀ (B : LkEndM E) (x : E × B.X) (m : B.J → E), B.par.SumHolds x m ↔ B.Holds x m
def endM_vars : Prop := ∀ B : LkEndM E, B.par.VarsOK ∧ B.par.ValInj
def endM_deg : Prop := ∀ B : LkEndM E, B.OK → B.par.DegOK
def endM_joint : Prop :=
  ∀ (B : LkEndM E) (Ex : ExtSpec) (Wt Kc : Type) (A0 : Rels Kc B.X Ex Wt) (msg : Wt → B.J → E),
    B.relsIn A0 msg = B.par.baseIn A0 msg

/-- At the base. -/
def endM_goodAt : Prop :=
  ∀ (B : LkEndM E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc B.X Ex (M × Wp)) (msg : M → B.J → E), B.OK →
    GoodAt (B.par.core Ex) (B.par.honC Ex fun w => msg w.1) (B.relsIn A0 fun w => msg w.1)
      (B.par.baseMid A0 fun w => msg w.1) (fun _ _ _ wp => wp) (B.par.numsC Ex Kc)

/-- Over a signature. -/
def endM_good : Prop :=
  ∀ (B : LkEndM E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type)
      (A0 : Rels Kc B.X E₀ (S.Msg × Wp)) (msg : S.Msg → B.J → E), B.OK →
    GoodB ((B.par.core E₀).keep S.Smp S.ext) (S.liftH (B.par.honC E₀ fun w => msg w.1))
      (S.over (B.relsIn A0 fun w => msg w.1)) (S.over (B.par.baseMid A0 fun w => msg w.1))
      (fun _ _ w => w) ((B.par.numsC E₀ Kc).keep S.Smp S.ext)

/-- The end claim is one linear row with a public target. -/
def endM_row : Prop :=
  ∀ (B : LkEndM E) (zz : B.par.Mid) (m : B.J → E),
    B.par.MidHolds zz m ↔ (B.par.slU B.rowB).Holds (B.par.tU (B.outOf zz), B.outOf zz) m
/-- its public target: the last value less ε -/
def endM_tg : Prop :=
  ∀ (B : LkEndM E) (zz : B.par.Mid), B.par.tU (B.outOf zz) = zz.fin - zz.eps

def endM_len : Prop := ∀ (B : LkEndM E) (Ex : ExtSpec), (B.par.core Ex).shape.length = B.k + 1

/-- Errors and numbers of values: 1 of q, then each variable's degree of q. -/
def endM_errs : Prop :=
  ∀ (B : LkEndM E) (Ex : ExtSpec) (Kc : Type),
    (B.par.numsC Ex Kc).err.toList = 1 :: List.ofFn B.dg ∧
    (B.par.core Ex).shape.chalList = Fintype.card E :: List.replicate B.k (Fintype.card E)

end Spec
end

section
variable (E : Type) [Field E] [Fintype E]

theorem endM_sum : Spec.endM_sum E := by
  intro B x m
  have e : hSumAll (B.par.vars x.2) (B.par.sum x.2 m) =
      Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 fun r => b (B.rw r)) (B.z x.2) := by
    show hSumAll (pVars (pfMix E B.k B.dg) (pdMix E B.k B.dg (B.z x.2))) (B.par.sum x.2 m) = _
    rw [mix_sum E]
    unfold Alg.mle
    refine Finset.sum_congr rfl fun b _ => ?_
    have hx : B.fn x.2 (pH _ (pdMix E B.k B.dg (B.z x.2)) (ppMix E B.k B.dg (Alg.corner b))) =
        Alg.corner b :=
      mix_fn_pt E B.k B.dg (pdMix E B.k B.dg (B.z x.2)) (Alg.corner b)
    have hs : B.par.sum x.2 m
          (pH _ (pdMix E B.k B.dg (B.z x.2)) (ppMix E B.k B.dg (Alg.corner b))) =
        1 + m (B.tAt b) * B.cp x.2 fun r => b (B.rw r) := by
      show 1 + ∑ _u : Unit, Alg.mle (B.cp x.2) (fun r => B.fn x.2 _ (B.rw r)) *
        B.Y m (B.fn x.2 _) = _
      rw [hx]
      unfold LkEndM.Y
      have hc : (fun r => (Alg.corner b : Fin B.k → E) (B.rw r)) =
          Alg.corner fun r => b (B.rw r) := rfl
      rw [hc, Alg.mle_corner, Alg.mle_corner]
      simp [mul_comm]
    exact congrArg (fun s => Alg.eqk (B.z x.2) b * s) hs
  show hSumAll (B.par.vars x.2) (B.par.sum x.2 m) + ∑ j, B.inc x.2 j * m j = x.1 ↔ _
  rw [e]
  exact Iff.rfl

theorem endM_vars : Spec.endM_vars E := fun B =>
  ⟨fun s => mix_ok E B.k B.dg (B.z s), mix_val E B.k B.dg⟩

theorem endM_deg : Spec.endM_deg E := by
  intro B hB st (m : B.J → E)
  have hcp : Alg.DegLE (fun i => B.dg i - 1) fun z : Fin B.k → E =>
      Alg.mle (B.cp st) fun r => z (B.rw r) :=
    (Alg.DegLE.mle (B.cp st)).comp B.rw hB.inj (fun i => B.dg i - 1) fun r => by
      show 1 ≤ B.dg (B.rw r) - 1
      have := hB.row r
      omega
  have hg : Alg.DegLE B.dg fun z =>
      1 + (Alg.mle (B.cp st) fun r => z (B.rw r)) * B.Y m z :=
    (Alg.DegLE.const _ 1).add ((hcp.mul (Alg.DegLE.mle _)).mono fun i => by
      show B.dg i - 1 + 1 ≤ B.dg i
      have := hB.one i
      omega)
  have h := mix_hdeg E B.k B.dg (pdMix E B.k B.dg (B.z st)) _ hg
  have e : B.par.sum st m =
      fun X =>
        1 + (Alg.mle (B.cp st) fun r => hFnMix E B.k B.dg (pdMix E B.k B.dg (B.z st)) X (B.rw r)) *
              B.Y m (hFnMix E B.k B.dg (pdMix E B.k B.dg (B.z st)) X) := by
    funext X
    show 1 + ∑ _u : Unit, (Alg.mle (B.cp st) fun r => B.fn st X (B.rw r)) * B.Y m (B.fn st X) = _
    simp
  rw [e]
  exact h

theorem endM_joint : Spec.endM_joint E := by
  intro B Ex Wt Kc A0 msg
  have e : B.par.SumHolds = B.Holds :=
    funext fun x => funext fun m => propext (endM_sum E B x m)
  unfold PscPar.baseIn PscPar.baseRels
  rw [e]
  rfl

theorem endM_goodAt : Spec.endM_goodAt E := by
  intro B Ex M Wp Kc A0 msg hB
  rw [endM_joint E]
  exact psc_core_goodAt E B.par Ex M Wp Kc A0 msg (endM_vars E B).1
    (endM_deg E B hB) (endM_vars E B).2

theorem endM_good : Spec.endM_good E := by
  intro B S E₀ Wp Kc A0 msg hB
  rw [endM_joint E]
  exact psc_core_goodB_sig E S B.par E₀ Wp Kc A0 msg (endM_vars E B).1
    (endM_deg E B hB) (endM_vars E B).2

theorem LkEndM.linB (B : LkEndM E) : B.par.LinB B.rowB := by
  intro s m b X
  show Alg.mle (fun b => m (B.tAt b)) (B.fn s X) = ∑ j, B.rowB s b X j * m j
  unfold LkEndM.rowB Alg.mle
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h := Finset.sum_ite_eq Finset.univ (B.tAt c) fun j => Alg.eqk (B.fn s X) c * m j
  rw [if_pos (Finset.mem_univ _)] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  congr

theorem endM_row : Spec.endM_row E := by
  intro B zz m
  haveI hA : IsEmpty B.par.A := inferInstanceAs (IsEmpty Empty)
  have h1 := psc_mid_empty E B.par hA zz m
  have e : (⟨zz.st, zz.eps, zz.pt, zz.fin, isEmptyElim⟩ : B.par.Out) = B.outOf zz := by
    unfold LkEndM.outOf
    congr
    funext a
    exact a.elim
  rw [e] at h1
  exact h1.trans (psc_row_U E B.par B.rowB (B.linB E) (B.outOf zz) m)

theorem endM_tg : Spec.endM_tg E := fun B zz => by
  show zz.fin - zz.eps * 1 = _
  rw [mul_one]

theorem endM_len : Spec.endM_len E := fun B Ex => by
  show (pRound0 E :: (pfMix E B.k B.dg).map pRound).length = _
  simp [mix_len]

theorem endM_errs : Spec.endM_errs E := by
  intro B Ex Kc
  constructor
  · show 1 :: (pErr B.par.fmt).toList = _
    rw [LdLkp.pErr_list]
    exact congrArg (List.cons 1) (mix_degs E B.k B.dg)
  · show Fintype.card E :: (pRounds B.par.fmt).chalList = _
    rw [LdLkp.pRounds_list]
    exact congrArg (List.cons (Fintype.card E)) (mix_chals E B.k B.dg)

end
end Cb

/-! ## 3. The instance: the table side of a lookup, with the order as a parameter -/

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

/-- The degrees: variable i is the tree's coordinate σ i: 1 at a plane's coordinate, 2 at a row's.
-/
def dgEnd (w d : ℕ) (σ : Equiv.Perm (Fin (w + d))) : Fin (w + d) → ℕ := fun i =>
  if (σ i : ℕ) < w then 1 else 2

namespace LkInst
variable {E : Type} [Field E] [Fintype E] (I : LkInst E) [DecidableEq I.J] (n : ℕ)

/-- The closing of the forest's top claim, with a degree for each variable, in the order σ. -/
def endM (σ : Equiv.Perm (Fin (I.w + I.d)))
    (wE : PIdx (pfMix E (I.w + I.d) (dgEnd I.w I.d σ)) → I.J) : LkEndM E where
  X := ((I.DT2 n).lv I.d).T.St
  J := I.J
  k := I.w + I.d
  dg := dgEnd I.w I.d σ
  tAt := fun b => I.tAt fun v => b (σ.symm v)
  z := fun s i => ((I.DT2 n).lv I.d).pnt s (σ i)
  kr := I.d
  rw := fun r => σ.symm (Fin.natAdd I.w r)
  cp := fun s r =>
    I.lam (((I.DT2 n).lv I.d).base s) - 1 - I.tab (I.st (((I.DT2 n).lv I.d).base s)) (numLE r)
  inc := fun s => pushJ ((I.DT2 n).lv I.d).toJ (((I.DT2 n).lv I.d).T.slS s)
  wAt := wE

end LkInst
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp
variable (E : Type) [Field E] [Fintype E]

def instM_ok : Prop := ∀ (I : LkInst E) [DecidableEq I.J] (n : ℕ) σ wE, (I.endM n σ wE).OK

/-- If all 2^w bit positions count (n + 1 = 2^w): the sum claim at the top of the forest is the
closing's claim. -/
def instM_top_iff : Prop :=
  ∀ (I : LkInst E) [DecidableEq I.J] (n : ℕ) σ wE, n + 1 = 2 ^ I.w →
    ∀ (x : E × ((I.DT2 n).lv I.d).T.St) (m : I.J → E),
      ((I.DT2 n).lv I.d).T.SumHolds x (fun j => m (((I.DT2 n).lv I.d).toJ j)) ↔
      (I.endM n σ wE).Holds x m

/-- If all 2^w bit positions count: the tree's joint at level d is the closing's input joint. -/
def instM_top : Prop :=
  ∀ (I : LkInst E) [DecidableEq I.J] (n : ℕ) σ wE, n + 1 = 2 ^ I.w →
    ∀ (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → I.J → E)
      (A0 : Rels Kc ((I.DT2 n).lv 0).T.St Ex (M × Wp)),
    (I.DT2 n).jtAt msg A0 I.d =
      (I.endM n σ wE).relsIn ((I.DT2 n).ride msg A0 I.d) fun w => msg w.1

/-- With σ the reversal (from the top coordinate down): d rounds of degree 2, then w rounds of
degree 1. That this is the programs' order is no part of this statement. -/
def dgEnd_rev : Prop :=
  ∀ w d : ℕ, List.ofFn (dgEnd w d Fin.revPerm) = List.replicate d 2 ++ List.replicate w 1

end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

/-- The number of a corner of w + d coordinates: the first w are the low bits. -/
theorem numLE_split (w d : ℕ) (b : Fin (w + d) → Bool) :
    numLE b = numLE (fun i : Fin w => b (Fin.castAdd d i)) +
      2 ^ w * numLE fun i : Fin d => b (Fin.natAdd w i) := by
  unfold numLE
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.val_natAdd, pow_add]
  split_ifs <;> simp

theorem numLE_div (w d : ℕ) (b : Fin (w + d) → Bool) :
    numLE b / 2 ^ w = numLE fun i : Fin d => b (Fin.natAdd w i) := by
  rw [numLE_split, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
    Nat.div_eq_of_lt (ldLkpNum_lt _ _), Nat.zero_add]

section
variable (E : Type) [Field E] [Fintype E]

theorem instM_ok : Spec.instM_ok E := fun I _ n σ wE =>
  ⟨fun r r' h => Fin.natAdd_injective _ _ (σ.symm.injective h),
    fun r => by
      show 2 ≤ if ((σ (σ.symm (Fin.natAdd I.w r)) : Fin (I.w + I.d)) : ℕ) < I.w then 1 else 2
      rw [Equiv.apply_symm_apply, Fin.val_natAdd, if_neg (by omega)],
    fun i => by
      show 1 ≤ if ((σ i : Fin (I.w + I.d)) : ℕ) < I.w then 1 else 2
      split_ifs <;> omega⟩

theorem instM_top_iff : Spec.instM_top_iff E := by
  intro I _ n σ wE hn x m
  rw [ldLkpP_sum E (I.DT2 n) (ldLkpInst2_step E I n) I.d x m]
  have hU : (I.DT2 n).U (((I.DT2 n).lv I.d).base x.2) m I.d =
      fun c : Fin (I.w + I.d) → Bool =>
        1 + m (I.tAt c) * (I.endM n σ wE).cp x.2 fun r => c (Fin.natAdd I.w r) := by
    funext c
    refine (ldLkpNum_topT E I.w I.d _ _ _ c).trans ?_
    show 1 + (if numLE c % 2 ^ I.w < n + 1 then m (I.bAt (numLE c / 2 ^ I.w) (numLE c % 2 ^ I.w))
            else 0) * _ = _
    rw [if_pos (by rw [hn]; exact Nat.mod_lt _ (Nat.two_pow_pos I.w))]
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

theorem instM_top : Spec.instM_top E := fun I _ n σ wE hn _ _ _ _ msg _ =>
  LdLkp.rels_ext (funext fun x =>
      funext fun _ =>
        funext fun w => propext (and_congr_right fun _ => instM_top_iff E I n σ wE hn x (msg w.1)))
    (funext fun a =>
      funext fun w => propext (and_congr_right fun _ => instM_top_iff E I n σ wE hn a.1 (msg w.1)))
    rfl rfl

end

theorem dgEnd_rev : Spec.dgEnd_rev := by
  intro w d
  apply List.ext_getElem
  · simp [Nat.add_comm]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    have hi : i < w + d := by simpa using h1
    show (if ((Fin.revPerm (⟨i, hi⟩ : Fin (w + d)) : Fin (w + d)) : ℕ) < w then 1 else 2) = _
    have hv : ((Fin.revPerm (⟨i, hi⟩ : Fin (w + d)) : Fin (w + d)) : ℕ) = w + d - (i + 1) := by
      rw [Fin.revPerm_apply, Fin.val_rev]
    rw [hv]
    by_cases hd : i < d
    · rw [List.getElem_append_left (by simpa using hd), List.getElem_replicate, if_neg (by omega)]
    · rw [List.getElem_append_right (by simpa using hd), List.getElem_replicate, if_pos (by omega)]

end Cb
