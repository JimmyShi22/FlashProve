-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/FlatTie.lean: the verifier's arithmetic in the masked sumcheck
(OnBytes/Iop/Psc.lean), read into a commutative ring, is the step of a sumcheck's verifier on plain
lists of ring elements (`TwV.runVars`, `TwV.takeSc`, Cb/G9/FlatStep.lean; «the flat step» below).

Definitions, and theorems with their proofs. «The program» is the Lean verifier in OnBytes/, as in
OnBytes/Model/HideLaws.lean. All theorems are on the program's own functions: `Psc.polyAt`,
`Psc.dot`, `Psc.Weight.equality`, `Psc.Weight.complete`, `Psc.claimAfter`, `Psc.powers`,
`Psc.hidingWalk`. The verifier's routines in OnBytes/Iop/Psc.lean (`Psc.run`) and for the sub-proofs
(OnBytes/Model/Psc.lean, `pscRound`) both complete a round's polynomial by `Weight.complete` and
read it by `polyAt`. `claimAfter` is called by `Psc.run` alone; it also serves to state the running
claim of the sub-proofs' routine (OnBytes/Tie/Pv/Psc/PscWhole.lean). An element of the program's
field is three words. A reading ρ (`Reading`, OnBytes/Model/HideLaws.lean) maps it into a
commutative ring K and commutes with the arithmetic; `Reading.gl` is the reading into the challenge
field Cb.Gl.E. Every theorem here holds for every reading. The readings of `polyAt` and `dot` are
that file's (`Reading.polyAt`, `Reading.dot`, `dotValue_replicate`).

Main names:
  `evalGo_sumFrom`: the flat step's sum of terms is `sumFrom` of OnBytes/Model/HideLaws.lean.
  `step_eq`: one round. For a variable under equality weights at z whose polynomials have d
    coefficients, a message q of at most d - 1 elements, the running claim R and the challenge g:
    the program's completed polynomial at g reads as (R - z · Σ q) + Σ_t q_t g^(t+1): the flat step.
  `eqW zd`: the weights of a list of pairs (z, d). `flR`: the program's rounds (message, challenge)
    as plain data.
  `claimAfter_eq`: all rounds of the variables: `runVars` on the plain data gives the program's
    running claim after the rounds, read, and the challenges, read; for every list of pairs (z, d)
    and every list of as many rounds whose messages fit.
  `Fits zd rs`: as many rounds as variables; each message has exactly d - 1 elements.
  `flH`, `takeSc_eq`: one sumcheck: from the sum of the hiding polynomial, eps, the rounds and the
    shown values as plain data, `takeSc` gives eps, the challenges, the program's last claim and the
    values, all read, and hands back what follows.
  `powers_eq`, `walkK`, `hidingWalk_eq`: what `hidingWalk` computes at equality weights: the weights
    g^t of the hiding polynomial's coefficients in the program's order, and the product of the
    public polynomials, which reads 1.

Limits: equality weights alone (the variable Y is the case z = 0): a lookup has no other. In the
plain data (`flH`) the sum of the hiding polynomial is alone in its message; a sumcheck whose caller
has received elements of that message before the sum is not reached. Nothing on soundness, on an
honest prover or on hiding.


-/
import OnBytes.Model.HideLaws
import Cb.G9.FlatStep
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscTie
open OnBytes OnBytes.Psc OnBytes.Model TwV

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The flat step's sum of terms, from degree t + 1 up, is `sumFrom` of the read coefficients. -/
theorem evalGo_sumFrom (g : E) : ∀ (q : List E) (t : ℕ),
    evalGo (ρ.val g) t (q.map ρ.val) = sumFrom (fun i c => ρ.val c * ρ.val g ^ i) (t + 1) q
  | [], _ => rfl
  | c :: q, t => by
    show ρ.val c * ρ.val g ^ (t + 1) + evalGo (ρ.val g) (t + 1) (q.map ρ.val) =
      ρ.val c * ρ.val g ^ (t + 1) + sumFrom (fun i c => ρ.val c * ρ.val g ^ i) (t + 1 + 1) q
    rw [evalGo_sumFrom g q (t + 1)]

/-- What the program completes at equality weights. -/
theorem complete_equality (z : E) (d : ℕ) (q : List E) (R : E) :
    (Weight.equality z d).complete q R =
      mulE (subE R (dot (oneE :: List.replicate (d - 1) z) (zeroE :: q))) oneE :: q := rfl

/-- One round. -/
theorem step_eq (z : E) (d : ℕ) (q : List E) (R g : E) (h : q.length + 1 ≤ d) :
    ρ.val (polyAt ((Weight.equality z d).complete q R) g) =
      (ρ.val R - ρ.val z * (q.map ρ.val).sum) + evalGo (ρ.val g) 0 (q.map ρ.val) := by
  have hp := ρ.polyAt g ((Weight.equality z d).complete q R) 0
  rw [pow_zero, one_mul] at hp
  rw [← hp, complete_equality, evalGo_sumFrom]
  have hd : dotValue ρ (oneE :: List.replicate (d - 1) z) (zeroE :: q) =
      ρ.val z * (q.map ρ.val).sum := by
    have hr := dotValue_replicate ρ z (d - 1) q (by omega)
    simp only [dotValue, List.zip_cons_cons, List.map_cons, List.sum_cons, ρ.zero, mul_zero,
      zero_add] at hr ⊢
    exact hr
  show ρ.val (mulE (subE R (dot (oneE :: List.replicate (d - 1) z) (zeroE :: q))) oneE) *
      ρ.val g ^ 0 + sumFrom (fun i c => ρ.val c * ρ.val g ^ i) (0 + 1) q = _
  rw [ρ.mul, ρ.sub, ρ.one, ρ.dot, hd, pow_zero, mul_one, mul_one]

/-- The weights of a list of pairs (point's coordinate, number of coefficients). -/
def eqW (zd : List (E × ℕ)) : List Weight := zd.map fun p => Weight.equality p.1 p.2

/-- The program's rounds as plain data. -/
def flR (rs : List (List E × E)) : Rounds K := rs.map fun r => (r.1.map ρ.val, [ρ.val r.2])

/-- As many rounds as variables, and each message has one element less than its variable has
coefficients: what the program tests of a round. -/
def Fits : List (E × ℕ) → List (List E × E) → Prop
  | [], [] => True
  | p :: zd, r :: rs => r.1.length + 1 = p.2 ∧ Fits zd rs
  | _, _ => False

/-- One round of `claimAfter`. -/
theorem claimAfter_cons (w : Weight) (ws : List Weight) (q : List E) (g : E)
    (rs : List (List E × E)) (R : E) :
    claimAfter (w :: ws) ((q, g) :: rs) R = claimAfter ws rs (polyAt (w.complete q R) g) := by
  rw [claimAfter]

/-- One variable of `runVars`. -/
theorem runVars_cons (σ z : K) (zs : List K) (r : List K × List K) (rs : Rounds K) :
    runVars σ (z :: zs) (r :: rs) =
      ((runVars ((σ - z * r.1.sum) + evalGo (r.2.headD 0) 0 r.1) zs rs).1,
        r.2.headD 0 :: (runVars ((σ - z * r.1.sum) + evalGo (r.2.headD 0) 0 r.1) zs rs).2) := by
  rw [runVars]

/-- `runVars` without a variable hands the claim back. -/
theorem runVars_nil (σ : K) (rs : Rounds K) : runVars σ [] rs = (σ, []) := by
  rw [runVars]
  intro _ _ _ _ h
  exact absurd h (by simp)

/-- All rounds of the variables. -/
theorem claimAfter_eq (zd : List (E × ℕ)) : ∀ (rs : List (List E × E)) (R : E) (rest : Rounds K),
    Fits zd rs →
    runVars (ρ.val R) (zd.map fun p => ρ.val p.1) (flR ρ rs ++ rest) =
      (ρ.val (claimAfter (eqW zd) rs R), rs.map fun r => ρ.val r.2) := by
  induction zd with
  | nil =>
    intro rs R rest h
    cases rs with
    | nil =>
      rw [List.map_nil, runVars_nil, eqW, List.map_nil, claimAfter]
      · rfl
      · intro _ _ _ _ _ h
        exact absurd h (by simp)
    | cons _ _ => exact h.elim
  | cons p zd ih =>
    intro rs R rest h
    cases rs with
    | nil => exact h.elim
    | cons r rs =>
      obtain ⟨q, g⟩ := r
      have e1 : eqW (p :: zd) = Weight.equality p.1 p.2 :: eqW zd := by
        simp only [eqW, List.map_cons]
      have e2 : flR ρ ((q, g) :: rs) ++ rest = (q.map ρ.val, [ρ.val g]) :: (flR ρ rs ++ rest) := by
        simp only [flR, List.map_cons, List.cons_append]
      rw [e1, e2, claimAfter_cons, List.map_cons, runVars_cons, List.map_cons]
      simp only [List.headD_cons]
      rw [← step_eq ρ p.1 p.2 q R g (Nat.le_of_eq h.1), ih rs _ rest h.2]

/-- Where the rounds fit there are as many variables as rounds. -/
theorem Fits.length : ∀ {zd : List (E × ℕ)} {rs : List (List E × E)}, Fits zd rs →
    zd.length = rs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (Fits.length h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- One sumcheck as plain data: the sum of the hiding polynomial and eps; the rounds; the shown
values, if there are any. -/
def flH (mu eps : E) (rs : List (List E × E)) (values : Option (List E)) : Rounds K :=
  ([ρ.val mu], [ρ.val eps]) :: (flR ρ rs ++ match values with
    | none => []
    | some v => [(v.map ρ.val, [])])

/-- One sumcheck. -/
theorem takeSc_eq (zd : List (E × ℕ)) (mu eps target : E) (rs : List (List E × E))
    (values : Option (List E)) (rest : Rounds K) (h : Fits zd rs) :
    takeSc (flH ρ mu eps rs values ++ rest) (ρ.val target) (zd.map fun p => ρ.val p.1)
        values.isSome =
      (⟨ρ.val eps, rs.map fun r => ρ.val r.2,
          ρ.val (claimAfter (eqW zd) rs (addE mu (mulE eps target))),
          (values.getD []).map ρ.val⟩, rest) := by
  have hl : (zd.map fun p => ρ.val p.1).length = (flR ρ rs).length := by
    simp [flR, h.length]
  cases values with
  | none =>
    have hr := claimAfter_eq ρ zd rs (addE mu (mulE eps target)) rest h
    rw [ρ.add, ρ.mul] at hr
    unfold takeSc flH
    simp only [List.append_nil, List.cons_append, List.headD_cons, List.tail_cons, hr,
      Option.isSome_none, Bool.false_eq_true, if_false, Option.getD_none, List.map_nil]
    refine Prod.ext rfl ?_
    show ((([ρ.val mu], [ρ.val eps]) : List K × List K) :: (flR ρ rs ++ rest)).drop
      (1 + (zd.map fun p => ρ.val p.1).length + 0) = rest
    rw [hl, show 1 + (flR ρ rs).length + 0 = (flR ρ rs).length + 1 by omega, List.drop_succ_cons]
    simp
  | some v =>
    have hr := claimAfter_eq ρ zd rs (addE mu (mulE eps target)) ((v.map ρ.val, []) :: rest) h
    rw [ρ.add, ρ.mul] at hr
    unfold takeSc flH
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.headD_cons,
      List.tail_cons, hr, Option.isSome_some, if_true, Option.getD_some]
    refine Prod.ext (congrArg (fun b : List K => (⟨ρ.val eps, _, _, b⟩ : Sc K)) ?_) ?_
    · show (((([ρ.val mu], [ρ.val eps]) : List K × List K) ::
        (flR ρ rs ++ (v.map ρ.val, []) :: rest)).getD
        (1 + (zd.map fun p => ρ.val p.1).length) ([], [])).1 = _
      rw [hl, Nat.add_comm 1, List.getD_cons_succ, List.getD_append_right _ _ _ _ (le_refl _),
        Nat.sub_self]
      rfl
    · show ((([ρ.val mu], [ρ.val eps]) : List K × List K) ::
        (flR ρ rs ++ (v.map ρ.val, []) :: rest)).drop
        (1 + (zd.map fun p => ρ.val p.1).length + 1) = rest
      rw [hl, show 1 + (flR ρ rs).length + 1 = ((flR ρ rs).length + 1) + 1 by omega,
        List.drop_succ_cons]
      simp

/-! ## The hiding polynomial's linear form -/

theorem powersLoop_eq (x : E) : ∀ (n : ℕ) (c : E) (done : List E),
    (Psc.powersLoop x n c done).map ρ.val =
      (done.reverse.map ρ.val) ++ (List.range n).map fun t => ρ.val c * ρ.val x ^ t
  | 0, c, done => by simp [Psc.powersLoop]
  | n + 1, c, done => by
    rw [Psc.powersLoop, powersLoop_eq x n (mulE c x) (c :: done), List.reverse_cons,
      List.map_append, List.append_assoc, List.range_succ_eq_map]
    congr 1
    simp only [List.map_cons, List.map_nil, List.singleton_append, pow_zero, mul_one, List.map_map,
      List.cons.injEq, true_and]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp, ρ.mul, Nat.succ_eq_add_one]
    ring

/-- The program's list c, c x, c x², .., read. -/
theorem powers_eq (c x : E) (n : ℕ) :
    (Psc.powers c x n).map ρ.val = (List.range n).map fun t => ρ.val c * ρ.val x ^ t := by
  unfold Psc.powers
  rw [powersLoop_eq]
  rfl

/-- The weights of the hiding polynomial's coefficients at the challenges, where every public
polynomial is 1: from pairs (number of coefficients d, challenge g), in the program's order: by
variable, then by degree upwards from 1; the last variable with its constant first. -/
def walkK : List (ℕ × K) → List K
  | [] => []
  | [(d, g)] => (List.range d).map fun t => g ^ t
  | (d, g) :: q :: r => ((List.range (d - 1)).map fun t => g ^ (t + 1)) ++ walkK (q :: r)

/-- At equality weights the public polynomial reads 1 at every challenge. -/
theorem psi_equality (z : E) (d : ℕ) (g : E) : ρ.val (polyAt (Weight.equality z d).psi g) = 1 := by
  show ρ.val (addE (mulE zeroE g) oneE) = 1
  rw [ρ.add, ρ.mul, ρ.zero, ρ.one, zero_mul, zero_add]

/-- What the program's `hidingWalk` computes at equality weights. -/
theorem hidingWalk_eq : ∀ (l : List ((E × ℕ) × E)),
    ((hidingWalk (l.map fun p => (Weight.equality p.1.1 p.1.2, p.2))).1.map ρ.val =
        walkK (l.map fun p => (p.1.2, ρ.val p.2))) ∧
      ρ.val (hidingWalk (l.map fun p => (Weight.equality p.1.1 p.1.2, p.2))).2 = 1
  | [] => ⟨rfl, ρ.one⟩
  | [p] => by
    refine ⟨?_, psi_equality ρ p.1.1 p.1.2 p.2⟩
    show (Psc.powers oneE p.2 p.1.2).map ρ.val = _
    rw [powers_eq]
    simp only [ρ.one, one_mul]
    rfl
  | p :: q :: r => by
    obtain ⟨h1, h2⟩ := hidingWalk_eq (q :: r)
    constructor
    · show (Psc.powers (mulE (hidingWalk ((q :: r).map fun p =>
          (Weight.equality p.1.1 p.1.2, p.2))).2 p.2) p.2 (p.1.2 - 1) ++
        (hidingWalk ((q :: r).map fun p => (Weight.equality p.1.1 p.1.2, p.2))).1).map ρ.val = _
      rw [List.map_append, h1, powers_eq, ρ.mul, h2, one_mul]
      show _ = ((List.range (p.1.2 - 1)).map fun t => ρ.val p.2 ^ (t + 1)) ++ _
      congr 1
      refine List.map_congr_left fun t _ => ?_
      ring
    · show ρ.val (mulE (hidingWalk ((q :: r).map fun p =>
          (Weight.equality p.1.1 p.1.2, p.2))).2 (polyAt (Weight.equality p.1.1 p.1.2).psi p.2)) = 1
      rw [ρ.mul, h2, psi_equality, one_mul]

end OnBytes.PscTie

#print axioms OnBytes.PscTie.step_eq
#print axioms OnBytes.PscTie.claimAfter_eq
#print axioms OnBytes.PscTie.takeSc_eq
#print axioms OnBytes.PscTie.hidingWalk_eq
