-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/CallRng.lean: the planner's routine planRng, by itself, and the typed reduction
that has its round.

A schedule of a chain can be written as a list of calls of the planner's named routines. The draw of
the matrix of a smallness test is then the call planRng columns. That routine takes one number, the
columns of all matrices together. The number of combinations is not among its arguments: it follows
from the setting and the scope (rngCombinations). OnBytes/Tie/Pv/Tail/Plan.lean speaks of planSmall,
which first compares that number with the sub-proof's tau and then calls planRng. This file says the
same of planRng alone, and lays a typed reduction beside it. Definitions, statements and proofs.

Main names:
  `rngSize st c`: the sizes at which planRng c works under the setting st: c columns, and as many
    combinations as follow from st in a request's scope.
  `rng_runs`: from an idle state planRng c ends well only in an idle state and adds just the round
    rngRound st (rngSize st c).
  `rngRound_congr`: the round reads the columns and the combinations of a record, nothing else.
  `rngIOR st c X E`: the library's reduction that draws a coefficient for each of the
    c * rngCombinations st .request entries and puts what is drawn beside the explicit statement.
  `call_rng`: from an idle state, if planRng c ends well: the state is idle again; one round is
    added; the rounds of rngIOR have the shape of its entry; with one instance the error "one part
    in 2 ^ tau of all values", divided by the number of values, is at most its bound.
  `call_rng_block`: the same of the block of Cb/Pv/Tail/Block.lean at sizes s, if s has c columns in
    all and as many combinations as follow from st.
  `call_rng_record`: the same at the sizes read off a record of the Lean verifier (sizeOf), if its
    number of matrices is the length of its list and its tau is what follows from st.

Limits: nothing here says that a reduction is sound at this error. rngIOR knows the number of drawn
entries and no more: which entry belongs to which matrix, column and combination, how many rows a
matrix has, what is read of it, the radix, the digits' tables and the shift are no arguments of
planRng: whoever wants the block's relations at a call must bring the sizes s with the two equations
of call_rng_block. At a bare call of planRng nothing compares a sub-proof's tau with the number that
follows from the setting: that test stands in planSmall (OnBytes/Params/SubRounds.lean), in front of
its call of planRng. So the equation on tau in call_rng_block and call_rng_record is a premise that
the caller must bring. The shape is the one before proof of work is added.
-/
import OnBytes.Tie.Pv.Tail.SizeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes OnBytes.Model OnBytes.Params OnBytes.G4 Cb.Pv.Tail

/-- The sizes at which planRng c works under the setting st. -/
def rngSize (st : Setting) (c : ℕ) : SmallSize :=
  { columns := c, tau := rngCombinations st .request, digits := default }

/-- The routine planRng by itself. -/
theorem rng_runs (st : Setting) (c : ℕ) (p q : PlanState) (hp : Idle st p)
    (h : planRng c p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (rngSize st c)) := by
  have h' : (theSetting >>= fun s2 => theScope >>= fun c2 =>
      needs (rngCombinations s2 c2 == 0 ||
        decide (c ≤ (2 ^ 64 - 1 - 31) / rngCombinations s2 c2)) >>= fun _ =>
      close "RNG" .small (Bound.exact (Binary.twoTo (-(rngCombinations s2 c2 : Int))))
        { trits := c * rngCombinations s2 c2, combinations := rngCombinations s2 c2,
          priced := .asSaid }) p = .ok ((), q) := h
  obtain ⟨s2, m4, g4, k4⟩ := plan_bind h'
  obtain ⟨rfl, rfl⟩ : p.set = s2 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  obtain ⟨c2, m5, g5, k5⟩ := plan_bind k4
  obtain ⟨rfl, rfl⟩ : p.scope = c2 ∧ p = m5 := Prod.mk.inj (Except.ok.inj g5)
  obtain ⟨_, m6, g6, k6⟩ := plan_bind k5
  obtain ⟨_, rfl⟩ := needs_ok g6
  have e : rngCombinations p.set p.scope = (rngSize st c).tau := by
    rw [hp.set, hp.scope]
    rfl
  rw [e] at k6
  obtain ⟨a, r, _⟩ := close_rng (x := rngSize st c) hp k6
  exact ⟨a, r⟩

/-- The round reads the columns and the combinations of a record, nothing else. -/
theorem rngRound_congr (st : Setting) {x y : SmallSize} (h1 : x.columns = y.columns)
    (h2 : x.tau = y.tau) : rngRound st x = rngRound st y := by
  simp only [rngRound, rngError, rngDraws, h1, h2]

/-- The reduction that draws the entries of the call planRng c under the setting st. -/
def rngIOR (st : Setting) (c : ℕ) (X : Type) (E : ExtSpec) :
    IOR X E (X × (Fin (c * rngCombinations st .request) → Prob.Coef)) E :=
  IOR.draw (Fin (c * rngCombinations st .request) → Prob.Coef) Prod.mk E

/-- The call planRng c and the reduction rngIOR. -/
theorem call_rng (st : Setting) (c : ℕ) (X : Type) (E : ExtSpec) (p q : PlanState)
    (hp : Idle st p) (h : planRng c p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (rngSize st c)) ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (rngIOR st c X E).shape [(rngRound st (rngSize st c)).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ))
            (drawErr (Fin (c * rngCombinations st .request) → Prob.Coef) (rngSize st c)).toList
            (rngIOR st c X E).shape.chalList)
          [planVal (rngRound st (rngSize st c)).error]) := by
  obtain ⟨a, r⟩ := rng_runs st c p q hp h
  have hD : Nonempty ((Fin (c * rngCombinations st .request) → Prob.Coef) ≃
      (Fin ((rngSize st c).columns * (rngSize st c).tau) → Prob.Coef)) := ⟨Equiv.refl _⟩
  refine ⟨a, r, List.Forall₂.cons (rngIs_toAll Cb.Gl.E Cb.Gl.F (round_is _ _ hD st))
    List.Forall₂.nil, fun hi => ?_⟩
  show List.Forall₂ (· ≤ ·) (List.zipWith _ (drawErr _ (rngSize st c)).toList
    (Shape.chalList [IOR.drawRound (Fin (c * rngCombinations st .request) → Prob.Coef)])) _
  rw [err_list _ _ hD, chal_list _ _ hD]
  exact List.Forall₂.cons (rngCount_val_le st (rngSize st c) hi) List.Forall₂.nil

/-- The call planRng c and the block at sizes with c columns and the setting's combinations. -/
theorem call_rng_block {K : Type} {s : Size} (Λ : Letters K s) (st : Setting) (c : ℕ)
    (hc : s.columns = c) (ht : s.tau = rngCombinations st .request) (p q : PlanState)
    (hp : Idle st p) (h : planRng c p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (rngSize st c)) ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(rngRound st (rngSize st c)).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
          [planVal (rngRound st (rngSize st c)).error]) := by
  obtain ⟨a, r⟩ := rng_runs st c p q hp h
  have e : rngRound st (smallOf s default) = rngRound st (rngSize st c) :=
    rngRound_congr st hc ht
  have hD : Nonempty (Dr s ≃
      (Fin ((smallOf s default).columns * (smallOf s default).tau) → Prob.Coef)) :=
    ⟨flatPort s⟩
  rw [← e]
  rw [← e] at r
  refine ⟨a, r, List.Forall₂.cons (rngIs_toAll Cb.Gl.E Cb.Gl.F (round_is _ _ hD st))
    List.Forall₂.nil, fun hi => ?_⟩
  show List.Forall₂ (· ≤ ·) (List.zipWith _ (drawErr (Dr s) (smallOf s default)).toList
    (Shape.chalList [IOR.drawRound (Dr s)])) _
  rw [err_list _ _ hD, chal_list _ _ hD]
  exact List.Forall₂.cons (rngCount_val_le st (smallOf s default) hi) List.Forall₂.nil

/-- The same at the sizes read off a record of the Lean verifier. -/
theorem call_rng_record {K : Type} (tl : HTailF2) (Λ : Letters K (sizeOf tl).size) (st : Setting)
    (hn : tl.NM = tl.mats.size) (ht : tl.tau = rngCombinations st .request) (p q : PlanState)
    (hp : Idle st p) (h : planRng tl.foldColumns p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (rngSize st tl.foldColumns)) ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(rngRound st (rngSize st tl.foldColumns)).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
          [planVal (rngRound st (rngSize st tl.foldColumns)).error]) :=
  call_rng_block Λ st tl.foldColumns (sizeOf_columns tl hn) ht p q hp h

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rng_runs
#print axioms OnBytes.Tie.Pv.Tail.call_rng
#print axioms OnBytes.Tie.Pv.Tail.call_rng_block
#print axioms OnBytes.Tie.Pv.Tail.call_rng_record
