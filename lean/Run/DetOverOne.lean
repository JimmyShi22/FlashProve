-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DetOverOne.lean: the run of an algorithm over the single oracle is its run over the family of
typed oracles that the encoding of the queries reads out of that oracle.

Theorems, for the run "every coin toss yields 0" (Rom/Cache.lean: `OComp.det`). Generic. An
encoding of the queries is `m : OracleCoding S lam` (Rom/Family.lean): an answer of a typed oracle is cut
into blocks of lam bits, and block j of the answer of o at q is the single oracle's answer at the
string m.code o q j. `c.overOne m` is c with each typed query replaced by the queries for all its
blocks; `c.overOneN m need` (Rom/OverOneN.lean) asks for the blocks that need marks.

Why: Rom/Prefix.lean has this for the law of the run (`runEager_overOne`). A verifier tosses no
coin, and a run on a file needs the value.

Main names:
  `det_overOne`: (c.overOne m).det g = c.det (readBlocks m g).
  `readSome m need g`: the family that is read out when only the needed blocks are asked: the fixed
    digest stands at the others.
  `det_overOneN`: (c.overOneN m need).det g = c.det (readSome m need g).
So a run with typed oracles and the run over a single oracle give the same answer, if the first
run's family is the family read out.

Limits: this file does not say which encoding, which oracle. It does not say that the algorithm's
answer does not hang on the blocks that are not asked (Rom/OverOneN.lean has the condition for
that).
-/
import Rom.Prefix
import Rom.OverOneN
import Rom.Cache

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {lam : ℕ} {α : Type}

theorem det_askAll (g : Fam (rom lam)) :
    ∀ (n : ℕ) (pts : Fin n → List Bool), (askAll lam n pts).det g = fun j => g () (pts j)
  | 0, _ => funext fun j => j.elim0
  | n + 1, pts => by
      show ((askAll lam n fun i => pts i.succ).bind fun rest =>
          OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) (g () (pts 0)) rest)).det g = _
      rw [OComp.det_bind, det_askAll g n]
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- Over the one oracle, all blocks asked: the result (`det`) is that over `readBlocks m g`. -/
theorem det_overOne (m : OracleCoding S lam) (g : Fam (rom lam)) (c : OComp S α) :
    (c.overOne m).det g = c.det (readBlocks m g) := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact ih 0
  | query o q k ih =>
      show ((askAll lam (m.blocks o) (m.code o q)).bind fun bs =>
          (k ((m.rng o).symm bs)).overOne m).det g = _
      rw [OComp.det_bind, det_askAll, ih]
      rfl

/-- The family that is read out when only the needed blocks are asked; the fixed digest `dig0 lam`
stands at the others. -/
def readSome (m : OracleCoding S lam) (need : Need m) (g : Fam (rom lam)) : Fam S :=
  fun o q => (m.rng o).symm fun j => if need o q j = true then g () (m.code o q j) else dig0 lam

theorem det_askSome (g : Fam (rom lam)) :
    ∀ (n : ℕ) (nd : Fin n → Bool) (pts : Fin n → List Bool),
      (askSome lam n nd pts).det g = fun j => if nd j = true then g () (pts j) else dig0 lam
  | 0, _, _ => funext fun j => j.elim0
  | n + 1, nd, pts => by
      cases h : nd 0 with
      | true =>
          rw [askSome, h]
          show ((askSome lam n (fun i => nd i.succ) fun i => pts i.succ).bind fun rest =>
              OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) (g () (pts 0)) rest)).det g = _
          rw [OComp.det_bind, det_askSome g n]
          funext j
          refine Fin.cases ?_ (fun i => ?_) j
          · show g () (pts 0) = if nd 0 = true then g () (pts 0) else dig0 lam
            rw [if_pos h]
          · rfl
      | false =>
          rw [askSome, h]
          show ((askSome lam n (fun i => nd i.succ) fun i => pts i.succ).bind fun rest =>
              OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) (dig0 lam) rest)).det g = _
          rw [OComp.det_bind, det_askSome g n]
          funext j
          refine Fin.cases ?_ (fun i => ?_) j
          · show dig0 lam = if nd 0 = true then g () (pts 0) else dig0 lam
            rw [if_neg (by rw [h]; exact Bool.false_ne_true)]
          · rfl

/-- Over the one oracle, the needed blocks alone asked: the result (`det`) is that over
`readSome m need g`. -/
theorem det_overOneN (m : OracleCoding S lam) (need : Need m) (g : Fam (rom lam)) (c : OComp S α) :
    (c.overOneN m need).det g = c.det (readSome m need g) := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact ih 0
  | query o q k ih =>
      show ((askSome lam (m.blocks o) (need o q) (m.code o q)).bind fun bs =>
          (k ((m.rng o).symm bs)).overOneN m need).det g = _
      rw [OComp.det_bind, det_askSome, ih]
      rfl

end Rom
