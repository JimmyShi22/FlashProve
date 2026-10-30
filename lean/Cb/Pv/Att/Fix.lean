-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Fix.lean: which coefficient a round of a plain sumcheck leaves out.

In the programs a round over a plain variable sends all coefficients of its polynomial but the
linear one, and the round in the further variable all but the constant one; the verifier completes
the polynomial from the running claim without a division (OnBytes/Iop/Psc.lean: Weight.plain has
fixed := 1, fixedInv := 1; Weight.atZero has fixed := 0, fixedInv := 1).

Main names:
  fixPlain: for the library's plain cube variables: the power 1 with the inverse 1 (meant at a
    degree of at least 1).
  fixSnoc: a choice for a list of variables with one more variable at its end.
  PlainSc.fix: the choice for the parameters of Cb/Pv/Att/Plain.lean.
  mon1_plain: the sum of X over a plain variable's two nodes is 1, if its degree is at least 1.
  fixPlain_ok, fixSnoc_ok, plain_fix: the choices are lawful (HFixs.OK).
  plain_out: so the block of Cb/Pv/Att/Ride.lean at this choice rejects no transcript.

Limits. That this is the programs' choice is by reading of the lines cited: no statement here
speaks of the port's routines. Nothing is said on an honest prover or on hiding.

-/
import Cb.Pv.Att.Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E]

theorem mon1_plain (n : ℕ) (h : 1 ≤ n) : ((pfCube E n).var (pdPlain E n)).mon 1 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  show ∑ b : Bool, (1 : E) * (if b then (1 : E) else 0) ^ (((1 : Fin (k + 1 + 1)) : ℕ)) = 1
  rw [Fintype.sum_bool]
  simp

def fixPlain : (k : ℕ) → (n : Fin k → ℕ) →
    HFixs (pVars (ldPartFmt E k n) (ldPartDat E k n fun _ => none))
  | 0, _ => ()
  | k + 1, n => ((1, 1), fixPlain k fun i => n i.succ)

theorem fixPlain_ok : ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 1 ≤ n i) →
    HFixs.OK (pVars (ldPartFmt E k n) (ldPartDat E k n fun _ => none)) (fixPlain k n)
  | 0, _, _ => trivial
  | k + 1, n, h =>
    ⟨by
      show (1 : E) * ((pfCube E (n 0)).var (pdPlain E (n 0))).mon 1 = 1
      rw [one_mul, mon1_plain (n 0) (h 0)],
     fixPlain_ok k (fun i => n i.succ) fun i => h i.succ⟩

def fixSnoc : (l : List (PFmt E)) → (d : PDats l) → (f : PFmt E) → (e : PDat E f) →
    HFixs (pVars l d) → Fin (f.n + 1) × E → HFixs (pVars (l ++ [f]) (PDats.snoc l d f e))
  | [], _, _, _, _, p => (p, ())
  | _ :: l, d, f, e, G, p => (G.1, fixSnoc l d.2 f e G.2 p)

omit [Fintype E] in
theorem fixSnoc_ok : ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f)
    (G : HFixs (pVars l d)) (p : Fin (f.n + 1) × E), HFixs.OK (pVars l d) G →
    p.2 * (f.var e).mon p.1 = 1 →
    HFixs.OK (pVars (l ++ [f]) (PDats.snoc l d f e)) (fixSnoc l d f e G p)
  | [], _, _, _, _, _, _, hp => ⟨hp, trivial⟩
  | _ :: l, d, f, e, G, p, hG, hp => ⟨hG.1, fixSnoc_ok l d.2 f e G.2 p hG.2 hp⟩

/-- The choice: the linear coefficient at a cube variable, the constant one at the further one. -/
noncomputable def PlainSc.fix (T : PlainSc E) : ∀ st, HFixs (T.our.par.vars st) := fun _ =>
  fixSnoc _ T.dat (pDummy E T.DY) (pDummyD E T.DY) (fixPlain T.nv T.deg) (0, 1)

theorem plain_fix (T : PlainSc E) (h : T.OK) : ∀ st, HFixs.OK (T.our.par.vars st) (T.fix st) :=
  fun _ => fixSnoc_ok _ T.dat _ _ _ _ (fixPlain_ok T.nv T.deg h.one) (by
    show (1 : E) * ((pDummy E T.DY).var (pDummyD E T.DY)).mon 0 = 1
    rw [one_mul, mon0_dummy])

/-- At this choice the block rejects nothing. -/
theorem plain_out (T : PlainSc E) (h : T.OK) (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St)
    (Ex : ExtSpec) (x : X) (y : Ex.Str) (τ : Tr (shapeRN T.our.par n)) :
    (rideNR T.our.par n T.fix cl Ex).out x y τ =
      some ((x, riders T.our.par n τ),
        shortV T.our.par T.fix (cl x (riders T.our.par n τ)) (unrideN T.our.par n τ)) :=
  rideN_out T.our.par n T.fix cl Ex (plain_fix T h) x y τ

end Cb.Pv.Att
