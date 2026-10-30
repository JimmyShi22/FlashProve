-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/TestChain.lean: a test of Cb/Pv/Att/Chain.lean at a closed toy: a chain of one draw and
one sumcheck whose conditions are proved and whose claim at the start is an equation on two entries.

Definitions, statements and proofs. The toy. The messages are five entries. A statement is a pair of
targets (t₀, t₁). The claim at the start: entry 0 is t₀ and entry 1 is t₁. The verifier draws β. The
sumcheck has no variable but the dummy one; its one map is entry 0 + β · entry 1, and its target is
t₀ + β t₁. Entries 2 and 3 are the places of the hiding polynomial's coefficients, entry 4 that of
the map's mask.

Main names:
  `toy E`: the chain. `toy_ok`: its conditions (`Ch.OK`), with the count 1 at the draw by `law_pow`.
  `toy_next`: the claim behind the draw says: entry 0 + β · entry 1 = t₀ + β t₁.
  `toy_todo`: the claim at the start. `toy_turn`: it fails as soon as entry 0 is turned.
  `toy_knowAt`: `Ch.knowAt` at the toy, without a premise.

Limits: a test at one toy. Nothing on an honest prover or on zero knowledge.

-/
import Cb.Pv.Att.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.TestChain
open Iop Prob Cb IOR TWhole Johnson.L5.Layers

variable (E : Type) [Field E] [Fintype E]

/-- The toy's sumcheck: no cube variable; the state is β; one map: entry 0 + β · entry 1. -/
def toyT : PlainSc E where
  nv := 0
  deg := fun i => i.elim0
  A := Unit
  DY := 1
  St := E
  J := Fin 5
  map := fun β m _ _ => m 0 + β * m 1
  S := fun _ _ v => v ()
  inc := fun _ _ => 0
  wAt := fun i => match (show Fin 1 ⊕ Unit from i) with
    | .inl _ => 2
    | .inr _ => 3
  cAt := fun _ => 4

theorem toyT_ok : (toyT E).OK where
  one := fun i => i.elim0
  degX := fun (β : E) (m : Fin 5 → E) (u : Unit → E) => by
    show Alg.DegLE _ fun _ => m 0 + β * m 1 + u ()
    exact Alg.DegLE.const _ _
  degY := fun _ _ v u => ⟨![v (), u ()], fun y => by
    show v () + u () * y = hev ![v (), u ()] y
    simp [hev, Fin.sum_univ_two, mul_comm]⟩

/-- The sumcheck's letters, at statements ((t₀, t₁), β). -/
def toyS : SumL E (Fin 5 → E) ((E × E) × E) :=
  ⟨toyT E, toyT_ok E, 0, fun x _ => (x.1.1 + x.2 * x.1.2, x.2), fun m => m, fun _ _ _ => True⟩

/-- The chain: a draw, then the sumcheck. -/
noncomputable def toy : Ch E (Fin 5 → E) (E × E) :=
  .draw (drE E) 1 (fun x m => m 0 = x.1 ∧ m 1 = x.2) ((toyS E).stage (toyS E).Out (.done _))

/-- The claim behind the draw. -/
theorem toy_next (x : (E × E) × E) (m : Fin 5 → E) :
    ((toyS E).stage (toyS E).Out (.done _)).Todo x m ↔ m 0 + x.2 * m 1 = x.1.1 + x.2 * x.1.2 := by
  have hs : (toyT E).our.par.SumHolds (x.1.1 + x.2 * x.1.2, x.2) m ↔
      m 0 + x.2 * m 1 = x.1.1 + x.2 * x.1.2 := by
    refine (plain_sum (toyT E) (x.1.1 + x.2 * x.1.2, x.2) m).trans ?_
    show ∑ _b : Fin 0 → Bool, (m 0 + x.2 * m 1) + ∑ j : Fin 5, (0 : E) * m j = _ ↔ _
    simp
  constructor
  · rintro ⟨_, _, h, _⟩
    exact hs.1 h
  · intro h
    exact ⟨fun i => i.elim0, trivial, hs.2 h,
      ⟨x.2, 0, (show E × Unit from (0, ())), 0, fun _ => 0⟩, trivial⟩

theorem toy_ok : (toy E).OK :=
  ⟨law_pow 2 (fun (x : E × E) (m : Fin 5 → E) => ![m 0 - x.1, m 1 - x.2]) (fun _ _ => True)
      (fun x m => m 0 = x.1 ∧ m 1 = x.2) ((toyS E).stage (toyS E).Out (.done _)).Todo
      (fun x m h _ => ⟨sub_eq_zero.1 (h 0), sub_eq_zero.1 (h 1)⟩)
      (fun x β m h => ⟨by
        have h2 : m 0 + β * m 1 = x.1 + β * x.2 := (toy_next E (x, β) m).1 h
        show ∑ b : Fin 2, β ^ (b : ℕ) * (![m 0 - x.1, m 1 - x.2] : Fin 2 → E) b = 0
        simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination h2, trivial⟩),
    (toyS E).stage_ok _ _ (fun _ _ h1 _ => h1) trivial⟩

/-- The claim at the start. -/
theorem toy_todo (x : E × E) (m : Fin 5 → E) : (toy E).Todo x m ↔ m 0 = x.1 ∧ m 1 = x.2 := Iff.rfl

/-- It fails as soon as entry 0 is turned. -/
theorem toy_turn (x : E × E) (m : Fin 5 → E) (d : E) (hd : d ≠ 0) (h : (toy E).Todo x m) :
    ¬ (toy E).Todo x (Function.update m 0 (m 0 + d)) := fun h' => by
  have h1 : m 0 + d = x.1 := by simpa using h'.1
  exact hd (by rw [h.1] at h1; simpa using h1)

/-- Knowledge soundness at the toy, without a premise. -/
theorem toy_knowAt (Ex : ExtSpec) {Kc Wp : Type} (A0 : Rels Kc (E × E) Ex ((Fin 5 → E) × Wp)) :
    KnowAt ((toy E).R Ex) (jt A0 (fun x => x) fun x m => True ∧ (toy E).Todo x m)
      (jt A0 (fun e => (toy E).back e) ((toy E).Last fun _ _ => True)) (fun _ _ _ wp => wp)
      ((toy E).eps Ex) :=
  Ch.knowAt Ex A0 (toy E) (fun x => x) (fun _ _ => True) (toy_ok E)

/-- Its errors. -/
theorem toy_nums (Ex : ExtSpec) : errList ((toy E).eps Ex) = [1, 1, 1, 0] := by
  rw [Ch.errList_eps]
  show [1] ++ ((toyS E).stage (toyS E).Out (.done _)).nums = _
  rw [SumL.stage_nums]
  rfl

end Cb.Pv.Att.TestChain
