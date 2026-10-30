-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailRngOf.lean: the caller of the draw of the matrix of a smallness test at letters in
which the tables' weights hang on the statement.

Johnson/Top/H/TailRngAt.lean has the caller at the letters `thetaAt`
(OnBytes/Tie/Pv/Tail/LettersAt.lean), whose weights are those of one record of the verifier: they
are the same at all statements. In the protocol the weights of a table hang on points that were
drawn in front of the smallness test, and a block of a proof file stands for all statements. The
letters of Cb/Pv/Tail/Tables.lean (`TLetters`) have the weights as a function phi of the statement.
Here the caller is made of any such letters. Definitions, statements and proofs.

Main names:
  `tailCallerOf t Θ Sg rd`: the caller at the sizes t.size and the letters Θ; a signature Sg with a
    reading rd of its messages as Θ's messages.
  `tailCallerOf_w`: its weight of read r of matrix μ on row i at the statement x is
    `wOf t (Θ.phi x) μ r i`.
  `tailCallerOf_mem`, `tailCallerOf_isOf`: under `t.size.OK` it meets the kind's condition, and the
    kind's block at it is a value of the kind.
  `tailCallerOf_relIn`, `tailCallerOf_relOut`: the block's two relations, by definition.
  `tailCallerAt_eq`: the caller of Johnson/Top/H/TailRngAt.lean is this one at `thetaAt`.
  `tailCallerOf_plan`: at t := the sizes of the verifier's record: the block's rounds have the shape
    of the plan's entry, and with one instance its error, divided by the number of values, is at
    most the plan's bound; under the two premises of `tailCallerAt_plan`.

Limits: those of Johnson/Top/H/TailRngAt.lean. Which function phi a sub-proof has is not said.
`tailCallerOf_isOf` holds of every caller that meets the condition: it says nothing of a file.
At the plan's own record, whose list of tables and list of first columns are
empty, `sizeOf tl` has no table and the clauses on reads say nothing: the caller is meant at a
record in which the tables' shapes and the first columns are laid.
-/
import Johnson.Top.H.TailRngAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR VerifiableInference.OnPublicFiles OnBytes OnBytes.Model OnBytes.Road.Rows
  OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.Params OnBytes.G4

section
variable (t : TSize) (Θ : TLetters Cb.Gl.E t) (Sg : Sig Cb.Gl.E) (rd : Sg.Msg → Θ.M)

/-- The caller at letters whose weights hang on the statement. -/
@[reducible] def tailCallerOf : TailCaller where
  s := t.size
  Sg := Sg
  X := Θ.X
  Ex := Θ.E
  Wp := Θ.W
  w := Θ.letters.w
  sym := fun m => Θ.letters.sym (rd m)
  tab := fun m => Θ.letters.tab (rd m)
  dig := Θ.letters.dig
  ride := fun a m wp => Θ.ride a (rd m) wp

theorem tailCallerOf_w (x : Θ.X) (μ : Fin t.size.NM) (r : Fin (t.size.nr μ))
    (i : Fin (t.size.m μ)) : (tailCallerOf t Θ Sg rd).w x μ r i = wOf t (Θ.phi x) μ r i := rfl

theorem tailCallerOf_mem (h : t.size.OK) : KTailRng.mem (tailCallerOf t Θ Sg rd) := h

theorem tailCallerOf_isOf (h : t.size.OK) :
    (KTailRng.blk (tailCallerOf t Θ Sg rd)).IsOf KTailRng := ⟨tailCallerOf t Θ Sg rd, h, rfl⟩

theorem tailCallerOf_relIn (x : Θ.X) (m : Sg.Msg) :
    relIn (tailCallerOf t Θ Sg rd).letters x m ↔ relIn Θ.letters x (rd m) := Iff.rfl

theorem tailCallerOf_relOut (x : Θ.X) (β : Dr t.size) (m : Sg.Msg)
    (Z : Cb.Pv.Tail.Dig Cb.Gl.E t.size) :
    relOut (tailCallerOf t Θ Sg rd).letters x β m Z ↔ relOut Θ.letters x β (rd m) Z := Iff.rfl

end

/-- The caller at one record's weights is this one. -/
theorem tailCallerAt_eq {J : Type} [Fintype J] (ρ : OnBytes.Model.Reading Cb.Gl.E) (Y : Lay J)
    (tl : HTailF2) (Sg : Sig Cb.Gl.E) (rd : Sg.Msg → JE Y tl → Cb.Gl.E) (iU3 K3 : ℕ) (X : Type)
    (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → Cb.Gl.E) →
      Cb.Pv.Tail.Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl).size × W₀ → Prop) :
    tailCallerAt ρ Y tl Sg rd iU3 K3 X Ex W₀ ride =
      tailCallerOf (OnBytes.Tie.Pv.Tail.sizeOf tl) (thetaAt ρ Y tl iU3 K3 X Ex W₀ ride) Sg rd :=
  rfl

/-- The block's rounds and errors against the plan's, at the sizes of the verifier's record. -/
theorem tailCallerOf_plan (tl : HTailF2) (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl))
    (Sg : Sig Cb.Gl.E) (rd : Sg.Msg → Θ.M) (st : Setting) (hn : tl.NM = tl.mats.size)
    (ht : tl.tau = rngCombinations st .request) (p q : PlanState) (hp : Idle st p)
    (h : planRng tl.foldColumns p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (rngSize st tl.foldColumns)) ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (KTailRng.blk (tailCallerOf _ Θ Sg rd)).R.shape
        [(rngRound st (rngSize st tl.foldColumns)).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ))
            (KTailRng.blk (tailCallerOf _ Θ Sg rd)).err.toList
            (KTailRng.blk (tailCallerOf _ Θ Sg rd)).R.shape.chalList)
          [planVal (rngRound st (rngSize st tl.foldColumns)).error]) :=
  call_rng_record tl (tailCallerOf _ Θ Sg rd).letters st hn ht p q hp h

end KObj

#print axioms KObj.tailCallerOf_w
#print axioms KObj.tailCallerOf_isOf
#print axioms KObj.tailCallerAt_eq
#print axioms KObj.tailCallerOf_plan
