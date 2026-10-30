-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailRngAt.lean: the caller of the draw of the matrix of a smallness test at the Lean
verifier's own record of that test, and the block there as a value of the kind.

Johnson/Top/H/TailRng.lean has the kind for every caller. OnBytes/Tie/Pv/Tail/SizeOf.lean reads the
sizes off the verifier's record of a smallness test; OnBytes/Tie/Pv/Tail/LettersAt.lean reads the
block's letters off that record and a lay of the committed entries. Here these are put into a
caller. Definitions, statements and proofs.

Main names:
  `tailCallerAt`: the caller: the sizes `(sizeOf tl).size`; the weights, symbols and reads of
    `thetaAt`; a signature Sg with a reading rd of its messages as the early entries.
  `tailCallerAt_mem`: it meets the kind's condition, for every record.
  `tailCallerAt_isOf`: the kind's block at it is a value of the kind.
  `tailCallerAt_relIn`, `tailCallerAt_relOut`: the block's two relations at it are those of
    `thetaAt`'s letters at the early entries that rd reads, by definition.
  `tailBlk_shape`, `tailBlk_err`: the kind's block has the rounds and the errors of the block of
    Cb/Pv/Tail/Block.lean.
  `tailCallerAt_plan`: from an idle state of a plan in writing, if the planner's planRng at the
    record's number of columns ends well: one round is added; the block's rounds have the shape of
    its entry; with one instance the block's error, divided by the number of values, is at most
    its bound. Under: the record's number of matrices is the length of its list, and its tau is
    the number of combinations that follows from the setting.

Limits: Sg, rd, the lay, the explicit statement, the further oracles and what rides stay letters:
which oracle messages a sub-proof has sent before the draw, and that rd reads their entries as the
lay says, is not said. The record must be the one from which the smallness test's messages start:
before the verifier closes its list of tables the sizes have no table
(OnBytes/Tie/Pv/Tail/SizeOf.lean). The weights are those of one record of the verifier: they are the
same at all statements. In the protocol a table's weights hang on points that are drawn in front of
the smallness test, and a block of a proof file stands for all statements: the caller for a file is
`tailCallerOf` (Johnson/Top/H/TailRngOf.lean). No proof file is written here: that a written file
has this block at a place is for whoever writes the file.
At the plan's own record, whose list of tables and list of first columns are
empty, `sizeOf tl` has no table and the clauses on reads say nothing: the caller is meant at a
record in which the tables' shapes and the first columns are laid.
-/
import Johnson.Top.H.TailRng
import OnBytes.Tie.Pv.Tail.LettersAt
import OnBytes.Tie.Pv.Tail.CallRng

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR VerifiableInference.OnPublicFiles OnBytes OnBytes.Model OnBytes.Road.Rows
  OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.Params OnBytes.G4

/-- The kind's block has the rounds of the block at the base. -/
theorem tailBlk_shape (c : TailCaller) :
    (KTailRng.blk c).R.shape = (Cb.Pv.Tail.R c.letters).shape := rfl

/-- And its errors. -/
theorem tailBlk_err (c : TailCaller) : (KTailRng.blk c).err = Cb.Pv.Tail.eps c.letters := rfl

section
variable {J : Type} [Fintype J] (ρ : OnBytes.Model.Reading Cb.Gl.E) (Y : Lay J) (tl : HTailF2)
  (Sg : Sig Cb.Gl.E) (rd : Sg.Msg → JE Y tl → Cb.Gl.E) (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec)
  (W₀ : Type)
  (ride : X × Ex.Str → (JE Y tl → Cb.Gl.E) →
    Cb.Pv.Tail.Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl).size × W₀ → Prop)

local notation "Th" => TLetters.letters (thetaAt ρ Y tl iU3 K3 X Ex W₀ ride)

/-- The caller at the verifier's record. -/
@[reducible] def tailCallerAt : TailCaller where
  s := (OnBytes.Tie.Pv.Tail.sizeOf tl).size
  Sg := Sg
  X := X
  Ex := Ex
  Wp := Cb.Pv.Tail.Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl).size × W₀
  w := (Th).w
  sym := fun m => (Th).sym (rd m)
  tab := fun m => (Th).tab (rd m)
  dig := (Th).dig
  ride := fun a m wp => ride a (rd m) wp

local notation "Ca" => tailCallerAt ρ Y tl Sg rd iU3 K3 X Ex W₀ ride

theorem tailCallerAt_mem : KTailRng.mem (Ca) := sizeOf_ok tl

theorem tailCallerAt_isOf : (KTailRng.blk (Ca)).IsOf KTailRng :=
  ⟨Ca, sizeOf_ok tl, rfl⟩

theorem tailCallerAt_relIn (x : X) (m : Sg.Msg) :
    relIn (Ca).letters x m ↔ relIn (Th) x (rd m) := Iff.rfl

theorem tailCallerAt_relOut (x : X) (β : Dr (OnBytes.Tie.Pv.Tail.sizeOf tl).size) (m : Sg.Msg)
    (Z : Cb.Pv.Tail.Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl).size) :
    relOut (Ca).letters x β m Z ↔ relOut (Th) x β (rd m) Z := Iff.rfl

/-- The block's rounds and errors are the plan's. -/
theorem tailCallerAt_plan (st : Setting) (hn : tl.NM = tl.mats.size)
    (ht : tl.tau = rngCombinations st .request) (p q : PlanState) (hp : Idle st p)
    (h : planRng tl.foldColumns p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st (rngSize st tl.foldColumns)) ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (KTailRng.blk (Ca)).R.shape
        [(rngRound st (rngSize st tl.foldColumns)).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (KTailRng.blk (Ca)).err.toList
            (KTailRng.blk (Ca)).R.shape.chalList)
          [planVal (rngRound st (rngSize st tl.foldColumns)).error]) :=
  call_rng_record tl (Ca).letters st hn ht p q hp h

end

end KObj

#print axioms KObj.tailCallerAt_isOf
#print axioms KObj.tailCallerAt_plan
