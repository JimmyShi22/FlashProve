-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumKeep.lean: the prover's side of the masked sumcheck with a state
that is kept from round to round. `sumPart` (Honest/Sum.lean) gives its caller's functions the
input and the challenges again in every round, so a caller that sums over tables computes them
again in every round. `keepPart` sends the same messages and passes the caller's tables on from
round to round. Executable definitions, and one definition that is meant as a hypothesis. No theorem
is stated.

How it relates to Honest/Sum.lean. That file is unchanged. `keepPart` is `sumPart` at a job that
reads the kept state, with the second half of each move (`Move.hand`, what is passed on after the
round's challenge) replaced. No message of the masked sumcheck is written a second time here. That
the two parts send the same messages under `KeepJob.Faithful` is not proved in this file.

  1  `Front.outer`   what is before a part, without the kept state
  2  `KeepJob`, `KeepJob.madeAt`, `KeepJob.keptAt`, `KeepJob.job`   what the caller supplies; the
     kept state computed from the start; the kept state as a round reads it; the job for `sumPart`
  3  `KeepJob.pass`, `withPass`, `keepPart`   what is passed on after each round; the part
  4  `KeepJob.Faithful`   the hypothesis under which the messages are `sumPart`'s

The state. The part's state has the type `X × Option K`. The first component is what `sumPart` at
the caller's earlier job would be given; no move of the part changes it. The second is the kept
state: `none` before the part, `some` after the part's first round, and `none` again after its
last round, so the tables are dropped there. A kind places the part in its own state by
`Part.lift`.

What can be kept. `Move.hand` is given the input, the challenges and what was passed on. It is given
no coin and nothing that was sent (Honest/Frame.lean). So the kept state is computed from the input
and the challenges alone, by type.

Limits.
  * Where the second component of the state is `some k`, `KeepJob.keptAt` returns `k` without a
    test. Along the part's own moves that is the state computed from the start; at any other state
    nothing compares the two.
  * `KeepJob.start` is not given the rounds shown before the part (`Front.seen`). A summand with a
    factor that was sent cannot be kept in this way, and `KeepJob.Faithful` cannot hold of a job
    whose `round`, `inY` or `ends` depends on `Front.seen`.
  * The points at which variables are summed and the lead's values are not kept: every round asks
    the earlier job's `points` again.
  * The state is kept within one part. Nothing is kept from one part of a list to the next.
  * As in `sumPart`, no move returns an error: a list that is too short is padded with 0, one that
    is too long is cut.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)

variable {V W X K C Y : Type}

/-! ## 1 What is before a part -/

/-- What is before a part whose state holds a kept state, without that kept state: what the earlier
job's functions are given. -/
def Front.outer (f : Front (X × Option K)) : Front X := ⟨f.heard, f.own.1, f.seen⟩

/-! ## 2 The job -/

/-- **What the caller of `keepPart` supplies.** `K`: the type of the kept state, for example tables
with the variables of the earlier rounds bound. -/
structure KeepJob (W X K : Type) where
  /-- the earlier job. Its `shape`, `points` and `lead` are used as they are. Its `round`, `inY` and
  `ends` are not called: they are what `Faithful` compares the fields below with -/
  base : SumJob W X
  /-- the kept state before the first variable's round, computed once: from the input, the
  challenges before the part and what was passed on -/
  start : W → List Fmt.Drawn → X → K
  /-- the kept state after a variable's challenge -/
  bind : K → E → K
  /-- the summand's round polynomial in the next variable, all its coefficients -/
  round : K → List E
  /-- the same in Y, after all variables' challenges: from the end values' mask entries -/
  inY : K → List E → List E
  /-- the true end values, after all variables' challenges -/
  ends : K → List E

/-- **The kept state computed from the start**: `rs`: the challenges of the first variables. -/
def KeepJob.madeAt (J : KeepJob W X K) (w : W) (h : List Fmt.Drawn) (x : X) (rs : List E) : K :=
  rs.foldl J.bind (J.start w h x)

/-- **The kept state as a round reads it**: the one that was passed on. It is returned without a
test. Where none was passed on it is computed from the start. -/
def KeepJob.keptAt (J : KeepJob W X K) (w : W) (f : Front (X × Option K)) (rs : List E) : K :=
  match f.own.2 with
  | some k => k
  | none => J.madeAt w f.heard f.own.1 rs

/-- **The job for `sumPart`**: the earlier job's shape, points and lead; the three other functions
read the kept state. -/
def KeepJob.job (J : KeepJob W X K) : SumJob W (X × Option K) :=
  { shape := J.base.shape
    points := fun w f => J.base.points w f.outer
    lead := fun w f => J.base.lead w f.outer
    round := fun w f rs => J.round (J.keptAt w f rs)
    inY := fun w f rs m => J.inY (J.keptAt w f rs) m
    ends := fun w f rs => J.ends (J.keptAt w f rs) }

/-! ## 3 The part -/

/-- **What is passed on after the part's round number `n`**, from 0. `t`: the state, which holds the
round's challenge already. After the part's last round: no kept state. After the round "PSC Y": the
state as it is. After the first round: `start`. After a variable's round: the kept state bound at
the round's challenge; where none was passed on it is computed from the start. The first component
is never changed. -/
def KeepJob.pass (J : KeepJob W X K) (n : Nat) (t : State W (X × Option K)) : X × Option K :=
  if n + 1 == (scalarsOf J.base.shape).length then (t.own.1, none)
  else if J.base.shape.vs.length < n then t.own
  else
    (t.own.1, some
      (match n, t.own.2 with
       | _ + 1, some k => J.bind k ((drawnE (t.lately 1)).headD zeroE)
       | _, _ =>
         J.madeAt t.input (t.heard.take (t.heard.length - (n + 1))) t.own.1
           ((drawnE (t.lately (n + 1))).drop 1)))

/-- Moves with what they pass on replaced: the move number `n + i` of the list passes on
`pass (n + i)`. The messages are unchanged. -/
def withPass (pass : Nat → State W Y → Y) : Nat → List (Move C W Y) → List (Move C W Y)
  | _, [] => []
  | n, mv :: l => ⟨mv.say, pass n⟩ :: withPass pass (n + 1) l

/-- **The masked sumcheck's part with a kept state.** `name`, `endName`: the names of the blocks of
coins that it spends, as for `sumPart`. Its counts, its names and its two stops are those of
`sumPart` at the earlier job's shape. -/
def keepPart (name endName : String) (J : KeepJob W X K) : Part V W (X × Option K) :=
  let p : Part V W (X × Option K) := sumPart name endName J.job
  { p with moves := withPass J.pass 0 p.moves }

/-! ## 4 The hypothesis -/

/-- **The kept state gives what the earlier job computes.** A definition, meant as a hypothesis: at
the kept state computed from the start, `round`, `inY` and `ends` return what the earlier job's
functions return, at as many challenges as occur in a run: fewer than there are variables for
`round`, as many for the two others. It is asked at every `Front`, so it can hold only of an earlier
job whose three functions do not depend on `Front.seen`. -/
structure KeepJob.Faithful (J : KeepJob W X K) : Prop where
  round : ∀ (w : W) (f : Front X) (rs : List E), rs.length < J.base.shape.vs.length →
    J.round (J.madeAt w f.heard f.own rs) = J.base.round w f rs
  inY : ∀ (w : W) (f : Front X) (rs m : List E), rs.length = J.base.shape.vs.length →
    J.inY (J.madeAt w f.heard f.own rs) m = J.base.inY w f rs m
  ends : ∀ (w : W) (f : Front X) (rs : List E), rs.length = J.base.shape.vs.length →
    J.ends (J.madeAt w f.heard f.own rs) = J.base.ends w f rs

end ProofFile.Honest
