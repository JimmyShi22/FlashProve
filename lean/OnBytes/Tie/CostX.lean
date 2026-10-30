-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/CostX.lean: how many questions the library's strict reader of a chain that opens stored
tables asks at most: a number that is a function of the chain's description alone.

The library writes that reader once, over a variable monad m, with the hash h as its first argument
(Fmt/Rules8X.lean). For the reader without stored tables it has a number `Run.fileN` and, for every
count of questions c : Run.CostP m and every hash of which each call asks at most k, the bound
`Run.fileN S * k` (Run/CostFmt.lean, Run/CostFmtProofs.lean). This file extends the number by the
stored tables' openings and proves the bound for the six functions with stored tables, by the same
steps.

Main definitions, all in units of k.
 `storedN ts`    the openings of one round's stored trees: the sum over the trees of
                 (depth + 1) · (the number of draws in the tree's part).
 `roundNX r ts`  one round: `Run.roundN r + storedN ts`.
 `roundsNX rs`   the sum over the rounds.
 `fileNX S`      3 + `roundsNX` of the rounds, each with its stored trees.
Main theorems, for every count c and every hash h of which each call asks at most k.
 `le_readStored`, `le_roundX`, `le_foldRoundsX`   the parts.
 `le_readChainX`, `le_wholeChainX`, `le_verifyXW`   the reader asks at most `fileNX S * k`.
 `fileNX_plain`  with no stored tree in any round `fileNX` is `Run.fileN`.
 `fileNX_congr`  `fileNX` looks at the rounds and the stored trees alone, not at the statement.

What is not claimed. Nothing on soundness, and no probability. The numbers are upper bounds: nothing
says that one is attained, and a walk that meets a vertex from two sides hashes it once. A count
c : Run.CostP m is any predicate with three rules, and the predicate that always holds is one: what
a bound says depends on the count at which it is used. `fileNX` counts the call that hashes the
parameter bytes. It does not count the digest of the configuration (`S.base.cfg`, another value),
which the reader takes as a constant, nor the seeds of a stored table's record, nor a second chain.
`fileNX` is evaluated at no description here (a test that is not in this library evaluates it at
three). The
program does not call any function that is named in this file: "the program" is the Lean port that
is built from OnBytes/, not the C++ verifier, and its reader is another text.

-/
import Run.CostFmtProofs
import Fmt.Rules8X

set_option autoImplicit false

namespace OnBytes.Tie.CostX

/-- The questions of the openings of one round's stored trees, in units of k: for each tree its
depth plus one, times the number of draws in its part. -/
def storedN : List Fmt.Stored → Nat
  | [] => 0
  | t :: ts => (t.sh.a + 1) * t.count + storedN ts

/-- The questions of one round with its stored trees, in units of k. -/
def roundNX (r : Fmt.Round) (ts : List Fmt.Stored) : Nat := Run.roundN r + storedN ts

/-- The questions of the rounds, each with its stored trees, in units of k. -/
def roundsNX : List (Fmt.Round × List Fmt.Stored) → Nat
  | [] => 0
  | r :: rs => roundNX r.1 r.2 + roundsNX rs

/-- **The questions of a chain that opens stored tables, in units of k**: three for the head (the
parameters' digest, the run's value and the chain's first value: the format's calls number 169, 172
and 160; a chain without random bytes makes no call 172) and the rounds' numbers. A function of the
description alone. -/
def fileNX (S : Fmt.SpecX) : Nat := 3 + roundsNX (S.base.rounds.zip S.stored)

/-- With no stored tree in any round the rounds' number is the library's. -/
theorem roundsNX_plain :
    ∀ l : List Fmt.Round, roundsNX (l.zip (l.map fun _ => [])) = Run.roundsN l
  | [] => rfl
  | r :: l => by
    show Run.roundN r + 0 + roundsNX (l.zip (l.map fun _ => [])) = Run.roundN r + Run.roundsN l
    rw [roundsNX_plain l, Nat.add_zero]

/-- With no stored tree in any round `fileNX` is the library's `Run.fileN`. -/
theorem fileNX_plain (S : Fmt.Spec) : fileNX (Fmt.SpecX.plain S) = Run.fileN S :=
  congrArg (3 + ·) (roundsNX_plain S.rounds)

/-- `fileNX` looks at the rounds and the stored trees alone: two descriptions that have these in
common have one number, whatever their statements, parameter bytes and labels. -/
theorem fileNX_congr (S T : Fmt.SpecX) (hr : S.base.rounds = T.base.rounds)
    (hs : S.stored = T.stored) : fileNX S = fileNX T := by
  unfold fileNX
  rw [hr, hs]

variable {m : Type → Type} [Monad m] (c : Run.CostP m)
  (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

/-- If each call of the hash asks at most k, the reader of one round's openings of stored trees
asks at most `storedN ts * k`, whatever the draws and the bytes. -/
theorem le_readStored (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List Nat)
    (b : ByteArray) :
    ∀ (ts : List Fmt.Stored) (sn : Fmt.Seen) (i : Nat),
      c.le (Fmt.readStored h cfg statement P poss b ts sn i) (storedN ts * k) fun _ => True
  | [], _, _ => c.pureLe _ _ _ trivial
  | t :: ts, sn, i => by
    unfold Fmt.readStored
    simp only []
    have hl : (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))).length ≤ t.count := by
      refine Nat.le_trans (Run.CostP.listOf_len _) ?_
      unfold Fmt.partOf
      rw [List.length_map, List.length_take]
      exact Nat.min_le_left _ _
    refine c.le_mono _ ((t.sh.a + 1) * (t.count * k) + storedN ts * k) _ _ _
      (c.le_bind _ _ _ _ _ _
        (c.le_mono _ _ _ _ _ (c.readOpeningW h k hk cfg P.field t.salt t.sh _ _ b i)
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
      (by simp only [storedN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
    cases r with
    | none => exact c.pureLe _ _ _ trivial
    | some o =>
      simp only []
      split
      · split
        · exact c.pureLe _ _ _ trivial
        · refine c.le_mono _ (storedN ts * k + 0) _ _ _
            (c.le_bind _ _ _ 0 _ _ (le_readStored cfg statement P poss b ts _ _) fun r _ => ?_)
            (Nat.le_refl _) fun _ h => h
          cases r <;> exact c.le_pure _ _ trivial
      · exact c.pureLe _ _ _ trivial

/-- If each call of the hash asks at most k, the reader of one round with its stored trees asks at
most `roundNX r ts * k`. -/
theorem le_roundX (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored) :
    c.le (Fmt.roundX h cfg statement P run b s r ts) (roundNX r ts * k) fun _ => True := by
  unfold Fmt.roundX
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_mono _
          ((Fmt.firstBlock r.entry.work + (Fmt.wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 * k +
            (storedN ts * k + (Run.opensN r.entry.poss r.opens * k + 0)))
          _ _ _ (c.le_bind _ _ _ _ _ _ (c.queryW h k hk _ _ _ _ _ _) fun q _ => ?_)
          (by simp only [roundNX, Run.roundN, Nat.add_mul]; omega) fun _ h => h
        cases q with
        | none => exact c.pureLe _ _ _ trivial
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_bind _ _ _ _ (fun _ => True) _
              (le_readStored c h k hk cfg statement P _ b ts _ _) fun q _ => ?_
            cases q with
            | none => exact c.pureLe _ _ _ trivial
            | some x =>
              refine c.le_bind _ _ _ 0 (fun _ => True) _ ?_ fun q _ => ?_
              · have key : ∀ (roots : Array ByteArray) (sn : Fmt.Seen) (i : Nat),
                    c.le (Fmt.readOpens h cfg P run roots
                        (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn i)
                      (Run.opensN r.entry.poss r.opens * k) fun _ => True := fun roots sn i => by
                  have := c.readOpens h k hk cfg P run roots
                    (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn i
                  rw [Run.CostP.drawRound_poss] at this
                  exact this
                exact key _ _ _
              · cases q <;> exact c.le_pure _ _ trivial

/-- If each call of the hash asks at most k, the fold over the rounds asks at most
`roundsNX rs * k`. -/
theorem le_foldRoundsX (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s : Fmt.St),
      c.le (Fmt.foldRoundsX h cfg statement P run b rs s) (roundsNX rs * k) fun _ => True
  | [], _ => c.pureLe _ _ _ trivial
  | r :: rs, s => by
    simp only [Fmt.foldRoundsX]
    refine c.le_mono _ (roundNX r.1 r.2 * k + roundsNX rs * k) _ _ _
      (c.le_bind _ _ _ _ _ _ (le_roundX c h k hk cfg statement P run b s r.1 r.2) fun q _ => ?_)
      (by simp only [roundsNX, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
    cases q with
    | none => exact c.pureLe _ _ _ trivial
    | some s' => exact le_foldRoundsX cfg statement P run b rs s'

/-- **If each call of the hash asks at most k, the reader of a chain that opens stored tables asks
at most `fileNX S * k`**, from any place i of any byte string b and at any record of met vertices.
What this says depends on the count c: at the count that always holds it says nothing.
OnBytes/Tie/AskX.lean uses it at "no coin, and at most t questions on every path". -/
theorem le_readChainX (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    c.le (Fmt.readChainX h S seen b i) (fileNX S * k) fun _ => True := by
  unfold Fmt.readChainX
  split
  · exact c.pureLe _ _ _ trivial
  · simp only []
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ (k + (2 * k + (roundsNX (S.base.rounds.zip S.stored) * k + 0))) _ _ _
        (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
          c.le_bind _ _ _ _ _ _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
        (by simp only [fileNX, Nat.add_mul]; omega) fun _ h => h
      cases q with
      | none => exact c.pureLe _ _ _ trivial
      | some hd =>
        refine c.le_bind _ _ _ 0 _ _ (le_foldRoundsX c h k hk _ _ _ _ _ _ _) fun q _ => ?_
        cases q <;> exact c.le_pure _ _ trivial

/-- The same bound for the reader that also asks that nothing stands behind the chain. What this
says depends on the count c: at the count that always holds it says nothing. -/
theorem le_wholeChainX (S : Fmt.SpecX) (b : ByteArray) :
    c.le (Fmt.wholeChainX h S b) (fileNX S * k) fun _ => True := by
  simp only [Fmt.wholeChainX]
  refine c.le_bind _ _ _ 0 _ _ (le_readChainX c h k hk S [] b 0) fun q _ => ?_
  cases q <;> exact c.le_pure _ _ trivial

/-- The same bound for the reader followed by a decision on the view. What this says depends on the
count c: at the count that always holds it says nothing. -/
theorem le_verifyXW {Y : Type} (S : Fmt.SpecX) (dec : Y → Fmt.View → Bool) (y : Y)
    (file : ByteArray) :
    c.le (Fmt.verifyXW h S dec y file) (fileNX S * k) fun _ => True := by
  simp only [Fmt.verifyXW]
  refine c.le_bind _ _ _ 0 _ _ (le_wholeChainX c h k hk S file) fun q _ => ?_
  cases q <;> exact c.le_pure _ _ trivial

end OnBytes.Tie.CostX
