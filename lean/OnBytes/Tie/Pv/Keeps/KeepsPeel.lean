-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsPeel.lean: the tactics that take a success of a routine apart, with the
mark of a failed named test carried backward.

Beside what the tactic apart of OnBytes/Tie/Pv/Keeps/KeepsRuns.lean does:
 1. The mark. Clean s: the context in s has no mark of a failed named test. For each state s_i that
    the success passes, b_i says: if the state at the very end is Clean, so is s_i. (A routine that
    is KeepsM wipes no mark, so a mark at s_i would still stand at the end.)
 2. The states come in their parts: L_i, F_i, c_i for a routine of a link (peel3), F_i, c_i for a
    routine of a sub-proof (peel2), c_i for a block (peel1).
 3. down r: a success of a lifted routine goes down one layer, and the equation "this layer's state
    is as it was" is used up at once (the two letters become one). down_sub r: the same for
    LinkM.sub.

peel3 h d: h : Runs (a sequence of calls) s b s', d : View s. For call number i the context gets
  a_i: the value that the call returned
  L_i F_i c_i: the state that it left
  r_i: Runs call_i (the state before) a_i (L_i, F_i, c_i)
  d_i: View (L_i, F_i, c_i), which is c_i.ch.dry = false by definition
  b_i: Clean s' → Clean (L_i, F_i, c_i); b_0 is on the state at the start
A match or an if goes by cases; a case whose routine never succeeds is closed. The success of the
last call stays under the name h. No definition is unfolded. To go into call 16, whose success r16
ends in the state of b16: unfold Name at r16; peel3_from r16 d15 b16 21 (its names count from 21;
b20 is then once more on the state before call 16).

The tactics that this file declares, each in a sentence:
  peel_from k h d B n: takes the success h of a sequence of calls apart, on the view d, with B : "no
    mark at the very end, so none at h's end"; the states come in k parts; the names count from n.
  peel3_from, peel2_from, peel1_from h d B n: peel_from at k = 3, 2, 1.
  peel3, peel2, peel1 h d: the same for a success that ends where the whole run ends, with names
    from 1.
  down r: the success r of a lifted routine goes down one layer, and the layer's two letters become
    one.
  down_sub r: the same for LinkM.sub.

Limits: tactics and a few small laws. One direction: from a success.
-/
import OnBytes.Tie.Pv.Keeps.KeepsRuns2

namespace OnBytes.L5

open OnBytes OnBytes.Model

/-- The context in the state has no mark of a failed named test. -/
def Clean {m : Type → Type} [Monad m] [HasRuns m] (s : HasRuns.St m) : Prop :=
  (HasRuns.ctx s).failed = none

/-- A routine that keeps wipes no mark: if it leaves none, there was none. -/
theorem runs_clean {m : Type → Type} [Monad m] [HasKeeps m] [HasRuns m] [RunsKeep m] {α : Type}
    {x : m α} [k : KeepsM x] {s : HasRuns.St m} {a : α} {s' : HasRuns.St m}
    (h : Runs x s a s') (c : Clean s') : Clean s :=
  (RunsKeep.kept k.out h).mark c

open Lean in
syntax "peel_from " num ident ident term:max num : tactic

open Lean in
macro_rules
  | `(tactic| peel_from $depth $h $d $B $n) => do
    let i := n.getNat
    let nm (p : String) (j : Nat) : Ident := mkIdent (Name.mkSimple (p ++ toString j))
    let next : TSyntax `num := Syntax.mkNumLit (toString (i + 1))
    let a := nm "a" i
    let r := nm "r" i
    let dd := nm "d" i
    let take ← match depth.getNat with
      | 3 => `(tactic| obtain ⟨$a:ident, ⟨$(nm "L" i):ident, $(nm "F" i):ident, $(nm "c" i):ident⟩,
                $r:ident, $dd:ident, $h:ident⟩ := hh)
      | 2 => `(tactic| obtain ⟨$a:ident, ⟨$(nm "F" i):ident, $(nm "c" i):ident⟩,
                $r:ident, $dd:ident, $h:ident⟩ := hh)
      | _ => `(tactic| obtain ⟨$a:ident, $(nm "c" i):ident, $r:ident, $dd:ident, $h:ident⟩ := hh)
    `(tactic| first
      | (is_sequence $h
         have hh := step $h $d
         clear $h
         $take
         (peel_from $depth $h $dd $B $next) <;>
           (have $(nm "b" (i - 1)) := fun k => runs_clean $r ($(nm "b" i) k)))
      | (split at $h:ident <;> first | exact Fails.elim $h | peel_from $depth $h $d $B $n)
      | (have $(nm "b" (i - 1)) := fun k => runs_clean $h ($B k)))

macro "peel3_from " h:ident d:ident B:term:max n:num : tactic =>
  `(tactic| peel_from 3 $h $d $B $n)
macro "peel2_from " h:ident d:ident B:term:max n:num : tactic =>
  `(tactic| peel_from 2 $h $d $B $n)
macro "peel1_from " h:ident d:ident B:term:max n:num : tactic =>
  `(tactic| peel_from 1 $h $d $B $n)
macro "peel3 " h:ident d:ident : tactic => `(tactic| peel_from 3 $h $d id 1)
macro "peel2 " h:ident d:ident : tactic => `(tactic| peel_from 2 $h $d id 1)
macro "peel1 " h:ident d:ident : tactic => `(tactic| peel_from 1 $h $d id 1)

/-- A success of a lifted routine goes down one layer; the layer's two letters become one. -/
macro "down " r:ident : tactic =>
  `(tactic| (have hh := runs_up $r; clear $r; obtain ⟨$r:ident, ee⟩ := hh;
               dsimp only at ee; subst ee))

/-- The same for LinkM.sub. -/
macro "down_sub " r:ident : tactic =>
  `(tactic| (have hh := runs_sub $r; clear $r; obtain ⟨$r:ident, ee⟩ := hh;
               dsimp only at ee; subst ee))

/-- Reading the next slot in a link. -/
theorem slot_L {s : HasRuns.St LinkM} {a : Nat} {s' : HasRuns.St LinkM}
    (h : Runs (liftM SubM.slot : LinkM Nat) s a s') : a = s.2.1.next ∧ s' = s := by
  obtain ⟨h1, e1⟩ := runs_up h
  obtain ⟨h2, e2⟩ := runs_ask (f := fun F => some F.next) h1
  exact ⟨(Option.some.inj h2).symm, Prod.ext e1 e2⟩

#print axioms runs_clean
#print axioms slot_L

end OnBytes.L5
