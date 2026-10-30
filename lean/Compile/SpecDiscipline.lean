-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SpecDiscipline.lean: the rules for tokens in token programs: the definitions that do not
depend on the scheme's programs (words of this library: lean/GLOSSARY.md). The form in which the
compiled scheme's programs obey the rules (`SafeO`, `TidyO`) and the statements are in
Compile/Batch/SpecDiscipline.lean, which builds on this file. Lemmas: Compile/Discipline.lean.

Purpose. A token program is a `Step` (Rom/Defer.lean; token, plain, marked, charged, mode I:
Notation, at the end of this head). The lemma on deferred programming (`Rom.Spec.defer`) asks of
every run in mode I: no violation of the rules, bounds on the numbers of plain and of marked queries
to each oracle, and a lower bound on the length of every charged token (`Rom.DSt.Within`).

The form. Nothing here mentions the contents of the table of oracle answers or a probability.
* `afterPlain`, `afterFresh`, `afterMark`, `afterReveal`: the states after a plain query, a new
  token, a marked query and a reveal, which are the states of `Rom.Step.run` with an arbitrary table
  (`markBad`: its check at a marked query; `markDue`: what a release does to the record of one
  query). So a further invariant (also one that is about the table) can be carried through a program
  by one induction on the program under `SafeO`, from four lemmas on these four states.
* `Rules S`: the parameters of the rules.
* `Grows Ch R e M d d'`: what a run may have added; `nEv d o`: the number of marked queries to o so
  far.
* `TreeTok`: the tokens of a tree; `cntLeaves`, `nSym`, `eTree`, `mTree`, `mProve`: counts of leaves
  and of queries; `os`: the leaf oracle and the three Fiat-Shamir oracles. `os` and the counts of
  queries are over the names `ON` of Compile/Oracles.lean, which are not the compiled scheme's
  oracles (`OracleName`, Compile/Batch/Oracles.lean; its own: `osB`, `eTreeE`, `mTreeE`, `mProveB`,
  Compile/Batch/SpecDiscipline.lean).

Notation: the rules for tokens: the list "Rules:" in the head of Rom/Defer.lean; `Tok`: a natural
number (Rom/Defer.lean); "the value of token i is at place i" (`DSt.vals`, there); a marked query:
`Step.marked o t us pt inj k` (Rom/Defer.lean, where it is called a marked evaluation): "every
marked evaluation is charged to one token t, in which its point is injective; it may hold further
tokens us" (the head there); a plain query: `Step.plain o q k` (there); mode I, mode R: the Bool of
`Step.run` (Rom/Defer.lean): "modeI = true is mode I, false is mode R"; `d.Within e M ℓ os`
(`Rom.DSt.Within`; `e`, `M`, `ℓ`: of type `S.ι → ℕ`; its `os`: any `Finset S.ι`): "what a run may do
at most: e o plain and M o marked evaluations of o; marked ones only at oracles of os, each charged
to a token of at least ℓ o bits; no violation of the rules".
-/
import Compile.Spec

namespace Compile.Disc
open Iop Rom

/-! ## 1. Generic in the family of oracles -/

section Generic
variable {S : OSpec} {sp : Split S} {α : Type}

/-- the check of Rom.Step.run at a marked query -/
def markBad (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) : Bool :=
  decide (d.vals.length ≤ t) || us.any (fun u => decide (d.vals.length ≤ u)) || us.contains t ||
    d.shown.contains t ||
    d.evs.any fun e => decide (e.o = o) && (e.charged == t || e.others.contains t)

/-- what a release does to the record of one query -/
def markDue (shown : List Tok) (e : Ev S) : Ev S :=
  if !e.released && shown.contains e.charged then { e with released := true } else e

/-- the state after a plain query to o; T is the new table -/
def afterPlain (d : DSt S) (o : S.ι) (T : Table S) : DSt S :=
  { d with table := T, nPlain := Function.update d.nPlain o (d.nPlain o + 1) }
/-- the state after a new token with the string v -/
def afterFresh (d : DSt S) (v : Bits) : DSt S := { d with vals := d.vals ++ [v] }
/-- the state after the marked query P to o with the answer r; T is the new table -/
def afterMark (sp : Split S) (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) : DSt S :=
  { d with
    table := T, vals := d.vals ++ [List.ofFn (sp.split o r).2],
    evs := d.evs ++ [⟨o, P, r, t, us, d.vals.length, false⟩], viol := d.viol || markBad d o t us }
/-- the state after a reveal of ts; T is the new table -/
def afterReveal (d : DSt S) (ts : List Tok) (T : Table S) : DSt S :=
  { d with table := T, shown := d.shown ++ ts, evs := d.evs.map (markDue (d.shown ++ ts)),
           viol := d.viol || !closedUnder (d.shown ++ ts) (d.evs.map (markDue (d.shown ++ ts))) ||
             ts.any (fun u => decide (d.vals.length ≤ u)) }

/-- The parameters of the rules. -/
structure Rules (S : OSpec) where
  /-- oracles whose tails are never charged -/
  Term : S.ι → Prop
  /-- the allowed plain queries -/
  Pl : ∀ o, S.Dom o → Prop
  /-- the allowed marked queries -/
  Mk : ∀ o, S.Dom o → Prop
  /-- the least length of a token that is charged at o -/
  bits : S.ι → ℕ

/-- the number of marked queries to o so far -/
def nEv (d : DSt S) (o : S.ι) : ℕ := (d.evs.filter fun v => decide (v.o = o)).length

/-- What a run may have added on the way from d to d'. Ch: the tokens of d that it may have charged;
R: the tokens of d that it may have shown; e o and M o: how many plain and marked queries to o it
may have added. -/
structure Grows (Ch R : Tok → Prop) (e M : S.ι → ℕ) (d d' : DSt S) : Prop where
  vals : d.vals <+: d'.vals
  shown : ∀ t ∈ d'.shown, t ∈ d.shown ∨ R t ∨ d.vals.length ≤ t
  /-- a query of d' is one of d (perhaps released by now), or new: then its tail is a new token, and
  its charged token is new or in Ch -/
  evs : ∀ e' ∈ d'.evs, (∃ e₀ ∈ d.evs, e₀.o = e'.o ∧ e₀.charged = e'.charged ∧ e₀.tail = e'.tail) ∨
    (d.vals.length ≤ e'.tail ∧ (Ch e'.charged ∨ d.vals.length ≤ e'.charged))
  plain : ∀ o, d'.nPlain o ≤ d.nPlain o + e o
  marked : ∀ o, nEv d' o ≤ nEv d o + M o

end Generic

/-! ## 2. Tokens of a tree, and counts -/

section Scheme
variable {I X : Type} {lam : ℕ}

/-- the leaf oracle and the three Fiat-Shamir oracles -/
def os : Finset ON := {ON.leaf, ON.fs Tag.test, ON.fs Tag.link, ON.fs Tag.onl}

/-- u is one of the tokens of the tree -/
def TreeTok (t : TreeH lam) (u : Tok) : Prop := ∃ s s', some (s, s') ∈ t.salts ∧ (u = s ∨ u = s')

/-- how many of the 2^depth leaves satisfy f -/
def cntLeaves (depth : ℕ) (f : ℕ → Bool) : ℕ := ((List.range (2 ^ depth)).filter f).length

/-- leaves with a symbol, of all trees of one execution -/
def nSym {K : ℕ} : (s : Shape) → WireS lam K s → ℕ
  | [], _ => 0
  | _ :: s, (w, W) => cntLeaves w.depth (fun j => (w.posAt j).isSome) + nSym s W

/-- plain and marked queries of one tree with a symbol at the leaves with f (at `node`: an upper
bound) -/
def eTree (depth : ℕ) (f : ℕ → Bool) : ON → ℕ
  | .leaf => cntLeaves depth (fun j => !f j)
  | .node => 2 ^ depth
  | _ => 0
def mTree (depth : ℕ) (f : ℕ → Bool) : ON → ℕ
  | .leaf => cntLeaves depth f
  | _ => 0

def mProve {K : ℕ} (t : Tag) (s : Shape) (W : WireS lam K s) : ON → ℕ
  | .leaf => nSym s W
  | .fs t' => if t' = t then s.length else 0
  | _ => 0

end Scheme

end Compile.Disc
