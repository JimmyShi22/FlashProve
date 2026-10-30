-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsTab.lean: which Merkle opening in the lenient reader's output belongs to which tree in the
order of sending. A part of Run/PageIs.lean. Definitions and statements only. Many statements of
this library are written twice: a definition in the namespace `Spec` states a proposition, and a
theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why. The compiled verifier goes through the trees in the order in which their roots are sent (a tree
is a component of the round that sends its root); the function "opens" of the parser's argument
string finds a tree's opening by the tree's number in a table (`opensB`, Run/ParseChain.lean). The
file, the readers and the view go through the openings in the order of the rounds after whose draws
they come. Within the limits of the generic construction the openings are matched one to one with
the trees that are opened. That construction is the function from a description to a protocol
(Run/PlanQTypes.lean). Its limits (`PQ.ok`, same file) have among their clauses: at most one root a
round, the chain's own trees alone, each opened at most once. No typed term and no hash occurs in
this file, only lists; a hash function h is a parameter of the hypothesis `LaxFacts h S o` and
occurs nowhere else.

1. What the file contains.
   Three definitions (`obOf`, `TreeRow`, `TreeBare`) and five statements (`Run.PQ.Spec.pi_want`,
   `pi_row`, `pi_rowOf`, `pi_perm`, `pi_sent`).
   `TreeBare S o n sh`: own tree n is opened nowhere: no opening of the description names it
     (`shapeOfOwn S n = none`); sh is the shape that stands in for it (`bareShape S.firstTree n`,
     Run/PlanQTypes.lean); the table has no record under sh.tree; the verifier wants no (n, y).

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. This file proves nothing. All five statements are proved, as stated here, in
Run/PageIsTabProofs.lean. Each has the hypotheses `ok S = true` and `LaxFacts h S o` (what the
lenient reader's output o is: parameters' digest, run's value, first value, rounds;
Run/PageIs.lean), for any hash function h, which the lines below leave out.
   `pi_want`: what the verifier wants, as a list: `wanted (rds S)` (what was drawn) = the openings
     in the file's order, each with its list: (the tree's number less S.firstTree, y).
   `pi_row`: every own tree that has a shape has its opening (`TreeRow`), or is opened nowhere
     (`TreeBare`).
   `pi_rowOf`: every opening is some own tree's.
   `pi_perm`: the openings' trees (number less S.firstTree), in the file's order, are a permutation
     of those numbers among 0 .. (the number of roots sent) − 1 that some opening of the description
     names: no opening stands twice and none is missing. `pi_row` and `pi_rowOf` do not exclude an
     opening that is listed twice; with `pi_perm`, sums and "for all" over the opened trees can be
     carried from the order of sending to the file's order.
   `pi_sent`: round by round: a round of `rds S` has a tree exactly if its items read hold a root,
     and then exactly one, of 32 bytes. So the list of the rounds' trees and the list of roots go
     together.

4. What is not claimed.
   Nothing on hashes, on the verifier or on soundness: no verifier occurs in the statements; "the
   verifier wants" stands for the list `wanted` (Run/PlanQTypes.lean), from which the protocol's
   field `reads` is made there.

Sources. No text from outside enters.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIs

set_option autoImplicit false

namespace Run.PQ
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- an opening of the reader's output as the parser's record -/
def obOf (x : _root_.Fmt.Shape × List ℕ × OpenOut) : OpenB :=
  ⟨x.1.a, x.2.1, x.2.2.cols, x.2.2.salts, x.2.2.given⟩

/-- x is the opening of own tree n, of shape sh. -/
structure TreeRow (S : _root_.Fmt.Spec) (o : ChainOut) (n : ℕ) (sh : _root_.Fmt.Shape)
    (x : _root_.Fmt.Shape × List ℕ × OpenOut) : Prop where
  mem   : ∃ ro ∈ o.rounds.toList, x ∈ ro.opens
  shape : x.1 = sh
  no    : sh.tree = S.firstTree + n
  plain : sh.stored = false
  look  : (opensB o).lookup sh.tree = some (sh.W, obOf x)
  want  : ∀ y, (n, y) ∈ wanted (rds S) (o.rounds.toList.map (·.drawn)) ↔ y ∈ x.2.1
  root  : (rootsB o)[n]? = some x.2.2.root

/-- Own tree n is opened nowhere, and sh is the shape that stands in for it. -/
structure TreeBare (S : _root_.Fmt.Spec) (o : ChainOut) (n : ℕ) (sh : _root_.Fmt.Shape) : Prop where
  nowhere : shapeOfOwn S n = none
  shape : sh = bareShape S.firstTree n
  look  : (opensB o).lookup sh.tree = none
  want  : ∀ y, (n, y) ∉ wanted (rds S) (o.rounds.toList.map (·.drawn))

namespace Spec

def pi_want : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut), ok S = true → LaxFacts h S o →
    wanted (rds S) (o.rounds.toList.map (·.drawn)) =
      o.rounds.toList.flatMap fun ro =>
        ro.opens.flatMap fun x => x.2.1.map fun y => (x.1.tree - S.firstTree, y)

def pi_row : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut), ok S = true → LaxFacts h S o →
    ∀ n sh, treeSh (rds S) n = some sh → (∃ x, TreeRow S o n sh x) ∨ TreeBare S o n sh

def pi_rowOf : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut), ok S = true → LaxFacts h S o →
    ∀ ro ∈ o.rounds.toList, ∀ x ∈ ro.opens, ∃ n, treeSh (rds S) n = some x.1 ∧ TreeRow S o n x.1 x

def pi_sent : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut), ok S = true → LaxFacts h S o →
    List.Forall₂
      (fun (d : RD) (ro : RoundOut) =>
        (d.tree = none ∧ _root_.Fmt.rootsOf ro.vals = []) ∨
        (d.tree.isSome = true ∧ ∃ r : ByteArray, r.size = 32 ∧ _root_.Fmt.rootsOf ro.vals = [r]))
      (rds S) o.rounds.toList

/-- States that, if `ok S = true` and `LaxFacts h S o`, each own tree is opened at most once: the
openings' tree numbers less S.firstTree, in the file's order, are a permutation of the numbers of
the roots sent that some opening of the description names. -/
def pi_perm : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut), ok S = true → LaxFacts h S o →
    ((o.rounds.toList.flatMap (·.opens)).map fun x => x.1.tree - S.firstTree).Perm
      ((List.range (rootsB o).length).filter fun n => (shapeOfOwn S n).isSome)

end Spec
end Run.PQ
