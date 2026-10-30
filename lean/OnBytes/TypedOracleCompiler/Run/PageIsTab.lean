-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsTab.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIsTab.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
TreeRow, TreeBare, pi_want, pi_row, pi_rowOf, pi_sent, pi_perm.

Run/PageIsTab.lean: a part of Run/PageIs.lean: which opening in the lenient reader's output belongs
to which tree in the order of sending. DEFINITIONS AND STATEMENTS ONLY.

Why. The compiled verifier goes through the trees in the order in which their roots are sent (a tree
is a component of the round that sends its root) and finds a tree's opening by the tree's number in
a table (Run/ParseChain.lean: opensB). The file, the readers and the view go through the openings in
the order of the rounds behind whose draws they stand. Within the limits of the generic construction
(PQ.ok: at most one root a round; the chain's own trees alone; each opened at most once) the
openings are matched one to one with the trees that are opened. No typed term and no hash occurs
here, only lists.

Sources. No text from outside enters.

1. What the file contains.
   obOf x               An opening of the reader's output as a record of the type OpenB
                        (Run/ParseBS.lean).
   TreeRow S o n sh x   x is the opening of own tree n, of shape sh: it stands in some round's list;
                        its shape is sh, a tree made in the run (not a stored one), of the number
                        S.firstTree + n; the table finds it under sh.tree; the verifier wants (n, y)
                        exactly for the y of its list; the n-th root sent is the root noted in it.
   TreeBare S o n sh    Own tree n is opened nowhere: no opening of the description names it
                        (shapeOfOwn S n = none); sh is the shape that stands in for it (bareShape
                        S.firstTree n); the table has no record under sh.tree; the verifier wants no
                        (n, y).
   Five statements (Run.PQ.Spec.pi_want, pi_row, pi_rowOf, pi_perm, pi_sent).

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. THIS FILE PROVES NOTHING. ALL FIVE STATEMENTS ARE PROVED, AS STATED HERE, IN
Run/PageIsTabProofs.lean.
   pi_want      What the verifier wants, as a list: wanted (rds S) (what was drawn) = the openings
                in the file's order, each with its list: (the tree's number less S.firstTree, y).
   pi_row       Every own tree that has a shape has its opening, or is opened nowhere: treeSh (rds
                S) n = some sh → (∃ x, TreeRow S o n sh x) ∨ TreeBare S o n sh.
   pi_rowOf     Every opening is some own tree's: x in some round's list → ∃ n, treeSh (rds S) n =
                some x.1 ∧ TreeRow S o n x.1 x.
   pi_perm      The openings' trees (number less S.firstTree), in the file's order, are a
                permutation of those numbers among 0 .. (the number of roots sent) − 1 that some
                opening of the description names: no opening stands twice and none is missing.
                pi_row and pi_rowOf do not exclude an opening that is listed twice; with pi_perm,
                sums and "for all" over the opened trees can be carried from the order of sending to
                the file's order.
   pi_sent      Round by round: a round of rds S has a tree exactly if its items read hold a root,
                and then exactly one. So the list of the rounds' trees and the list of roots go
                together.

   TRIED, NOT PROVED (one evaluation, not part of these files, at Fmt.formatHash, before the proofs existed).
   Forms of four of the statements that can be computed (the two lists of pi_want compared; for n
   below 5 a row looked for by program; pi_sent's pairs counted), at the description of
   Fmt/M1PlanKnownT.lean, on the 38 of the 47 files of Fmt/M1FilesT.lean, as that set lay then, that
   the lenient reader reads: none fails (at the honest file: 3 trees, 3 openings, 3 roots, 11 wanted
   pairs).

4. What is not claimed.
   Nothing on hashes, on the verifier or on soundness.

Terms: lean/GLOSSARY.md.

-/
import Run.PageIsTab
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseLaws
import OnBytes.TypedOracleCompiler.Run.PageIs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- x is the opening of own tree n, of shape sh -/
structure TreeRow (S : _root_.Fmt.Spec) (o : ChainOut) (n : ℕ) (sh : _root_.Fmt.Shape)
    (x : _root_.Fmt.Shape × List ℕ × OpenOut) : Prop where
  mem   : ∃ ro ∈ o.rounds.toList, x ∈ ro.opens
  shape : x.1 = sh
  no    : sh.tree = S.firstTree + n
  plain : sh.stored = false
  look  : (opensB o).lookup sh.tree = some (sh.W, obOf x)
  want  : ∀ y, (n, y) ∈ wanted (rds S) (o.rounds.toList.map (·.drawn)) ↔ y ∈ x.2.1
  root  : (rootsB o)[n]? = some x.2.2.root

/-- own tree n is opened nowhere, and sh is the shape that stands in for it -/
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
        d.trees.length = (_root_.Fmt.rootsOf ro.vals).length ∧
        ∀ r ∈ _root_.Fmt.rootsOf ro.vals, r.size = 32)
      (rds S) o.rounds.toList

/-- each own tree is opened at most once: the openings' trees, in the file's order, are the numbers
of the roots sent that some opening of the description names, each once -/
def pi_perm : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut), ok S = true → LaxFacts h S o →
    ((o.rounds.toList.flatMap (·.opens)).map fun x => x.1.tree - S.firstTree).Perm
      ((List.range (rootsB o).length).filter fun n => (shapeOfOwn S n).isSome)

end Spec
end TypedOracleCompiler.Run.PQ
