-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/PairAside.lean: TWO OF THE NINETEEN COMPONENTS OF THE CHAIN's SHAPE, `look` AND
`lookHeard` (Johnson/Desc/First/Shape/Chain.lean), SET ASIDE: a shape less the two; a shape with the
two laid in; AND THAT A SHAPE IS WHAT IT IS LESS THE TWO, WITH ITS OWN TWO: `eta_lk`. No premise.
Six definitions, three theorems. General; nothing is evaluated.

Purpose. The run on shapes over a link is to be shown by Lean's kernel in pieces, between written
shapes (`run_of_pieces`, Johnson/Desc/ProofFile/Honest/Thread/ShapeRun.lean). Inside a link the two
components hold the lookup's record: by a count at link 1 some 5.6 of the 7.8 million nodes of a
border's term, and a value that the kernel has not been seen to make whole. The law on pieces takes
any term as a border. So an inner border can be a written shape with nothing at the two, WITH THE
PAIR THAT THE PIECE IN FRONT LEFT LAID IN AS A TERM: what no member reads of it is never made. This
file has what that wants and no more.

Main names.
* `Pair`; `pairOf x`: a shape's own two. `withLkC a p`, `withLk x p`: the two laid to p. `less x`:
  nothing at the two. `pairE r`: the pair of what a run returned. In withLkC's match the two blanks
  are the fourteenth and fifteenth of the nineteen factors: look and lookHeard, by Chain.lean's
  readers; `withLkC_setters` holds that.
* `withLkC_setters`: withLkC a p = (a.layLook p.1).layLookHeard p.2: it is what the library's two
  setters lay.
* **`eta_lk`**: less x = c ⊢ x = withLk c (pairOf x). **`ok_of_less`**: r = .ok x and less x = c ⊢ r
  = .ok (withLk c (pairE r)).

Why withLkC takes the tuple apart by a match. Spelled by the library's two setters, and likewise by
one ChainSh.mk over the library's readers, "what was laid first is gone" and the eta did not pass by
rfl: at one ride the elaborator met its limit of heartbeats; at two Lean's kernel answered
"deterministic timeout" (the cause is not known). By the match both sides reduce to one tuple; and
the tie to the two setters passes by rfl.

Limits. Equalities of terms. That any member leaves the two components as they were is NOT said
here, and is not wanted by the join that this file serves (JoinPieces.lean). "What no member reads
of it is never made" holds of a piece that reads neither component; WHERE A PIECE READS ONE, WHOEVER
EVALUATES THAT PIECE's FACT MUST RUN THE PIECE IN FRONT INSIDE IT: pairE is a match on the run's
outcome, so no part of the pair can be read before that run is brought to its return. pairE answers
(none, none) at a refused run. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.PairAside
open Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape

/-- The two components. -/
abbrev Pair : Type := Option HeardAll × Option HeardAll

/-- A shape's own pair. -/
def pairOf (x : ShA) : Pair := (x.1.look, x.1.lookHeard)

/-- A chain's shape with the two components laid to p: the tuple taken apart and laid anew. -/
def withLkC : ChainSh → Pair → ChainSh
  | (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, _, a15, a16, a17, a18), p =>
    (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, p.1, p.2, a15, a16, a17, a18)

/-- It is what the library's two setters lay, one behind the other. -/
theorem withLkC_setters (a : ChainSh) (p : Pair) :
    withLkC a p = (a.layLook p.1).layLookHeard p.2 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := a
  rfl

/-- x with the two components laid to p. -/
def withLk (x : ShA) (p : Pair) : ShA := (withLkC x.1 p, x.2)

/-- x with nothing at the two components. -/
def less (x : ShA) : ShA := withLk x (none, none)

/-- The pair of what a run returned; (none, none) where it refused. -/
def pairE (r : Except String ShA) : Pair :=
  match r with
  | .ok x => pairOf x
  | .error _ => (none, none)

/-- **A shape is what it is less the two, with its own pair.** The premise can hold only at a c with
nothing at the two components: at any other c it is false, and the law says nothing. -/
theorem eta_lk {x c : ShA} (h : less x = c) : x = withLk c (pairOf x) := by
  subst h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
    F⟩ := x
  rfl

/-- Where a run returns x and x less the two is c, it returns c with the run's own pair. -/
theorem ok_of_less {r : Except String ShA} {x c : ShA} (hr : r = .ok x) (h : less x = c) :
    r = .ok (withLk c (pairE r)) := by
  subst hr
  exact congrArg Except.ok (eta_lk h)

end Johnson.AtFull.Shape.PairAside

#print axioms Johnson.AtFull.Shape.PairAside.Pair
#print axioms Johnson.AtFull.Shape.PairAside.pairOf
#print axioms Johnson.AtFull.Shape.PairAside.withLkC
#print axioms Johnson.AtFull.Shape.PairAside.withLkC_setters
#print axioms Johnson.AtFull.Shape.PairAside.withLk
#print axioms Johnson.AtFull.Shape.PairAside.less
#print axioms Johnson.AtFull.Shape.PairAside.pairE
#print axioms Johnson.AtFull.Shape.PairAside.eta_lk
#print axioms Johnson.AtFull.Shape.PairAside.ok_of_less
