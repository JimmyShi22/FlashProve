--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Link/FoldWordsE.lean: THE FOLD's PROVER ON WORDS
(Johnson/Prover/Link/FoldWordsOf.lean) AT THE PROGRAM's OWN TYPE OF AN ELEMENT: OnBytes.E
(OnBytes/Base.lean), a record of three words, where FoldWordsOf.lean stands on the format's triples
(Fmt.M1.E). The same two functions through the library's two maps E.triple and E.ofTriple: no
arithmetic is written here. Definitions with code; no theorem. This file defines part of the honest
prover.

Main names (namespace Johnson.Prover.Link).
bookWordsE k l a list of elements as the 2 k + 1 words: "none" unless it has just so many.
foldSigmaE k w "FOLD epsilon": the one scalar.
foldRoundE k h c d m mu keptV w eps gs a "FOLD round": the constant and the quadratic coefficient.

w IS TYPED AT ITS NUMBER, as in FoldWordsOf.lean: w : Fin (2 * k + 1) → OnBytes.E. A caller that
holds a list goes through bookWordsE, which refuses a list of another length.

Limits. Those of FoldWordsOf.lean: nothing is proved; outside FoldSizes (of the arrays' triples) the
values mean nothing; the cost. Tests: two #guard lines at the foot: at made-up words the wrapper's
values, as triples, are FoldWordsOf.lean's at the same data: what can ring: an argument handed to
another's place (ten arguments, of three types), but for c with m and d with mu, in which the
summand is symmetric; and a triple that does not come back through the two maps. The maps' direction
is held by the types, not by these lines. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FoldWordsOf
import OnBytes.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link

/-- A list of elements as the 2 k + 1 words: none unless it has just so many. -/
def bookWordsE (k : Nat) (l : List OnBytes.E) : Option (Fin (2 * k + 1) → OnBytes.E) :=
  if h : l.length = 2 * k + 1 then some fun i => l[i.val]'(by rw [h]; exact i.isLt) else none

/-- **"FOLD epsilon": the one scalar**, at the program's elements. -/
def foldSigmaE (k : Nat) (w : Fin (2 * k + 1) → OnBytes.E) : OnBytes.E :=
  .ofTriple (foldSigmaW k fun i => (w i).triple)

/-- **A "FOLD round": the constant and the quadratic coefficient**, at the program's elements. -/
def foldRoundE (k h : Nat) (c d m mu : Array OnBytes.E) (keptV : OnBytes.E)
    (w : Fin (2 * k + 1) → OnBytes.E) (eps : OnBytes.E) (gs : List OnBytes.E) :
    OnBytes.E × OnBytes.E :=
  let q := foldRoundW k h (c.map (·.triple)) (d.map (·.triple)) (m.map (·.triple))
    (mu.map (·.triple)) keptV.triple (fun i => (w i).triple) eps.triple (gs.map (·.triple))
  (.ofTriple q.1, .ofTriple q.2)

-- each argument goes to its own place, and the triples come back
#guard (foldSigmaE 2 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).triple =
  foldSigmaW 2 fun i => Fmt.M1.FoldOwn.mk .two (100 + i.val)
#guard
  let v (n s : Nat) := Fmt.M1.FoldOwn.mkV .two n s
  let e (t : Fmt.M1.E) : OnBytes.E := .ofTriple t
  let q := foldRoundE 2 1 ((v 8 1).map e) ((v 6 2).map e) ((v 8 3).map e) ((v 6 4).map e)
    (e (Fmt.M1.FoldOwn.mk .two 5)) (fun i => e (Fmt.M1.FoldOwn.mk .two (100 + i.val)))
    (e (Fmt.M1.FoldOwn.mk .two 6)) [e (Fmt.M1.FoldOwn.mk .two 7)]
  (q.1.triple, q.2.triple) = foldRoundW 2 1 (v 8 1) (v 6 2) (v 8 3) (v 6 4)
    (Fmt.M1.FoldOwn.mk .two 5) (fun i => Fmt.M1.FoldOwn.mk .two (100 + i.val))
    (Fmt.M1.FoldOwn.mk .two 6) [Fmt.M1.FoldOwn.mk .two 7]

end Johnson.Prover.Link
