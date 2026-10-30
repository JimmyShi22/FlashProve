--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Link/FoldWordsOf.lean: THE FOLD's PROVER ON WORDS, AS TWO PURE FUNCTIONS OF PLAIN
DATA: what "FOLD epsilon" and each "FOLD round" send. Definitions with code; no theorem. This file
defines part of the honest prover.

NO NEW PROGRAM: the library's own word program is called (Fmt.M1.FoldOwn, Fmt/M1Fold.lean: sigma,
roundAt, coeffs): the one that the library's own honest prover calls at these rounds (go,
Fmt/M1Own.lean). Beside it: the term of the kept forms, which that program has not: in round i it is
a_i (1 - X), a_i = keptV (1 - g_1) .. (1 - g_(i-1)) (keptQ, Johnson/Prover/Link/FoldKept.lean): so
eps a_i is added to the constant and nothing to the quadratic coefficient.

Main names (namespace Johnson.Prover.Link).
uOfBook k w the 2 k + 1 words w as the library's record of coefficients.
bookWords k l a list of words as such a w: "none" unless the list has just 2 k + 1 entries.
trialW the library's record of a fold's data, of plain arguments.
FoldSizes k h l lz c d m mu THE NAMED PREMISE ON THE FOUR ARRAYS' SIZES: public shapes.
foldSigmaW k w "FOLD epsilon": the one scalar.
foldRoundW k h c d m mu keptV w eps gs a "FOLD round": the constant and the quadratic coefficient.
      The round's number is gs.length.

w IS TYPED AT ITS NUMBER: w : Fin (2 * k + 1) → E. No function of this file lays a 0 where one of
the 2 k + 1 words is due: at 1 ≤ l ≤ k and t = 1, 2, and at the constant, uOfBook reads a word of w;
the library's functions read its record at no other (l, t). A caller that holds a list goes through
bookWords, which refuses a list of another length.

THE ORDER OF w IS THE CALLER's: (1,1) (1,2) .. (k-1,1) (k-1,2) (k,0) (k,1) (k,2): the constant
before the last pair. THE INDEX OF A TABLE is the library's: entry p of row b of a table of 2^n rows
has the index b + 2^n p. Whoever lays the table that holds these coefficients must make it of
uOfBook k w at the same w (the library's freshRows): no function of this file does.

Limits. NOTHING IS PROVED HERE: that these words read as the field's terms hMu and foldQK
(FoldHolds.lean, FoldKept.lean) is owed; every such law is to carry FoldSizes by name. OUTSIDE
FoldSizes THE VALUES OF foldRoundW MEAN NOTHING (the library's functions read 0 beyond an array's
end). Beyond the last round a value, no refusal. Tests: Johnson/Prover/Link/FoldWordsToy.lean. COST:
round i evaluates the summand at 3 * 2^(k - i - 1) points, each over the whole tables: for tests,
not for the sizes of the programs. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Fmt.M1Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open Fmt Fmt.M1 Fmt.M1.FoldOwn

/-- The 2 k + 1 words w, read in the order (1,1) (1,2) .. (k-1,1) (k-1,2) (k,0) (k,1) (k,2), as the
library's record of coefficients: (l,t) is the coefficient of X_l^t X_(l+1) .. X_k, (k,0) the
constant. At 1 ≤ l ≤ k and t = 1, 2 the number lies below 2 k + 1: a word of w is read. At the
record's other places, which the library's functions do not read, stands some word of w, or 0. -/
def uOfBook (k : Nat) (w : Fin (2 * k + 1) → E) : Hide :=
  ⟨fun l t =>
      let i := if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t
      if h : i < 2 * k + 1 then w ⟨i, h⟩ else Fld.zeroE,
    w ⟨2 * (k - 1), by omega⟩⟩

/-- A list of words as the 2 k + 1 words: none unless it has just so many. -/
def bookWords (k : Nat) (l : List E) : Option (Fin (2 * k + 1) → E) :=
  if h : l.length = 2 * k + 1 then some fun i => l[i.val]'(by rw [h]; exact i.isLt) else none

/-- The library's record of a fold's data, of plain arguments. The row's target and the length of a
mask row are laid as 0, the list of drawn elements as []: no function of this file reads them. -/
def trialW (k h : Nat) (c d m mu : Array E) (w : Fin (2 * k + 1) → E) (eps : E) : Trial :=
  { k := k, h := h, G := ⟨c, d, Fld.zeroE⟩, m := m, mu := mu, U := uOfBook k w, eps := eps, g := [],
    lzk := 0 }

/-- **The sizes of the four arrays**: 2^k rows of l entries; 2^h rows of lz entries. Public
shapes. -/
def FoldSizes (k h l lz : Nat) (c d m mu : Array E) : Prop :=
  c.size = 2 ^ k * l ∧ m.size = 2 ^ k * l ∧ d.size = 2 ^ h * lz ∧ mu.size = 2 ^ h * lz

/-- **"FOLD epsilon": the one scalar**: of k and the 2 k + 1 words. -/
def foldSigmaW (k : Nat) (w : Fin (2 * k + 1) → E) : E :=
  (trialW k 0 #[] #[] #[] #[] w Fld.zeroE).sigma .two

/-- **A "FOLD round": the round polynomial's constant and quadratic coefficients**: of the data,
what "FOLD epsilon" drew (eps) and what the rounds "FOLD round" in front of this one drew (gs).
keptV: the value of the row's forms on the kept members' tables. -/
def foldRoundW (k h : Nat) (c d m mu : Array E) (keptV : E) (w : Fin (2 * k + 1) → E) (eps : E)
    (gs : List E) : E × E :=
  let T := trialW k h c d m mu w eps
  let q := coeffs .two (roundAt .two T gs Fld.zeroE) (roundAt .two T gs Fld.oneE)
    (roundAt .two T gs (Fld.two.negE Fld.oneE))
  (Fld.two.addE q.1 (Fld.two.mulE eps
      (gs.foldl (fun s g => Fld.two.mulE s (Fld.two.subE Fld.oneE g)) keptV)), q.2.2)

end Johnson.Prover.Link
