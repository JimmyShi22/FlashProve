-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/ToyPlan.lean: a small plan of a model, for trials of the honest prover of the
layers' own rounds (K4). Definitions with code, and one test. No theorem.

WHAT IT IS NOT. It is no stored example's plan and no model's: its numbers are chosen so that the
layers' public tests pass and K4's tables are small. Nor is the place that `toyQOf` lays a place in
a chain made of this plan: its four numbers are written by hand, and the six rounds in front, the
same in both groups, are six synthetic challenges (`toyFrontSizes`,
Johnson/Desc/K4/Honest/ToyState.lean): no round of a lookup is counted.

WHAT IT DEFINES. The shape is that of the library's own small configuration
(OnBytes/Model/TestLayer.lean), with that file's list of the lookup's calls (`Test.pc`, the lines
"call" of a parameter file) and its file of scales, turned at these numbers: 16 tokens; width 8 in
two heads of 4, one key head; inner width 32, an expert's 16; two routed experts; blocks of 32 rows
in a long read; matrices of 256 rows, af in three parts; NOT TURNED: matrix b, of the lookup's
counts, keeps its 8,192 rows, here in 2,048 columns, and is by far the largest; a vocabulary of 16
tokens; 64 columns in the matrix of weights, whose rows are rounded up to a multiple of 32; calls of
2^14 keys, but one of 2^15, which so has two trees, as one call of the small configuration has.
Eight layers in two groups stay, so that a first and a later group can be tried. All public numbers
are made by the verifier's own functions, in the order of TestLayer.lean's `pub`.
  `toyShape`, `toyKL`, `toyV`, `toyLk`, `toyTokens`   the numbers
  `toyPub`, `toyPlans`   the layers' public numbers; the two groups' plans
  `toyQOf`, `toyQ g`     the public data of K4's place in group g, behind six rounds: of plans that
                         are made already; with the plans made anew

How small it can be, by our reading of the verifier's tests; no line of this file tries a smaller
plan: at least 16 tokens; more than one layer bit (K4's own `covers`); each of the three product
layers has at least 9 variables, which bounds an expert's inner width from below by 16 at these
numbers of tokens and layers.

WHAT THE ONE TEST TRIES, AND WHAT IT DOES NOT. It is an evaluation by Lean's evaluator at the build:
no proof. It tries that the verifier's own functions return at these numbers (`toyPlans`), that K4's
`covers` says yes, and fifteen numbers (five of the layout, four of the rounds' sizes, three for
each group's plan) against sizes that were reckoned by hand from the format's page. It does not try
`toyQOf` or `toyQ`, the tokens, another shape, or a shape at which a public test says no.

Limits. The lookup's tables keep their 65,536 rows at every shape, so making the plan costs some
seconds where it is interpreted: a test that reads the plan pays that anew.
Nothing on any property.
No property is claimed.
-/
import OnBytes.Model.TestLayer
import Johnson.Desc.K4.Honest.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (wsLayOf)
open OnBytes.Model.Layer

/-- The shape. -/
def toyShape : Shape :=
  { Test.h with
    lt := 4, la := 5, d := 8, H := 2, Gk := 1, dh := 4, f := 32, fe := 16, NE := 2, nmin := 14,
    D := 32, lmaf := 8, NAf := 3, lmad := 8, NAd := 1, lmar := 8, lmq := 8, lmx := 8,
    iota := #[0, 0, 0, 1, 0, 0, 0, 0] }

/-- The file of scales: the small configuration's own. -/
def toyKL : Array Nat := Test.KL

/-- The size of the vocabulary; the bits of a column's number in the matrix of weights. -/
def toyV : Nat := 16
def toyLk : Nat := 6

/-- The request's tokens. -/
def toyTokens : Array Nat := (Array.range 16).map fun t => (5 * t + 3) % 16

/-- All public numbers, as TestLayer.lean's `pub` makes them at its own shape. -/
def toyPub : Except String Pub := do
  let h := toyShape
  let y ← layout h Test.pc
  let sc ← scalesOf h toyKL
  scalesHeld h sc
  noWrap h sc y.dq
  weightWidthsHeld h y.kinds
  let wsLay ← wsLayOf
    { D := h.D, L := h.L, d := h.d, dh := h.dh, dkv := y.dkv, dq := y.dq, f := h.f, fe := h.fe,
      NE := h.NE, V := toyV } h.p3 toyLk
  let rope ← ropeOf h
  Pub.of y sc rope wsLay toyV toyTokens { lidb := h.lidb, tau := h.tau, hb := 128 }

/-- The plans of the two groups. -/
def toyPlans : Except String (Pub × Array HPlan2) := do
  let P ← toyPub
  pure (P, ← plansG P)

/-- K4's place in group g, of the plans: link and segment 2 g, piece 3, behind six rounds. -/
def toyQOf (x : Pub × Array HPlan2) (g : Nat) : Option K4Pub :=
  x.2[g]?.map fun hp =>
    { P := x.1, hp := hp, g := g, link := 2 * g, piece := 3, r0 := 6, seg := 2 * g }

/-- **The public data of K4's place in group g.** -/
def toyQ (g : Nat) : Option K4Pub := toyPlans.toOption.bind (toyQOf · g)

-- ONE TEST, SO THAT THE PLAN IS MADE ONCE: the public tests pass; K4 covers the plan; the sizes.
-- THE WRITTEN SIZES ARE RECKONED BY HAND from the format's page, the table of rounds
-- (docs/format/11-2-feed-forward-segment.md): the three product levels have 3 + 3 + 4, 2 + 5 + 4
-- and 1 + 4 + 4 variables;
-- the panels have 296 + 154 = 450 places, so 9 rounds; 6 x 4 + 4 x 2 weight claims, and the
-- embedding's; 3 + 2 + 14 + 1 + 7 + 7 + 1 + 12 + 15 + 1 + 13 + 1 + 9 = 86 rounds, two fewer later
#guard (toyPlans.toOption.map fun x =>
    (covers x.1, [x.1.y.T, x.1.y.Lam, x.1.y.LamM, x.1.y.NI, x.1.y.S2],
      [x.1.rd.muV, x.1.rd.muH, x.1.rd.muH2, x.1.wsLay.lk],
      x.2.toList.zipIdx.map fun p => (p.1.lamS, p.1.NCL, (rounds x.1 p.1 p.2).length))) ==
  some (true, [16, 4, 2, 8, 2], [10, 11, 9, 6], [(9, 33, 86), (9, 32, 84)])

end OnBytes.Desc.First.K4.Honest
