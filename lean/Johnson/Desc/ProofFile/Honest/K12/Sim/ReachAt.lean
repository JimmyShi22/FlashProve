-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ReachAt.lean: a test: the test `reachB` (Sim/Reach.lean) at
the closed places of a proximity test that the library has: the proof file's four at both sizes, the
key file's four at the full size, a copy's one (the link proof's) at both sizes; and one small
synthetic place. Fifteen theorems with no variable, on public numbers, each proved by an evaluation
in Lean's kernel. No property is claimed.

Terms. A place is a term of type `P12` (Johnson/Desc/K12/Frame.lean): the numbers of a proximity
test at one address in a file's description; a closed place is such a term with no variable.
`reachB` is a definition of type `Bool` on the place: it gathers the hypotheses on public numbers of
the theorem `law_of_coreB` (Sim/AllRest.lean), with two facts more. In the limits, "the law" is
`law_of_coreB`, and its premises are its hypotheses. The clauses of `reachB`, under the names that
the theorems quote, and the terms in them (stage, declared round, first reading round, depth) are
explained in the head of Sim/Reach.lean. The two sizes are the full size and the smaller size of the
library's examples. A place is counted once for both sizes: four of the proof file, four of the key
file and one of a copy are nine places, and here fourteen closed terms.

What comes out. "True" at three of the nine places: the proof file's last test behind the links (L),
at both sizes · the key file's test on the ranges (R) · a copy's test, at both sizes. "False" at
six: the folded row's (U), Omega's (O) and the own test (W), of the proof file at both sizes and of
the key file: their first reading round is declared to open two or three trees; at O the first fold
sends its own table too. With the clause on one tree the clause "of the first stage's depth" fails,
at all six. No other clause fails anywhere: three stages or more, h ≤ k and the sizes at the
declared counts hold at all fourteen.

  `reach_L_full`, `reach_L_small`, `reach_KR_full`, `reach_copy_full`, `reach_copy_small`,
    `reach_toy`: `reachB` is true at `piLFull`, `piL`, `piKRFull`, `p12Of frP`, `p12Of srP` and
    `Toy.p`, in this order
  `reach_U_full`, `reach_U_small`, `reach_KU_full`: at `piUFull`, `piU` and `piKUFull`: `reachNo`,
    the names of just the clauses that fail, is "the first reading round opens one tree", "of the
    first stage's depth"; `opensOf`, the depths of the trees that the first reading round is
    declared to open, is [24, 13], [17, 13] and [24, 13]
  `reach_O_full`, `reach_O_small`, `reach_KO_full`: at `piOFull`, `piO` and `piKOFull`: `reachNo` is
    "the first fold sends no table of its own" (the field `nums.ownMask` is true) and then the two
    names as at U; `opensOf` is [22, 13, 13], [18, 13, 13] and [22, 13, 13]
  `reach_W_full`, `reach_W_small`, `reach_KW_full`: at `piWFull`, `piW` and `piKWFull`: `reachNo` is
    the two names as at U; `opensOf` is [13, 22, 22], [13, 18, 18] and [13, 22, 22]

By what. Every proof is `decide +kernel`: Lean's kernel evaluates `reachB`, `reachNo` and `opensOf`
(all three: Sim/Reach.lean) at the closed term. No lemma is called. The file raises `maxRecDepth` to
100000. The places, in the namespace `H2K.Member`: `piUFull`, `piOFull`, `piWFull`, `piLFull`:
Johnson/Desc/K12/Law/PlacesFull.lean; in the same folder `piU`, `piO`, `piW`, `piL`:
PlacesSmall.lean; `piKUFull`, `piKOFull`, `piKWFull`: PlacesKeyFull.lean; `piKRFull`:
PlaceKeyRangesFull.lean. In the namespace `Desc.K15`: `p12Of` (Johnson/Desc/K15/HsemSays.lean)
computes a copy's place from the link's parameters, `frP` at the full size and `srP` at the smaller
(Johnson/Desc/K15/TypedP.lean). `Toy.p` (Johnson/Desc/ProofFile/Honest/K12/Toy.lean) is `p12` of
Johnson/Prover/Link/ToyParts.lean.

Limits.
- Those of Sim/Reach.lean: a "true" counts nothing by itself: the law's other premises are not
  touched; no converse is proved for a "false".
- Three clauses of `reachL` are false at none of the fifteen terms: "three stages or more", h ≤ k
  after the first stage, and the sizes at the declared counts. They have no negative test here: no
  evaluation shows that one of them can fail.
- The places are closed terms that a program made off the print of a run (the limits of
  Johnson/Desc/K12/Law/PlacesFull.lean, PlacesSmall.lean, PlacesKeyFull.lean,
  PlaceKeyRangesFull.lean; Johnson/Desc/K15/TypedP.lean): that they are the places of a file is no
  theorem. A print is the text that a run printed. At a copy the program copied a part of the
  parameters `frP` and `srP`, from which `p12Of` computes the place. The small synthetic place is
  the place of no file.
- No closed place of the key file at the smaller size was found.
- Other closed terms of type `P12` in the library are not evaluated here: for instance `piO10`
  (Johnson/Desc/K12/Law/MemberO.lean), which is `piO` at another address, and the small synthetic
  place of ToyOwn.lean (next to Toy.lean).
- Whether the clause `same` of `OnRest` (Sim/Row.lean) can be met at a place where the test says
  "true" is not treated: at L, which that file's head takes for the proof file's main test, an
  honest run cannot meet it as it stands: by reading; no theorem.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Reach
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Law.PlacesSmall
import Johnson.Desc.K12.Law.PlacesKeyFull
import Johnson.Desc.K12.Law.PlaceKeyRangesFull
import Johnson.Desc.K15.HsemSays
import Johnson.Desc.K15.TypedP
import Johnson.Desc.ProofFile.Honest.K12.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open H2K.Member

/-! ## 1 Where the test says "true" -/

theorem reach_L_full : reachB piLFull = true := by decide +kernel
theorem reach_L_small : reachB piL = true := by decide +kernel
theorem reach_KR_full : reachB piKRFull = true := by decide +kernel
theorem reach_copy_full : reachB (Desc.K15.p12Of Desc.K15.frP) = true := by decide +kernel
theorem reach_copy_small : reachB (Desc.K15.p12Of Desc.K15.srP) = true := by decide +kernel
theorem reach_toy : reachB Toy.p = true := by decide +kernel

/-! ## 2 Where it says "false": the names of just the clauses that fail; the openings' depths -/

theorem reach_U_full : reachNo piUFull =
    ["the first reading round opens one tree", "of the first stage's depth"] ∧
    opensOf piUFull = [24, 13] := by decide +kernel

theorem reach_O_full : reachNo piOFull =
    ["the first fold sends no table of its own", "the first reading round opens one tree",
      "of the first stage's depth"] ∧
    opensOf piOFull = [22, 13, 13] := by decide +kernel

theorem reach_W_full : reachNo piWFull =
    ["the first reading round opens one tree", "of the first stage's depth"] ∧
    opensOf piWFull = [13, 22, 22] := by decide +kernel

theorem reach_U_small : reachNo piU =
    ["the first reading round opens one tree", "of the first stage's depth"] ∧
    opensOf piU = [17, 13] := by decide +kernel

theorem reach_O_small : reachNo piO =
    ["the first fold sends no table of its own", "the first reading round opens one tree",
      "of the first stage's depth"] ∧
    opensOf piO = [18, 13, 13] := by decide +kernel

theorem reach_W_small : reachNo piW =
    ["the first reading round opens one tree", "of the first stage's depth"] ∧
    opensOf piW = [13, 18, 18] := by decide +kernel

theorem reach_KU_full : reachNo piKUFull =
    ["the first reading round opens one tree", "of the first stage's depth"] ∧
    opensOf piKUFull = [24, 13] := by decide +kernel

theorem reach_KO_full : reachNo piKOFull =
    ["the first fold sends no table of its own", "the first reading round opens one tree",
      "of the first stage's depth"] ∧
    opensOf piKOFull = [22, 13, 13] := by decide +kernel

theorem reach_KW_full : reachNo piKWFull =
    ["the first reading round opens one tree", "of the first stage's depth"] ∧
    opensOf piKWFull = [13, 22, 22] := by decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.reach_L_full
#print axioms ProofFile.Honest.K12.reach_L_small
#print axioms ProofFile.Honest.K12.reach_KR_full
#print axioms ProofFile.Honest.K12.reach_copy_full
#print axioms ProofFile.Honest.K12.reach_copy_small
#print axioms ProofFile.Honest.K12.reach_toy
#print axioms ProofFile.Honest.K12.reach_U_full
#print axioms ProofFile.Honest.K12.reach_O_full
#print axioms ProofFile.Honest.K12.reach_W_full
#print axioms ProofFile.Honest.K12.reach_U_small
#print axioms ProofFile.Honest.K12.reach_O_small
#print axioms ProofFile.Honest.K12.reach_W_small
#print axioms ProofFile.Honest.K12.reach_KU_full
#print axioms ProofFile.Honest.K12.reach_KO_full
#print axioms ProofFile.Honest.K12.reach_KW_full
