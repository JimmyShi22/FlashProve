-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/True.lean

What it means that a request is true under an acceptance policy (C, θ, cap), and which policies the
statements on it are for.

`ppOf s pol` is the table s of scales (`Cm.Scales`, Cm/Rel2.lean, which has no policy) with the
policy pol, as a table `ScalesAndPolicy` (Inst/Model/ProgTests.lean). `PolCond` is `AcceptancePolicy.OK`
(Inst/Model/ProgramRPol.lean); `IsTrueUnder` is `RinfPP` (Inst/Model/Scales.lean) at `ppOf s pol`.

`PolCond` is wider than the clause on the policy in `Lawful` (Inst/Model/Scales.lean: C < 2^32,
θ ≤ C, cap ≤ 1,024): the laws of the relation pair (Policy/Rel/LedgerRelLaws.lean) ask no more of a
policy. Every policy of a lawful `ScalesAndPolicy`
(`Lawful.polOK`) and every policy with `PolTests` (Inst/Model/ProgTests.lean; `polCond_of_tests`)
meets it.

The source of the clipped-gap policy: lean/CREDITS.md, the row on Token-DiFR (arXiv 2511.20621).

Limits:
* `PolCond` does not say that a policy is sensible (Policy/Rel/TrueGuards.lean,
  Policy/Rel/PosGuards.lean).
* θ bounds the mean of the clipped costs over the request's own counted positions, and cap a count;
  neither bounds each token. At a counted position, a checked token that costs more than C may be
  any token at all: it enters the sum only as C, and takes one of cap's places. One that costs at
  most C may have a gap up to (θ - 2^8) times the number of counted positions (`sweep`,
  Inst/Model/ProgramRGuards.lean), and r and e choose that number.
* `IsTrueUnder` is defined at every table s; the laws are for lawful tables.
* The constant 2^8 in the cost is fixed. What the head of Inst/Model/ProgramR.lean lists as not said
  is not said here either.
-/
import Cm.Rel2

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open Inst.Model

/-- The table of scales s with the policy pol. -/
abbrev ppOf (s : Cm.Scales) (pol : AcceptancePolicy) : ScalesAndPolicy := ⟨s.w, s.nf, pol⟩

theorem ppOf_kap (s : Cm.Scales) (pol : AcceptancePolicy) : (ppOf s pol).kap = s.kap := rfl
theorem ppOf_nf (s : Cm.Scales) (pol : AcceptancePolicy) : (ppOf s pol).nf = s.nf := rfl
theorem ppOf_pol (s : Cm.Scales) (pol : AcceptancePolicy) : (ppOf s pol).pol = pol := rfl

/-- The condition on a policy: C, θ < 2^40, cap < 2^16. -/
abbrev PolCond (pol : AcceptancePolicy) : Prop := pol.OK

/-- A policy that passes `PolTests` meets the condition. -/
theorem polCond_of_tests {pol : AcceptancePolicy} (h : PolTests pol) : PolCond pol :=
  ⟨by have := h.lineC; omega, by have := h.lineTheta; omega, h.cap16⟩

/-- The policy of exact match, (2^8, 2^8, 0), passes `PolTests`. -/
theorem polTests_exact : PolTests ⟨256, 256, 0⟩ := (polTests_iff _).2 (by decide)

/-- The policy of exact match meets the condition. -/
theorem polCond_exact : PolCond ⟨256, 256, 0⟩ := polCond_of_tests polTests_exact

/-- The request x is true at the index i under the policy pol = (C, θ, cap), at the table s of
scales. Written out (`RinfR_written_out`, Inst/Model/ProgramRPol.lean; the notions: the head of
Inst/Model/ProgramR.lean): a request has 1,024 tokens x_0 .. x_1023, an announced token y and two
numbers r, e. Position t is covered if r ≤ t < e. It checks token x_(t+1); position 1,023 checks y.
It is counted if it is covered and t < 1,023. The gap of a token w under logits l is the maximum
over all tokens v of l[v] - l[w] + [v < w]: 0 exactly at the least token of largest logit, the first
choice. The cost of a position is 2^8 plus the gap of its checked token under the integer program's
logits at that position. The request is true if:
* the integer program at the table s, with the lookup tables `tbRef` and the weights that i holds,
  fails no range test on the 1,024 tokens, at any position, covered or not;
* it has its form: r < e ≤ 1,024, and y = 0 if e < 1,024 (`Head3`);
* (a) the costs of the counted positions, each clipped at C, add up to at most θ times their number;
* (b) at most cap of the counted positions cost more than C;
* (c) if e = 1,024, y has gap 0 at position 1,023, whatever the policy. -/
def IsTrueUnder (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) : Prop :=
  RinfPP (ppOf s pol) i.index x

end Policy
