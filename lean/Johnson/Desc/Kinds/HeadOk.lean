-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadOk.lean: THE OUTPUT HEAD'S OWN ROUNDS: the tests on the plan and on the
request: with code, on public numbers alone. It shows nothing by itself: that a form which is 0 in
the field then says something of integers is argued nowhere here. Definitions with code; no theorem.

After the format's 11.4, "The tests on the public numbers", with two tests of other parts that its
formulas assume (S2 divides d; 2 <= V <= 2^24) and one condition of the standard parameter form (KF
<= MF), without which no call ends in an acceptance.
The list is the format's own and is kept whole, though not every clause can say no alone: some
follow from others, stand twice (epsF < 2^48) or hold of constants.
NOT HERE. On y: that it is a token: asked where y is heard; that it is 0 if e < T: asked in the last
test (ReplyKind.lean: decideE, fin). On
numbers that these rounds do not name: the sizes of the committed matrices; the list of the lookup's
calls and their key bits (by which all calls share the point (zl, zt)); the number of scalars; the
lines toksrc = 1, s <= 63 and wb_head = 13 (to which the bound BW belongs); that V's logarithm is at
most the stored table's.

-/
import Johnson.Desc.Kinds.HeadCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
variable [Sizes] [Policy] [Request]

/-- The policy's three numbers. A cost clipped at C is at most C, and there are at most T positions:
a larger theta or cap says no more. slackCap has two digits. -/
def Policy.ok : Bool := theta ≤ C && cap ≤ T && cap < 2 ^ 16

/-- The request. That y is below V is asked where y is heard; that it is 0 where e < T, in the last
test. -/
def Request.ok : Bool := r < e && e ≤ T && (List.range T).all fun t => tok t < V

/-- The ranges of the sizes. sT: the table's exponent: sT + 4 = sh is the step table. -/
def Sizes.ranges (sT : Nat) : Bool :=
  24 ≤ MF && MF ≤ 47 && MF ≤ KF + 14 && 17 ≤ KF && KF ≤ 32 && KF ≤ MF && 1 ≤ epsF && epsF < 2 ^ 48
    && F == 24 && (sh == 7 || sh == 8) && sT + 4 == sh && 2 ≤ V && V ≤ 2 ^ 24 && 2 * V ≤ 2 ^ F
    && d % S2 == 0 && JVa % S2 == 0 && 9 ≤ lPd + lt

/-- What the conditions below assume: a cell is below Ty (the range check's matter), a weight of the
head below BW (the key file's), an activation below BC (the clamp's). -/
def Ty : Nat := 2 ^ 18
@[inherit_doc Ty] def BW : Nat := 2 ^ 12
@[inherit_doc Ty] def BC : Nat := 2 ^ 11

/-- THE NO-OVERFLOW CONDITIONS: the format's thirteen, in its order and under its names, each with
what it is for; then the two of the layers' list that are about the final norm too. Each is an
inequality between integers; the bound 2^60 is below the field's prime, 2^64 - 2^32 + 1. The two
named three-digits only let an honest prover pass; the others carry a key or an equation from the
field to the integers. -/
def noOverflow : List (String × String × Bool) :=
  let Ty2 := 257 * Ty
  let TyX := Ty * ((256 ^ 5 - 1) / 255)
  let SH := 2 * d * BC * BW + 1             -- more than any difference of two logits
  let Be := 65793 * Ty + offE
  [("U-NF", "the rounding fixes one quotient", 2 ^ (16 + KF) ≤ 2 ^ 60),
   ("W-NF", "the key remLow",
      2 ^ MF + 2 ^ 38 + 2 ^ (KF - 1) + 2 ^ (15 + KF) + 2 ^ 16 * (Ty2 + off2) < 2 ^ 60),
   ("W-HD0", "a margin made of three digits", 2 ^ 8 + 2 ^ (sh + 16) + 2 ^ (sh + 31) ≤ 2 ^ 40),
   ("W-HD0", "the top digit's equation holds in the integers",
      SH + 2 ^ 40 + 2 ^ 8 * BIG + 2 ^ sh * (Ty2 + off2) + Ty + off1 < 2 ^ 60),
   ("three-digits", "an honest margin fits three digits",
      SH ≤ BIG && SH + BIG + 2 ^ 32 ≤ (2 ^ 16 + 1) * 2 ^ (sh + 15)),
   ("three-digits", "above the clip a middle digit can be chosen where the table gives 1",
      SH + 2 ^ (sh + 15) ≤ BIG),
   ("HE", "a key of the table", 2 ^ 16 * (Be + 2 ^ F + 1) + 2 ^ 16 < 2 ^ 60),
   ("Z", "the equation table", JV * 2 ^ F + 2 ^ 24 + (JV - V + 1) * 2 ^ F < 2 ^ 60),
   ("E2", "the equation mean", T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) + theta * T < 2 ^ 60),
   ("E3", "the equation count", T * (2 ^ 8 + 2 ^ 16) + cap < 2 ^ 60),
   ("E4", "the equation clip", 2 ^ 40 + 2 ^ 40 + C < 2 ^ 60),
   ("J-E", "the embedding: not the head's, but tested in this list",
      TyX + 16843009 * 2 ^ 21 < 2 ^ 60),
   ("guard-radix", "the key clamp",
      (Ty2 + 32768) + 2 ^ 28 * (Ty2 + 4096) < 2 ^ 59 && Ty2 + 32768 + 65536 < 2 ^ 28),
   ("no-wrap-ledger", "the sum of squares", 5 * d * Ty ^ 2 < 2 ^ 53),
   ("no-wrap-ledger-eps", "the root's low half", epsF < 2 ^ 48)]

/-- The tests on the plan alone. The request is no part of the plan: Request.ok is asked where the
instance comes in. In the proof file's description the test that runs is S.reqOk
(Johnson/Desc/First/State.lean), at the first record and in front of the seated decision. -/
def planOk (sT : Nat) : Bool := Policy.ok && Sizes.ranges sT && noOverflow.all (·.2.2)

end VerifiableInference.Desc.Kinds.Head
