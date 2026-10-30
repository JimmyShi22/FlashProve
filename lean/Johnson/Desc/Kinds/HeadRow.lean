-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadRow.lean: a part of THE OUTPUT HEAD'S OWN ROUNDS (Head.lean): the order of
the twelve reads; why the claims give the statement; what is open. Two definitions under second
names, which no other file of this library uses. Definitions with code; no theorem.

-/
import Johnson.Desc.Kinds.Head
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

/-- `rounds` (Head.lean), under a second name. -/
abbrev placeRounds [Sizes] : List Round := rounds
/-- `hear`, under a second name and at another type, for a test that hands the rounds as plain data
(the flat text's Tape: OnBytes/K/Kc/Flat.lean): each round is written back as a view shows
it: its scalars, its drawn elements, nothing else; then hear; of the tape as many rounds are left as
hear has left. -/
def placeHear [Sizes] [FinalNorm.In] (F : OnBytes.Model.Fork) (t : OnBytes.K.Kc.Tape) :
    Option (HeardAll × OnBytes.Model.Fork × OnBytes.K.Kc.Tape) :=
  (hear F (t.map fun r => { vals := r.sent.map fun x => .e x.triple,
                            drawn := ⟨r.drawn.map (·.triple), [], [], none⟩ })).map fun x =>
    (x.1, x.2.1, t.drop (t.length - x.2.2.length))

/-- The twelve reads, in the order in which the vector of reads holds them: to the range check. -/
def placeReads : List (FinalNorm.Read ⊕ Read) :=
  [.inr .wideAtKeys, .inr .wideAtCosts, .inl .streamAtSquares, .inl .streamAtNormed,
   .inl .actAtKeys, .inr .actAtLogits, .inl .rowAtKeys, .inl .rowAtPV, .inl .rowAtProducts,
   .inl .rowAtNormed, .inr .rowAtCosts, .inr .rowCount]

/-
WHY THE CLAIMS GIVE THE STATEMENT: the argument of the programs' comments. It takes for granted that
all forms are 0, that the lookup and the range check say of the cells what they are meant to, and
the tests on the plan (HeadOk.lean).
 1  All six numbers are at least 0, and every digit is in its range, by the lookup.
 2  A margin is its three digits, so it is at least 0: paid + BIG over >= gap. The bracket breaks
    ties downward.
 3  table: no middle digit is 0 at a position with a cost: paid + BIG over >= gap + 2^sh = cost.
 4  clip: paid + slackClip = C, so paid <= C. table and clip speak of every position and are tested
    at the one point zt, which was drawn after the cells were committed.
 5  over = 0: cost <= paid <= C. over > 0: the position is charged at least C.
    So min(cost, C) <= paid + C over.
 6  mean: sum (paid + C over) + sum slackMean = theta RC: (a). count: sum over + sum slackCap = cap;
    a cost above C forces over >= 1 (line 5, with paid <= C), and a position counts once: the number
    of costs above C is at most sum over, so at most cap: (b).
 7  Position T - 1, if it is checked (e = T), has no numbers: its margins are bare: gap = 0: (c).
 8  A pair (v, t) that is not real (v >= V, or t not checked) has digits 0 and the table's row 0.
OPEN: argued on no page that the writers know.
 A  From the field to the integers: the top digit has no cell and is formed with an inverse; the
    digits overlap; it rests on the no-overflow conditions, on a cell's bound from the range check,
    and on a bound on the weights that a request's proof does not show.
 B  zt serves five: the lookup, two sumchecks, table and clip. table and clip have no round of their
    own, so no term in the count of errors.
 C  Why the form that a sumcheck leaves, with the summand on the end values as shown, binds the
    hidden end values; and why, for a square, "both end values are equal, and the first is the
    stream's value" needs no further draw.
-/

end VerifiableInference.Desc.Kinds.Head
