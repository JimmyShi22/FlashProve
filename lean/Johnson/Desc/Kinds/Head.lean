-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Head.lean: THE OUTPUT HEAD'S OWN ROUNDS, a kind of block of the protocol. It
reduces claims: it opens no oracle and tests no value by itself. Definitions only; nothing is proved
here. What is public and what is committed: HeadPublic.lean, to be read first.
THE STATEMENT, in integers. act: the final normalization of the committed matrix stream, clamped.
Wh: the committed head weights. logit t v = sum over k < d of act t k * Wh k v: the logit of
vocabulary entry v at position t. win t: the token that position t is about: token t + 1 of the
request; at the last position, T - 1, the prover's next token y.
  gap t = the maximum over v < V of  logit t v - logit t (win t) + [v < win t]:
it is 0 exactly if win t is the top choice, the lowest index on ties. The positions r <= t < e are
checked; a checked position below T - 1 has the cost gap t + 2^sh.
  (a) The costs, each counted as at most C, add up to at most theta times their number RC.
  (b) At most cap positions have a cost above C.
  (c) If e = T: gap (T - 1) = 0: y is the last position's top choice, whatever the policy.
C and theta are in units of a cost; the least cost is 2^sh. Exact match: C = theta = 2^sh, cap = 0.
Other values say less: theta = C with cap = T admits any tokens of the request; (c) stands even so.
THE LAW, STATED IN HeadLaw.lean AND PROVED (1: lemma1, Law/Values.lean; 2: lemma2a,
Law/Lemma2a.lean; 3: lemma2b, Law/Lemma2b.lean; of the normalization nothing is stated). In all
three the request's test holds and y is a token. 1, without chance: if the tests on the plan hold,
Wh is at
most 2^12 and act at most 2047 in size, every cell is below 2^18, the six numbers' 21 digits are
bytes, and AT EVERY ENTRY AND POSITION each of the five keys is a row of its table (the table's row
0 holds 2^F, every row from 1 to 2^F) and clip and table hold, and mean and count hold: then (a),
(b), (c). 2, without chance: at any point clip, table and the keys are the sums of their values at
the entries and positions under the equality weights. 3, round by round: if the list of hidden
scalars in front has a place for each number, each element sent or drawn is written canonically (its
words below p), logitForms are 0, the reads and the claim on the weights are true and no bad element
was drawn (at most three a round), claimed is the true sum. From forms that are 0 at drawn points to
1's conditions the way is stated and proved in two laws around the lookup, k06Out and k06Back
(Law/Clamp.lean); there the laws of the lookup, the range check and the merge are named premises,
and the bound |Wh| ≤ 2^12 is shown by no test, no kind and no request's proof. The head's bad
elements are counted round by round, each round's list at most the plan's price (k06Rounds,
Law/K06Rounds.lean, under 0 < lt), and carried into a piece's errors by k6Own (Law/K6Own.lean),
under premises on the piece that no piece is shown to meet; those files bound no probability.
OPEN (HeadRow.lean). A: from the field to the integers at the top digit, which has no cell. B: clip
and table have no draw of their own: they are riders of the lookup at its point zt, and the rider's
law at them is proved with the plain lookup's list of bad challenges, no term added (k6_good,
Johnson/Top/H/K3RiderK6.lean, by tail_good, K3RiderTail.lean), under FoNums.ok and lt ≤ dT; reading
its clause behind as the head's two sums wants IsTail and zt.size = lt (k6_tgt), the lookup's caller
c₀, the record of cells cOf and rdm are letters there, and those files claim no soundness of any
text that runs. C: why the form that a masked sumcheck leaves, with the summand on the end values as
shown, binds the hidden end values.
WHERE IT STANDS. y is sent in the clear; the prover commits to the head's cells and to masks; the
lookup runs, and its draws fix the point zt on the positions; THESE ROUNDS; the prover commits to
the reads; the range check (it bounds each cell, and ties each read to its cells); the merge (it
reduces the claim on Wh to a row of the stored commitment); one element is drawn and all forms are
added under its powers: one linear equation is tested.
THE FIELD. E: the cubic extension of F_p, p = 2^64 - 2^32 + 1. An integer stands for its image in
F_p; the tests on the plan (HeadOk.lean) keep both sides of each equation below 2^60.
LETTERS (HeadCells.lean). A form is affine in hidden scalars and in entries of reads (entry x i). Of
a hidden scalar x the verifier sees x.shown, a masked value; x.var is x as a variable of a form.
eq z i: the equality weight of the index i at the point z. ew k v: the public weight of entry v of
key k at the lookup's point; wx k: their sum over v < V; below v: marginTop's over the entries below
v. atCosts n, summed n: the hidden number n, summed over the positions with a cost under eq zt, or
plainly; ERC: their weight under eq zt; phiC t: eq zt t at such a position, else 0. BIG = 2^37.
-/
import Johnson.Desc.Kinds.HeadCells
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace VerifiableInference.Desc.Kinds.Head
open OnBytes (E)
open Norm (lt d lPd T)
open FinalNorm (zt zl)

/-! ## ROUNDS, as data: each round's name, how many scalars the prover sends, how many elements are
drawn. 16 + 2 lPd + 4 lt rounds. No round sends a commitment. In order, as (sent, drawn):
  the normalization: a point (0, lt) · a batching (9, 1) · a level in lPd + lt variables ·
  a batching (7, 1) · a sumcheck in lt variables with 4 end values · one in lt variables with 2;
  the head: a sumcheck in lt + lPd variables with 2 end values.
A MASKED SUMCHECK in n variables with m end values: (2, 1): the claimed sum and the hiding
polynomial's sum; eps is drawn · n times (2, 1): two coefficients; a challenge · (2, 1): two
coefficients in one further variable; beta is drawn, never 0 · (m, 0): the end values, masked.
A level: the same with 2 end values; its sum is a form fixed before: (1, 1) first; (0, 1) last. -/
def rounds [Sizes] : List Round := Norm.rounds ++ FinalNorm.rounds ++ sumcheck.rounds (lt + lPd) 2
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-! ## DECIDES -/
/-- The verifier hears, and tests the rounds' shape alone. First the normalization's two parts. Then
one masked sumcheck with two end values, act and UH at the challenges, of the relation
  2^lPd claimed = sum over t and k < d of  eq zt t * act t k * UH k t,
  UH k t = [t checked] (wx Wh k (win t) - sum over v < V of ew v * Wh k v).
That is the sum over t, v of eq zt t [t checked] ew v (logit t (win t) - logit t v). halves n: n
coordinates 1/2, at which an equality-weighted sum is 2^-n times the plain sum. -/
def hear : Hear HeardAll := do
  let norm ← Norm.hear
  let final ← FinalNorm.hear
  let logits ← sumcheck (zt ++ halves lPd) 2
  pure (norm, final, { logits })
variable [Norm.Heard] [FinalNorm.Heard] [Heard]

/-! ## READS: no oracle. Twelve vectors of sums of cells, under weights that are fixed by now, are
asked of the prover, who commits to them next: seven in HeadNorm.lean, and these five. -/
/-- Which matrix a read sums, and under which weights: long: inside a block of features, and on the
positions; short: on the positions. rH, rs: the sumcheck's challenges on positions, on features. -/
def Read.of : Read → Matrix × Weights
  | .wideAtKeys  => (.wide, .long (eq zl) (eq zt))
  | .wideAtCosts => (.wide, .long (fun _ => 1) phiC)
  | .actAtLogits => (.act,  .short (eq rH))
  | .rowAtCosts  => (.row,  .short phiC)
  | .rowCount    => (.row,  .short fun t => if costed t then 1 else 0)
variable [FinalNorm.Reads] [Reads]

/-! ## CLAIMS -/
/-- THE MARGIN of vocabulary entry v at a checked position t is
  logit t (win t) + paid t + BIG over t - logit t v - [v < win t]
(at t = T - 1, which has no cost, paid and over are absent). It is written low + 2^sh mid +
2^(sh+15) top, three digits in ranges: so it is not negative. mid has 16 bits: the digits overlap,
so that an honest prover can choose mid >= 1 wherever the margin is at least 2^sh. The top digit has
no cell: its key is the margin less the lower digits, divided in the field. At a pair with v >= V or
t not checked there is no margin, and the three keys are in range only if all are 0. -/
def top : Form :=
  let ties : E := ∑ t < T, if checked t then eq zt t * below (win t) else 0
  OnBytes.invE (2 ^ (sh + 15)) • ((2 ^ lPd : Nat) • logits.claimed.var
    + wx .marginTop • (atCosts .paid + BIG • atCosts .over) - ties
    - (2 ^ sh : Nat) • mid .marginTop - low .marginTop)
/-- Handed to the lookup as values; they are not among the forms that must be 0: five keys, each
summed at the lookup's point. top, mid: 16 bits. low: 8 bits. The table, in two halves cut at entry
JVa: mid + 2^16 (table value) is u + 2^16 (row u's value); it is the step table 2^F, 2, 1, 1, ..: a
test that mid is not 0. -/
def key : Key → Form
  | .marginTop => top
  | .marginMid => mid .marginMid
  | .marginLow => low .marginLow
  | .tableA    => mid .tableA + (2 ^ 16 : Nat) • tableValue .tableA
  | .tableB    => mid .tableB (v0 := JVa) + (2 ^ 16 : Nat) • tableValue .tableB (v0 := JVa)

/-- THE POLICY: four forms that must be 0. mean, count: (a), (b) as plain sums, with slacks >= 0. -/
def mean : Form := summed .paid + C • summed .over + summed .slackMean - theta * RC
def count : Form := summed .over + summed .slackCap - (if RC > 0 then cap else 0)
/-- At each position with a cost, tested at the one point zt: paid + slackClip = C: so paid <= C. -/
def clip : Form := atCosts .paid + atCosts .slackClip - C * ERC
/-- Likewise: slackTable and the position's V table values add up to 2^F. Row 0 of the table holds
2^F, every row from 1 to 2^F, and V >= 2: so no middle digit is 0, every margin is at least 2^sh,
and paid + BIG over >= gap + 2^sh = cost. The form sums all JV entries and takes (JV - V) 2^F out
again: an entry from V on has the middle digit 0 (see top), so its table value is 2^F exactly. -/
def table : Form := atCosts .slackTable + tableValuesAtCosts - ((JV - V + 1) * 2 ^ F) * ERC
def policy : List Form := [mean, count, clip, table]

/-- The sumcheck's own form: it holds the masks; its argument is the summand on the end values as
shown (see OPEN, C). Then: the first end value is act at the challenges. The second, UH there, goes
to the merge as a claim on Wh: forTheMerge (HeadCells.lean). (Who lays the claim that the merge
takes in the proof file's description: HeadFrame.lean, at Seat.) -/
def logitForms : List Form :=
  [logits.left ((logits.end_ 0).shown * (logits.end_ 1).shown),
   (logits.end_ 0).var - ∑ k < d, eq rs k • FinalNorm.actAt (entry .actAtLogits) k]
/-- THE 35 FORMS, in three named runs: they are not neighbours in the order in which all claims of
this part of the proof are batched. -/
def claims : List (String × List Form) :=
  [("norm", FinalNorm.forms), ("policy", policy), ("logits", logitForms)]
/-- GUESTS: tests that have no draw of their own and borrow another block's point: here the lookup's
zt, of degree 1 in each coordinate: they are riders of the lookup (the head, B). -/
def guests : List (String × Form) := [("clip", clip), ("table", table)]

/-! ## SENDS (the honest prover): written in Lean in part alone: Law/HeadSends.lean (lean/GAPS.md).
As a record of Johnson/Desc/Block.lean (name, place, tests on the plan, rounds, decide, claims):
HeadKind.lean, over HeadFrame.lean (what is read of the carried record and laid into it).
Asked elsewhere: Request.ok (HeadOk.lean: r < e <= T; every token below V), where the instance comes
in; that y is a token, by the next token's block; that the lookup's calls share zt, by the lookup.
In the proof file's description the test that runs is S.reqOk (Johnson/Desc/First/State.lean), at
the first record and in front of the seated decision.
-/
end VerifiableInference.Desc.Kinds.Head
