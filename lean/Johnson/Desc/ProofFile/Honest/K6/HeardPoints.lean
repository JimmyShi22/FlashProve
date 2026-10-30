-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/HeardPoints.lean: THE OUTPUT HEAD'S OWN ROUNDS: THREE POINTS OF
WHAT THE VERIFIER'S STATE HOLDS AS HEARD AT THE HEAD, BEHIND AN ACCEPT OF THE SUB-PROTOCOL, ARE THE
ROUNDS' OWN CHALLENGES BY ROUND NUMBER: wpl.r (of the sumcheck on the squares: lPd + lt challenges),
tV.r (of the one on the products: lt) and tH.r (of the head's own: the first lt of lt + lPd) are
`headSumR` (Honest/K6/HeardWhole.lean) at parts number 2, 5 and 7, counted from 0. These parts have
lPd + lt + 3, lt + 3 and lt + lPd + 3 rounds (`headCut`, Honest/K6/Ask.lean): the terms for the
three points read none of the three further rounds of each; whether another field of the state keeps
what these drew is not said here. The test `linkedK6T` (Honest/K6/LinkedTest.lean, which this file
does not import) reads, of a list of challenges, the terms that stand here for tV.r and tH.r whole,
and the term for wpl.r behind `extract (lPd - ls) (lPd + lt)`. Lemmas on the verifier's state: of
the definitions under Johnson/Desc/ProofFile/Honest/ the statements name that reader by round number
and the two sizes `headLPd` and `headLt` (Honest/K6/Ask.lean), and no other. EVERY THEOREM BUT THE
FIRST TWO IS CONDITIONAL.

  `headSumR_size`, `headSumR_take`   the reader by round number gives n entries; the first n of
                         n + m are those of n. No premise: where the list has no round of that
                         number, or the round drew nothing, the entry is 0; `elemOf`
                         (Honest/K6/Ask.lean) takes what a round drew first and nothing more of it.
                         With the first, each of the three points below has its size by one
                         rewriting: lPd + lt, lt, lt
  `k6_points_at_accept`  behind an accepting step of the member. CONDITIONAL: M (the form in which
                         the IOP as written in Lean seats the member) · hst (the step accepts) ·
                         hW (the ledger in front is well laid)
  `k6_points_at_decide`  behind an accept of the bare sub-protocol's decision (that of `blockAt`;
                         h stands there for the shape of the output head, not for the premise
                         of the next two). CONDITIONAL: hd · hW
  `k6_points_at_341`     at number 341, counted from 0, of the first chain's flat list, from a
                         reached state. CONDITIONAL: h (`P5J.AtMg`, Johnson/P5J/AtMg.lean: the
                         library's bundle of premises at the full size, which that file calls "the
                         head": a hypothesis, not the output head of this file's title) · hr (the
                         state in front is reached: `Reach` at ft = 0; the type XP, the function
                         start and z stay free) · hb (b is the member) · hst (its step accepts, at
                         whichever ft)
  `k6_points_behind_341` at a state that is reached behind the member. CONDITIONAL: h · hr'. There
                         are a state reached in front, the member, and rounds and columns at which
                         its step accepts from the one to the other (rs.length = b.rounds.length;
                         ft = 0; the step returns cols.length), with the three equations at these
                         rounds

In each of the four conditional ends the three equations are on an x with s'.here = .head o and
o.x = some x: s' is at the output head and has x as what it heard. In the last theorem four clauses
stand in front of these two: reached in front · the member · the number of rounds · the step.

How: calls. `tables_at_accept` (Honest/K6/HeardAtYes.lean) has the three fields as those of
`headHeardWhole`; two of them are `headSumR` by unfolding, the third is the first lt coordinates of
`headSumR` at lt + lPd. At the decision: `heard_of_decide` (same file) and `hearing_tie`
(Honest/K6/HeardTie.lean), the letters laid as the proof of `tables_at_accept` lays them, with
`Came.given_ok` (Johnson/Desc/Kinds/Law/FromGiven.lean) and `zt_of_points`
(Johnson/Desc/K6/Honest/Law/Returns.lean). At 341: the member's form by `P4.k6_member_at_mg`
(Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean), the well-laid ledger by `P4.wellLaid_341` and
`P4.plan_at` (Johnson/P4R/FreeAt341N.lean). `headSumR_take` follows the lines of `headSumR_cut`
(Honest/K6/LinkedMark.lean), a file that is neither imported nor in the library.

Limits.
  - `heardOf_at_accept` (Honest/K6/HeardAtYes.lean) has fourteen fields of what was heard, these
    three among them; of the others nothing is said here. THE SIZE OF Zl (the field of what was
    heard that is cut off g1.zx, a point that the lookup on the head's calls left) IS NOT PROVED
    HERE: it hangs on the length of that point. `P1K8.zlSize_at_block`
    (Johnson/P1K8R/ZlSizeAtStep.lean; its statement is `P1K8.ZlSizeAtBlock`,
    Johnson/P1K8R/ZlSizeAtStepStatement.lean) states it: behind an accept of the bare
    sub-protocol's decision, under one premise on the sizes. Neither file is imported.
  - Of any rounds at which the sub-protocol accepts, not of an honest run's. That a state is reached
    at 341, or that the member accepts anywhere: not proved here. `P5J.AtMg` can be met: the richer
    bundle `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), which gives it, has a member at two named sets of
    public files (`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean ·
    `AtFullSide.Top.headMember_zGap`, AtFullSide/Top/HeadMemberAtGap.lean; neither is imported).
  - `k6_points_behind_341` says "there are rounds": not which rounds a session played: whoever holds
    the session's own step calls `k6_points_at_341`.
  - This file ties no test on challenges, `linkedK6T` among them, to a test of the verifier's.
  - THE FULL SIZE ALONE, and the format's second hash function alone, in the last two. Modules under
    lean/Johnson/Goal/ are among what this file imports: it imports none by name and calls nothing
    that is declared there. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.HeardAtYes
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P4R.FreeAt341N

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block OpenedColumn Place Claim Chain)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds (Point Head.Par Head.Request Head.Law.readsOf)
open VerifiableInference.Desc.Kinds.Head (parOf seatAt blockAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf WellLaid K6MemberIs zt_of_points)
open Johnson.Desc.First.Walk.Tied (Reach)

/-! ## 1 The reader by round number -/

/-- It gives n entries, at whichever list. -/
theorem headSumR_size (p : Head.Par) (i n : Nat) (own : List Fmt.Drawn) :
    (headSumR p i n own).size = n := by
  unfold headSumR
  simp

/-- The first n of its n + m entries are its n entries. -/
theorem headSumR_take (p : Head.Par) (i n m : Nat) (own : List Fmt.Drawn) :
    (headSumR p i (n + m) own).extract 0 n = headSumR p i n own := by
  apply Array.ext'
  unfold headSumR
  rw [Array.toList_extract, List.extract_eq_take_drop]
  apply List.ext_getElem?
  intro t
  show ((((List.range (n + m)).map fun j => elemOf own (headInFront p i + 1 + j)).drop 0).take
    (n - 0))[t]? = ((List.range n).map fun j => elemOf own (headInFront p i + 1 + j))[t]?
  rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map, List.getElem?_map]
  by_cases ht : t < n - 0
  · rw [if_pos ht, List.getElem?_range (show 0 + t < n + m by omega),
      List.getElem?_range (show t < n by omega)]
    show some (elemOf own (headInFront p i + 1 + (0 + t))) =
      some (elemOf own (headInFront p i + 1 + t))
    rw [Nat.zero_add]
  · rw [if_neg ht, List.getElem?_eq_none
      (show (List.range n).length ≤ t by rw [List.length_range]; omega)]
    rfl

/-! ## 2 Behind an accept -/

/-- **THE THREE POINTS BEHIND AN ACCEPTING STEP OF THE MEMBER.** CONDITIONAL: the member's form;
that its step accepts; a well-laid ledger in front. -/
theorem k6_points_at_accept {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
    {a : Place} {b : Block S Claim} (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n))
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s)) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard), s'.here = .head o ∧ o.x = some x ∧
      x.wpl.r =
        headSumR (parOf W.hS (workOf W)) 2
          (headLPd (parOf W.hS (workOf W)) +
            headLt (parOf W.hS (workOf W)))
          (rs.map (·.drawn)) ∧
      x.tV.r =
        headSumR (parOf W.hS (workOf W)) 5
          (headLt (parOf W.hS (workOf W))) (rs.map (·.drawn)) ∧
      x.tH.r =
        headSumR (parOf W.hS (workOf W)) 7
          (headLt (parOf W.hS (workOf W))) (rs.map (·.drawn)) := by
  obtain ⟨o, x, g1, y, ho, hx, _, _, _, e2, e3, _, e5, _⟩ := tables_at_accept M hst hW
  exact ⟨o, x, ho, hx, e2, e3,
    e5.trans (headSumR_take _ 7 (headLt (parOf W.hS (workOf W)))
      (headLPd (parOf W.hS (workOf W))) _)⟩

/-- **THE THREE POINTS BEHIND AN ACCEPT OF THE BARE SUB-PROTOCOL'S DECISION.** CONDITIONAL: that the
decision accepts; a well-laid ledger in front. -/
theorem k6_points_at_decide (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s')
    (hW : WellLaid ((seatAt h iU3).ledger s)) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard), s'.here = .head o ∧ o.x = some x ∧
      x.wpl.r =
        headSumR (parOf h work) 2
          (headLPd (parOf h work) +
            headLt (parOf h work))
          (rs.map (·.drawn)) ∧
      x.tV.r =
        headSumR (parOf h work) 5
          (headLt (parOf h work)) (rs.map (·.drawn)) ∧
      x.tH.r =
        headSumR (parOf h work) 7
          (headLt (parOf h work)) (rs.map (·.drawn)) := by
  obtain ⟨g, H, F, o, g1, hg, hh, ho, _, hx⟩ := heard_of_decide h iU3 work l s s' rs gs hd
  obtain ⟨z, y, _, _, hP, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := (parOf h work).sizes
  letI : VerifiableInference.Desc.Kinds.Head.Policy := (parOf h work).policy
  letI : Head.Request := (seatAt h iU3).request s
  letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  letI : VerifiableInference.Desc.Kinds.FinalNorm.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf h work).floor z.1 z.2).norm
  letI : VerifiableInference.Desc.Kinds.Head.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf h work).floor z.1 z.2).head
  have hzt := @zt_of_points (parOf h work).sizes _ _ _ hP
  obtain ⟨_, _, a2, _, _, a5, _, a7⟩ := hearing_tie (parOf h work) rfl hW hh hzt
  exact ⟨o, _, ho, hx, a2, a5,
    (congrArg (fun r : Point => r.extract 0 (headLt (parOf h work))) a7).trans
      (headSumR_take _ 7 (headLt (parOf h work)) (headLPd (parOf h work)) _)⟩

/-! ## 3 At number 341, counted from 0, of the first chain's flat list -/

section AtHead
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
include h

/-- **THE THREE POINTS BEHIND THE MEMBER'S ACCEPTING STEP FROM A REACHED STATE.** CONDITIONAL: h
(`P5J.AtMg`); the state in front is reached at border 341; b is the member; its step accepts. -/
theorem k6_points_at_341 {XP : Type} {start : XP → S} {z : XP} {s s' : S}
    (hr : Reach 0 cF.blocksInOrder start 341 (z, s)) {b : Block S Claim} (hb : cF.blocksInOrder[341]? = some b)
    {ft : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (hst : b.step ft s rs cols = .ok (s', n)) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard), s'.here = .head o ∧ o.x = some x ∧
      x.wpl.r =
        headSumR (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) 2
          (headLPd (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) +
            headLt (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))))
          (rs.map (·.drawn)) ∧
      x.tV.r =
        headSumR (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) 5
          (headLt (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) (rs.map (·.drawn)) ∧
      x.tH.r =
        headSumR (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) 7
          (headLt (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) (rs.map (·.drawn)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', e, M⟩ := P4.k6_member_at_mg h
  obtain rfl : b' = b := Option.some.inj (e.symm.trans hb)
  exact k6_points_at_accept M hst
    (P4.wellLaid_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hr _ _)

/-- **AT A STATE THAT IS REACHED BEHIND THE MEMBER**: there are a state reached in front, the
member, and rounds and columns at which its step accepts from the one to the other; at these rounds
the three equations hold. CONDITIONAL: h (`P5J.AtMg`); the state is reached at border 341 + 1. -/
theorem k6_points_behind_341 {XP : Type} {start : XP → S} {z : XP} {s' : S}
    (hr' : Reach 0 cF.blocksInOrder start (341 + 1) (z, s')) :
    ∃ (s : S) (b : Block S Claim) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (o : HeadOwn)
      (x : OnBytes.Model.Head.Heard),
      Reach 0 cF.blocksInOrder start 341 (z, s) ∧ cF.blocksInOrder[341]? = some b ∧
      rs.length = b.rounds.length ∧ b.step 0 s rs cols = .ok (s', cols.length) ∧
      s'.here = .head o ∧ o.x = some x ∧
      x.wpl.r =
        headSumR (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) 2
          (headLPd (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) +
            headLt (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))))
          (rs.map (·.drawn)) ∧
      x.tV.r =
        headSumR (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) 5
          (headLt (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) (rs.map (·.drawn)) ∧
      x.tH.r =
        headSumR (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) 7
          (headLt (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) (rs.map (·.drawn)) := by
  cases hr' with
  | succ hr hb hy =>
    obtain ⟨R, c, hl, hst⟩ := hy
    obtain ⟨o, x, ho, hx, e1, e2, e3⟩ := k6_points_at_341 h hr hb hst
    exact ⟨_, _, R, c, o, x, hr, hb, hl, hst, ho, hx, e1, e2, e3⟩

end AtHead

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSumR_size
#print axioms ProofFile.Honest.K6.headSumR_take
#print axioms ProofFile.Honest.K6.k6_points_at_accept
#print axioms ProofFile.Honest.K6.k6_points_at_decide
#print axioms ProofFile.Honest.K6.k6_points_at_341
#print axioms ProofFile.Honest.K6.k6_points_behind_341
