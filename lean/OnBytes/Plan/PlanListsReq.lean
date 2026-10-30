-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/PlanListsReq.lean: the whole plan of a proof's first chain, as a list, with the
sub-proofs' rounds as lists that are given.

The like of OnBytes/Plan/PlanListsKey.lean for the first of a proof's three chains (`firstPlan`,
OnBytes/Params/DeriveReq.lean); the other two are a shared chain and a second chain
(OnBytes/Params/PlanListsChains.lean). The chain's frame goes group by group (`reqPlanFrom`): a
reply in plain, if the link has one; the sending of the group's oracle messages; from the second
group on the round of positions at which the group before is opened, which also takes in the
sending's answers; then, while a link is left, the rounds of the link's sub-proof moment by moment
with the sendings between them, the round that batches, and the fold that closes the link; and at
the last group the proximity test. After the frame come what is sent after the links, the batching
of the pending rows, the first part of the test on the table, and SEAL. The sub-proofs' routines are
arguments of the frame (`Subproofs`). So are their lists here: `SubRuns` asks that each routine adds
the rounds of its list, from nothing open to nothing open, under a request's own scope.
OnBytes/Model/LinkRoundsList.lean proves that of the model's sub-proofs. For
every sizing of a
proof: nothing is evaluated.

Main definitions: `reqSampled`, `reqSendOwn`, `reqSendOpen`, `SubRuns`, `sentAtMoment`,
`momentsRows`, `momentsList`, `locRound`, `membersOf`, `carriedRows`, `closedGroup`, `reqListFrom`,
`battList`, `firstChainList`.
Main theorems: `runs_scopeRequest`, `runs_reqSend_own`, `runs_reqSend_open`, `runs_reqMoments`,
`runs_reqTail`, `runs_reqReply`, `runs_reqMid`, `runs_reqPlanFrom`, `runs_firstRounds`,
`firstPlan_rounds`.
What is not claimed: that the plan is finished or holds: that is the hypothesis of
`firstPlan_rounds`. The converse: that a plan whose described rounds hold is finished or holds.
Where a number of trees does not follow, a sending's list is written as empty; the plan is then
refused, and no theorem here keeps that the number was there. So is the first part of the test on
the table where the plans' sizes do not follow (`linFirstList`); that they were there is kept in
OnBytes/Plan/PlanListsProof.lean. That the last test has two stages is not kept. `SubRuns` asks,
through `Runs`, that a sub-proof's routine leaves the scope as it found it; the frame bears one that
changes it, and of such a routine nothing is said here. Of the routines' own tests nothing is kept.
What the planner counts at a group with kept oracle messages is read off the definitions. A group's
kept messages are here those that the switch into it sends anew (`keptOf`), also one that the group
reads for the last time and does not keep again. A closed link's group has 2 ^ clog2 (1 + R) slots,
R the main rows of the next group's kept messages together (`closedGroup`). The switch into a group
leaves on it one claim, one old sample row for each answer of each of its kept messages, and 3 + R'
rows for each drawn position, R' the main rows of its own kept messages together (`carriedRows`). A
message counts with the main rows that its shape says (`mainRows`): no message's number is rounded
up to a power of two by itself, as `rowBlock` (OnBytes/Iop/Req.lean) does for rows that are not
kept; only 1 + R is rounded up. That the program's blocks state these rounds in a dry run. Nothing
on the kinds of written rounds: an entry of a plan has none. Nothing on the C++ planner, of which
OnBytes/Params/ and OnBytes/Plan/ are renderings. For proofs only; the program, that is the Lean
port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.DeriveReq
import OnBytes.Plan.PlanListsKey

set_option autoImplicit false

namespace OnBytes.Plan

open OnBytes.Params

section
variable {s : Setting}

/-- Setting the scope to a request's own, where it is that already, changes nothing. -/
theorem runs_scopeRequest (b r a : Nat) :
    Runs s .request b r a (modify fun p => { p with scope := .request } : Planning PUnit) () []
      b r a := by
  intro p p' v' hs hc hb hr ha h
  have h' : (Except.ok ((), ({ p with scope := .request } : PlanState)) :
      Except String (Unit × PlanState)) = .ok (v', p') := h
  cases h'
  exact ⟨rfl, hs, rfl, by simp, hb, hr, ha, by simp⟩

/-- The samples of a sending of oracle messages of a link's group, in the words of `reqSend`. -/
def reqSampled (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) : List SampleSize :=
  (zipT (List.range sent.length) sent).filter (fun x => 0 < x.2.shape.answers) |>.map
    fun x => (⟨cubeBitsOf codes x.2.shape,
      [if x.1 < sent.length - riders then group else atStart]⟩ : SampleSize)

/-- The rounds of such a sending with a round of its own for the answers. Written as empty where the
number of trees does not follow; the plan is then refused. -/
def reqSendOwn (s : Setting) (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) : List RoundSpec :=
  ((treesOf codes sent.toArray).map
    (sendList s (reqSampled codes sent group atStart riders))).getD []

/-- The round of such a sending whose answers stay open. Written as empty where the number of trees
does not follow; the plan is then refused. -/
def reqSendOpen (s : Setting) (codes : Codes) (sent : List OracleNotice)
    (group atStart : GroupSize) (riders : Nat) : List RoundSpec :=
  ((treesOf codes sent.toArray).map fun n =>
    [sendSeed s (reqSampled codes sent group atStart riders) n]).getD []

variable {c : Scope}

/-- The sending with its own round for the answers. -/
theorem runs_reqSend_own (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) :
    Runs s c 0 0 0 (reqSend codes sent group atStart riders true) ()
      (reqSendOwn s codes sent group atStart riders) 0 0 0 := by
  unfold reqSend reqSendOwn
  refine runs_must (L := sendList s (reqSampled codes sent group atStart riders)) ?_
  intro n
  exact runs_send _ n

/-- The sending whose answers stay open. -/
theorem runs_reqSend_open (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) :
    Runs s c 0 0 0 (reqSend codes sent group atStart riders false) ()
      (reqSendOpen s codes sent group atStart riders)
      (24 * (s.samples * (reqSampled codes sent group atStart riders).length)) 0
      (s.samples * (reqSampled codes sent group atStart riders).length) := by
  unfold reqSend reqSendOpen
  refine runs_must
    (L := fun n => [sendSeed s (reqSampled codes sent group atStart riders) n]) ?_
  intro n
  exact runs_send_open _ n

end

/-- What is asked of the sub-proofs' routines: under a request's own scope, from nothing open to
nothing open, the routine of link l at a moment m adds the rounds of the list `L l m`, and what is
sent after the links those of `after`. `Runs` also asks that a routine leaves the scope as it found
it. The frame sets the scope anew after each of these routines, so it bears one that changes the
scope; of such a routine the theorems here say nothing. -/
structure SubRuns (s : Setting) (sub : Subproofs) (L : Nat → Nat → List RoundSpec)
    (after : List RoundSpec) : Prop where
  plan : ∀ l m, Runs s .request 0 0 0 (sub.plan l m) () (L l m) 0 0 0
  after : Runs s .request 0 0 0 sub.afterLinks () after 0 0 0

/-- The oracle messages of a link that are sent at a moment. -/
def sentAtMoment (msgs : List ReqMessage) (moment : Nat) : List OracleNotice :=
  (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩

/-- The sample rows that the moments of a link from `moment` on add, as many as the fuel. -/
def momentsRows (msgs : List ReqMessage) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, moment =>
    sumT ((sentAtMoment msgs moment).map (·.shape.answers)) + momentsRows msgs fuel (moment + 1)

/-- The rounds of the moments of link l from `moment` on, as many as the fuel: the sending of a
moment's oracle messages and the sub-proof's rounds after it. -/
def momentsList (z : ProofSized) (L : Nat → Nat → List RoundSpec) (l : Nat)
    (msgs : List ReqMessage) : Nat → Nat → List RoundSpec
  | 0, _ => []
  | fuel + 1, moment =>
    reqSendOwn z.set z.codes (sentAtMoment msgs moment) z.link.group z.batch.own.first 0 ++
      (L l moment ++ momentsList z L l msgs fuel (moment + 1))

/-- The moments of a link. -/
theorem runs_reqMoments {z : ProofSized} {sub : Subproofs} {L : Nat → Nat → List RoundSpec}
    {after : List RoundSpec} (S : SubRuns z.set sub L after) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment : Nat, Runs z.set .request 0 0 0 (Params.reqMoments z sub l msgs fuel moment)
      (momentsRows msgs fuel moment) (momentsList z L l msgs fuel moment) 0 0 0
  | 0, _ => runs_pure 0 0 0 0
  | fuel + 1, moment => by
      unfold Params.reqMoments
      exact Runs.cast (runs_bind (runs_reqSend_own _ _ _ _ _) (runs_bind (S.plan l moment)
        (runs_bind (runs_scopeRequest 0 0 0) (runs_bind (runs_reqMoments S l msgs fuel (moment + 1))
          (runs_pure _ 0 0 0))))) (by simp [momentsList, sentAtMoment])

/-- The round of positions at which a closed link's group is opened, with what is open of the
sending before it. -/
def locRound (s : Setting) (c : Scope) (g : GroupSize) (b r a : Nat) : RoundSpec :=
  .said "LOC" .query (Bound.pow (analysis s g).mainAt.agree (baseCount s c g))
    { poss := baseCount s c g, logN := g.main.logN, group := pricedOf g, priced := .asSaid } b r a

/-- The oracle messages that are members of group number l, in the words of `reqPlanFrom`: the
target of the switch, if it is not the first group; the kept messages; the link's messages of moment
0; the fold's mask. -/
def membersOf (z : ProofSized) (l : Nat) (g : ReqGroup) (msgs : List ReqMessage) :
    List OracleNotice :=
  (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
    (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
    (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
    [foldMaskNotice (ioppFoldShape ⟨z.request.code, z.request.maskCode, g.k, g.h⟩ {})]

/-- The rows that the switch into group number l leaves on it: none at the first group; else the
carried claim, the kept messages' old sample rows, and 3 + (kept rows) for each drawn position. -/
def carriedRows (z : ProofSized) (l : Nat) (g : ReqGroup) (before : GroupSize) : Nat :=
  if 0 < l then
    1 + sumT ((keptOf g).map (·.shape.answers)) +
      baseCount z.set .request before * (3 + sumT ((keptOf g).map (·.shape.mainRows)))
  else 0

/-- The group of a link as it is closed: the links' group with the group's numbers of row variables,
and 2 ^ clog2 (1 + R) slots, R the main rows of the messages that are sent anew in the next group
(`keptOf`), whether that group keeps them again or not. -/
def closedGroup (z : ProofSized) (g : ReqGroup) (gs : List ReqGroup) : GroupSize :=
  { z.link.group with
    k := g.k, h := g.h,
    slots := 2 ^ clog2 (1 + sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))) }

/-- The frame's rounds from group number l on, with the sub-proofs' lists between them. The last
argument is the group of the link that was closed last; it is not read at l = 0. Where no link is
left the list ends with the last test, whatever groups are left. -/
def reqListFrom (z : ProofSized) (L : Nat → Nat → List RoundSpec) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → List RoundSpec
  | _, [], _, _, _ => []
  | l, g :: gs, links, open_, before =>
    let msgs := (links.head?.map (·.messages)).getD []
    let members := membersOf z l g msgs
    let sent := if l == 0 then members ++ z.request.atStart else members
    let sg := if links.head?.isSome then z.link.group else z.last.first
    let riders := if l == 0 then z.request.atStart.length else 0
    let n := (reqSampled z.codes sent sg z.batch.own.first riders).length
    (if (links.head?.map (·.plain)).getD 0 != 0 then
      [.silent "REPLY" (24 * (links.head?.map (·.plain)).getD 0) 0] else []) ++
    ((if l == 0 then reqSendOwn z.set z.codes sent sg z.batch.own.first riders
      else reqSendOpen z.set z.codes sent sg z.batch.own.first riders ++
        [locRound z.set .request before (24 * (z.set.samples * n)) 0 (z.set.samples * n)]) ++
    (match links.head? with
    | none =>
      ioppList z.set .request z.last.stages
        (carriedRows z l g before + sumT (members.map (·.shape.answers))) 0
        z.request.choice.masksRide
    | some _ =>
      L l 0 ++ (momentsList z L l msgs ((msgs.getLast?.map (·.moment + 1)).getD 0 - 1) 1 ++
        (batRound z.set [closedGroup z g gs]
            (open_.headD 0 + carriedRows z l g before + sumT (members.map (·.shape.answers)) +
              momentsRows msgs ((msgs.getLast?.map (·.moment + 1)).getD 0 - 1) 1) ::
          (foldList z.set (closedGroup z g gs) 0 ++
            reqListFrom z L (l + 1) gs (links.drop 1) (open_.drop 1) (closedGroup z g gs))))))

/-- What follows the sending and the round of positions in a group: the last test, if no link is
left; else the link's sub-proof with its moments, the batching, the fold, and the groups after. -/
theorem runs_reqTail {z : ProofSized} {sub : Subproofs} {L : Nat → Nat → List RoundSpec}
    {after : List RoundSpec} (S : SubRuns z.set sub L after) (l : Nat) (link : Option ReqLink)
    (msgs : List ReqMessage) (fuel o C rows : Nat) (closed : GroupSize) {next : Planning Unit}
    {rest : List RoundSpec} (ih : Runs z.set .request 0 0 0 next () rest 0 0 0) :
    Runs z.set .request 0 0 0
      (match link with
      | none => planIopp z.last.stages (C + rows) 0 z.request.choice.masksRide
      | some _ => do
        sub.plan l 0
        modify fun p => { p with scope := .request }
        let more ← Params.reqMoments z sub l msgs fuel 1
        planBat [closed] (o + C + rows + more)
        planFold closed 0
        next) ()
      (match link with
      | none => ioppList z.set .request z.last.stages (C + rows) 0 z.request.choice.masksRide
      | some _ =>
        L l 0 ++ (momentsList z L l msgs fuel 1 ++
          (batRound z.set [closed] (o + C + rows + momentsRows msgs fuel 1) ::
            (foldList z.set closed 0 ++ rest)))) 0 0 0 := by
  cases link with
  | none => exact runs_iopp _ _ _ _
  | some v =>
    exact Runs.cast (runs_bind (S.plan l 0) (runs_bind (runs_scopeRequest 0 0 0)
      (runs_bind (runs_reqMoments S l msgs fuel 1) (runs_bind (runs_bat _ _)
        (runs_bind (runs_fold _ _) ih))))) (by simp)

/-- The reply in plain, if the link has one, and what follows. -/
theorem runs_reqReply {s : Setting} {c : Scope} (n : Nat) {k : Unit → Planning Unit}
    {rest : List RoundSpec} (h : Runs s c 0 0 0 (k ()) () rest 0 0 0) :
    Runs s c 0 0 0
      (if (n != 0) = true then do
        planScalars n
        let y ← closeNone "REPLY"
        k y
      else do
        let y ← pure PUnit.unit
        k y) ()
      ((if (n != 0) = true then [.silent "REPLY" (24 * n) 0] else []) ++ rest) 0 0 0 := by
  by_cases hp : (n != 0) = true
  · rw [if_pos hp, if_pos hp]
    exact Runs.cast (runs_bind (runs_scalars0 n 0 0) (runs_bind (runs_closeNone _ _ _ _) h))
      (by simp)
  · rw [if_neg hp, if_neg hp]
    exact Runs.cast (runs_bind (runs_pure () 0 0 0) h) (by simp)

/-- The sending of a group's oracle messages and, from the second group on, the round of positions
at which the group before is opened; and what follows, which reads the rows that are carried. -/
theorem runs_reqMid {s : Setting} (l : Nat) (codes : Codes) (sent : List OracleNotice)
    (sg atStart : GroupSize) (riders : Nat) (before : GroupSize) (A B : Nat)
    {k : Nat → Planning Unit} {rest : Nat → List RoundSpec}
    (hk : ∀ C, Runs s .request 0 0 0 (k C) () (rest C) 0 0 0) :
    Runs s .request 0 0 0
      (do
        reqSend codes sent sg atStart riders (l == 0)
        if 0 < l then do
          let t ← planLoc before
          let y ← pure (A + t * B)
          k y
        else do
          let y ← pure 0
          k y) ()
      ((if l == 0 then reqSendOwn s codes sent sg atStart riders
        else reqSendOpen s codes sent sg atStart riders ++
          [locRound s .request before
            (24 * (s.samples * (reqSampled codes sent sg atStart riders).length)) 0
            (s.samples * (reqSampled codes sent sg atStart riders).length)]) ++
        rest (if 0 < l then A + baseCount s .request before * B else 0)) 0 0 0 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp only [Nat.lt_irrefl, beq_self_eq_true, if_true, if_false]
    exact Runs.cast (runs_bind (runs_reqSend_own _ _ _ _ _) (runs_bind (runs_pure 0 0 0 0) (hk 0)))
      (by simp)
  · have h0 : (l == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    simp only [h0, hl, if_true, Bool.false_eq_true, if_false]
    exact Runs.cast (runs_bind (runs_reqSend_open _ _ _ _ _) (runs_bind (runs_loc before _ _ _)
      (runs_bind (runs_pure _ 0 0 0) (hk _)))) (by simp [locRound])

/-- The frame's rounds from group number l on. -/
theorem runs_reqPlanFrom {z : ProofSized} {sub : Subproofs} {L : Nat → Nat → List RoundSpec}
    {after : List RoundSpec} (S : SubRuns z.set sub L after) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize),
      Runs z.set .request 0 0 0 (reqPlanFrom z sub l gs links open_ before) ()
        (reqListFrom z L l gs links open_ before) 0 0 0
  | [], _, _, _, _ => by
      unfold reqPlanFrom reqListFrom
      exact runs_pure () 0 0 0
  | g :: gs, l, links, open_, before => by
      unfold reqPlanFrom reqListFrom
      refine runs_reqReply _ ?_
      exact runs_reqMid l _ _ _ _ _ before _ _ (fun C => runs_reqTail S l _ _ _ _ C _ _
        (runs_reqPlanFrom S gs (l + 1) (links.drop 1) (open_.drop 1) (closedGroup z g gs)))

/-- The rounds by which several pending rows become one. -/
def battList (s : Setting) (rows kCol : Nat) : List RoundSpec :=
  .said "BAT-sigma" .field (powersError s rows) { drawE := 1, rows := rows, priced := .asSaid }
    0 0 0 :: pscList s { degree := List.replicate kCol 3, withY := false }

/-- The rounds of a proof's first chain: the frame of the chain of links with the sub-proofs' lists
between; what is sent after the links; the batching of the pending rows, if there are several; the
first part of the test on the table; SEAL. -/
def firstChainList (z : ProofSized) (sub : Subproofs) (L : Nat → Nat → List RoundSpec)
    (after : List RoundSpec) : List RoundSpec :=
  reqListFrom z L 0 (reqGroups z.request).toList z.request.link sub.openRows z.link.group ++
    (after ++ ((if 1 < sub.pendingRows then battList z.set sub.pendingRows z.batch.shape.kCol
        else []) ++
      (linFirstList z.set z.codes z.batch ++ [sealRound])))

/-- The routine of a proof's first chain. -/
theorem runs_firstRounds {z : ProofSized} {sub : Subproofs} {L : Nat → Nat → List RoundSpec}
    {after : List RoundSpec} (S : SubRuns z.set sub L after) :
    Runs z.set .request 0 0 0
      (do
        reqPlan z sub
        sub.afterLinks
        modify fun p => { p with scope := .request }
        if 1 < sub.pendingRows then planBatt sub.pendingRows z.batch.shape.kCol
        linPlanFirst z.codes z.batch
        planSeal) () (firstChainList z sub L after) 0 0 0 := by
  unfold reqPlan firstChainList
  exact Runs.cast (runs_bind (runs_reqPlanFrom S _ 0 _ _ _) (runs_bind S.after
    (runs_bind (runs_scopeRequest 0 0 0) (runs_when (runs_batt _ _)
      (runs_bind (runs_linPlanFirst _ _) runs_seal))))) (by simp [battList])

/-- **The plan of a proof's first chain**, against its list: the setting, the rounds of the list,
what `close` has tested of each round with a verifier's message, and each round holds in the
planner's reckoning. -/
theorem firstPlan_rounds {z : ProofSized} {sub : Subproofs} {L : Nat → Nat → List RoundSpec}
    {after : List RoundSpec} (S : SubRuns z.set sub L after) {P : Planned}
    (h : firstPlan z sub = .ok P) : PlanIs P z.set .request (firstChainList z sub L after) :=
  planIs_of (runs_firstRounds S) h

end OnBytes.Plan

#print axioms OnBytes.Plan.firstPlan_rounds
#print axioms OnBytes.Plan.runs_reqSend_own
#print axioms OnBytes.Plan.runs_reqSend_open
#print axioms OnBytes.Plan.runs_reqMoments
#print axioms OnBytes.Plan.runs_reqPlanFrom
