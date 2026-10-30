-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Keeps.lean: what a yes of the sub-protocol "the output head's own rounds"
(K6) leaves of the verifier's state as it was, and how what it turns has turned: one definition, and
that a yes gives it. Over the library alone: no prover's text and no frame of the honest side is
read here.

  `ownRest`, `restK6`  the head's own part, and the state, without the three fields that a yes
                       turns
  `K6Keeps`            THE SENTENCE on the state in front and the state behind
  `below_of_takes`     from two of the library's sentences on two ledgers to a third
  `ledgers_blockAt`    the state behind a yes written out, with the two ledgers
  `k6_keeps_blockAt`, `k6_keeps_seated`, `k6_keeps_member`, `k6_keeps_step`   CONDITIONAL ON THE YES
                       ALONE (the last two: and on "B narrows the seated block"): a yes of the bare
                       block's decision; of the block as a lot seats it; of the decision, and of the
                       step, of any block that narrows that one
  `k6_takes_le`        CONDITIONAL: the slots that were taken are at most a number of the plan's
  `K6Keeps.own`, `K6Keeps.here`, `K6Keeps.heard`, `K6Keeps.kept`   four consequences; the last: the
                       library's own older sentence on both states (`K6Kept`,
                       Johnson/Desc/Kinds/Law/RowPromise.lean)

What is called and what is typed anew. Called: the state behind a yes (`Came.decide_record`, same
file); a later ledger (`blockAt_later`, Law/KeepsAt.lean); just t slots are taken (`blockAt_takes`,
Law/TakesAt.lean); the way from the seated block to the bare one (`seatedClaims_some`,
`tested_decide`, Law/SeatedBridge.lean); from a step to a decision (`Came.step_decide`,
Law/RowPins.lean). `Below` is the sentence of another kind's file on two ledgers
(Johnson/Desc/First/Att/K05HearBelow.lean); it has no letter of that kind's. Typed anew: that the
hearing turns no field of the ledger but four (Honest/Law/KeepsBare.lean): the library has that for
the number of slots (`Touch`, Law/Takes.lean), the arrays (Law/KeepsTrees.lean) and the list of
debts (Law/KeepsOwed.lean), each by a walk of its own; there all other fields at once.

Nearest relatives in the library, none of which is this sentence: `Came.rides` (Law/RowPromise.lean:
a rule: any reading of the state that does not hang on the three fields is as it was, at the bare
block); `blockAt_leaves`, `seated_leaves` (Law/K6Leaves.lean: the statement and what goes on to the
later chains are as they were); `k6Hear_leaves` (Law/K6K7LotLeaves.lean: the like at a member of a
lot); `K6Kept` (above).

Limits.
  - "THE LEDGER IN FRONT HAS ITS SIZES" IS NOT PAID HERE. Clauses (8) and (9) of the sentence stand
    under that premise. The library pays it at every state that is reached at the sub-protocol's
    border, in the goals' scope and at the full size, where the lookup's member in front passes its
    test on the plan, which is had from the description's own test on the plan (`free_at_341`,
    `wellLaid_341`, Johnson/P4R/FreeAt341N.lean; the starter: `placeH2_free`,
    Johnson/Desc/Kinds/Law/HeadLedgerMade.lean). And the promise's table asks the public item of the
    Bool `ledgerB` (Johnson/Desc/First/FillKeeper.lean: a ledger is open and has its sizes) in front
    of this sub-protocol (`pubRowOf`, Johnson/Desc/First/Borders.lean): so where the promise in
    front holds, the premise is to be had from it too. Not typed here: either tie.
  - THAT THE MEMBER AS THE DESCRIPTION SEATS IT NARROWS THE SEATED BLOCK IS NOT SHOWN HERE: it is
    Honest/Law/KeepsMember.lean's.
  - No pair of states is shown at which a yes is said.
  - What another sub-protocol's item reads of the state has not been looked at: the sentence says
    what a yes fixes of the state behind.
  - `K6Keeps` is a definition: nothing is claimed of it. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.KeepsBare
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes (zeroE)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later Sized Filled)
open VerifiableInference.Desc (Block Claim OpenedColumn)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Att.P (Below bare)
open VerifiableInference.Desc.Kinds.Head.Law (Takes K6Kept)

/-- The head's own part of the state without its ledger, what its own rounds have heard, and the
squares' level's state. -/
def ownRest (o : HeadOwn) : HeadOwn := { o with F := {}, x := none, squaresP := none }

/-- The state without these three fields. -/
def restK6 (s : S) : S :=
  match s.here with
  | .head o => { s with here := .head (ownRest o) }
  | _ => s

/-- **WHAT A YES LEAVES OF THE STATE AS IT WAS, AND HOW WHAT IT TURNS HAS TURNED.** s: the state in
front; s': behind. (1) No mark of failure behind. (2) Every field of the state but three of the
head's own part is as it was: the three are the ledger, what the sub-protocol's rounds have heard,
and the squares' level's state. (3) Both states stand in the head's link, (4) which is opened; (5),
(6) behind, the two fields on what was heard are laid. Of the ledger: (7) the one behind is a later
state of the one in front: as many slots; what lies under a filled slot is kept. WHERE THE LEDGER
IN FRONT HAS ITS SIZES: (8) below the next free number in front the three arrays on slots are as
they were, and every field but these three and that number is as it was (its arrays for the claims,
its list of debts and its counters of claims among them); (9) the next free number has moved on by
some t, nothing is turned from the new one on either, and each of the t slots is filled. It is
a definition: a premise's form. Nothing is claimed of it. -/
def K6Keeps (s s' : S) : Prop :=
  s'.failed = none ∧ restK6 s' = restK6 s ∧ ∃ o o', s.here = .head o ∧ s'.here = .head o' ∧
    o.opened = true ∧ o'.x.isSome = true ∧ o'.squaresP.isSome = true ∧ Later o.F o'.F ∧
    (Sized o.F → Below o.F o'.F ∧ ∃ t, Takes o.F o'.F t)

/-- From "it has taken just t numbers" and "no other field has turned". -/
theorem below_of_takes {F G : Fork} {t : Nat} (hF : Sized F) (T : Takes F G t)
    (hb : bare G = bare F) : Below F G := by
  refine ⟨by rw [T.next]; exact Nat.le_add_right _ _, hb, fun j hj => ?_⟩
  obtain ⟨a1, a2, a3⟩ := T.touch.out j (Or.inl hj)
  refine ⟨a1, a2, fun d => ?_⟩
  have sF : F.gotF.size = F.ns := hF.2.2
  have sG : G.gotF.size = F.ns := by rw [T.touch.sized.2.2, T.touch.ns]
  by_cases hjn : j < F.ns
  · have iF : j < F.gotF.size := by rw [sF]; exact hjn
    have iG : j < G.gotF.size := by rw [sG]; exact hjn
    unfold Filled at a3
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem iF,
      Array.getElem?_eq_getElem iG] at a3 ⊢
    simp only [Option.getD_some] at a3 ⊢
    cases hg : G.gotF[j] <;> cases hf : F.gotF[j] <;> simp [hg, hf] at a3 ⊢
  · have oF : F.gotF.size ≤ j := by rw [sF]; exact Nat.le_of_not_lt hjn
    have oG : G.gotF.size ≤ j := by rw [sG]; exact Nat.le_of_not_lt hjn
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none oF,
      Array.getElem?_eq_none oG]

/-- The two ledgers at a yes of the bare block's decision, by the seat's own reader. -/
theorem ledgers_blockAt (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc),
      s.here = .head o ∧ o.opened = true ∧ s.failed = none ∧
      s' = { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } ∧
      (seatAt h iU3).ledger s = o.F ∧ (seatAt h iU3).ledger s' = F1 := by
  obtain ⟨o, F1, X, Q, ho, hop, hf, hs'⟩ := Law.Came.decide_record h iU3 work l hd
  refine ⟨o, F1, X, Q, ho, hop, hf, hs', ?_, ?_⟩
  · show s.fork?.getD {} = o.F
    simp [S.fork?, ho, hop]
  · rw [hs']
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]

/-- **A yes of the bare block's decision leaves that.** CONDITIONAL: the yes is the one premise. -/
theorem k6_keeps_blockAt (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') : K6Keeps s s' := by
  obtain ⟨o, F1, X, Q, ho, hop, hf, hs', hl, hl'⟩ := ledgers_blockAt h iU3 work l hd
  have L := Law.blockAt_later h iU3 work l s s' rs gs hd
  rw [hl, hl'] at L
  refine ⟨by rw [hs']; exact hf, ?_, o, { o with F := F1, x := some X, squaresP := some Q }, ho,
    by rw [hs'], hop, rfl, rfl, L, fun hz => ?_⟩
  · rw [hs']
    unfold restK6
    rw [ho]
    rfl
  · have hS : Sized ((seatAt h iU3).ledger s) := by rw [hl]; exact hz
    obtain ⟨t, _, T⟩ := Law.blockAt_takes h iU3 work l s s' rs gs hS hd
    have B := blockAt_bare h iU3 work l s s' rs gs hS hd
    rw [hl, hl'] at T B
    exact ⟨below_of_takes hz T B, t, T⟩

/-- **A yes of the block as a lot seats it leaves that.** CONDITIONAL: the yes. -/
theorem k6_keeps_seated {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS : Block S Claim} (hS : seatedClaims W l bef = some bS) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : bS.decide s rs gs = .ok s') : K6Keeps s s' := by
  obtain ⟨b0, h0, rfl⟩ := Law.seatedClaims_some hS
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  have h1 := ((Law.tested_decide _ _ _ _ _ _ _ _).1 hd).1
  exact k6_keeps_blockAt (gs := gs) W.hS i _ l h1

/-- **A yes of the DECISION of any block that narrows it leaves that.** CONDITIONAL: the yes, and
that B narrows the seated block: THAT THE MEMBER AS THE DESCRIPTION SEATS IT DOES SO IS NOT SHOWN
HERE. -/
theorem k6_keeps_member {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS B : Block S Claim} (hS : seatedClaims W l bef = some bS) (hN : B.Narrows bS) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hd : B.decide s rs gs = .ok s') :
    K6Keeps s s' :=
  k6_keeps_seated hS (hN.2 _ _ _ _ hd)

/-- **A yes of its STEP leaves that.** CONDITIONAL, as the last. -/
theorem k6_keeps_step {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS B : Block S Claim} (hS : seatedClaims W l bef = some bS) (hN : B.Narrows bS) {ft n : Nat}
    {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} (h : B.step ft s rs cols = .ok (s', n)) :
    K6Keeps s s' := by
  obtain ⟨gs, hd⟩ := Law.Came.step_decide ft B s rs cols s' n h
  exact k6_keeps_member hS hN hd

/-- **For whoever counts slots**: the number of slots that were taken is at most a number of the
plan's. CONDITIONAL: a yes of the block as a lot seats it; the ledger in front has its sizes. -/
theorem k6_takes_le {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS : Block S Claim} (hS : seatedClaims W l bef = some bS) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : bS.decide s rs gs = .ok s') {o o' : HeadOwn}
    (ho : s.here = .head o) (ho' : s'.here = .head o') (hz : Sized o.F) :
    ∃ t, t ≤ Law.takesOf (parOf W.hS
        ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)) ∧ Takes o.F o'.F t := by
  obtain ⟨b0, h0, rfl⟩ := Law.seatedClaims_some hS
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  have h1 : (blockAt W.hS i ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)
      l).decide s rs gs = .ok s' := ((Law.tested_decide _ _ _ _ _ _ _ _).1 hd).1
  obtain ⟨o1, F1, X, Q, h2, _, _, hs', hl, hl'⟩ := ledgers_blockAt W.hS i _ l h1
  rw [ho] at h2
  cases h2
  rw [hs'] at ho'
  cases ho'
  obtain ⟨t, ht, T⟩ := Law.blockAt_takes W.hS i _ l s s' rs gs (by rw [hl]; exact hz) h1
  rw [hl, hl'] at T
  exact ⟨t, ht, T⟩

/-- The head's own part behind is the one in front with three fields laid anew. -/
theorem K6Keeps.own {s s' : S} (K : K6Keeps s s') :
    ∃ o o', s.here = .head o ∧ s'.here = .head o' ∧
      o' = { o with F := o'.F, x := o'.x, squaresP := o'.squaresP } := by
  obtain ⟨_, hr, o, o', ho, ho', _⟩ := K
  refine ⟨o, o', ho, ho', ?_⟩
  unfold restK6 at hr
  rw [ho, ho'] at hr
  have e : ownRest o' = ownRest o := by
    have h := congrArg S.here hr
    simpa using h
  exact congrArg (fun a : HeadOwn => { a with F := o'.F, x := o'.x, squaresP := o'.squaresP }) e

/-- The state behind is the state in front with another "where the chain stands". -/
theorem K6Keeps.here {s s' : S} (K : K6Keeps s s') : s' = { s with here := s'.here } := by
  obtain ⟨_, hr, o, o', ho, ho', _⟩ := K
  unfold restK6 at hr
  rw [ho, ho'] at hr
  exact congrArg (fun t : S => { t with here := s'.here }) hr

/-- Behind, the chain stands in the head's link, and what the sub-protocol's rounds have heard is
laid. -/
theorem K6Keeps.heard {s s' : S} (K : K6Keeps s s') :
    ∃ a, s'.here = .head a ∧ a.x.isSome = true := by
  obtain ⟨_, _, _, o', _, ho', _, hx, _⟩ := K
  exact ⟨o', ho', hx⟩

/-- It gives the library's own older text on both states (Kinds/Law/RowPromise.lean). -/
theorem K6Keeps.kept (W : OnBytes.Model.Verify.Public) {s s' : S} (K : K6Keeps s s') :
    K6Kept W s s' := by
  obtain ⟨o, o', ho, ho', e⟩ := K.own
  have hs := K.here
  obtain ⟨_, _, o1, o1', h1, h1', hop, _, _, L, _⟩ := K
  rw [ho] at h1
  rw [ho'] at h1'
  cases h1
  cases h1'
  have hop' : o'.opened = true := by rw [e]; exact hop
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Later (s.fork?.getD {}) (s'.fork?.getD {})
    simpa [S.fork?, ho, ho', hop, hop'] using L
  · rw [hs]
    rfl
  · rw [hs]
    rfl
  · have el : o'.lookHeard = o.lookHeard := by rw [e]
    simp [S.lookHeard?, ho, ho', hop, hop', el]

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.below_of_takes
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.ledgers_blockAt
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_blockAt
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_seated
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_member
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_step
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.k6_takes_le
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps.own
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps.here
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps.heard
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.K6Keeps.kept
