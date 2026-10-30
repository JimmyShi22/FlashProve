-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/LinkSent.lean: THE KIND's OWN DECISION SAYS YES AT A SEGMENT's FIRST
PLACE, THE SENDING BEING THE ONE THAT THE KIND RUNS (`sendByL8`), FROM PREMISES THAT STAND IN FRONT
OF THE SENDING, BUT FOR ONE (the test on the round "LOC", which is still asked at what the sending
hands on). One structure of premises; statements with their proofs.

WHY. Returns/Link.lean has the law with the sending as a letter: one of its 29 premises says that
the sending returns y, and eleven more are asked at y or at what y hands on (`took`, `trees`,
`oldCode`, `loc`, `reads` with thirteen clauses, `front` with twenty, `numbers`, `theMask`, `join`,
`differ`, `noneLeft`); its limits say that nothing shows these. HERE THE SENDING IS LAID IN: it
returns `sentAt` (Returns/Sends.lean), and what is asked behind it comes down to the front:
`FrontFits` by Returns/SentFront.lean, `ReadFits` by Returns/SentRead.lean, the own messages' fields
by Returns/SentOwn.lean and Returns/SendsMore.lean.

  `sendingAt`, `sendingAt_sent` the sending as the shared sending's public letter, at a front: the
                    front's codes; the place's two numbers; one part: what the switch announces
  `sentOf` what the sending returns, at a state
  `groupAt` the new group, as the front makes it
  `LinkPlain` ALL PREMISES: 32 FIELDS. AS IN `LinkFits`, ON THE STATE IN FRONT AND THE PLAN:
                    fourteen of its first sixteen. THE SENDING's TEN: the first entry's test on the
                    plan · the first round fits its entry · the sending kind's own test on the plan
                    · statement and book are in step · the first round shows no item, draws no
                    position and no matrix entry, and just the place's seeds · NO SEED's FACTOR IS
                    SPELT BY THREE WORDS 0 · the second round's first items hold the place's
                    answers. ONE TIE TO THE PLAN: the trees laid are as many as the first entry's
                    roots. THE OLD MAIN CODE. THE TEST ON THE ROUND "LOC" (`locOk`, taken whole). IN
                    FRONT OF THE SENDING: `ReadFits` · `FrontCore` (thirteen clauses) · each own
                    message's announcement fits the new group · no column is left. As many groups of
                    columns as the place reads trees
  `took_of_answers`, `more_link` one of `LinkFits`' premises, and one of `OwnPlain`'s, that follow:
                    the second round shows items enough; there is a message for the fresh mask.
                    THREE MORE FOLLOW IN THE PROOF: the second entry counts no rows (by unfolding) ·
                    the guard is the program's test on the target, which `FrontCore` has · the new
                    group is there, without member or test begun (`group_new`, Returns/Front.lean)
  `linkFits_sent` `LinkPlain` gives `LinkFits` at `sendByL8` and `sentOf`
  `link_returns_sent` SO: under `LinkPlain` the decision says yes

Limits. NO PREMISE HAS THE FORM "... = .ok ..." ANY MORE. `locOk` is a test on public data and the
second round, taken whole; it reads of what the sending returns the count of answers taken alone.
ONE PREMISE SITS ON THE VERIFIER's OWN DRAW (no seed's factor is spelt by three words 0) and one on
its range: no state and no honest move pays these. `FrontCore` has clauses that no yes gives (the
rest in main rows; the two bounds; the codes' lengths; a main row and an answer in each kept
target), and three that compare field elements of the state with (1, 1) (inside `TablesFit`). The
library has the like of `more_link` at all three sorts of place, from a yes of the front
(`others_of_front`, Johnson/Top/H0/Tw/K2C/SentAtPlan.lean): not called. `LinkPlain` is shown at no
state here. The head's place and the place behind the last segment are not here. The law speaks of
the kind's own decision: where a block is seated, a run returns only if it also leaves the reply as
it was: not stated here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.SentOwn
import Johnson.Desc.K2.Honest.Returns.Link

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat locOk behindArgs)
open VerifiableInference.Desc.First.Send (planOk1)
open Johnson.Desc.First.Walk (firstDue)
open Johnson.Prover.Send (SendFront)
open _root_.Tw.K2 (Front sendByL8 switchNotices)

/-- The sending as the shared sending's public letter, at a front. -/
def sendingAt (p : P2) (x : Front) : K1.Par :=
  { place := default, codes := x.st.codes, gp := ⟨(par9 p).samples, (par9 p).firstTree⟩, work := 0
    parts := [("", switchNotices x.T x.others)] }

theorem sendingAt_sent (p : P2) (x : Front) :
    (sendingAt p x).sent = switchNotices x.T x.others := by
  simp [sendingAt, K1.Par.sent]

/-- What the sending returns, at a state. -/
def sentOf (p : P2) (s : S) (L : Params.ReqLink) (Q : ReqGroup) (r₁ r₂ : Fmt.RoundView) :
    _root_.Tw.K2.Sent :=
  sentAt (sendingAt p (frontAt s L Q)) (frontAt s L Q).st s.book s.roots r₁ r₂

/-- The new group, as the front makes it: the frame's two codes; no member, no row, no test begun.
-/
def groupAt (s : S) : Group :=
  { code := s.check.frame.shape.code, maskCode := s.check.frame.shape.maskCode }

/-- **All premises**: each but `loc` stands in front of the sending. c: the old main code. -/
structure LinkPlain (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (L : Params.ReqLink) (Q : ReqGroup) (c₀ z₀ c : Code) : Prop where
  stands : p.stands = .link
  range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  here : s.here = .between
  due : firstDue s.check = true
  waits : s.noneWaits = true
  first : s.check.frame.next = .first
  later : s.check.frame.link ≠ 0
  link : s.check.frame.shape.link[s.check.frame.link]? = some L
  group : s.check.frame.groups[s.check.frame.link]? = some Q
  code : s.st.codes.base[s.check.frame.shape.code]? = some c₀
  maskCode : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀
  shorter : z₀.logN ≤ c₀.logN
  plain : L.plain = 0
  number : s.st.groups.size = p.grp
  entry : planOk1 none (switchNotices (frontAt s L Q).T (frontAt s L Q).others) (par9 p).eSeed =
    true
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  plan : K1.planOkOwn (sendingAt p (frontAt s L Q)) = true
  step : (frontAt s L Q).st.oracles.size = s.book.place.size
  draw : (r₁.drawn.elems.map E.ofTriple).length =
    (sendingAt p (frontAt s L Q)).seeds * ((sendingAt p (frontAt s L Q)).coordinates + 1)
  vals : r₁.vals = []
  poss : r₁.drawn.poss = []
  trits : r₁.drawn.trits = []
  factor : ∀ z ∈ K1.seedsOf (sendingAt p (frontAt s L Q)) r₁, isZeroE z.2 = false
  answers : (K1.answersIn (K1.cutTo (sendingAt p (frontAt s L Q)) r₂)).length =
    (sendingAt p (frontAt s L Q)).answers
  trees : ((layTrees (sendingAt p (frontAt s L Q)).codes
    (sendingAt p (frontAt s L Q)).sent).getD {}).shapes.size = (par9 p).eSeed.roots
  oldCode : (frontAt s L Q).st.codes.base[(frontAt s L Q).f.rows.code]? = some c
  loc : locOk (behindArgs (par9 p) (frontAt s L Q) (sentOf p s L Q r₁ r₂) r₂ (flat p gs)) c.logN =
    true
  reads : ReadFits (inFront (par9 p) (frontAt s L Q) s.book (sentOf p s L Q r₁ r₂) r₂ (flat p gs))
    (Positions.ofDraws c.logN r₂.drawn.poss)
  front : FrontCore (frontAt s L Q) c s.check.frame.shape.code r₂.drawn.poss
  own : ∀ (j : Nat) (m : Params.ReqMessage), (frontAt s L Q).own[j]? = some m →
    ∃ n, (frontAt s L Q).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
      (n.shape.mainRows = 0 ∨ n.shape.code = s.check.frame.shape.code) ∧
      (n.shape.maskRows = 0 ∨ n.shape.maskCode = s.check.frame.shape.maskCode) ∧
      (0 < m.life → 0 < n.shape.mainRows)
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (inFront (par9 p) (frontAt s L Q) s.book (sentOf p s L Q r₁ r₂) r₂ (flat p gs)))
    (flat p gs) = []
  groups : gs.length = p.read.length

/-- The second round shows at least as many items as it holds answers among its first ones. -/
theorem took_of_answers (Z : K1.Par) (r₂ : Fmt.RoundView)
    (h : (K1.answersIn (K1.cutTo Z r₂)).length = Z.answers) : Z.answers ≤ r₂.vals.length := by
  have h1 : (K1.answersIn (K1.cutTo Z r₂)).length ≤ (r₂.vals.take Z.answers).length :=
    List.length_filterMap_le _ _
  have h2 : (r₂.vals.take Z.answers).length ≤ r₂.vals.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

/-- At a segment's front there is one message more behind the kept copies than own messages: the
fresh mask. -/
theorem more_link (s : S) (L : Params.ReqLink) (Q : ReqGroup) :
    (frontAt s L Q).own.length < (frontAt s L Q).others.size := by
  show (s.check.frame.atMoment 0).length <
    (ReqFrame.notices (s.check.frame.atMoment 0) ++
      #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})]).size
  simp [ReqFrame.notices]

/-- **The premises in front give the law's premises, at the sending that the kind runs.** -/
theorem linkFits_sent {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ c : Code}
    (H : LinkPlain p s r₁ r₂ gs L Q c₀ z₀ c) :
    LinkFits sendByL8 p s r₁ r₂ gs L Q c₀ z₀ (sentOf p s L Q r₁ r₂) c (groupAt s)
      ((frontAt s L Q).st.oracles.size +
        (1 + (frontAt s L Q).T.kept.size + (frontAt s L Q).own.length)) := by
  have hs := sendingAt_sent p (frontAt s L Q)
  have fr : FrontPlain (frontAt s L Q) c (groupAt s) r₂.drawn.poss :=
    FrontCore.plain (G := groupAt s) H.front (group_new s.st _ _) rfl rfl
  have ow : OwnPlain (frontAt s L Q) (groupAt s) := ⟨more_link s L Q, H.own⟩
  have ol : Older
      (inFront (par9 p) (frontAt s L Q) s.book (sentOf p s L Q r₁ r₂) r₂ (flat p gs))
      (behindArgs (par9 p) (frontAt s L Q) (sentOf p s L Q r₁ r₂) r₂ (flat p gs)) :=
    older_sent (par9 p) (frontAt s L Q) s.book s.roots r₁ r₂ (flat p gs)
      (sendingAt p (frontAt s L Q))
  exact
    { stands := H.stands, range := H.range, here := H.here, due := H.due, waits := H.waits
      first := H.first, later := H.later, link := H.link, group := H.group, code := H.code
      maskCode := H.maskCode, shorter := H.shorter, plain := H.plain, number := H.number
      noRows := rfl
      guard := (_root_.Tw.K2.targetOk_eq _ _ _).trans H.front.check
      sends := by
        rw [H.waits]
        exact sendByL8_returns (par9 p) (sendingAt p (frontAt s L Q)) _ _ _ _ r₁ r₂ rfl hs H.entry
          H.fits₁ (SendFront.of_lengths _ _ rfl H.plan H.step H.front.lengths) H.front.lengths
          H.draw H.vals H.poss H.trits H.factor H.answers
      took := took_of_answers _ _ H.answers
      trees := by
        show (sentOf p s L Q r₁ r₂).roots = _
        unfold sentOf
        rw [sentAt_roots, H.trees]
      oldCode := by
        show (sentOf p s L Q r₁ r₂).st.codes.base[(frontAt s L Q).f.rows.code]? = some c
        unfold sentOf
        rw [sentAt_codes]
        exact H.oldCode
      loc := H.loc
      reads := H.reads.older ol
      front := frontFits_sent (par9 p) (frontAt s L Q) s.book s.roots r₁ r₂ (flat p gs) _ rfl hs fr
      numbers := sentAt_others _ _ _ _ r₁ r₂ (frontAt s L Q).T (frontAt s L Q).others hs
      theMask := own_mask (par9 p) (frontAt s L Q) s.book s.roots r₁ r₂ (flat p gs) _ hs
        (Positions.ofDraws c.logN r₂.drawn.poss) ow
      join := own_join (par9 p) (frontAt s L Q) s.book s.roots r₁ r₂ (flat p gs) _ hs _ ow
      differ := own_differ (par9 p) (frontAt s L Q) s.book s.roots r₁ r₂ (flat p gs) _ hs _
      noneLeft := by
        rw [ol.sameTrees H.reads.placed]
        refine (leftAfter_older _ ol.trees _ _ fun t ht => ?_).trans H.noneLeft
        obtain ⟨tr, h0⟩ := allOpen_tree _ _ _ _ _ _ t ht H.reads.opens
        exact (Array.getElem?_eq_some_iff.1 h0).1
      groups := H.groups }

/-- **The kind's own decision says yes at a segment's first place**: no premise says that a call
returns. -/
theorem link_returns_sent {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ c : Code}
    (H : LinkPlain p s r₁ r₂ gs L Q c₀ z₀ c) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' :=
  link_returns (linkFits_sent H)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.sendingAt_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.linkFits_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.took_of_answers
#print axioms VerifiableInference.Desc.K2.Honest.Returns.more_link
