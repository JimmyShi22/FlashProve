-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsSent.lean: THE SWITCH ITSELF RETURNS AT A GENERAL FRONT, THE
SENDING BEING THE ONE THAT THE KIND RUNS (`sendByL8`); SO THE KIND's OWN DECISION SAYS YES AT THE
HEAD's PLACE AND AT THE PLACE BEHIND THE LAST SEGMENT. Three structures of premises; statements with
their proofs.

WHY. Returns/LinkSent.lean has the like at a segment's first place. At the two other sorts of place
the kind's decision is shorter (`HeadIs`, `FinIs`, Johnson/Top/H0/Tw/K2C/Closed.lean): the range of
the positions, where the state stands, the group's number, one look-up, THE SAME CALL OF THE SWITCH
AT THE PLACE's OWN FRONT, and "every column is taken". What stands around it at these places (the
quiet steps) is other members'.

  `CallPlain` THE PREMISES ON THE CALL, at a front x, a book and a count of roots: the sending's
                    ten · the trees laid are as many as the first entry's roots · the old main code
                    · the test on the round "LOC" (`locOk`, taken whole) · `ReadFits` at the
                    statement and the book in front · `FrontPlain` (sixteen clauses)
  `switchE_returns_sent` under `CallPlain`, where the round closed before owes no count: the
                    switch returns; the count of roots behind; THE COLUMNS THAT IT LEAVES, at the
                    book in front
  `HeadPlain`, `head_returns_sent` the head's place: the decision says yes
  `FinPlain`, `finish_returns_sent` the place behind the last segment: the decision says yes

By: `sendByL8_returns` (Returns/Sends.lean) · `frontFits_sent` (Returns/SentFront.lean) ·
`ReadFits.older`, `older_sent` (Returns/SentRead.lean) · `leftAfter_older` (Returns/SentOwn.lean) ·
`took_of_answers` (Returns/LinkSent.lean) · `switchBehind_returns_whole` (Returns/Whole.lean) · the
library's `switchE_of`, `head_of`, `finish_of` (Johnson/Top/H0/Tw/K2C/AsksWhole.lean).

Limits. NO PREMISE HAS THE FORM "... = .ok ...". `locOk` is still asked at what the sending hands
on: it reads of it the count of answers taken alone. At these two places the new group was made by
an earlier step: so all sixteen clauses of `FrontPlain` are premises, the group's three among them.
`FrontPlain` has clauses that no yes gives, and three that compare field elements of the state with
(1, 1) (Returns/SentFront.lean's limits). `linkFits_sent` (Returns/LinkSent.lean) repeats the proof
of `switchE_returns_sent` at a segment's front: `LinkPlain` holds `CallPlain`'s fields there, with
`FrontCore` for `FrontPlain`: left so. IF A STATE HOLDS A WRITTEN-OUT VARIABLE WHOSE PAIR IS NOT (1,
1), IN THE CARRIED CLAIM, A KEPT FORM OR A STORED SAMPLE ROW, THE STRUCTURES CANNOT BE MET THERE.
THE THREE STRUCTURES ARE SHOWN AT NO STATE HERE. The laws speak of the kind's own decision: nothing
on the quiet steps, on `Block.step` or on a seated block. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.LinkSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat locOk behindArgs switchE_of head_of
  finish_of headFrontOf finFrontOf)
open VerifiableInference.Desc.First.Send (planOk1)
open Johnson.Prover.Send (SendFront)
open _root_.Tw.K2 (Front Col S9 sendByL8 switchBehind switchE switchNotices)

/-- **The premises on the call of the switch**, at a front. B, roots: the book and the count of
roots in front. c: the old main code. G: the new group. -/
structure CallPlain (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (c : Code) (G : Group) : Prop where
  entry : planOk1 none (switchNotices x.T x.others) (par9 p).eSeed = true
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  plan : K1.planOkOwn (sendingAt p x) = true
  step : x.st.oracles.size = B.place.size
  draw : (r₁.drawn.elems.map E.ofTriple).length =
    (sendingAt p x).seeds * ((sendingAt p x).coordinates + 1)
  vals : r₁.vals = []
  poss : r₁.drawn.poss = []
  trits : r₁.drawn.trits = []
  factor : ∀ z ∈ K1.seedsOf (sendingAt p x) r₁, isZeroE z.2 = false
  answers : (K1.answersIn (K1.cutTo (sendingAt p x) r₂)).length = (sendingAt p x).answers
  trees : ((layTrees (sendingAt p x).codes (sendingAt p x).sent).getD {}).shapes.size =
    (par9 p).eSeed.roots
  oldCode : x.st.codes.base[x.f.rows.code]? = some c
  loc : locOk (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols) c.logN =
    true
  reads : ReadFits (inFront (par9 p) x B (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols)
    (Positions.ofDraws c.logN r₂.drawn.poss)
  front : FrontPlain x c G r₂.drawn.poss

/-- **The switch returns**, the sending being the one that the kind runs. -/
theorem switchE_returns_sent {p : P2} {x : Front} {s : S9} {r₁ r₂ : Fmt.RoundView} {cols : List OpenedColumn}
    {c : Code} {G : Group} (hw : s.settled = true)
    (H : CallPlain p x s.book s.roots r₁ r₂ cols c G) :
    ∃ w, switchE switchBehind (par9 p) sendByL8 s x r₁ r₂ cols =
        .ok (w, s.roots + (par9 p).eSeed.roots) ∧
      w.opened = leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
        (treesOf (inFront (par9 p) x s.book
          (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂) r₂ cols)) cols := by
  have hs := sendingAt_sent p x
  have ol := older_sent (par9 p) x s.book s.roots r₁ r₂ cols (sendingAt p x)
  have hSend : sendByL8 (par9 p) x.st s.book s.roots s.settled (switchNotices x.T x.others) r₁ r₂ =
      .ok (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂) := by
    rw [hw]
    exact sendByL8_returns (par9 p) (sendingAt p x) _ _ _ _ r₁ r₂ rfl hs H.entry H.fits₁
      (SendFront.of_lengths _ _ rfl H.plan H.step H.front.lengths) H.front.lengths H.draw H.vals
      H.poss H.trits H.factor H.answers
  have hTrees : (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂).roots =
      s.roots + (par9 p).eSeed.roots := by rw [sentAt_roots, H.trees]
  have hCode : (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂).st.codes.base[x.f.rows.code]? =
      some c := by
    rw [sentAt_codes]
    exact H.oldCode
  obtain ⟨_, _, _, _, _, h⟩ := switchBehind_returns_whole
    (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂) r₂ cols) c G hCode
    H.loc (H.reads.older ol) (frontFits_sent (par9 p) x s.book s.roots r₁ r₂ cols _ rfl hs H.front)
  have hE := switchE_of (behind := switchBehind) (P := par9 p) (send := sendByL8) (s := s) (x := x)
    (rS := r₁) (rL := r₂) (cols := cols)
    ⟨hw, rfl, (_root_.Tw.K2.targetOk_eq _ _ _).trans H.front.check, hSend,
      took_of_answers _ _ H.answers, hTrees, h, rfl⟩
  rw [hTrees] at hE
  refine ⟨_, hE, ?_⟩
  show leftAfter (Positions.ofDraws c.logN r₂.drawn.poss)
    (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂).book
    (treesOf (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st s.book s.roots r₁ r₂) r₂ cols))
    cols = _
  rw [ol.sameTrees H.reads.placed]
  refine leftAfter_older _ ol.trees _ _ fun t ht => ?_
  obtain ⟨tr, h0⟩ := allOpen_tree _ _ _ _ _ _ t ht H.reads.opens
  exact (Array.getElem?_eq_some_iff.1 h0).1

/-- **All premises at the head's place.** a: what the head holds. Q: the segment's group, off the
frame. -/
structure HeadPlain (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : HeadOwn) (Q : ReqGroup) (c : Code) (G : Group) : Prop where
  stands : p.stands = .head
  range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  here : s.here = .head a
  number : a.fr.group = p.grp
  group : s.check.frame.groups[s.check.frame.link]? = some Q
  waits : s.noneWaits = true
  call : CallPlain p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) c G
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (inFront (par9 p) (headFrontOf s a Q.target) s.book
      (sentAt (sendingAt p (headFrontOf s a Q.target)) (headFrontOf s a Q.target).st s.book s.roots
        r₁ r₂) r₂ (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

/-- **The kind's own decision says yes at the head's place.** -/
theorem head_returns_sent {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {a : HeadOwn} {Q : ReqGroup} {c : Code} {G : Group} (H : HeadPlain p s r₁ r₂ gs a Q c G) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' := by
  obtain ⟨w, hE, ho⟩ := switchE_returns_sent
    (s := ⟨s.st, s.book, s.roots, a.fr, [], s.noneWaits⟩) H.waits H.call
  exact ⟨_, head_of H.stands ⟨H.range, H.here, H.number, H.group, hE,
    ⟨ho.trans H.noneLeft, H.groups⟩, rfl⟩⟩

/-- **All premises at the place behind the last segment.** a: what the finish holds. Q: the group
that it has laid. -/
structure FinPlain (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : FinOwn) (Q : ReqGroup) (c : Code) (G : Group) : Prop where
  stands : p.stands = .finish
  range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  here : s.here = .fin a
  number : a.fr.group = p.grp
  laid : a.G = some Q
  waits : s.noneWaits = true
  call : CallPlain p (finFrontOf s a Q) s.book s.roots r₁ r₂ (flat p gs) c G
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (inFront (par9 p) (finFrontOf s a Q) s.book
      (sentAt (sendingAt p (finFrontOf s a Q)) (finFrontOf s a Q).st s.book s.roots r₁ r₂) r₂
      (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

/-- **The kind's own decision says yes at the place behind the last segment.** -/
theorem finish_returns_sent {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : FinOwn} {Q : ReqGroup} {c : Code} {G : Group}
    (H : FinPlain p s r₁ r₂ gs a Q c G) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' := by
  obtain ⟨w, hE, ho⟩ := switchE_returns_sent
    (s := ⟨s.st, s.book, s.roots, a.fr, [], s.noneWaits⟩) H.waits H.call
  exact ⟨_, finish_of H.stands ⟨H.range, H.here, H.number, H.laid, hE,
    ⟨ho.trans H.noneLeft, H.groups⟩, rfl⟩⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.switchE_returns_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_returns_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finish_returns_sent
