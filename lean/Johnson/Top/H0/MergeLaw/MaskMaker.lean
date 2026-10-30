-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskMaker.lean: where the output head's segment is opened, the frame in its
own copy of the state of the calls holds the numbers of the segment's first messages: so the test
`maskMsgB` (MaskFront.lean) accepts there, at a number that is counted back from the number of the
statement's oracle messages. Definitions, and theorems with their proofs.

Why. `maskMsgB O` reads the open segment's frame's fields next, link, shape and own. At the output
head's segment that frame is made in two steps. The quiet step in front of the reply's round
(`K2.headFrontQ`, Johnson/Top/H0/Tw/K2C/Head.lean) makes a frame with no own message, which rests in
the head's part of the state. The quiet step behind the code switch (`K2.headOpenQ`) lays the
numbers that the switch's sending returned behind that list, says that the frame stands inside a
segment, tests the frame's number of the segment, and opens the segment with that frame.

Main names:
  `K2.placeH2_opened`: an accepting step of the code switch with the quiet step behind it: the open
    segment's frame's next, link, shape and own, and how many messages the statement has gained. It
    follows `K2.placeH2_frame` (Johnson/Top/H0/Tw/K2C/HeadNumbers.lean), which says own, and neither
    next nor link nor the count.
  `sentIds_get`, `sentIds_size`, `cut_get`, `headNotices_size`: the numbers of a sending, cut; how
    many messages the switch's sending at the output head's segment holds.
  `momentCount shape l t`, `firstCount shape l`, `firstCount_eq`, `atMoment_count`: how many
    messages segment l sends at its moment t, and at its first moment, by the shape. With code.
  `HeadFresh s`: the state stands in the output head's segment; the frame that rests in the head's
    part has no own message, and the shape and the number of the segment of the chain's own copy.
  `OpenedAt l s`: segment l stands open; its frame stands inside a segment, at the number l; and own
    message number m, m below `firstCount`, has the number O with O + (firstCount + 1) = (the
    statement's number of messages) + m: at a segment other than number 0 the first sending holds,
    behind the segment's first messages, one message more, the fresh mask. (The clause on the
    context's number is spent by no file yet.)
  `placeH2_makes`: from `HeadFresh` in front, an accepting step makes `OpenedAt P.l` behind.
  `OpenedAt.mask`: so `maskMsgB O` accepts there.
  `headFrontQ_fresh`, `headFront_decides`, `replyAt_leaves`, `h1_fresh`: who makes `HeadFresh`: the
    quiet step in front of the reply's round makes it, under a guard or not; the reply's own step
    leaves it.
  `decides_guarded`: a guarded sub-protocol's accepting step is one of the sub-protocol's own.
  NEGATIVE TESTS: `not_headFresh_between`, `not_openedAt_between`: neither holds between two
    segments; `not_openedAt_no_own`: `OpenedAt` fails where the open frame holds no own message,
    though the shape gives the segment a first message and the statement has messages enough.
    `toy_counts`: the two counts at MaskFront.lean's small frame.

Limits. `placeH2_makes` asks nothing where the sub-protocol never accepts: so at numbers that do not
say "the output head's segment", and at segment 0, where both quiet steps reject; and the last
clause of `OpenedAt` asks nothing where `firstCount` is 0. No accepting step is exhibited here, and
no state at which `HeadFresh` or `OpenedAt` holds. That the IOP as written in Lean holds these
sub-protocols at the first two places of the output head's segment is not said here. No example at
the release's own values. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskFront
import Johnson.Top.H0.Tw.K2C.HeadNumbers
import Johnson.Top.H0.Tw.K2C.StillKeeps
import Johnson.Stored.ReplySeatAt
import Johnson.Desc.SeatGuard
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront firstBehind)
open Johnson.Desc.First.Walk (firstKept)

/-- **The open segment's frame behind the code switch with the quiet step behind it**, at the output
head's segment. -/
theorem placeH2_opened {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    ∃ (a : HeadOwn) (G : ReqGroup) (L : LinkCtx), s.here = .head a ∧
      s'.link? = some L ∧ L.link = P.l ∧ L.check.frame.link = P.l ∧ a.fr.link = P.l ∧
      L.check.frame.next = .laterOrClose ∧ L.check.frame.shape = a.fr.shape ∧
      s'.st.oracles.size = s.st.oracles.size +
        (switchNotices G.target (headFrontOf s a G.target).others).size ∧
      L.check.frame.own = a.fr.own ++ ((sentIds s.st.oracles.size
        (switchNotices G.target (headFrontOf s a G.target).others).size).extract
          (1 + G.target.kept.size)
          (switchNotices G.target (headFrontOf s a G.target).others).size).extract 0
            (s.check.frame.atMoment 0).length := by
  have hp := placeH2_stands h
  simp only [Block.andThen] at h
  obtain ⟨m, h₁, h₂⟩ := bindOk h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h₁'
  obtain ⟨lay, _, _, _, e3⟩ := switch_numbers k.hSwitch
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P m s').1 h₂
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P m s' h₂
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hmc : m.check = s.check := by rw [k.hOut]
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  obtain ⟨_, hlk, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hfl : f.link = P.l := hlk
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hsz : s'.st.oracles.size = s.st.oracles.size +
      (switchNotices G.target (headFrontOf s a G.target).others).size := by
    rw [headOpenQ_size h₂]
    obtain ⟨x, hx, e1, _, e2, _⟩ := yes_size h₁'
    rcases hx with ⟨hq, _⟩ | ⟨_, a', G', ha', hG', rfl⟩ | ⟨hq, _⟩
    · rw [hp] at hq
      cases hq
    · have ea : a' = a := by
        have := ha'.symm.trans k.hHere
        injection this
      have eG : G' = G := Option.some.inj (hG'.symm.trans k.hGroup)
      subst ea
      subst eG
      rewrite [e2, e1]
      rfl
    · rw [hp] at hq
      cases hq
  refine ⟨a, G, L, k.hHere, ?_, by rw [hL], ?_, ?_, ?_, ?_, hsz, ?_⟩
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [hL]
    exact hlk
  · rw [bA.frame] at hfl
    have e' : a2.fr.link = P.l := hfl
    rw [ha2] at e'
    exact e'
  · rw [hL]
    show f.next = _
    rewrite [bA.frame]
    rfl
  · rw [hL]
    show f.shape = _
    rewrite [bA.frame]
    show a2.fr.shape = _
    rewrite [ha2]
    rfl
  · rw [hL]
    show f.own = _
    rw [bA.frame]
    show a2.fr.own ++ mine = _
    rw [bA.theOwn, ha2]
    show a.fr.own ++ w.out.others.extract 0 (m.check.frame.atMoment 0).length = _
    rw [hmc, e3]
    rfl

end VerifiableInference.Desc.First.K2

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.Model (LinkCtx)
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Keeps (Decides)

/-! ## The numbers of a sending, cut -/

/-- Entry i of the numbers of a sending of N messages behind n0 messages. -/
theorem sentIds_get {n0 N i : ℕ} (hi : i < N) : (K2.sentIds n0 N)[i]? = some (n0 + i) := by
  unfold K2.sentIds
  rw [Array.getElem?_map, Array.getElem?_range, if_pos hi, Option.map_some, Nat.add_comm]

/-- There are N of them. -/
theorem sentIds_size (n0 N : ℕ) : (K2.sentIds n0 N).size = N := by
  simp [K2.sentIds]

/-- Entry m of the first len of the numbers from number a on. -/
theorem cut_get {n0 N a len m : ℕ} (h1 : m < len) (h2 : a + m < N) :
    (((K2.sentIds n0 N).extract a N).extract 0 len)[m]? = some (n0 + (a + m)) := by
  have s0 : (K2.sentIds n0 N).size = N := sentIds_size n0 N
  have s1 : ((K2.sentIds n0 N).extract a N).size = N - a := by
    rw [Array.size_extract, s0]
    omega
  rw [Array.getElem?_extract, if_pos (by rw [s1]; omega), Nat.zero_add, Array.getElem?_extract,
    if_pos (by rw [s0]; omega)]
  exact sentIds_get h2

/-- The switch's sending at the output head's segment: the target, the kept copies, the segment's
first messages, the fresh mask. -/
theorem headNotices_size (s : S) (a : HeadOwn) (G : ReqGroup) :
    (_root_.Tw.K2.switchNotices G.target (K2.headFrontOf s a G.target).others).size =
      1 + G.target.kept.size + ((s.check.frame.atMoment 0).length + 1) := by
  have e : (ReqFrame.notices (s.check.frame.atMoment 0)).size =
      (s.check.frame.atMoment 0).length := by
    unfold ReqFrame.notices
    rw [List.size_toArray, List.length_map]
  have e2 : (K2.headFrontOf s a G.target).others =
      ReqFrame.notices (s.check.frame.atMoment 0) ++
        #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})] := rfl
  unfold _root_.Tw.K2.switchNotices
  rewrite [e2, Array.size_append, Array.size_append, Array.size_append, Array.size_map, e]
  rfl

/-! ## Fresh in front, opened behind -/

/-- How many messages segment l sends at its moment t, by the request's shape. -/
def momentCount (shape : ReqShape) (l t : ℕ) : ℕ :=
  (((shape.link[l]?.map (·.messages)).getD []).filter fun m => m.moment == t).length

/-- How many messages segment l sends at its first moment, by the request's shape. -/
def firstCount (shape : ReqShape) (l : ℕ) : ℕ :=
  (((shape.link[l]?.map (·.messages)).getD []).filter fun m => m.moment == 0).length

/-- The first moment is moment 0. -/
theorem firstCount_eq (shape : ReqShape) (l : ℕ) : firstCount shape l = momentCount shape l 0 := rfl

/-- The frame's own list of its segment's first messages has that length. -/
theorem atMoment_count (f : ReqFrame) : (f.atMoment 0).length = firstCount f.shape f.link := rfl

/-- **The state stands in the output head's segment, and the frame that rests in the head's part is
fresh**: it has no own message, and the shape and the number of the segment of the chain's own copy.
-/
def HeadFresh (s : S) : Prop :=
  ∃ a, s.here = .head a ∧
    a.fr.own = #[] ∧ a.fr.shape = s.check.frame.shape ∧ a.fr.link = s.check.frame.link

/-- **Segment l stands open, and its frame holds the numbers of its first messages**, counted back
from the statement's number of messages: as it is right behind the opening of a segment other than
number 0, whose first sending holds one message more behind them. -/
def OpenedAt (l : ℕ) (s : S) : Prop :=
  ∃ L, s.link? = some L ∧ L.link = l ∧ L.check.frame.link = l ∧
    L.check.frame.next = .laterOrClose ∧
    ∀ m O, m < firstCount L.check.frame.shape l →
      O + (firstCount L.check.frame.shape l + 1) = s.st.oracles.size + m →
      L.check.frame.own[m]? = some O

/-- **From "fresh" in front, an accepting step of the code switch with the quiet step behind it
makes "opened" behind**, at the number of the segment that the quiet step tests. -/
theorem placeH2_makes {p : K2.P2} {n : String} {P : K2.HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : ((K2.codeSwitchKind p : Block S Unit).andThen n (K2.headOpened n p.place P)).decide s rs gs = .ok s')
    (hf : HeadFresh s) : OpenedAt P.l s' := by
  obtain ⟨a, G, L, ha, hL, e1, e2, e3, e4, e5, e6, e7⟩ := K2.placeH2_opened h
  obtain ⟨a', ha', f1, f2, f3⟩ := hf
  obtain rfl : a' = a := by
    have := ha'.symm.trans ha
    injection this
  have hc : (s.check.frame.atMoment 0).length = firstCount L.check.frame.shape P.l := by
    rw [atMoment_count, e5, f2, ← f3, e3]
  refine ⟨L, hL, e1, e2, e4, fun m O hm hO => ?_⟩
  rw [e6, headNotices_size, hc] at hO
  rw [e7, f1, Array.empty_append, headNotices_size, hc,
    cut_get hm (by omega)]
  congr 1
  omega

/-- **So the test accepts there**, at the number counted back from the number of messages. sh: the
open segment's frame's shape. -/
theorem OpenedAt.mask {l m O : ℕ} {s : S} {sh : ReqShape} (h : OpenedAt l s)
    (hsh : ∀ L, s.link? = some L → L.check.frame.shape = sh) (hm : maskNoOf sh l = some m)
    (hlt : m < firstCount sh l) (hO : O + (firstCount sh l + 1) = s.st.oracles.size + m) :
    maskMsgB O s = true := by
  obtain ⟨L, hL, _, e2, e3, e4⟩ := h
  have es := hsh L hL
  rw [es] at e4
  exact maskMsgB_of hL ((maskOracle_iff _ _).2 ⟨e3, m, by rw [es, e2]; exact hm, e4 m O hlt hO⟩)

/-! ## Negative tests -/

/-- NEGATIVE TEST: between two segments the state is not "fresh". -/
theorem not_headFresh_between {s : S} (h : s.here = .between) : ¬ HeadFresh s := by
  rintro ⟨a, ha, -⟩
  rw [h] at ha
  cases ha

/-- NEGATIVE TEST: between two segments no segment is "opened". -/
theorem not_openedAt_between {l : ℕ} {s : S} (h : s.here = .between) : ¬ OpenedAt l s := by
  rintro ⟨L, hL, -⟩
  simp [S.link?, h] at hL

/-- NEGATIVE TEST: "opened" fails where the open frame holds no own message, though the shape gives
the segment a first message and the statement has messages enough. -/
theorem not_openedAt_no_own {l : ℕ} {s : S} {L : LinkCtx} (hL : s.link? = some L)
    (h0 : L.check.frame.own = #[]) (hc : 0 < firstCount L.check.frame.shape l)
    (hn : firstCount L.check.frame.shape l + 1 ≤ s.st.oracles.size) : ¬ OpenedAt l s := by
  rintro ⟨L', hL', -, -, -, h⟩
  obtain rfl : L' = L := Option.some.inj (hL'.symm.trans hL)
  have e := h 0 (s.st.oracles.size - (firstCount L'.check.frame.shape l + 1)) hc (by omega)
  rw [h0] at e
  simp at e

/-- The two counts at MaskFront.lean's small frame. -/
theorem toy_counts : firstCount toyFrame.shape 0 = 1 ∧ maskNoOf toyFrame.shape 0 = some 0 :=
  ⟨rfl, rfl⟩

/-! ## Who makes "fresh" -/

/-- The quiet step in front of the reply's round makes it. -/
theorem headFrontQ_fresh {tl : OnBytes.Model.HTailF2} {s s' : S}
    (h : K2.headFrontQ tl s = .ok s') : HeadFresh s' := by
  obtain ⟨x, s₁, a, k⟩ := (K2.headFrontQ_iff tl s s').1 h
  obtain ⟨L, G, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.front
  have hc : s₁.check = s.check := by
    rw [K2.enterHeadQ k.enters]
    unfold S.enterHead
    rewrite [if_pos k.between]
    rfl
  have hc' : s'.check = s.check := by
    rw [k.out]
    exact hc
  refine ⟨{ a with fr := x.f }, by rw [k.out], ?_⟩
  rw [hc']
  show x.f.own = #[] ∧ x.f.shape = s.check.frame.shape ∧ x.f.link = s.check.frame.link
  rw [fa.out]
  exact ⟨rfl, rfl, rfl⟩

/-- The reply's own accepting step leaves where the chain stands and the chain's own copy of the
state of the calls. -/
theorem replyAt_leaves {l V : ℕ} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (Kinds.Reply.blockAt l V).decide s rs gs = .ok s') :
    s'.here = s.here ∧ s'.check = s.check := by
  unfold Kinds.Reply.blockAt Kinds.Reply.entered at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · have h' : Kinds.Reply.decideE V Kinds.Reply.seatAt s rs = .ok s' := h
      unfold Kinds.Reply.decideE at h'
      split at h'
      · split at h'
        · cases h'
        · split at h'
          · cases h'
          · split at h'
            · cases h'
              exact ⟨rfl, rfl⟩
            · cases h'
      · cases h'
  · cases h

variable {Cl : Type}

/-- A guarded sub-protocol's accepting step is one of the sub-protocol's own. -/
theorem decides_guarded {R : S → S → Prop} {b : Block S Cl} (hb : Decides R b)
    (same : S → S → Bool) (but : Place → Bool) : Decides R (b.guarded same but) := by
  intro s rs gs s' h
  have h' : (if but b.place then b.decide s rs gs
      else (b.decide s rs gs).bind (seatSame same s)) = .ok s' := h
  split at h'
  · exact hb s rs gs s' h'
  · obtain ⟨t, h1, h2⟩ := Keeps.ebind_ok h'
    unfold seatSame at h2
    split at h2
    · cases h2
      exact hb s rs gs _ h1
    · cases h2

/-- **The first place of the output head's segment makes "fresh"**: a sub-protocol whose accepting
step makes it, with the reply's own behind. -/
theorem h1_fresh {front : Block S Unit} (hfr : Decides (fun _ s' => HeadFresh s') front)
    (n : String) (l V : ℕ) :
    Decides (fun _ s' => HeadFresh s') (front.andThen n (Kinds.Reply.blockAt l V)) := by
  intro s rs gs s' h
  have h' : (front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind
      (fun t => (Kinds.Reply.blockAt l V).decide t (rs.drop front.rounds.length)
        (gs.drop front.openings)) = .ok s' := h
  obtain ⟨t, h1, h2⟩ := Keeps.ebind_ok h'
  obtain ⟨e1, e2⟩ := replyAt_leaves h2
  obtain ⟨a, ha, hq⟩ : HeadFresh t := hfr _ _ _ _ h1
  refine ⟨a, e1.trans ha, ?_⟩
  rw [e2]
  exact hq

/-- The quiet step as a sub-protocol without a round, at whatever name and place. -/
theorem headFront_decides (name : String) (chain : ℕ) (link : Option ℕ) (piece : ℕ)
    (tl : OnBytes.Model.HTailF2) :
    Decides (fun _ s' => HeadFresh s')
      (roundlessBlock name chain link piece (K2.headFrontQ tl) : Block S Cl) :=
  fun s _ _ s' h => headFrontQ_fresh (tl := tl) (s := s) (s' := s') h

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.K2.placeH2_opened
#print axioms VerifiableInference.Desc.First.MergeLaw.sentIds_get
#print axioms VerifiableInference.Desc.First.MergeLaw.sentIds_size
#print axioms VerifiableInference.Desc.First.MergeLaw.cut_get
#print axioms VerifiableInference.Desc.First.MergeLaw.headNotices_size
#print axioms VerifiableInference.Desc.First.MergeLaw.firstCount_eq
#print axioms VerifiableInference.Desc.First.MergeLaw.atMoment_count
#print axioms VerifiableInference.Desc.First.MergeLaw.not_headFresh_between
#print axioms VerifiableInference.Desc.First.MergeLaw.not_openedAt_between
#print axioms VerifiableInference.Desc.First.MergeLaw.not_openedAt_no_own
#print axioms VerifiableInference.Desc.First.MergeLaw.toy_counts
#print axioms VerifiableInference.Desc.First.MergeLaw.placeH2_makes
#print axioms VerifiableInference.Desc.First.MergeLaw.OpenedAt.mask
#print axioms VerifiableInference.Desc.First.MergeLaw.headFrontQ_fresh
#print axioms VerifiableInference.Desc.First.MergeLaw.replyAt_leaves
#print axioms VerifiableInference.Desc.First.MergeLaw.decides_guarded
#print axioms VerifiableInference.Desc.First.MergeLaw.h1_fresh
#print axioms VerifiableInference.Desc.First.MergeLaw.headFront_decides
