-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsBehind.lean: AT THE HEAD's PLACE AND AT THE PLACE BEHIND THE LAST
SEGMENT THE KIND's OWN DECISION SAYS YES UNDER THIRTEEN CLAUSES ON THE FRONT (`FrontCore`,
Returns/SentFront.lean), NOT SIXTEEN (`FrontPlain`): THAT THE NEW GROUP IS THERE, WITHOUT MEMBER AND
WITHOUT A TEST BEGUN, IS TAKEN FROM THE LIBRARY. Three structures of premises; one definition;
statements with their proofs.

WHERE THE GROUP IS MADE. At both places an earlier quiet step opens it (`headFrontQ`,
Johnson/Top/H0/Tw/K2C/Head.lean; `finishFrontQ`, K2C/Finish.lean). BEHIND THE LAST SEGMENT the
decision runs at the very state that this step left. AT THE HEAD IT DOES NOT: the sub-protocol that
hears the reply stands between. So the head's half asks two clauses ON THE STATE OF THE DECISION:
the library's own `HeadFresh` (K2C/HandsEnds.lean), WHICH THE LIBRARY PAYS (`headFresh_front`,
`fresh_behind`, `fresh_behind_H1`, K2C/HeadFreshAt.lean; at every state reached in front of the
head's switch, in scope: `fresh_reached`, K2C/HeadFreshReached.lean), and `HeadCode`, new here: what
`HeadFresh` leaves unnamed: the group's main code.

  `head_group`, `fin_group`   right behind the quiet front: the group at the number in the place's
                    own frame, AS A TERM: the library's fresh group at the shape's two codes
  `HeadCode`, `headCode_front`, `headCode_same`, `headCode_behind`   that group's main code is the
                    shape's: behind the quiet front; it reads "here", the statement and the check
                    alone; behind the quiet front and the reply's block in a row
  `CallCore`, `CallCore.plain`   `CallPlain` (Returns/ArmsSent.lean) with `FrontCore` for
                    `FrontPlain`; it gives `CallPlain` where the group is there, in no test and
                    without member
  `HeadBehind`, `HeadBehind.plain`, `head_returns_behind`   the head's place
  `FinBehind`, `FinBehind.plain`, `finish_returns_behind`   the place behind the last segment,
                    behind its quiet front

By: the library's `headFrontQ_iff` (K2C/Asks.lean) · `firstFront_st`, `headFrontQ_groups`,
`headFrontQ_rest` (K2C/FrontGroup.lean) · `finishFrontQ_st`, `finishFrontQ_fr`,
`finishFrontQ_rest` (K2C/FinFront.lean) · `guarded_front` (K2C/HeadFreshAt.lean) · `place_rest`
(Johnson/Desc/Kinds/Law/ReplyRest.lean) · `FrontCore.plain` (Returns/SentFront.lean) ·
`head_returns_sent`, `finish_returns_sent` (Returns/ArmsSent.lean). NEAR RELATIVES IN THE LIBRARY:
`headFresh_front` has `head_group`'s proof and its very group, under an "there is"; `finish_fresh`
(K2C/PositionAtPlan.lean) has `fin_group`'s, under an "there is", with "no row" alone. NEW HERE IS
THE GROUP AS A TERM, for its main code.

Limits. `FinBehind` HAS ONE PREMISE OF THE FORM "... = .ok ...": that the quiet front returned this
state: THE YES OF ANOTHER STEP, not the decision's own nor the sending's; when the front inside it
returns: `finishFront_returns` (Returns/Front.lean). `HeadCode` IS PAID HERE BEHIND THE TWO STEPS IN
A ROW; in the goals' scope, at an opening, at every state reached in front of the head's switch over
the chain's own flat list: Returns/ArmsReached.lean. Those of Returns/ArmsSent.lean, but for the
group's three clauses. THE STRUCTURES ARE SHOWN AT NO STATE HERE. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.ArmsSent
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Top.H0.Tw.K2C.HeadFreshAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block roundlessBlock Place)
open VerifiableInference.Desc.Kinds (Reply.blockOf)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat locOk behindArgs headFrontOf
  finFrontOf headFrontQ finishFrontQ freshGroup withFresh headFrontQ_iff firstFront_st
  headFrontQ_groups headFrontQ_rest finishFrontQ_st finishFrontQ_fr finishFrontQ_rest
  guarded_front)
open VerifiableInference.Desc.First.Send (planOk1)
open _root_.Tw.K2 (Front Col sendByL8 switchNotices)

/-! ## 1 The new group -/

/-- **Behind the head's quiet front**: the group at the number in the head's own frame. -/
theorem head_group {tl : OnBytes.Model.HTailF2} {s₀ s : S} {a : HeadOwn}
    (h : headFrontQ tl s₀ = .ok s) (ha : s.here = .head a) :
    s.st.groups[a.fr.group]? =
      some (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) := by
  obtain ⟨x, s₁, a', k⟩ := (headFrontQ_iff tl s₀ s).1 h
  have e : a.fr.group = s₀.st.groups.size := by
    rw [k.out] at ha
    have e1 : ({ a' with fr := x.f } : HeadOwn) = a := by
      injection ha
    rw [← e1]
    exact (firstFront_st k.front).2
  rw [e, (headFrontQ_rest h).2.2.2.2.1]
  exact (headFrontQ_groups h).2.2.2.2

/-- **Behind the finish's quiet front**: the like. -/
theorem fin_group {s₀ s : S} {a : FinOwn} (h : finishFrontQ s₀ = .ok s) (ha : s.here = .fin a) :
    s.st.groups[a.fr.group]? =
      some (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) := by
  obtain ⟨a', _, h1, _, _, _, _, _, _, _, _, hg⟩ := finishFrontQ_fr h
  rw [ha] at h1
  have e1 : a = a' := by
    injection h1
  rw [e1, hg, (finishFrontQ_rest h).2.2.2.2.1, finishFrontQ_st h]
  simp [withFresh]

/-- The group at the number in the head's own frame has the shape's main code. -/
def HeadCode (s : S) : Prop :=
  ∀ a G, s.here = .head a → s.st.groups[a.fr.group]? = some G →
    G.code = s.check.frame.shape.code

theorem headCode_front {tl : OnBytes.Model.HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    HeadCode s' := by
  intro a G ha hG
  rw [head_group h ha] at hG
  rw [← Option.some.inj hG]
  rfl

/-- It reads "here", the statement and the check alone. -/
theorem headCode_same {s s' : S} (h1 : s'.here = s.here) (h2 : s'.st = s.st)
    (h3 : s'.check = s.check) (h : HeadCode s) : HeadCode s' := by
  intro a G ha hG
  rw [h1] at ha
  rw [h2] at hG
  rw [h3]
  exact h a G ha hG

/-- **Behind the two steps in a row**, in the letters of the library's `fresh_behind`. -/
theorem headCode_behind {W : OnBytes.Model.Verify.Public} {tl : OnBytes.Model.HTailF2} {l l' : Nat}
    {pl : Place} {nm : String} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (Block.andThen nm (Block.guarded ProofFile.sameReply (fun _ => false)
      ({ (roundlessBlock nm 1 (some l') 1 (headFrontQ tl) : Block S Unit) with place := pl }))
      (Reply.blockOf W l)).decide s rs gs = .ok s') : HeadCode s' := by
  obtain ⟨s₀, h0, a1, -, -, -, -, a6, a7, -⟩ :=
    Kinds.Head.Law.place_rest W l nm _ tl (fun _ _ _ _ e => guarded_front e) s rs gs s' h
  exact headCode_same (s := s₀) a7 a1 a6 (headCode_front h0)

/-! ## 2 The call -/

/-- `CallPlain` with the thirteen clauses on the front. code: the new group's main code. -/
structure CallCore (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (c : Code) (code : Nat) : Prop where
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
  front : FrontCore x c code r₂.drawn.poss

theorem CallCore.plain {p : P2} {x : Front} {B : TreeBook} {roots : Nat} {r₁ r₂ : Fmt.RoundView}
    {cols : List OpenedColumn} {c : Code} {G : Group} (H : CallCore p x B roots r₁ r₂ cols c G.code)
    (hg : x.st.groups[x.f.group]? = some G) (hr : G.inRun = false) (hm : G.members = #[]) :
    CallPlain p x B roots r₁ r₂ cols c G :=
  ⟨H.entry, H.fits₁, H.plan, H.step, H.draw, H.vals, H.poss, H.trits, H.factor, H.answers, H.trees,
    H.oldCode, H.loc, H.reads, H.front.plain hg hr hm⟩

/-! ## 3 The two places -/

/-- **All premises at the head's place**, on the state at which the decision runs. -/
structure HeadBehind (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : HeadOwn) (Q : ReqGroup) (c : Code) : Prop where
  fresh : First.K2.HeadFresh s
  code : HeadCode s
  stands : p.stands = .head
  range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  here : s.here = .head a
  number : a.fr.group = p.grp
  group : s.check.frame.groups[s.check.frame.link]? = some Q
  waits : s.noneWaits = true
  call : CallCore p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) c
    s.check.frame.shape.code
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (inFront (par9 p) (headFrontOf s a Q.target) s.book
      (sentAt (sendingAt p (headFrontOf s a Q.target)) (headFrontOf s a Q.target).st s.book s.roots
        r₁ r₂) r₂ (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

theorem HeadBehind.plain {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : HeadOwn} {Q : ReqGroup} {c : Code}
    (H : HeadBehind p s r₁ r₂ gs a Q c) : ∃ G, HeadPlain p s r₁ r₂ gs a Q c G := by
  obtain ⟨G, hG, _, hm, _, hr⟩ := H.fresh a H.here
  have hc := H.code a G H.here hG
  refine ⟨G, H.stands, H.range, H.here, H.number, H.group, H.waits, ?_, H.noneLeft, H.groups⟩
  refine CallCore.plain ?_ hG hr hm
  rw [hc]
  exact H.call

/-- **The kind's own decision says yes at the head's place.** -/
theorem head_returns_behind {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : HeadOwn} {Q : ReqGroup} {c : Code}
    (H : HeadBehind p s r₁ r₂ gs a Q c) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' := by
  obtain ⟨_, h⟩ := H.plain
  exact head_returns_sent h

/-- **All premises at the place behind the last segment, behind its quiet front.** -/
structure FinBehind (p : P2) (s₀ s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : FinOwn) (Q : ReqGroup) (c : Code) : Prop where
  quiet : finishFrontQ s₀ = .ok s
  stands : p.stands = .finish
  range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  here : s.here = .fin a
  number : a.fr.group = p.grp
  laid : a.G = some Q
  waits : s.noneWaits = true
  call : CallCore p (finFrontOf s a Q) s.book s.roots r₁ r₂ (flat p gs) c
    s.check.frame.shape.code
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (inFront (par9 p) (finFrontOf s a Q) s.book
      (sentAt (sendingAt p (finFrontOf s a Q)) (finFrontOf s a Q).st s.book s.roots r₁ r₂) r₂
      (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

theorem FinBehind.plain {p : P2} {s₀ s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : FinOwn} {Q : ReqGroup} {c : Code}
    (H : FinBehind p s₀ s r₁ r₂ gs a Q c) :
    FinPlain p s r₁ r₂ gs a Q c
      (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) :=
  ⟨H.stands, H.range, H.here, H.number, H.laid, H.waits,
    H.call.plain (G := freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode)
      (fin_group H.quiet H.here) rfl rfl, H.noneLeft, H.groups⟩

/-- **The kind's own decision says yes at the place behind the last segment, behind its quiet
front.** -/
theorem finish_returns_behind {p : P2} {s₀ s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : FinOwn} {Q : ReqGroup} {c : Code}
    (H : FinBehind p s₀ s r₁ r₂ gs a Q c) :
    ∃ s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' :=
  finish_returns_sent H.plain

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_group
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_group
#print axioms VerifiableInference.Desc.K2.Honest.Returns.headCode_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.headCode_same
#print axioms VerifiableInference.Desc.K2.Honest.Returns.headCode_behind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.CallCore.plain
#print axioms VerifiableInference.Desc.K2.Honest.Returns.HeadBehind.plain
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_returns_behind
#print axioms VerifiableInference.Desc.K2.Honest.Returns.FinBehind.plain
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finish_returns_behind
