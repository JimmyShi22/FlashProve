-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SentIsNotices.lean: the kind "the code switch" (K2): AT EVERY
PLACE OF THE KIND THE HONEST SIDE's LIST OF THE SWITCH's MESSAGES (`switchSent`,
Honest/K2/Part.lean) IS THE LIBRARY's TERM FOR WHAT THE SWITCH AT THAT LINK ANNOUNCES
(`First.K2.noticesAt`, Johnson/Goal/Meaning/K2Share/FrontNotices.lean); SO AT A LINK's PLACE IT IS
WHAT THE FRONT OF THE SWITCH's OWN STEP IN THE DESCRIPTION (`frontAt`) ANNOUNCES THERE, under that
file's premises; ITS LAST MESSAGE IS THE NEXT FOLD's FRESH MASK AS THE VERIFIER's TEXT ANNOUNCES IT
(`foldMaskNotice`, OnBytes/Iop/Fold.lean); SO THAT MASK HAS ONE ROW JUST WHERE THE GROUP's NUMBER h
IS 0. Statements with their proofs. A law on texts.

  `sent_is_notices`   at a frame and a link whose number is not 0: the list is `P1K2.noticesAt`
                    (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) at that link, moment 0
  `last_of_push`, `last_is_mask`   tools: the last member of a list with one member laid behind;
                    the last message that a switch announces is the last of "others"
  `frameOfPrep`     the frame that `switchPlaces` (Honest/K2/Half.lean) makes of the planner's
                    sizes, written here again; `place_data` ties the copy
  `place_data`      what `switchPlaces` lays at a place: target and "others", of the frame and the
                    link
  `place_sent`      `sent_is_notices` at a place of the kind with a link whose number is not 0
  `place_front`     at every place of the kind: `switchSent` is `First.K2.noticesAt` at the plan's
                    shape and the place's link
  `place_verifier`  at a link's place, under `RecAll`: what the front of the switch's own step
                    announces is `switchSent`
  `prep_shape`, `place_verifier₀`   the plan's shape is the first state's frame's; so the same with
                    `RecAll` at that shape
  `place_rows`      at a place of the kind: the message that `switchFresh` names has 2 ^ h mask
                    rows, h the number of the group into which the switch leads
  `place_oneRow`    so the premise `oneRow` (Honest/K2/Exact.lean) holds there just if that h is 0

Limits. `place_verifier` has `notices_at_link`'s premises and limits: `RecAll` is a premise; the
head's and the finish's places are not spoken of; the place's numbers n are tied to the place p by
nothing but "it stands at a link" and the frame's link. The front is the description's own step's, a
text "after" the verifier's: not the verifier's program. THE BLOCK's OWN LIST OF WHAT THE SWITCH
SENDS (the field `sent` of the place's numbers, made off `Plan.framesOf`) IS ANOTHER TERM: that it
agrees with these is not shown here: it is `place_nums` (Honest/K2/Law/SentIsBlocks.lean). Of
`P1K2.noticesAt` the lot makes the trees that the next switch reads, no more; at the finish, by the
author's reading, nobody calls it. The file imports one under Johnson/Goal/Meaning/ straight
(FrontNotices.lean). That the frame is the plan's own is `prepOf`'s. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Goal.Meaning.K2Share.FrontNotices
import Johnson.Top.H0.Tw.K2C.GroupAtNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes (ReqFrame OracleNotice foldMaskNotice)

/-- At a frame and a link whose number is not 0: the list is `P1K2.noticesAt` at that link, at the
moment 0. -/
theorem sent_is_notices (f₀ : ReqFrame) (l : Nat) (hl : l ≠ 0) (codes : OnBytes.Codes) (c m : Nat)
    (kept : List OnBytes.OracleShape) :
    switchSent ⟨codes, c, m, kept, (f₀.groups.getD l {}).target⟩
        (ReqFrame.notices ({ f₀ with link := l }.atMoment 0) ++
          #[foldMaskNotice (f₀.foldShape l {})]) =
      P1K2.noticesAt f₀ l 0 := by
  have h₀ : (l == 0) = false := by simpa using hl
  simp [switchSent, P1K2.noticesAt, h₀]
  rfl

/-- A tool: the last member of a list with one member laid behind. -/
theorem last_of_push {α : Type} [Inhabited α] (a : Array α) (n : α) :
    (a ++ #[n]).getD ((a ++ #[n]).size - 1) default = n := by
  simp

/-- The last message that a switch announces is the last of "others". -/
theorem last_is_mask (T : OnBytes.SwitchTarget) (xs : Array OracleNotice) (n : OracleNotice) :
    (Tw.K2.switchNotices T (xs ++ #[n])).getD ((Tw.K2.switchNotices T (xs ++ #[n])).size - 1)
      default = n := by
  unfold Tw.K2.switchNotices
  rw [← Array.append_assoc]
  exact last_of_push _ n

/-- The frame that `switchPlaces` makes of the planner's sizes. -/
def frameOfPrep (P : P1K2.Prep) : ReqFrame :=
  { shape := P.z.request, groups := OnBytes.reqGroups P.z.request }

/-- What `switchPlaces` lays at a place: target and "others", of the frame and the link. -/
theorem place_data {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    p.sizes.target = ((frameOfPrep P).groups.getD p.link {}).target ∧
      p.others = ReqFrame.notices ({ frameOfPrep P with link := p.link }.atMoment 0) ++
        #[foldMaskNotice ((frameOfPrep P).foldShape p.link {})] := by
  cases hs : spotsOf Z.cuts with
  | none =>
    simp only [switchPlaces, hP, hs] at hp
    cases hp
  | some sps =>
    simp only [switchPlaces, hP, hs] at hp
    obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
    exact ⟨rfl, rfl⟩

/-- At a place of the kind behind the first link. -/
theorem place_sent {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    (hl : p.link ≠ 0) :
    switchSent p.sizes p.others = P1K2.noticesAt (frameOfPrep P) p.link 0 := by
  obtain ⟨h₁, h₂⟩ := place_data hP hp
  have h := sent_is_notices (frameOfPrep P) p.link hl p.sizes.codes p.sizes.code p.sizes.maskCode
    p.sizes.kept
  rw [← h₁, ← h₂] at h
  exact h

/-- **At every place of the kind the honest side's list is the library's term for what the switch at
that link announces.** -/
theorem place_front {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    switchSent p.sizes p.others =
      VerifiableInference.Desc.First.K2.noticesAt P.z.request p.link := by
  obtain ⟨h₁, h₂⟩ := place_data hP hp
  show Tw.K2.switchNotices p.sizes.target p.others = _
  rw [h₁, h₂]
  rfl

/-- **At a link's place what the front of the switch's own step announces is the honest side's
list.** -/
theorem place_verifier {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {cs : OnBytes.Codes} {n : VerifiableInference.Desc.First.K2.P2}
    {s : VerifiableInference.Desc.First.S} {fx : Tw.K2.Front}
    (R : Meaning.K2.RecAll cs P.z.request s) (hl : s.check.frame.link = p.link)
    (hn : n.stands = .link) (h : VerifiableInference.Desc.First.K2.frontAt n s = some fx) :
    Tw.K2.switchNotices fx.T fx.others = switchSent p.sizes p.others :=
  (VerifiableInference.Desc.First.K2.notices_at_link R hl hn h).1.trans (place_front hP hp).symm

/-- The plan's shape is the first state's frame's: the library's `prepOf_request`
(Johnson/Top/H0/Tw/K2C/GroupAtNums.lean). -/
theorem prep_shape {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (h : P1K2.prepOf Z G = some P) : P.z.request = Z.s₀.check.frame.shape :=
  (P1K2.prepOf_request h).1

/-- The same, with `RecAll` at the first state's frame's shape. -/
theorem place_verifier₀ {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {cs : OnBytes.Codes} {n : VerifiableInference.Desc.First.K2.P2}
    {s : VerifiableInference.Desc.First.S} {fx : Tw.K2.Front}
    (R : Meaning.K2.RecAll cs Z.s₀.check.frame.shape s) (hl : s.check.frame.link = p.link)
    (hn : n.stands = .link) (h : VerifiableInference.Desc.First.K2.frontAt n s = some fx) :
    Tw.K2.switchNotices fx.T fx.others = switchSent p.sizes p.others :=
  place_verifier hP hp (prep_shape hP ▸ R) hl hn h

/-- The message that `switchFresh` names has 2 ^ h mask rows. -/
theorem place_rows {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    ∀ x ∈ switchFresh p.sizes p.others p.foldVars,
      ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows =
        2 ^ ((frameOfPrep P).groups.getD p.link {}).h := by
  intro x hx
  obtain ⟨-, h₂⟩ := place_data hP hp
  obtain rfl : ((switchSent p.sizes p.others).size - 1, p.foldVars) = x := Option.some.inj hx
  show ((Tw.K2.switchNotices p.sizes.target p.others).getD
    ((Tw.K2.switchNotices p.sizes.target p.others).size - 1) default).shape.maskRows = _
  rw [h₂, last_is_mask]
  rfl

/-- **The premise on the one row, at a place of the kind: a public number of the plan.** -/
theorem place_oneRow {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    (∀ x ∈ switchFresh p.sizes p.others p.foldVars,
      ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows = 1) ↔
      ((frameOfPrep P).groups.getD p.link {}).h = 0 := by
  constructor
  · intro h
    have h₁ := h ((switchSent p.sizes p.others).size - 1, p.foldVars) rfl
    rw [place_rows hP hp _ rfl] at h₁
    rcases Nat.pow_eq_one.1 h₁ with h₂ | h₂
    · omega
    · exact h₂
  · intro h x hx
    rw [place_rows hP hp x hx, h, Nat.pow_zero]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.sent_is_notices
#print axioms ProofFile.Honest.K2.Law.last_of_push
#print axioms ProofFile.Honest.K2.Law.last_is_mask
#print axioms ProofFile.Honest.K2.Law.frameOfPrep
#print axioms ProofFile.Honest.K2.Law.place_data
#print axioms ProofFile.Honest.K2.Law.place_sent
#print axioms ProofFile.Honest.K2.Law.place_front
#print axioms ProofFile.Honest.K2.Law.place_verifier
#print axioms ProofFile.Honest.K2.Law.prep_shape
#print axioms ProofFile.Honest.K2.Law.place_verifier₀
#print axioms ProofFile.Honest.K2.Law.place_rows
#print axioms ProofFile.Honest.K2.Law.place_oneRow
