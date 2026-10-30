-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPlanAt.lean.
The plan of a proof's first chain, at the place of a sub-proof's lookup.

OnBytes/Plan/PlanListsReq.lean and OnBytes/Plan/ReqFrames.lean give the plan of a proof's first
chain as a list of rounds: group by group, with the lists L l m of the sub-proofs' rounds between
the frame's. OnBytes/Model/LinkRoundsList.lean gives these lists for the model's sub-proofs
(linkList): at the moments 0 and 2 they begin with the rounds of a lookup of a group of calls
(forestList). This file names the place of such a lookup in the chain's list as a term, and says
what the plan has there.

* drop_take_mid, flatMap_at: two laws of lists.
* headN z n: the rounds of a group before its link's sub-proof. rounds_link: a group's rounds, cut
  there.
* preZero, postZero, chain_at0: the chain's list is preZero ++ (L n.l 0 ++ postZero), for the record
  n of group number i, if it has a link.
* preTwo, postTwo, chain_at2: the same for L n.l 2, if the link has two later moments or more.
* planIs_mid: a plan that is a list's rounds has, behind the rounds of pre, the rounds of the middle
  part; each of these is as close has tested it, and holds in the planner's reckoning.
* forest_at: where the middle part begins with forestList s (forestSize h) and FoNums.ok h holds:
  the plan has forestRounds s .request (forestSize h) at the place pre.length; their entries are
  forEnts, their errors errOf of the lookup's quotients; each holds; the field's rounds' work is 0
  or fits the nonce with six bits to spare.
* LookAt P s h k: these five clauses as one record. plan_at0, plan_at2: LookAt at the places
  (preZero ..).length and (preTwo ..).length, where the sub-proof's list begins with forestList.
* link_layer0, link_layer2, link_attention0, link_attention2, link_head0, link_head2: at which links
  and moments linkList begins with forestList, and of which size.

What LookAt pins and what not: it names the place k in its first clause alone, and the numbers h
through forestSize h alone (v, d, whether there are several calls). Two lookups of one size have the
same rounds, so LookAt holds at the place of each. A place is pinned by the term in the conclusions
of plan_at0 and plan_at2, not by LookAt.
Not shown here: that the verifier's run, or the dry run that makes a file's description, stands at
round number k where it calls the lookup. That the record n is there, has a link and has two later
moments (OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtFrames.lean says what n.l, n.link and n.moments are).
The premises of the six laws
on linkList: that the plan of the link's group is there. That the sizes in these laws are those of
the shapes with which the verifier's run calls the lookup: X is any record here, not only one that
the verifier makes of the public files.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPlanAtLook
import OnBytes.Tie.Pv.Lookup.Forest.FoFour
import OnBytes.Plan.ReqFrames

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params OnBytes.Plan TwPlan TwErr TwRound Cb.Fo

theorem drop_take_mid {α : Type} (pre X post : List α) :
    ((pre ++ (X ++ post)).drop pre.length).take X.length = X := by
  rw [List.drop_left, List.take_left]

theorem flatMap_at {α β : Type} (f : α → List β) : ∀ (l : List α) (i : Nat) (n : α),
    l[i]? = some n → l.flatMap f = (l.take i).flatMap f ++ (f n ++ (l.drop (i + 1)).flatMap f)
  | [], _, _, h => by cases h
  | a :: l, 0, n, h => by
    obtain rfl : a = n := Option.some.inj h
    rfl
  | a :: l, i + 1, n, h => by
    show f a ++ l.flatMap f = (f a ++ (l.take i).flatMap f) ++ (f n ++ (l.drop (i + 1)).flatMap f)
    rw [flatMap_at f l i n h, List.append_assoc]

section
variable (z : ProofSized) (sub : Subproofs) (L : Nat → Nat → List RoundSpec)
  (after : List RoundSpec)

/-- The rounds of a group before its link's sub-proof. -/
def headN (n : FrameN) : List RoundSpec :=
  (if n.plain != 0 then [.silent "REPLY" (24 * n.plain) 0] else []) ++
    (if n.l == 0 then reqSendOwn z.set z.codes n.sent n.sendGroup z.batch.own.first n.riders
      else reqSendOpen z.set z.codes n.sent n.sendGroup z.batch.own.first n.riders ++
        [locRound z.set .request n.before (24 * (z.set.samples * n.sampled)) 0
          (z.set.samples * n.sampled)])

/-- What closes a link: the batching and the fold. -/
def linkClose (n : FrameN) : List RoundSpec :=
  batRound z.set [n.closed] n.batRows :: foldList z.set n.closed 0

theorem rounds_link (n : FrameN) (v : ReqLink) (h : n.link = some v) :
    n.rounds z L = headN z n ++
      (L n.l 0 ++ (momentsList z L n.l n.msgs n.moments 1 ++ linkClose z n)) := by
  unfold FrameN.rounds headN linkClose
  rw [h, List.append_assoc]

/-- The chain's rounds before the sub-proof of group number i. -/
def preZero (i : Nat) (n : FrameN) : List RoundSpec :=
  ((framesOf z sub).take i).flatMap (FrameN.rounds z L) ++ headN z n

/-- The chain's rounds behind the first list of that sub-proof. -/
def postZero (i : Nat) (n : FrameN) : List RoundSpec :=
  (momentsList z L n.l n.msgs n.moments 1 ++ linkClose z n) ++
    (((framesOf z sub).drop (i + 1)).flatMap (FrameN.rounds z L) ++ afterFrames z sub L after)

/-- The place of a sub-proof's first list in the chain's list. -/
theorem chain_at0 (i : Nat) (n : FrameN) (v : ReqLink) (hi : (framesOf z sub)[i]? = some n)
    (hl : n.link = some v) :
    firstChainList z sub L after = preZero z sub L i n ++ (L n.l 0 ++ postZero z sub L after i n) :=
      by
  rw [firstChain_frames, flatMap_at _ _ i n hi, rounds_link z L n v hl]
  unfold preZero postZero
  simp only [List.append_assoc]

/-- The sending of a link's oracle messages of a later moment. -/
def momentSend (n : FrameN) (m : Nat) : List RoundSpec :=
  reqSendOwn z.set z.codes (sentAtMoment n.msgs m) z.link.group z.batch.own.first 0

/-- The chain's rounds before the list of moment 2 of the sub-proof of group number i. -/
def preTwo (i : Nat) (n : FrameN) : List RoundSpec :=
  preZero z sub L i n ++ (L n.l 0 ++ (momentSend z n 1 ++ (L n.l 1 ++ momentSend z n 2)))

/-- The chain's rounds behind that list. -/
def postTwo (i : Nat) (n : FrameN) : List RoundSpec :=
  (momentsList z L n.l n.msgs (n.moments - 2) 3 ++ linkClose z n) ++
    (((framesOf z sub).drop (i + 1)).flatMap (FrameN.rounds z L) ++ afterFrames z sub L after)

/-- The place of the list of moment 2. -/
theorem chain_at2 (i : Nat) (n : FrameN) (v : ReqLink) (hi : (framesOf z sub)[i]? = some n)
    (hl : n.link = some v) (hm : 2 ≤ n.moments) :
    firstChainList z sub L after = preTwo z sub L i n ++ (L n.l 2 ++ postTwo z sub L after i n) :=
      by
  obtain ⟨f, hf⟩ : ∃ f, n.moments = f + 2 := ⟨n.moments - 2, by omega⟩
  have e : momentsList z L n.l n.msgs n.moments 1 = momentSend z n 1 ++ (L n.l 1 ++
      (momentSend z n 2 ++ (L n.l 2 ++ momentsList z L n.l n.msgs (n.moments - 2) 3))) := by
    rw [hf, Nat.add_sub_cancel]
    rfl
  rw [chain_at0 z sub L after i n v hi hl]
  unfold preTwo postTwo postZero
  rw [e]
  simp only [List.append_assoc]

end

/-- A plan that is a list's rounds, at a part of the list. -/
theorem planIs_mid {P : Planned} {s : Setting} {c : Scope} {l pre X post : List RoundSpec}
    (h : PlanIs P s c l) (e : l = pre ++ (X ++ post)) :
    (P.rounds.drop pre.length).take X.length = X.map (·.round s c) ∧
      (∀ y ∈ X, y.Good s c) ∧ ∀ y ∈ X, roundHolds s (capped s) (y.round s c) = true := by
  have hm : ∀ y ∈ X, y ∈ l := fun y hy => by
    rw [e]
    exact List.mem_append_right _ (List.mem_append_left _ hy)
  refine ⟨?_, fun y hy => h.good y (hm y hy), fun y hy => h.holds y (hm y hy)⟩
  rw [h.rounds, e, List.map_append, List.map_append]
  have := drop_take_mid (pre.map (·.round s c)) (X.map (·.round s c)) (post.map (·.round s c))
  rwa [List.length_map, List.length_map] at this

/-- What the plan has at the place of a lookup of a group of calls. -/
theorem forest_at {P : Planned} {s : Setting} {l pre post : List RoundSpec}
    (hP : PlanIs P s .request l) (h : FoNums.Sh) (H : FoNums.ok h = true)
    (e : l = pre ++ (forestList s (OnBytes.Model.forestSize h) ++ post)) :
    (P.rounds.drop pre.length).take (forestRounds s .request (OnBytes.Model.forestSize h)).length =
        forestRounds s .request (OnBytes.Model.forestSize h) ∧
    (forestRounds s .request (OnBytes.Model.forestSize h)).map (·.entry) =
        forEnts (s.workOf .field .request) h ∧
    (forestRounds s .request (OnBytes.Model.forestSize h)).map (·.error) =
        (shHead (FoNums.several h) (2 ^ h.d, 1) ++
          ratN (FoNums.v' h) h.d FoNums.w FoNums.n).map (errOf s .request) ∧
    (∀ r ∈ forestRounds s .request (OnBytes.Model.forestSize h),
        roundHolds s (capped s) r = true) ∧
    (s.workOf .field .request = 0 ∨ s.workOf .field .request + 6 ≤ 8 * s.nonceBytes) := by
  obtain ⟨a1, a2, a3⟩ := planIs_mid hP e
  have es : OnBytes.Model.forestSize h = ⟨FoNums.v' h + 1, h.d, FoNums.several h⟩ := by
    rw [← ok_v H]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (forestRounds s .request (OnBytes.Model.forestSize h)).length =
        (forestList s (OnBytes.Model.forestSize h)).length := List.length_map _
    rw [this]
    exact a1
  · rw [es]
    exact forest_entries s .request _ _ _
  · rw [es]
    exact forest_errors s .request _ _ _
  · intro r hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr
    exact a3 y hy
  · have hmem : RoundSpec.said "LKP" .field (Bound.ratio (sumT ((lookupParts
        { v := (OnBytes.Model.forestSize h).v, d := (OnBytes.Model.forestSize h).d, mu := 5,
          shifted := (OnBytes.Model.forestSize h).shifted }).map (2 ^ ·)) - 1) s.cardE)
        { drawE := 1, priced := .callersWord } 0 0 0 ∈
        forestList s (OnBytes.Model.forestSize h) := by
      unfold forestList lookupList
      exact List.mem_append_right _ List.mem_cons_self
    have g := (a2 _ hmem).2.2
    by_cases h0 : s.workOf .field .request = 0
    · exact .inl h0
    · exact .inr (g h0)

/-- What a plan has at the place k of the lookup with the numbers h. -/
structure LookAt (P : Planned) (s : Setting) (h : FoNums.Sh) (k : Nat) : Prop where
  here : (P.rounds.drop k).take (forestRounds s .request (OnBytes.Model.forestSize h)).length =
    forestRounds s .request (OnBytes.Model.forestSize h)
  entries : (forestRounds s .request (OnBytes.Model.forestSize h)).map (·.entry) =
    forEnts (s.workOf .field .request) h
  errors : (forestRounds s .request (OnBytes.Model.forestSize h)).map (·.error) =
    (shHead (FoNums.several h) (2 ^ h.d, 1) ++
      ratN (FoNums.v' h) h.d FoNums.w FoNums.n).map (errOf s .request)
  holds : ∀ r ∈ forestRounds s .request (OnBytes.Model.forestSize h),
    roundHolds s (capped s) r = true
  work : s.workOf .field .request = 0 ∨ s.workOf .field .request + 6 ≤ 8 * s.nonceBytes

section
variable {P : Planned} {s : Setting} {z : ProofSized} {sub : Subproofs}
  {L : Nat → Nat → List RoundSpec} {after : List RoundSpec}

/-- The lookup at the head of a sub-proof's first list. -/
theorem plan_at0 (hP : PlanIs P s .request (firstChainList z sub L after)) (i : Nat) (n : FrameN)
    (v : ReqLink) (hi : (framesOf z sub)[i]? = some n) (hl : n.link = some v) (h : FoNums.Sh)
    (H : FoNums.ok h = true) (rest : List RoundSpec)
    (hL : L n.l 0 = forestList s (OnBytes.Model.forestSize h) ++ rest) :
    LookAt P s h (preZero z sub L i n).length := by
  have e : firstChainList z sub L after = preZero z sub L i n ++
      (forestList s (OnBytes.Model.forestSize h) ++ (rest ++ postZero z sub L after i n)) := by
    rw [chain_at0 z sub L after i n v hi hl, hL, List.append_assoc]
  obtain ⟨a1, a2, a3, a4, a5⟩ := forest_at hP h H e
  exact ⟨a1, a2, a3, a4, a5⟩

/-- The lookup at the head of a sub-proof's list of moment 2. -/
theorem plan_at2 (hP : PlanIs P s .request (firstChainList z sub L after)) (i : Nat) (n : FrameN)
    (v : ReqLink) (hi : (framesOf z sub)[i]? = some n) (hl : n.link = some v)
    (hm : 2 ≤ n.moments) (h : FoNums.Sh) (H : FoNums.ok h = true) (rest : List RoundSpec)
    (hL : L n.l 2 = forestList s (OnBytes.Model.forestSize h) ++ rest) :
    LookAt P s h (preTwo z sub L i n).length := by
  have e : firstChainList z sub L after = preTwo z sub L i n ++
      (forestList s (OnBytes.Model.forestSize h) ++ (rest ++ postTwo z sub L after i n)) := by
    rw [chain_at2 z sub L after i n v hi hl hm, hL, List.append_assoc]
  obtain ⟨a1, a2, a3, a4, a5⟩ := forest_at hP h H e
  exact ⟨a1, a2, a3, a4, a5⟩

end

/-! ### where the model's sub-proofs' lists begin with a lookup -/

section
open OnBytes.Model OnBytes.Model.Verify
variable (s : Setting) (c : Scope) (X : Public) (link : Nat)

theorem link_layer0 (hp : Layer.HPlan2) (h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = false)
    (h2 : (link % (if X.p4 then 2 else 1) == 0) = true)
    (hG : X.G[link / (if X.p4 then 2 else 1)]? = some hp) :
    linkList s c X link 0 = forestList s (forestSize X.y.fo) ++
      layerOwnList s (layerNumbers X.layers hp (link / (if X.p4 then 2 else 1))) := by
  unfold linkList
  rw [h1, h2, hG]
  rfl

theorem link_layer2 (hp : Layer.HPlan2) (h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = false)
    (h2 : (link % (if X.p4 then 2 else 1) == 0) = true)
    (hG : X.G[link / (if X.p4 then 2 else 1)]? = some hp) :
    linkList s c X link 2 = forestList s (forestSize hp.tl.f9) ++
      [batSigmaFrom s hp.nBatched 0] := by
  unfold linkList
  rw [h1, h2, hG]
  rfl

theorem link_attention0 (a : Attention.Plan)
    (h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = false)
    (h2 : (link % (if X.p4 then 2 else 1) == 0) = false)
    (hA : X.A[link / (if X.p4 then 2 else 1)]? = some a) :
    linkList s c X link 0 = forestList s (forestSize a.fs) ++ attentionOwnList s a.own := by
  unfold linkList
  rw [h1, h2, hA]
  show (forestList s (forestSize a.fs) ++ attentionOwnList s a.own) ++ ([] ++ []) = _
  rw [List.append_nil, List.append_nil]

theorem link_attention2 (a : Attention.Plan)
    (h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = false)
    (h2 : (link % (if X.p4 then 2 else 1) == 0) = false)
    (hA : X.A[link / (if X.p4 then 2 else 1)]? = some a) :
    linkList s c X link 2 = forestList s (forestSize a.seam.tl.f9) ++
      [batSigmaFrom s a.own.rows 0] := by
  unfold linkList
  rw [h1, h2, hA]
  rfl

theorem link_head0 (h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = true) :
    linkList s c X link 0 = forestList s (forestSize X.HLy.fs) ++
      headOwnList s (X.H.own X.hS) := by
  unfold linkList
  rw [h1]
  show (forestList s (forestSize X.HLy.fs) ++ headOwnList s (X.H.own X.hS)) ++ ([] ++ []) = _
  rw [List.append_nil, List.append_nil]

theorem link_head2 (h1 : (link == (if X.p4 then 2 else 1) * X.NGr) = true) :
    linkList s c X link 2 = forestList s (forestSize X.H.tl.f9) ++
      headEndList s (X.H.own X.hS) := by
  unfold linkList
  rw [h1]
  rfl

end

end TwLaw
