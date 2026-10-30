-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/FencesReached.lean: code switching (K2): THE FENCES OF ITS SHARES OF
e₁ (what hMade's joins ask of the state in front beside the book-keeping:
SentFence, Johnson/Road/K4/Rec/MadeSent.lean · K5Front · HeadFence, Johnson/P1K2R/)
AT REACHED STATES, IN SCOPE: FROM «in scope · the files read · the opening O
(IM.Open)» ALONE. A join over theorems of Johnson/IMR/. NO BLOCK IMPORTS THIS FILE.
  frame_at_link    at a state that is reached in front of sub-protocol 14 l + 2 (l < 25): the
                   chain's frame's shape is the plan's · its groups are reqGroups of it · its link
                   is l. By open_recAll · laid_at (Johnson/IMR/ListsEnds.lean · FrontPin.lean), as
                   inside swState_link: WITHOUT the two invariants on stored
                   sample rows, which these three facts do not need
  frame_at_head    in front of 339: the like at 24; and the head's own part's frame has no own
                   message yet (h1_headFr) and its groups are the chain's frame's (RecAll holds
                   every copy of the frame)
  sentFence_reached · headFence_reached · k5Front_reached   the fences
THE LAYOUT that the state holds is the plan's (Z.first.layout): by
rowsLayout_reached (Johnson/IMR/AtReach.lean): so NO PREMISE AT A STATE IS LEFT IN ANY OF THE
THREE FENCES. WHAT STAYS OF K5Front, CLOSED ON THE PLAN: hD5 (the public data's K5 shape is the
plan's) · hμc (μ stands below the number of link l's messages of moment 0).
  share_firstX · share_hearX   K2's shares of e₁ at the 24 places that open a link, over a fence
                               Fk under which the state is reached: the three fences GONE from the
                               premises
LIMITS. A join. e₁ IS NOT PAID. No premise is shown at a value. No soundness is claimed.

-/
import Johnson.IMR.FrontPin
import Johnson.IMR.ListsEnds
import Johnson.IMR.AtReach
import Johnson.Top.H0.Walk.Reach
import Johnson.P1K2R.MadeFirstSent
import Johnson.P1K2R.MadeSentHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open VerifiableInference.Desc.Sound (below)
open OnBytes.Road.K4.Rec (SentFence)
open P1K2 (HeadFence K5Front LinkPlan K5Plan HeadPlan EP prepOf numsAt pureLetters share_firstW
  share_hearW)
open VerifiableInference.Desc.First.K2 (LinkDebts SwitchDebts HeadFresh frontAt frameAt)
open VerifiableInference.Desc.First.FillSent (sentDataAt)
open IM (HandsR XK Yes linksW placesW subW Joined k2P)
open _root_.Tw.K2 (firstFront switchNotices)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem frame_at_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s)) :
    s.check.frame.shape = Z.first.shape ∧ s.check.frame.groups = reqGroups Z.first.shape ∧
      s.check.frame.link = l := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  have hlen : 14 * l + 2 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := l) (i := 0) hl (by decide)
    omega
  have R := open_recAll hS hR O (by omega) hlen f
  exact ⟨R.walk.shape, R.walk.groups, (laid_at hS hR O hl f).2⟩

theorem frame_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    s.check.frame.shape = Z.first.shape ∧ s.check.frame.groups = reqGroups Z.first.shape ∧
      s.check.frame.link = 24 ∧
      ∀ a, s.here = .head a → a.fr.own = #[] ∧ a.fr.groups = s.check.frame.groups := by
  obtain ⟨-, rs, cols, f₀⟩ := (reach_raw hr).fold
  have ix : ∀ i, IM.flatIx c 24 i = 338 + i := fun i =>
    (IM.flatIx_scope hS hR O (by decide) i).trans (by omega)
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [ix 0] at k
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  have hk : s.check.frame.link = 24 := by
    rw [h1_check d0']
    exact (laid_at hS hR O (l := 24) (by decide) fm).2
  have hlen : 339 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide)
    omega
  have R := open_recAll hS hR O (by decide) hlen f₀
  refine ⟨R.walk.shape, R.walk.groups, hk, fun a' ha' => ?_⟩
  obtain ⟨a, ha, o1, _, _⟩ := h1_headFr d0'
  obtain rfl : a = a' := by
    rw [ha] at ha'
    injection ha'
  have hm : a.fr ∈ framesIn s := by
    unfold framesIn
    rw [ha]
    simp
  exact ⟨o1, (R.frames _ hm).groups.trans R.walk.groups.symm⟩

theorem sentFence_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s)) :
    SentFence Z.first.shape s := by
  obtain ⟨a, b, _⟩ := frame_at_link hS hR O hl hr
  exact ⟨by rw [b, a], a⟩

theorem headFence_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    HeadFence Z.first.shape s := by
  obtain ⟨a, b, k, o⟩ := frame_at_head hS hR O hr
  exact ⟨by rw [b, a], a, k, o⟩

theorem k5Front_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s)) {D : PubData}
    (hD5 : D.d5.shape = Z.first.shape) {μ : Nat}
    (hμc : μ < (((Z.first.shape.link[l]?.map (·.messages)).getD []).filter
      fun y => y.moment == 0).length) : K5Front D l Z.first.layout μ s := by
  obtain ⟨a, b, k⟩ := frame_at_link hS hR O hl hr
  have hlen : 14 * l + 2 ≤ (frontOf c).length := by
    have k' := draw_in_front hS hR O (l := l) (i := 0) hl (by decide)
    omega
  have hlay := (rowsLayout_reached hS hR O (reach_raw hr) (by omega) hlen).1
  refine ⟨a.trans hD5.symm, by rw [b, a], k, hlay, ?_⟩
  have e : (s.check.frame.atMoment 0).length =
      (((s.check.frame.shape.link[s.check.frame.link]?.map (·.messages)).getD []).filter
        fun y => y.moment == 0).length := rfl
  rw [e, a, k]
  exact hμc

variable {Q : Type}

theorem share_firstX (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : Nat → S → Prop}
    {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    (hFk : ∀ s, Fk (14 * l + 2) s →
      ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (z, s))
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (bs : Pub → Q × S → Bool) (z : Q)
    (Pl : LinkPlan Z l D₀) {q : Attention.Plan} {μ : Nat}
    (P5 : subW l = .attention → K5Plan Z l D₀ N Z.first.layout q μ)
    (hD5 : D₀.d5.shape = Z.first.shape)
    (hμc : subW l = .attention →
      μ < (((Z.first.shape.link[l]?.map (·.messages)).getD []).filter
        fun y => y.moment == 0).length)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (Dd : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW (EP D₀ bs z) (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (hdS : D₀.dS = sentDataAt Z.first.shape N linksW placesW Z.p.built.links) :
    HandsR Fk N linksW placesW (EP D₀ bs z) ft (14 * l + 2) b :=
  share_firstW h1 h24 hlot hpl hJ D₀ bs z Pl P5
    (fun hatt s hf _ => by
      obtain ⟨z', hr⟩ := hFk s hf
      exact k5Front_reached hS hR O (by omega) hr hD5 (hμc hatt))
    hgrp Dd hdS
    (fun s hf _ => by
      obtain ⟨z', hr⟩ := hFk s hf
      exact sentFence_reached hS hR O (by omega) hr)

theorem share_hearX (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : Nat → S → Prop}
    {G₀ : ProofFile.Ground}
    (hFk : ∀ s, Fk 339 s → ∃ z, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    {b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (bs : Pub → Q × S → Bool) (z : Q)
    (Pl : HeadPlan G₀ D₀)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW (EP D₀ bs z) 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK N linksW placesW (EP D₀ bs z) 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll D₀ bs .tokenSmall (z, s) = true → pubAll D₀ bs .tokenSmall (z, s') = true)
    (hU : ∀ s, Fk 339 s → XK N linksW placesW (EP D₀ bs z) 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    (hdS : D₀.dS = sentDataAt Z.first.shape N linksW placesW Z.p.built.links)
    (hFp : ∀ HP, pureLetters G₀ 24 = some HP →
      ∃ X, Z.p.built.links[24]? = some X ∧ X.Fp.trees = HP.X.Fp.trees) :
    HandsR Fk N linksW placesW (EP D₀ bs z) ft 339 b' :=
  share_hearW hlot hpl D₀ bs z Pl hgrp fresh D htok hU hdS hFp
    (fun s hf _ => by
      obtain ⟨z', hr⟩ := hFk s hf
      exact headFence_reached hS hR O hr)

end Meaning.K2

#print axioms Meaning.K2.share_firstX
#print axioms Meaning.K2.share_hearX
#print axioms Meaning.K2.frame_at_link
#print axioms Meaning.K2.frame_at_head
#print axioms Meaning.K2.sentFence_reached
#print axioms Meaning.K2.headFence_reached
#print axioms Meaning.K2.k5Front_reached
