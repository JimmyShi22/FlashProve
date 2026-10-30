-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Behind/Reached.lean: the proofs of `SpeaksOfTests`, `FrontAtReached` and
`PromiseBehindStep` (Johnson/Desc/K11/Behind/ReachedStatement.lean), to the letter. Lemmas; none of
the library's goals.

How. The first: the lines of `speaks_at_front` (Johnson/Top/H0/MergeLaw/SpeaksAtFront.lean) behind
those that open the table's condition. The second: `leavesLenB`: `leaves_reach_paid`
(Johnson/K11R/LeavesPaid.lean) · `Speaks`: the first, at `K11.tablesLaid_346`
(Johnson/K11R/TablesAt346.lean) · `MergeFront`: its field mask by `maskAtB_seated`
(Johnson/K11R/MaskSeat.lean: general in the meaning) at the meaning without the three sentences on
strings, called as Johnson/Desc/ProofFile/Honest/K11/Plays/MaskAtHead.lean, a file that is not in
this library, calls it; the other three by `front_facts` (Johnson/Top/H0/MergeLaw/FrontFacts.lean)
at the library's facts on reached states (`P5J.foldFacts_at_head'`), the public test "indexIs", and
the closed facts that `K11.k11Eight_of_two` (Johnson/K11R/CondOfTwo.lean) draws from the hypothesis,
as `k11Cond_of_tight` (Johnson/K11R/CondOfTight.lean) lays them. The third: the member is the kind's
block at its seat (`headMergeAtFull`, Johnson/Desc/K11/Exchange/AtFull.lean); its step's yes is a
yes of the kind's decision (`headMergeSeated`, Johnson/Desc/K11/Returns/Seat.lean;
`IM.guardMark_yes`); then the second and `promiseBehindMerge` (Promise.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Behind.ReachedStatement
import Johnson.Desc.K11.Behind.Promise
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.Desc.K11.Returns.Seat
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Behind
open VerifiableInference.Desc (Link Claim Wit step_iff)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Pub Meaning onAt samplesHeld pubHeld flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open VerifiableInference.Desc.K13.Law (LFull laid_in_scope)
open VerifiableInference.Desc.K13 (indexIsC)
open Johnson.Desc.First.Walk.Tied (RchAt Reach reach_raw rchAt_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Returns (headMergeSeated)
open P5J (AtMgA mgAtAll F0T)

/-- **The five tests with code, from the eight items' public tests.** -/
theorem speaksOfTests : SpeaksOfTests := by
  intro Xi P Tok rows cols nR X D Mg z a l hl hH hq hlk ht
  have hRd : D.pubD.Rd 24 =
      VerifiableInference.Desc.K9.readersOfLink
        (VerifiableInference.Desc.K9.holesAt X (VerifiableInference.OnPublicFiles.headLink X) 24 l) l :=
    VerifiableInference.Desc.K9.readersAt_some D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24 l
      hlk
  have hsil : (VerifiableInference.Desc.K9.holesAt X (VerifiableInference.OnPublicFiles.headLink X) 24
      l).silent = VerifiableInference.Desc.Kinds.Head.Law.k6Silent
        (VerifiableInference.Desc.K9.phAt X 24) (VerifiableInference.Desc.K9.statesOfLink l) := by
    unfold VerifiableInference.Desc.K9.holesAt
    rw [hH]
    rfl
  have key : ∀ (k : ℕ) (r : String) (L : List (ℕ × String)), Pub.formsIn 24 k r ∈ keep24 →
      runsAt linksFull 24 k r = L → ∀ p ∈ L, (p.2 == "K8.equations") = false →
      speaksAt l p.1 p.2 a = true := by
    intro k r L hk hL p hp hne
    have h1 := hq _ hk
    have e : D.pubD.runs 24 k r = L := by
      show runsAt D.links 24 k r = L
      rw [hl]
      exact hL
    rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_formsIn, e, List.all_eq_true] at h1
    have h2 := forms_of_test _ _ _ _ _ _ _ (h1 p hp)
    rw [hRd] at h2
    exact speaks_of_forms _ l (VerifiableInference.Desc.K9.phAt X 24) p.1 hne hsil ht h2
  exact
    { planes2 := key 3 "planes" [(2, "planes")] (by simp [keep24]) (by decide) (2, "planes")
        (by simp) (by decide)
      join3 := key 4 "join" [(3, "join")] (by simp [keep24]) (by decide) (3, "join") (by simp)
        (by decide)
      norm3 := key 4 "own" [(3, "norm"), (3, "policy"), (3, "logits")] (by simp [keep24])
        (by decide) (3, "norm") (by simp) (by decide)
      policy3 := key 4 "own" [(3, "norm"), (3, "policy"), (3, "logits")] (by simp [keep24])
        (by decide) (3, "policy") (by simp) (by decide)
      logits3 := key 4 "own" [(3, "norm"), (3, "policy"), (3, "logits")] (by simp [keep24])
        (by decide) (3, "logits") (by simp) (by decide) }

set_option maxRecDepth 100000 in
/-- **The three facts on the state in front, at a reached state.** -/
theorem frontAtReached : FrontAtReached := by
  intro Z D r Zp Np cF x h Lk xM z s hLk hxM hR hf hx hHeld hPP
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
  unfold P1K2.EQ at c5
  rw [Bool.and_eq_true] at c5
  obtain ⟨cIn, cPub⟩ := c5
  have hall := List.all_eq_true.1 (by unfold pubHeld at cPub; exact cPub)
  have hH : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 := by
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
    unfold VerifiableInference.OnPublicFiles.headLink
    rw [p4, ng]
    rfl
  have hraw : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, s) := reach_raw hR
  -- the leaves' walk
  have hlen : leavesLenB s = true := leaves_reach_paid h.scope h.reads O h.laid.planOk hraw
  -- the five tests with code
  have ht : TablesLaid (VerifiableInference.Desc.K9.phAt (P5J.At.X Zp) 24) s := by
    have e := K11.tablesLaid_346 h.scope h.reads O (z, s) hraw
    rw [O.W] at e
    exact e
  have hsp : Speaks Lk s := speaksOfTests _ _ _ _ _ _ _ h.𝔇 mgBase z s Lk rfl hH
    (fun q hq => hall q (k11_hIn h.𝔇 mgBase rfl q (List.mem_append_right _ hq)))
    ((ToldDesc.linkAt_of_open O 24).trans hLk) ht
  -- the promise in front, at the meaning without the three sentences on strings
  have ha : onQ (Fr := ⟨0, [], id, 0⟩) h.𝔇.N (stringFree (mgAtAll h)) linksFull
      (flatPlacesOf linksFull true) (fun t => (z, t)) 346 (s, (fun _ => (0, []), fun _ => [])) := by
    refine ⟨trivial, Or.inr ⟨?_, hHeld, fun _ _ => ⟨trivial, trivial⟩, hPP⟩⟩
    show (_ && _ && _ && _ && _ && _) = true
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, cIn⟩, cPub⟩, c4⟩
  have hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 346
      ((z, s), ((fun _ => (0, []), fun _ => []) : (Frame.mk 0 [] id 0).E.Str)) := hR
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hl := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have FF := P5J.foldFacts_at_head' h.toAtMg (Str := (Frame.mk 0 [] id 0).E.Str)
    (fun b a => RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b a) (fun _ _ ha => ha)
    (L := LFull) (laid_in_scope h.scope h.laid.pub hy) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  have hnum : 181 + (firstCount (P5J.At.shape Zp) 24 + 1) +
      (momentCount Bs.G₀.first.shape 24 1 + momentCount Bs.G₀.first.shape 24 2) =
        h.𝔇.N.msgsAt (some mergeAt) + 0 :=
    LT28.K11Tests.maskNum_at_cut h.scope h.laid.pub hy (congrArg (·.shape) O.first) _
      (K11.hc_paid h)
  have hmask := maskAt_of_test (maskAtB_seated h.scope h.reads O (ft := 0) (start := ProofFile.startS Zp)
    (fun b a => RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b a) h.𝔇.N (stringFree (mgAtAll h)) linksFull
    (flatPlacesOf linksFull true) (h.𝔇.N.group 24) (seatOf xM) 0 181 LFull
    (P5J.At.foldD Zp cF LFull).M mergeAt .head (P5J.At.shape Zp) 0 (fun _ ha => rchAt_raw ha)
    (LT28.K11Tests.maskNo_in_scope h.scope h.laid.pub hy)
    (LT28.K11Tests.maskLt_in_scope h.scope h.laid.pub hy)
    (by rw [total_addsAt]; exact hnum) K11.k11_there (by decide +kernel)
    (LT28.K11Tests.maskSeat_at hxM)
    (LT28.K11Tests.maskOwn_in_scope h.scope h.laid.pub hy hl hxM _ _ _ _ _)
    (LT28.K11Tests.maskBits_in_scope h.scope h.laid.pub hy)
    (fun a ha hm => FF.seatsCarried 346 a ha hm) (fun a ha hm => FF.msgShapes 346 a ha hm)
    (fun a ha hm => FF.liveShape 346 a ha hm) z (s, (fun _ => (0, []), fun _ => [])) ha hr hf)
  -- the index masks' message
  obtain ⟨pM, _, xI, _, _, hxI, _⟩ := K11.members_atAll Zp cF Z.lay (k11AtRB_at_head h.toAtMg)
  have Q8 := K11.k11Eight_of_two h Bs xM xI hxM hxI
    (K11.k11Two_of_pend h Bs O (K11.pendAll_paid h Bs O))
  have hix : indexIsC h.𝔇.N.indexNo s = true := by
    have h0 : (mgAll h.𝔇 mgBase).pub .indexIs (z, s) = true :=
      hall .indexIs (k11_hIn h.𝔇 mgBase rfl .indexIs (by simp))
    rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_indexIs] at h0
    exact h0
  obtain ⟨f1, f2, f3⟩ := front_facts (ni := 256)
    (FF.room 346 _ k11PlaceW 24 hr hf k11_place rfl (by decide)) Q8.roomLeft
    (FF.pileWithin 346 _ hr hf) hix (FF.msgShapes 346 _ hr hf) (FF.codes 346 _ hr hf) Q8.idxShape
    (by
      rw [Q8.idxRows, Fmt.Places.logUp_two_pow]
      exact Q8.niIs)
  exact ⟨⟨hmask, f1, f2, f3⟩, hsp, hlen⟩

/-- **The four behind the member's yes, at a reached state.** -/
theorem promiseBehindStep : PromiseBehindStep := by
  intro Z D r Zp Np cF x h blk z s s' hblk hyes hR hf hx hHeld hPP
  obtain ⟨Bs, Lk, name, hmade, hlk, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain ⟨_, _, O⟩ := h.laid.opened
  have hLk : cF.links[24]? = some Lk := (ToldDesc.linkAt_of_open O 24).symm.trans hlk
  obtain rfl : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Zp Bs.G₀)) name
      IM.k11Place := Option.some.inj (hblk.symm.trans hfl)
  obtain ⟨rs, cols, n, hstep⟩ := hyes
  have hd := ((step_iff _ _ s s' _ cols _).1 hstep).2.1
  rw [headMergeSeated (K11.parOf Zp Bs.G₀) name IM.k11Place] at hd
  obtain ⟨pM, xM, _, e1, hxM, _, _⟩ := K11.members_atAll Zp cF Z.lay (k11AtRB_at_head h.toAtMg)
  obtain rfl : (73, 2) = pM := Option.some.inj (h.toAtMg.mask_place.symm.trans e1)
  obtain ⟨F, hsp, hlen⟩ := frontAtReached Z D r Zp Np cF x h Lk xM z s hLk hxM hR hf hx hHeld hPP
  exact promiseBehindMerge Z D r Zp Np cF x h Bs Lk xM 0 256 z s s' _ hmade hLk
    ((IM.guardMark_yes _ s s' _ _).1 hd).1 F hsp hlen hf hx hHeld hPP

end Johnson.Desc.First.ForkMerge.Behind

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Behind.speaksOfTests
#print axioms Johnson.Desc.First.ForkMerge.Behind.frontAtReached
#print axioms Johnson.Desc.First.ForkMerge.Behind.promiseBehindStep
