-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/BehindJoin.lean: THE FOUR PUBLIC TESTS THAT THE SUB-PROTOCOL "the output
head's own rounds" (K6) MAKES, BEHIND A YES OF THE MEMBER's STEP, AT THE COMPOSED MEANING:
`four_made_at` (Honest/Law/BehindFour.lean) with most of its premises paid by calls. General in the
composed meaning's data. Two theorems with one conclusion: `four_of_front'`, and `four_of_front`,
which asks two premises more. CONDITIONAL.

WHO PAYS WHAT. From the member's form and from that its step accepts (`K6MemberIs`,
Johnson/Desc/Kinds/Law/K6WayUp.lean): that the bare sub-protocol's step accepts, and the state's own
test on the request (`K6MemberIs.step_down`; in `four_of_front` the way down of
`K6MemberIs.step_iff`); `K6On` (`k6On_of_start`, Law/K6OrdLeft.lean, which also takes the member's
test on the plan and `K6Left` off the promise); `K6After` (`Came.rowPromise`, Law/RowPromise.lean);
the strict reading's yes (`below_of_yes`), under hcan. From what the promise in front says of the
state (`K6FrontItems`, Honest/Law/FrontItems.lean, FrontMore.lean): nine fields or lemmas there are
called: seven premises of `four_made_at` are paid by them outright; `k6Left` goes into `K6On`,
`tokenSmall` into the covered positions. The covered positions: `covered_answers`
(Law/SilentAnswers.lean) from the token heard, `replyTok_is` (Law/ReplyTokIs.lean) and the state's
own test on the request. Of the leaves: `leavesReady_item` (Law/LeavesReadyPaid.lean) and the
premise Lf. In the goals' scope: three tests with code, the planes' columns and the sizes (namespace
InScope: Law/K6PubInScope.lean, TablesPlanInScope.lean), as the library's `pubBehind_scope`
(Law/K6PubBehindScope.lean) pays them.

WHAT IS LEFT AS PREMISES of `four_of_front'`. What the promise in front says of the state (R:
`K6FrontItems`, whole). The member's form, its test on the plan, that its step accepts; hcan: every
word of the rounds is below the prime; the scope (three premises); that the output head's segment is
number 24 (which the scope gives too: `headLink_in_scope`, Johnson/P5J/RowsAtMg.lean, not among what
this file imports); two facts on the composed meaning's data (treesB, sorts) and two tests with code
that read more than the public parameters; the six facts on the link's list of rounds (four are
spent here) and the runs' readers; four premises on a reached state. `four_of_front` ASKS BESIDES
two facts on the member's guard and its place (hk, hsm): IDLE IN SUBSTANCE: they go into
`K6MemberIs.step_iff` alone, whose way down needs neither.

Limits. No yes is shown. Modules under lean/Johnson/Goal/ are among what this file imports:
it imports no module of that folder by name and calls nothing that is declared there: they lie
beneath the library's files that it calls. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.BehindFour
import Johnson.Desc.K6.Honest.Law.KeepsMember
import Johnson.Desc.K6.Honest.Law.FrontMore
import Johnson.Desc.Kinds.Law.K6OrdLeft
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K6PubBehindScope
import Johnson.Desc.Kinds.Law.ReplyTokIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (Block Claim OpenedColumn Link Place KindName Wit noDigest)
open VerifiableInference.Desc.First (S Pub Meaning)
open VerifiableInference.Desc.Sound (linksFull MsgT CellsQ mgAll)
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtTable
open VerifiableInference.Desc.Kinds.Head.Law.AtFold

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : Sound.MgData Xi P Tok rows cols nR Wp) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE FOUR PUBLIC TESTS THAT THE SUB-PROTOCOL MAKES, BEHIND A YES OF THE MEMBER's STEP**, from
what the promise in front says of the state (`K6FrontItems`), four facts on a reached state, the
scope and tests with code on public data. CONDITIONAL: the head's list WHAT IS LEFT AS PREMISES
names every premise; hk and hsm are idle in substance: `four_of_front'` has the same conclusion
without them. -/
theorem four_of_front {a : P × S} (R : K6FrontItems D Mg a) {s' : S} {same : S → S → Bool}
    {pl : Place} {b : Block S Claim} (M : K6MemberIs Wp 24 same pl b) (hk : pl.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (hp : b.planOk = true)
    {ft n : Nat} {rs : List Fmt.RoundView} {cls : List OpenedColumn}
    (hstep : b.step ft a.2 rs cls = .ok (s', n))
    (hcan : viewWordsBelowPrime ⟨rs.map noDigest, []⟩ = true)
    {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hRd : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok Wp)
    (hH : VerifiableInference.OnPublicFiles.headLink Wp = 24)
    (treesB : First.FillSent.treesAt D.built 24 = First.FillSent.looksOf Wp.H.Fp)
    (sorts : D.links[24]? = some .head) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
    (Lp : K12.Door.Laid) (Mm : List OracleShape)
    (hC2 : readsRoomC Wp lay6 (D.sent.arrayOf.getD 24 #[]) = true)
    (hC3 : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    {Lk : Link S Claim} (six : P4.SixAt Wp Lk) (small : S → Option K9.Read)
    (readers : D.Rd 24 =
      K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (Rr : K6Reached a.2) (Fo : AtFold.FoldAt Lp Mm D.cs D.shape lay6 a.2)
    (Lf : VerifiableInference.OnPublicFiles.LeavesFilled a.2) (Tk : TokSmall Wp.hS.V a.2) :
    ∀ i ∈ [Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join"], (mgAll D Mg).pub i (a.1, s') = true := by
  obtain ⟨z1, _, _, z4, _, _, _, z8⟩ := InScope.sizes_five hZ hRd hX
  have Fw := InScope.fs_in_scope hZ hRd hX
  have Pw := InScope.plan_in_scope hZ hRd hX
  -- the bare block's step, and the state's own test on the request
  obtain ⟨hbare, hstart⟩ := (M.step_iff hk hsm ft a.2 s' rs cls n).1 hstep
  have h6 := M.bare
  have hL := R.k6Left hH
  have hOn : K6On Wp a.2 := by
    obtain ⟨ms, bS, name, hS, hla⟩ := M
    exact k6On_of_start hS (by rw [← IM.alone_planOk hla]; exact hp) hstart hL
  have hA : K6After Wp s' := (Came.rowPromise Wp 24 _ h6 ft a.2 rs cls s' n hOn hbare).1
  obtain ⟨gs, hd0⟩ := Came.step_decide ft _ a.2 rs cls s' n hbare
  -- the decision reads no opened leaf: so at the empty list too
  have hd1 : (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24).decide a.2 (rs.map noDigest) [] =
      .ok s' := hd0
  have hd := below_of_yes _ hcan hd1
  have K : K6Keeps a.2 s' := k6_keeps_of_member_step M hstep
  -- the covered positions
  have hc : ∃ cov, s'.covered Wp.hS.T Wp.hS.V = .ok cov := by
    have h1 := R.tokenSmall
    unfold tokenHeardB at h1
    cases ht : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.2 with
    | none =>
      rw [ht] at h1
      cases h1
    | some y0 =>
      have hy : a.2.replyTok? = some y0 :=
        (replyTok_is Wp.hS.V (by rw [z8]; decide) a.2 Tk).trans ht
      have e1 : s'.replyTok? = a.2.replyTok? := by rw [K.here]; rfl
      have e2 : s'.reqOk Wp.hS.T Wp.hS.V = a.2.reqOk Wp.hS.T Wp.hS.V := by rw [K.here]; rfl
      exact covered_answers Wp.hS.T Wp.hS.V s' y0 (e1.trans hy) (hL.2.1 y0 ht) (e2.trans hstart)
  -- what the lookup on the calls left of the leaves
  have hLv : ∀ Fs gk, a.2.fork? = some Fs → a.2.lookHeard? = some gk →
      LeavesReady gk Fs ∧ OnBytes.PscRun.Filled Fs gk.sBit ∧
        ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled Fs x.1 := by
    intro Fs gk hF hg
    obtain ⟨p3, _, L3⟩ := R.left
    obtain ⟨F', g', w1, w2, v1, v2⟩ := leavesReady_item L3
    obtain rfl : Fs = F' := Option.some.inj (hF.symm.trans w1)
    obtain rfl : gk = g' := Option.some.inj (hg.symm.trans w2)
    exact ⟨v1, v2, fun x hx => (Lf gk Fs hg hF x hx).2⟩
  rw [Sound.mgAll_pub]
  refine four_made_at D Mg.pub a.1 h6 hd lay6 num Lp Mm hOn hA R.left R.noneWaits R.linkArr
    R.sentIs R.linkFresh R.book (R.oneRow hX treesB) Rr Fo hLv hc
    (InScope.k6Pub_in_scope hZ hRd hX) hC2 (InScope.tabsPlan_in_scope hZ hRd hX)
    (InScope.readsPlan_in_scope hZ hRd hX) hC3 sorts ?_ 4 Lk small six.1 six.2.1 six.2.2.1
    six.2.2.2.1 readers
  intro p3 h3 hp3 hs3
  obtain ⟨pc, ec, sc, _, _⟩ := InScope.calls_place hZ hX
  obtain rfl : p3 = pc := Option.some.inj (hp3.symm.trans ec)
  obtain rfl : Wp.HLy.fs = h3 := Option.some.inj (sc.symm.trans hs3)
  rw [Fw.NC, Fw.kT, z4, z1, Pw.mats]
  decide

/-- **THE FOUR PUBLIC TESTS THAT THE SUB-PROTOCOL MAKES, WHERE THE MEMBER's STEP ACCEPTS: AT EVERY
ADDRESS AND EVERY GUARD.** `four_of_front` without its two premises on the member's guard and place.
The proof is that one's, line for line, but for the way down (`K6MemberIs.step_down`). CONDITIONAL:
the head's list WHAT IS LEFT AS PREMISES names every premise. -/
theorem four_of_front' {a : P × S} (R : K6FrontItems D Mg a) {s' : S} {same : S → S → Bool}
    {pl : Place} {b : Block S Claim} (M : K6MemberIs Wp 24 same pl b) (hp : b.planOk = true)
    {ft n : Nat} {rs : List Fmt.RoundView} {cls : List OpenedColumn}
    (hstep : b.step ft a.2 rs cls = .ok (s', n))
    (hcan : viewWordsBelowPrime ⟨rs.map noDigest, []⟩ = true)
    {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hRd : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok Wp)
    (hH : VerifiableInference.OnPublicFiles.headLink Wp = 24)
    (treesB : First.FillSent.treesAt D.built 24 = First.FillSent.looksOf Wp.H.Fp)
    (sorts : D.links[24]? = some .head) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
    (Lp : K12.Door.Laid) (Mm : List OracleShape)
    (hC2 : readsRoomC Wp lay6 (D.sent.arrayOf.getD 24 #[]) = true)
    (hC3 : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    {Lk : Link S Claim} (six : P4.SixAt Wp Lk) (small : S → Option K9.Read)
    (readers : D.Rd 24 =
      K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (Rr : K6Reached a.2) (Fo : AtFold.FoldAt Lp Mm D.cs D.shape lay6 a.2)
    (Lf : VerifiableInference.OnPublicFiles.LeavesFilled a.2) (Tk : TokSmall Wp.hS.V a.2) :
    ∀ i ∈ [Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
      .formsInT 24 4 "join"], (mgAll D Mg).pub i (a.1, s') = true := by
  obtain ⟨z1, _, _, z4, _, _, _, z8⟩ := InScope.sizes_five hZ hRd hX
  have Fw := InScope.fs_in_scope hZ hRd hX
  have Pw := InScope.plan_in_scope hZ hRd hX
  -- the bare block's step, and the state's own test on the request
  obtain ⟨hbare, hstart⟩ := M.step_down hstep
  have h6 := M.bare
  have hL := R.k6Left hH
  have hOn : K6On Wp a.2 := by
    obtain ⟨ms, bS, name, hS, hla⟩ := M
    exact k6On_of_start hS (by rw [← IM.alone_planOk hla]; exact hp) hstart hL
  have hA : K6After Wp s' := (Came.rowPromise Wp 24 _ h6 ft a.2 rs cls s' n hOn hbare).1
  obtain ⟨gs, hd0⟩ := Came.step_decide ft _ a.2 rs cls s' n hbare
  -- the decision reads no opened leaf: so at the empty list too
  have hd1 : (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24).decide a.2 (rs.map noDigest) [] =
      .ok s' := hd0
  have hd := below_of_yes _ hcan hd1
  have K : K6Keeps a.2 s' := k6_keeps_of_member_step M hstep
  -- the covered positions
  have hc : ∃ cov, s'.covered Wp.hS.T Wp.hS.V = .ok cov := by
    have h1 := R.tokenSmall
    unfold tokenHeardB at h1
    cases ht : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.2 with
    | none =>
      rw [ht] at h1
      cases h1
    | some y0 =>
      have hy : a.2.replyTok? = some y0 :=
        (replyTok_is Wp.hS.V (by rw [z8]; decide) a.2 Tk).trans ht
      have e1 : s'.replyTok? = a.2.replyTok? := by rw [K.here]; rfl
      have e2 : s'.reqOk Wp.hS.T Wp.hS.V = a.2.reqOk Wp.hS.T Wp.hS.V := by rw [K.here]; rfl
      exact covered_answers Wp.hS.T Wp.hS.V s' y0 (e1.trans hy) (hL.2.1 y0 ht) (e2.trans hstart)
  -- what the lookup on the calls left of the leaves
  have hLv : ∀ Fs gk, a.2.fork? = some Fs → a.2.lookHeard? = some gk →
      LeavesReady gk Fs ∧ OnBytes.PscRun.Filled Fs gk.sBit ∧
        ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled Fs x.1 := by
    intro Fs gk hF hg
    obtain ⟨p3, _, L3⟩ := R.left
    obtain ⟨F', g', w1, w2, v1, v2⟩ := leavesReady_item L3
    obtain rfl : Fs = F' := Option.some.inj (hF.symm.trans w1)
    obtain rfl : gk = g' := Option.some.inj (hg.symm.trans w2)
    exact ⟨v1, v2, fun x hx => (Lf gk Fs hg hF x hx).2⟩
  rw [Sound.mgAll_pub]
  refine four_made_at D Mg.pub a.1 h6 hd lay6 num Lp Mm hOn hA R.left R.noneWaits R.linkArr
    R.sentIs R.linkFresh R.book (R.oneRow hX treesB) Rr Fo hLv hc
    (InScope.k6Pub_in_scope hZ hRd hX) hC2 (InScope.tabsPlan_in_scope hZ hRd hX)
    (InScope.readsPlan_in_scope hZ hRd hX) hC3 sorts ?_ 4 Lk small six.1 six.2.1 six.2.2.1
    six.2.2.2.1 readers
  intro p3 h3 hp3 hs3
  obtain ⟨pc, ec, sc, _, _⟩ := InScope.calls_place hZ hX
  obtain rfl : p3 = pc := Option.some.inj (hp3.symm.trans ec)
  obtain rfl : Wp.HLy.fs = h3 := Option.some.inj (sc.symm.trans hs3)
  rw [Fw.NC, Fw.kT, z4, z1, Pw.mats]
  decide

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.four_of_front
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.four_of_front'
