-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean: THE OUTPUT HEAD'S OWN ROUNDS: BEHIND ANY ACCEPTING
STEP OF THE MEMBER FROM A WELL-LAID LEDGER THE VERIFIER'S STATE HOLDS, AS WHAT WAS HEARD AT THE
HEAD, THE VALUES THAT Honest/K6/Heard.lean AND Honest/K6/HeardWhole.lean MAKE OF THE ROUNDS'
CHALLENGES BY ROUND NUMBER: HeardTie.lean's three tops at the state.
WHAT IT IS NOT. CONDITIONAL: THAT THE MEMBER'S STEP ACCEPTS IS A PREMISE; so are the member's form
(K6MemberIs) and, for every top but heard_at_yes and heard_at_accept, that the ledger in front is
well laid: THAT PREMISE IS SPENT ON NOTHING THAT THE TOPS KEEP (Law/K06HeardDraws.lean's head says
why it is asked).
heard_at_yes, logits_at_yes AND tables_at_yes ASK TWO PREMISES MORE, hk (the place's kind is not K7)
AND hsm (the guard same accepts two states that hold one reply): BOTH ARE IDLE: the half of
K6MemberIs.decide_iff that is spent holds at every place and every guard (K6MemberIs.decide_down):
section 4 has the same three without them; the three stay for their callers. FIELD BY FIELD, NOT
WHOLE: of sW, sPv, wpl.sL, wpl.sR, wpl.row and, in tV, tN and tH, sCl, sEnd, p and rowU nothing is
said (HeardTie.lean's head says why the whole equation is false). Of any rounds at which the member
accepts, not of an honest run's: no prover is in this file. Nothing on soundness, on completeness or
on what a proof hides. The frame of the honest side is not imported. No example in this file.
  putFork_request, putFork_reply   laying a ledger turns neither the request's words nor the reply.
  heard_of_decide   where the seated sub-protocol's decision accepts: the state behind stands in the
                    head's link and holds heardOf g1 H: g1 what the lookup left, H the hearing's
                    return at the rounds shown, at the letters that given returns at the state in
                    front.
  heard_at_yes      the same behind any accepting step of the member: the hearing is at the rounds
                    as the decision is shown them: without the sealed digest (noDigest).
  elemOf_elems, headPV_elems, noDigest_elems, logitsR_elems, headTHr_elems, headRs_elems,
  hearingOf_elems, heardWhole_elems   THE READERS BY ROUND NUMBER READ A CHALLENGE'S ELEMENTS ALONE:
                    so every top but heard_at_yes and heard_at_accept stands at the rounds' own
                    challenges, digest and all.
  logits_at_yes     tH.r, rs and win are Heard.lean's headTHr, headRs, headWin, at a chain's
                    challenges front ++ (own ++ later), base := front.length.
  tables_at_yes     PV, wpl.r, tV.r, tN.r, tH.r are HeardWhole.lean's headHeardWhole's, and the
                    maker of the head's tables of reads gives one answer at both.
  heard_at_accept, logits_at_accept, tables_at_accept   the three above without hk and hsm: the same
                    ends, word for word.
  heardOf_at_accept ALL FOURTEEN FIELDS OF HeardTie.lean's heardOf_tie AT THE STATE: win, g1, Zl,
                    PV, gp, wpl.r, wpl.tau, omV, tV.r, tN.r, tH.r, rs, qN, qH are headHeardWhole's
                    (five of them read nothing of the hearing: HeardTie.lean's head). The two tops
                    above it bring seven of the fourteen to the state.
CALLED: HeardTie.lean (logits_tie, heardOf_tie, tables_tie), K6/Honest/Law/Returns.lean
(zt_of_points), Law/K6WayUp.lean (K6MemberIs.decide_iff, K6MemberIs.decide_down); of the library:
step_iff (Johnson/Top/H0/StepLaws/StepLaws.lean), decide_hears_at, setHeard_form, putFork?_ok,
given_ok.

-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.HeardTie
import Johnson.Desc.K6.Honest.Law.Returns
import Johnson.Desc.Kinds.Law.K6WayUp
import Johnson.Desc.Kinds.Law.K06HonestWhole
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn Place KindName Claim noDigest)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds (Head.Par Head.Request Head.Given Head.HeardAll Head.heardOf
  Head.Law.readsOf Reply.token)
open VerifiableInference.Desc.Kinds.Head (parOf given seatAt blockAt requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf WellLaid K6MemberIs zt_of_points
  decide_hears_at setHeard_form putFork?_ok)

/-! ## 1 At the seated sub-protocol's decision -/

/-- Laying a ledger leaves the request as the seat reads it. -/
theorem putFork_request (s : S) (F : Fork) : requestOf (s.putFork F) = requestOf s := by
  unfold VerifiableInference.Desc.First.S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

/-- Laying a ledger leaves the reply. -/
theorem putFork_reply (s : S) (F : Fork) : (s.putFork F).out.reply = s.out.reply := by
  unfold VerifiableInference.Desc.First.S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

/-- **WHERE THE SEATED SUB-PROTOCOL'S DECISION ACCEPTS, THE STATE BEHIND HOLDS heardOf g1 H.** The
letters of all that follows the first conjunct are g's, through the class Given. -/
theorem heard_of_decide (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (g : Head.Given) (H : Head.HeardAll) (F : Fork) (o : HeadOwn)
      (g1 : OnBytes.Model.Forest.Heard),
      given (parOf h work) (seatAt h iU3) s = .ok g ∧
      VerifiableInference.Desc.Kinds.Head.hear ((seatAt h iU3).ledger s) rs = some (H, F, []) ∧
      s'.here = .head o ∧ o.lookHeard = some g1 ∧ o.x = some (Head.heardOf g1 H) := by
  obtain ⟨g, H, F, w, s1, s2, hg, hh, e1, e2, rfl⟩ := decide_hears_at h iU3 work l s s' rs gs hd
  obtain ⟨o, x, _, hx, rfl⟩ := setHeard_form h iU3 e2
  refine ⟨g, H, F, _, x, hg, hh, rfl, hx, ?_⟩
  obtain ⟨z, y, _, hy, _, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  obtain rfl : s1 = s.putFork F := putFork?_ok e1
  have hy' : (s.out.reply).map OnBytes.Desc.Reply.tokOf = some y := hy
  show some (@Head.heardOf (VerifiableInference.Desc.Kinds.Head.sizesOf h)
    (requestOf (s.putFork F))
    ⟨(((s.putFork F).out.reply).map OnBytes.Desc.Reply.tokOf).getD 0⟩ x H) = _
  rw [putFork_request, putFork_reply, hy']
  rfl

/-! ## 2 The readers by round number read a challenge's elements alone -/

section Elems
variable {l l' : List Fmt.Drawn}

theorem elemOf_elems (h : l.map (·.elems) = l'.map (·.elems)) (k : Nat) :
    elemOf l k = elemOf l' k := by
  have e : ∀ x : List Fmt.Drawn, elemOf x k =
      (((x.map (·.elems))[k]?).bind fun e => (e.map E.ofTriple).head?).getD zeroE := by
    intro x
    unfold elemOf elemsOf
    rw [List.getElem?_map]
    cases x[k]? <;> rfl
  rw [e, e, h]

theorem headPV_elems (h : l.map (·.elems) = l'.map (·.elems)) : headPV l = headPV l' := by
  have e : ∀ x : List Fmt.Drawn, headPV x =
      ((((x.map (·.elems)).head?).map fun e => e.map E.ofTriple).getD []).toArray := by
    intro x
    unfold headPV elemsOf
    rw [List.head?_map]
    cases x.head? <;> rfl
  rw [e, e, h]

/-- A round without its sealed digest sampled the same elements. -/
theorem noDigest_elems (rs : List Fmt.RoundView) :
    ((rs.map noDigest).map (·.drawn)).map (·.elems) = (rs.map (·.drawn)).map (·.elems) := by
  simp only [List.map_map]
  rfl

theorem logitsR_elems (p : Head.Par) (base : Nat) (h : l.map (·.elems) = l'.map (·.elems)) :
    headLogitsR p base l = headLogitsR p base l' := by
  unfold headLogitsR
  simp only [elemOf_elems h]

theorem headTHr_elems (p : Head.Par) (base : Nat) (h : l.map (·.elems) = l'.map (·.elems)) :
    headTHr p base l = headTHr p base l' := by
  unfold headTHr headHeardOf
  rw [logitsR_elems p base h]

theorem headRs_elems (p : Head.Par) (base : Nat) (h : l.map (·.elems) = l'.map (·.elems)) :
    headRs p base l = headRs p base l' := by
  unfold headRs headHeardOf
  rw [logitsR_elems p base h]

theorem hearingOf_elems (p : Head.Par) (h : l.map (·.elems) = l'.map (·.elems)) :
    headHearingOf p l = headHearingOf p l' := by
  unfold headHearingOf headGam headOm headSumR
  simp only [elemOf_elems h, headPV_elems h]

theorem heardWhole_elems (p : Head.Par) (q : Head.Request) (y : Nat)
    (g1 : OnBytes.Model.Forest.Heard) (h : l.map (·.elems) = l'.map (·.elems)) :
    headHeardWhole p q y g1 l = headHeardWhole p q y g1 l' := by
  unfold headHeardWhole
  rw [hearingOf_elems p h]

end Elems

/-! ## 3 At the member's accepting step -/

section Member
variable {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
  {b : Block S Claim}

/-- **BEHIND ANY ACCEPTING STEP OF THE MEMBER.** The hearing is at the rounds without the sealed
digest, as the decision is shown them. hk and hsm are idle: heard_at_accept. -/
theorem heard_at_yes (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n)) :
    ∃ (g : Head.Given) (H : Head.HeardAll) (F : Fork) (o : HeadOwn)
      (g1 : OnBytes.Model.Forest.Heard),
      given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s = .ok g ∧
      VerifiableInference.Desc.Kinds.Head.hear ((seatAt W.hS (Head.Law.readsOf W)).ledger s)
        (rs.map noDigest) = some (H, F, []) ∧
      s'.here = .head o ∧ o.lookHeard = some g1 ∧ o.x = some (Head.heardOf g1 H) := by
  obtain ⟨_, hd, _⟩ := (VerifiableInference.Desc.step_iff ft b s s' rs cols n).1 hst
  exact heard_of_decide W.hS (Head.Law.readsOf W) (workOf W) l s s' _ _
    ((M.decide_iff hk hsm s s' _ _).1 hd).1

/-- **tH.r, rs AND win AT THE STATE BEHIND THE MEMBER'S ACCEPTING STEP.** THE TOKEN y AND THE
REQUEST ARE READ IN FRONT (s), THE FIELD x BEHIND (s'). front, later: any two lists; meant: the
challenges heard before the sub-protocol began, and any behind its own. hk and hsm are idle:
logits_at_accept. -/
theorem logits_at_yes (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n))
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s)) (front later : List Fmt.Drawn) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard) (y : Nat),
      s'.here = .head o ∧ o.x = some x ∧
      Reply.token (seatAt W.hS (Head.Law.readsOf W)).toSeat s = some y ∧
      x.tH.r = headTHr (parOf W.hS (workOf W)) front.length
        (front ++ ((rs.map (·.drawn)) ++ later)) ∧
      x.rs = headRs (parOf W.hS (workOf W)) front.length (front ++ ((rs.map (·.drawn)) ++ later)) ∧
      x.win = headWin (parOf W.hS (workOf W)) (requestOf s) y := by
  obtain ⟨g, H, F, o, g1, hg, hh, ho, _, hx⟩ := heard_at_yes M hk hsm hst
  obtain ⟨z, y, _, hy, hP, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := (parOf W.hS (workOf W)).sizes
  letI : VerifiableInference.Desc.Kinds.Head.Policy := (parOf W.hS (workOf W)).policy
  letI : Head.Request := (seatAt W.hS (Head.Law.readsOf W)).request s
  letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  letI : VerifiableInference.Desc.Kinds.FinalNorm.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
  letI : VerifiableInference.Desc.Kinds.Head.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
  obtain ⟨t1, t2, t3⟩ := logits_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh
    (@zt_of_points (parOf W.hS (workOf W)).sizes _ _ _ hP) front later
  have e : (front ++ (((rs.map noDigest).map (·.drawn)) ++ later)).map (·.elems) =
      (front ++ ((rs.map (·.drawn)) ++ later)).map (·.elems) := by
    simp only [List.map_append, noDigest_elems]
  exact ⟨o, _, y, ho, hx, hy, t1.trans (headTHr_elems _ _ e), t2.trans (headRs_elems _ _ e),
    t3⟩

/-- **THE FIVE CHALLENGE FIELDS THAT THE MAKER OF THE HEAD'S TABLES READS, AND ITS ANSWER, AT THE
STATE BEHIND THE MEMBER'S ACCEPTING STEP.** The token y and the request are read in front (s); the
fields x and lookHeard behind (s'). hk and hsm are idle: tables_at_accept. -/
theorem tables_at_yes (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n))
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s)) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard) (g1 : OnBytes.Model.Forest.Heard) (y : Nat),
      s'.here = .head o ∧ o.x = some x ∧ o.lookHeard = some g1 ∧
      Reply.token (seatAt W.hS (Head.Law.readsOf W)).toSeat s = some y ∧
      x.PV = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).PV ∧
      x.wpl.r =
        (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).wpl.r ∧
      x.tV.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tV.r ∧
      x.tN.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tN.r ∧
      x.tH.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tH.r ∧
      ∀ (hS : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
        (hpl : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered),
        VerifiableInference.Desc.K8.ReadsQuiet.tables hS L hpl cov x =
          VerifiableInference.Desc.K8.ReadsQuiet.tables hS L hpl cov
            (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))) := by
  obtain ⟨g, H, F, o, g1, hg, hh, ho, hl, hx⟩ := heard_at_yes M hk hsm hst
  obtain ⟨z, y, _, hy, hP, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := (parOf W.hS (workOf W)).sizes
  letI : VerifiableInference.Desc.Kinds.Head.Policy := (parOf W.hS (workOf W)).policy
  letI : Head.Request := (seatAt W.hS (Head.Law.readsOf W)).request s
  letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  letI : VerifiableInference.Desc.Kinds.FinalNorm.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
  letI : VerifiableInference.Desc.Kinds.Head.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
  have hzt := @zt_of_points (parOf W.hS (workOf W)).sizes _ _ _ hP
  obtain ⟨_, _, _, b3, _, b5, _, _, b8, b9, b10, _, _, _⟩ :=
    heardOf_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh hzt
  refine ⟨o, _, g1, y, ho, hx, hl, hy, ?_⟩
  rw [← heardWhole_elems (parOf W.hS (workOf W)) (requestOf s) y g1 (noDigest_elems rs)]
  exact ⟨b3, b5, b8, b9, b10, fun hS L hpl cov =>
    tables_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh hzt hS L hpl cov⟩

/-! ## 4 The same from the member's form alone; and all fourteen fields -/

/-- **BEHIND ANY ACCEPTING STEP OF THE MEMBER**, at every place and every guard: heard_at_yes
without its two idle premises. -/
theorem heard_at_accept (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n)) :
    ∃ (g : Head.Given) (H : Head.HeardAll) (F : Fork) (o : HeadOwn)
      (g1 : OnBytes.Model.Forest.Heard),
      given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s = .ok g ∧
      VerifiableInference.Desc.Kinds.Head.hear ((seatAt W.hS (Head.Law.readsOf W)).ledger s)
        (rs.map noDigest) = some (H, F, []) ∧
      s'.here = .head o ∧ o.lookHeard = some g1 ∧ o.x = some (Head.heardOf g1 H) := by
  obtain ⟨_, hd, _⟩ := (VerifiableInference.Desc.step_iff ft b s s' rs cols n).1 hst
  exact heard_of_decide W.hS (Head.Law.readsOf W) (workOf W) l s s' _ _
    (M.decide_down hd).1

/-- **tH.r, rs AND win AT THE STATE BEHIND THE MEMBER'S ACCEPTING STEP**: logits_at_yes without its
two idle premises. front, later: any two lists. -/
theorem logits_at_accept (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n))
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s)) (front later : List Fmt.Drawn) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard) (y : Nat),
      s'.here = .head o ∧ o.x = some x ∧
      Reply.token (seatAt W.hS (Head.Law.readsOf W)).toSeat s = some y ∧
      x.tH.r = headTHr (parOf W.hS (workOf W)) front.length
        (front ++ ((rs.map (·.drawn)) ++ later)) ∧
      x.rs = headRs (parOf W.hS (workOf W)) front.length (front ++ ((rs.map (·.drawn)) ++ later)) ∧
      x.win = headWin (parOf W.hS (workOf W)) (requestOf s) y := by
  obtain ⟨g, H, F, o, g1, hg, hh, ho, _, hx⟩ := heard_at_accept M hst
  obtain ⟨z, y, _, hy, hP, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := (parOf W.hS (workOf W)).sizes
  letI : VerifiableInference.Desc.Kinds.Head.Policy := (parOf W.hS (workOf W)).policy
  letI : Head.Request := (seatAt W.hS (Head.Law.readsOf W)).request s
  letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  letI : VerifiableInference.Desc.Kinds.FinalNorm.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
  letI : VerifiableInference.Desc.Kinds.Head.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
  obtain ⟨t1, t2, t3⟩ := logits_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh
    (@zt_of_points (parOf W.hS (workOf W)).sizes _ _ _ hP) front later
  have e : (front ++ (((rs.map noDigest).map (·.drawn)) ++ later)).map (·.elems) =
      (front ++ ((rs.map (·.drawn)) ++ later)).map (·.elems) := by
    simp only [List.map_append, noDigest_elems]
  exact ⟨o, _, y, ho, hx, hy, t1.trans (headTHr_elems _ _ e), t2.trans (headRs_elems _ _ e),
    t3⟩

/-- **THE FIVE CHALLENGE FIELDS THAT THE MAKER OF THE HEAD'S TABLES READS, AND ITS ANSWER**:
tables_at_yes without its two idle premises. -/
theorem tables_at_accept (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n))
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s)) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard) (g1 : OnBytes.Model.Forest.Heard) (y : Nat),
      s'.here = .head o ∧ o.x = some x ∧ o.lookHeard = some g1 ∧
      Reply.token (seatAt W.hS (Head.Law.readsOf W)).toSeat s = some y ∧
      x.PV = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).PV ∧
      x.wpl.r =
        (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).wpl.r ∧
      x.tV.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tV.r ∧
      x.tN.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tN.r ∧
      x.tH.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tH.r ∧
      ∀ (hS : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
        (hpl : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered),
        VerifiableInference.Desc.K8.ReadsQuiet.tables hS L hpl cov x =
          VerifiableInference.Desc.K8.ReadsQuiet.tables hS L hpl cov
            (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))) := by
  obtain ⟨g, H, F, o, g1, hg, hh, ho, hl, hx⟩ := heard_at_accept M hst
  obtain ⟨z, y, _, hy, hP, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := (parOf W.hS (workOf W)).sizes
  letI : VerifiableInference.Desc.Kinds.Head.Policy := (parOf W.hS (workOf W)).policy
  letI : Head.Request := (seatAt W.hS (Head.Law.readsOf W)).request s
  letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  letI : VerifiableInference.Desc.Kinds.FinalNorm.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
  letI : VerifiableInference.Desc.Kinds.Head.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
  have hzt := @zt_of_points (parOf W.hS (workOf W)).sizes _ _ _ hP
  obtain ⟨_, _, _, b3, _, b5, _, _, b8, b9, b10, _, _, _⟩ :=
    heardOf_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh hzt
  refine ⟨o, _, g1, y, ho, hx, hl, hy, ?_⟩
  rw [← heardWhole_elems (parOf W.hS (workOf W)) (requestOf s) y g1 (noDigest_elems rs)]
  exact ⟨b3, b5, b8, b9, b10, fun hS L hpl cov =>
    tables_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh hzt hS L hpl cov⟩

/-- **ALL FOURTEEN FIELDS OF heardOf_tie AT THE STATE BEHIND THE MEMBER'S ACCEPTING STEP.** The
token y and the request are read in front (s); the fields x and lookHeard behind (s'). CONDITIONAL:
the member's form; that its step accepts; a well-laid ledger in front. -/
theorem heardOf_at_accept (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hst : b.step ft s rs cols = .ok (s', n))
    (hW : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s)) :
    ∃ (o : HeadOwn) (x : OnBytes.Model.Head.Heard) (g1 : OnBytes.Model.Forest.Heard) (y : Nat),
      s'.here = .head o ∧ o.x = some x ∧ o.lookHeard = some g1 ∧
      Reply.token (seatAt W.hS (Head.Law.readsOf W)).toSeat s = some y ∧
      x.win = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).win ∧
      x.g1 = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).g1 ∧
      x.Zl = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).Zl ∧
      x.PV = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).PV ∧
      x.gp = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).gp ∧
      x.wpl.r =
        (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).wpl.r ∧
      x.wpl.tau =
        (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).wpl.tau ∧
      x.omV = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).omV ∧
      x.tV.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tV.r ∧
      x.tN.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tN.r ∧
      x.tH.r = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).tH.r ∧
      x.rs = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).rs ∧
      x.qN = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).qN ∧
      x.qH = (headHeardWhole (parOf W.hS (workOf W)) (requestOf s) y g1 (rs.map (·.drawn))).qH := by
  obtain ⟨g, H, F, o, g1, hg, hh, ho, hl, hx⟩ := heard_at_accept M hst
  obtain ⟨z, y, _, hy, hP, rfl⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s g hg
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := (parOf W.hS (workOf W)).sizes
  letI : VerifiableInference.Desc.Kinds.Head.Policy := (parOf W.hS (workOf W)).policy
  letI : Head.Request := (seatAt W.hS (Head.Law.readsOf W)).request s
  letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  letI : VerifiableInference.Desc.Kinds.FinalNorm.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
  letI : VerifiableInference.Desc.Kinds.Head.In :=
    (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
  have hzt := @zt_of_points (parOf W.hS (workOf W)).sizes _ _ _ hP
  refine ⟨o, _, g1, y, ho, hx, hl, hy, ?_⟩
  rw [← heardWhole_elems (parOf W.hS (workOf W)) (requestOf s) y g1 (noDigest_elems rs)]
  exact heardOf_tie (parOf W.hS (workOf W)) y rfl rfl g1 hW hh hzt

end Member

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.putFork_request
#print axioms ProofFile.Honest.K6.putFork_reply
#print axioms ProofFile.Honest.K6.heard_of_decide
#print axioms ProofFile.Honest.K6.elemOf_elems
#print axioms ProofFile.Honest.K6.headPV_elems
#print axioms ProofFile.Honest.K6.noDigest_elems
#print axioms ProofFile.Honest.K6.logitsR_elems
#print axioms ProofFile.Honest.K6.headTHr_elems
#print axioms ProofFile.Honest.K6.headRs_elems
#print axioms ProofFile.Honest.K6.hearingOf_elems
#print axioms ProofFile.Honest.K6.heardWhole_elems
#print axioms ProofFile.Honest.K6.heard_at_yes
#print axioms ProofFile.Honest.K6.logits_at_yes
#print axioms ProofFile.Honest.K6.tables_at_yes
#print axioms ProofFile.Honest.K6.heard_at_accept
#print axioms ProofFile.Honest.K6.logits_at_accept
#print axioms ProofFile.Honest.K6.tables_at_accept
#print axioms ProofFile.Honest.K6.heardOf_at_accept
