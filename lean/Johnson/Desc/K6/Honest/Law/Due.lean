-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Due.lean: WHAT THE OUTPUT HEAD's LAW ASKS OF THE VERIFIER's STATE BEHIND
ITS OWN SUB-PROTOCOL (`RecordDue`, Johnson/Desc/Kinds/Law/K6OpenedCut.lean: twelve clauses) STANDS
BEHIND AN ACCEPTANCE OF THE MEMBER AS IT IS SEATED IN THE IOP AS WRITTEN IN LEAN, FROM FACTS ON THE
STATE IN FRONT AND ON PUBLIC DATA. CONDITIONAL. Two structures of premises, and statements with
their proofs. Over the library and four files on the member (Law/K6WayUp.lean,
Honest/Law/Keeps.lean, Honest/Law/KeepsBare.lean, Honest/Law/KeepsMember.lean); no prover's text, no
frame of the honest side and no table's promise is read here.

Why. The library has the twelve behind an accept of a PIECE of the reduction (`recordDue_at_piece`,
Law/K6RecordAt.lean; `recordRest_behind`, Law/K6RestAt.lean), and takes the facts in front off the
table's promise at the composed meaning. Whoever has a yes of the sub-protocol's own decision or
step, and the promise at another meaning, cannot call these. None of the twelve holds a value of the
witness: they are facts on the state and on public data.

  `K6DueFront`      NINE FACTS ON THE STATE IN FRONT, as one structure
  `K6DuePub`        five facts on public data and letters, as another
  `stateIsPlan_keeps`   behind a yes every reader of the open segment's part is a term off the
                    public parameters
  `recordRest_keeps`   six of the twelve clauses, and what the third is made of (`RecordRest`),
                    behind a yes
  `due_of_front`    **all twelve behind a yes of the member's decision**
  `due_of_step`     **and behind a yes of its step**
  `due_of_front'`, `due_of_step'`   the same two without the premises hk and hsm, which the two
                    above ask and the end does not hang on

What it is not. IMPLICATIONS. THAT A STATE OF A RUN MEETS `K6DueFront`, OR PUBLIC DATA `K6DuePub`,
IS SHOWN HERE OF NONE; no member of either is laid. THE YES IS THE STRICT ONE: of the member behind
the test "every word that is shown is below the prime" (`Sound.below`,
Johnson/Desc/Sound/ChainRule.lean): one of the twelve (what was heard is a hearing's) wants rounds
in canonical writing. The numbers are fixed: segment 24, piece 4, the mask row's message num 24 0,
whose mask rows are numbered by 0 bits: one row, the reads' public part `p8K6 Wp 24`, the readers of
the link Lk with the silent reader in the hole. Nothing on what was heard beyond the twelve. WHO
MIGHT PAY THE NINE: left, sentIs, fresh, book, lookLeft, wide and ns are the content, at the state,
of items and clauses of the table's promise in front of the sub-protocol (tokenSmall, ledger and
look; frame.sentIs; linkFresh; the book; left; ledger.treesAre, with two facts on public data;
freeAbove); fold and noTables are facts on every reached state. HOW IT GOES. `stateIsPlan_keeps` and
`recordRest_keeps` follow the proofs of `stateIsPlan_behind` and `recordRest_behind`
(Law/K6RestAt.lean) line by line: where these open the piece's accept ("the state behind is the
state in front with three fields of the head's own part laid anew") `K6Keeps` stands
(Honest/Law/Keeps.lean), and where they take an item off the promise its content is a premise.
`due_of_front` follows `recordDue_at_piece`. Called: `four_behind` (Law/HeadRidesSays.lean),
`k6On_of_start` (Law/K6OrdLeft.lean), `K6MemberIs.decide_iff`, `K6MemberIs.decide_down`,
`K6MemberIs.bare` (Law/K6WayUp.lean),
`k6_keeps_of_member` (Honest/Law/KeepsMember.lean), `K6Keeps.own`, `.here`, `.kept`, `segAt_parts`,
`link_of_seg` (Law/K6RestAt.lean), `reads_of_C`, `matsSeated_of_C`, `maskSeated_of_C`
(Law/K6SeatsTest.lean), `statedAt_of_is` (Law/K6AtMgAll.lean), `leftAt_cEnd`
(Johnson/Desc/First/Look/K3KeepsFree.lean), `dataSeated_of_laid` (Law/DataSeatedOfLaid.lean),
`wellLaid_later` (Law/RowPromise.lean), `alone_planOk` (Johnson/IMR/SeatForm.lean), `step_decide`
(Law/RowPins.lean). OF THE FOLDER
lean/Johnson/Goal/ two definitions are named, in `K6DuePub`'s fields laid and named:
`Meaning.laidThere` (Johnson/Goal/Meaning/HidSeatsOf.lean) and `Meaning.sizesOf`
(Johnson/Goal/Meaning/HidPlan.lean); no file of that folder is imported by this one, and nothing
else of it is called.
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.K6RestAt
import Johnson.Desc.Kinds.Law.K6RecordAt
import Johnson.Desc.Kinds.Law.K6OrdLeft
import Johnson.Desc.Kinds.Law.K6WayUp
import Johnson.Desc.K6.Honest.Law.KeepsMember

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block Claim OpenedColumn Place Link noDigest)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.FillSent (SentData)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps)

variable (arr : Nat → Nat → Nat) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
  (lay6 : ReqLayout) (num : Nat → Nat → Nat) (cs : OnBytes.Codes) (shape : ReqShape)
  (dS : SentData) (Lp : K12.Door.Laid) (M : List OracleShape) (arrs : Array (Nat × String))
  (pl : Option Place)

/-- **NINE FACTS ON THE STATE IN FRONT.** left: what is left of the law's condition in front
(`K6On`) when the plan's tests and the test on the request are taken away. noTables: no tables are
laid yet. wide: the array of the reads is as wide as the plan says. fold: five facts on every
reached state. sentIs, fresh, book: the open segment's frame, its list of arrays, and the book's and
the statement's sizes are the public terms. lookLeft: what the lookup on the calls left. ns: the
ledger has at most the plan's number of slots. -/
structure K6DueFront (s : S) : Prop where
  left : K6Left Wp s
  noTables : noTablesB s = true
  wide : readsWideB (readsOf Wp) ((p8K6 Wp 24).hp.nU.getD 2 0) s = true
  fold : FoldAt Lp M cs shape lay6 s
  sentIs : First.FillSent.sentIsB dS 24 s = true
  fresh : VerifiableInference.OnPublicFiles.linkFreshB arrs s = true
  book : First.bookAt N pl s = true
  lookLeft : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s
  ns : ∀ F, s.fork? = some F → F.ns ≤ Wp.H.ns

/-- **FIVE FACTS ON PUBLIC DATA AND LETTERS.** states: the link's sub-protocol number 3 states the
kind's four runs. seats, laid: two tests with code. named: every number that a seat of segment 24
names has just one tenant. stated: the stated data's arm at segment 24 is the output head's
(`uHeadK6`). -/
structure K6DuePub (St : Sound.Stated) (Lk : Link S Claim) : Prop where
  states : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 4 (K9.statesOfLink Lk) 3
  seats : seatsK6C arr N Wp lay6 num (num 24 0) 0 cs shape dS Lp M arrs (N.msgsAt pl) = true
  laid : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true
  named : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
    r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
    ColFour Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y) μ.val c →
    Sound.namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true
  stated : ∀ t : S, (∃ o, t.here = .head o) → Sound.linkNo t = 24 →
    Sound.StatedIs St (uHeadK6 Wp 24) t

variable {arr N Wp lay6 num cs shape dS Lp M arrs pl}

/-- **BEHIND A YES EVERY READER IS A TERM OFF THE PUBLIC PARAMETERS.** The part behind holds the
ledger behind; the state in front has a ledger; behind, the chain stands in the head's link. -/
theorem stateIsPlan_keeps {s s' : S} (K : K6Keeps s s') (F : FoldAt Lp M cs shape lay6 s)
    (hS : First.FillSent.sentIsB dS 24 s = true)
    (hfr : VerifiableInference.OnPublicFiles.linkFreshB arrs s = true)
    (hbo : First.bookAt N pl s = true) :
    ∃ aK, StateIsPlan lay6 cs shape dS Lp M arrs (N.msgsAt pl) s' aK ∧ s'.fork? = some aK.F ∧
      (∃ F0, s.fork? = some F0) ∧ ∃ o : First.HeadOwn, s'.here = .head o := by
  obtain ⟨o, o', ho, ho', eo⟩ := K.own
  have hs := K.here
  have hop : o.opened = true := by
    obtain ⟨_, _, o1, _, h1, _, hop, _⟩ := K
    rw [ho] at h1
    cases h1
    exact hop
  have e2 : s' =
      { s with here := .head { o with F := o'.F, x := o'.x, squaresP := o'.squaresP } } := by
    rw [← eo, ← ho']
    exact hs
  have hLa : s.link? = some o.L := by
    unfold First.S.link?
    rw [ho]
    show (if o.opened = true then some o.L else none) = _
    rw [if_pos hop]
  have hFa : s.fork? = some o.F := by
    unfold First.S.fork?
    rw [ho]
    show (if o.opened = true then some o.F else none) = _
    rw [if_pos hop]
  have hLb : s'.link? = some o.L := by
    rw [e2]
    show (if o.opened = true then some o.L else none) = _
    rw [if_pos hop]
  have hFb : s'.fork? = some o'.F := by
    rw [e2]
    show (if o.opened = true then some o'.F else none) = _
    rw [if_pos hop]
  have hTb : s'.tl? = some o.tl := by
    rw [e2]
    show (if o.opened = true then some o.tl else none) = _
    rw [if_pos hop]
  have hst : s'.st = s.st := by rw [e2]
  have hbk : s'.book = s.book := by rw [e2]
  have hlive : s.live = o.L.check := by
    unfold First.S.live
    rw [hLa]
  obtain ⟨aK, k1, k2, k3, k4⟩ := segAt_parts s' o.L o'.F o.tl hLb hFb hTb
  have hF : aK.F = o'.F := by
    have k1' := k1
    unfold K9.segAt? at k1'
    rw [hLb, hFb, hTb] at k1'
    rw [← Option.some.inj k1']
  unfold VerifiableInference.OnPublicFiles.linkFreshB at hfr
  rw [Bool.and_eq_true, hLa] at hfr
  have harr : o.L.arrayOf = arrs := eq_of_beq hfr.2
  unfold First.bookAt at hbo
  simp only [Bool.and_eq_true, beq_iff_eq] at hbo
  refine ⟨aK, ⟨k1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hF]; exact hFb, ⟨_, hFa⟩, _, ho'⟩
  · intro born message
    rw [k2]
    exact First.FillSent.whereIs_of_sentIs hLa hS born message
  · rw [k2]
    exact First.FillSent.link_of_sentIs hLa hS
  · rw [k2, ← hlive]
    exact F.shape
  · rw [k2, ← hlive]
    exact F.layout
  · rw [k2]
    exact harr
  · rw [k3, hst]
    exact F.codes
  · rw [k3, hst]
    exact F.msgs
  · rw [k4, hbk]
    exact F.seats
  · rw [k4, hbk, hbo.1.2, hbo.2]
  · rw [k3, hst, hbo.2]

/-- **SIX OF THE TWELVE, AND WHAT THE THIRD IS MADE OF, BEHIND A YES.** -/
theorem recordRest_keeps {s s' : S} (K : K6Keeps s s') (F : FoldAt Lp M cs shape lay6 s)
    (hS : First.FillSent.sentIsB dS 24 s = true)
    (hfr : VerifiableInference.OnPublicFiles.linkFreshB arrs s = true)
    (hbo : First.bookAt N pl s = true)
    (hC : seatsK6C arr N Wp lay6 num (num 24 0) 0 cs shape dS Lp M arrs (N.msgsAt pl) = true)
    (St : Sound.Stated)
    (hSt : ∀ t : S, (∃ o, t.here = .head o) → Sound.linkNo t = 24 →
      Sound.StatedIs St (uHeadK6 Wp 24) t)
    (hL : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s) :
    ∃ aK' cU, RecordRest arr N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) St s' aK' cU ∧
      s'.fork? = some aK'.F ∧ ∃ F0, s.fork? = some F0 := by
  obtain ⟨aK, I, hF, hF0, o', ho'⟩ := stateIsPlan_keeps K F hS hfr hbo
  obtain ⟨cU, c1, c2⟩ := reads_of_C hC I
  refine ⟨aK, cU, ⟨I.seg, I.layout, matsSeated_of_C hC I _ ?_, maskSeated_of_C hC I, c1, ?_, ?_⟩,
    hF, hF0⟩
  · intro x c hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · have hno : Sound.linkNo s' = 24 := by
      unfold Sound.linkNo
      rw [link_of_seg I.seg]
      exact I.link
    exact AtTable.statedAt_of_is Wp 24 St s' cU (hSt s' ⟨o', ho'⟩ hno) c2
  · intro gk hg
    obtain ⟨p, _, ⟨h, _, L⟩, _⟩ := hL
    obtain ⟨_, g, _, hg', he, _⟩ := VerifiableInference.OnPublicFiles.leftAt_cEnd _ _ _ _ _ _ _ L
    rw [(K.kept Wp).2.2.2] at hg
    obtain rfl : g = gk := Option.some.inj (hg'.symm.trans hg)
    exact he

/-- **ALL TWELVE BEHIND A YES OF THE MEMBER's DECISION.** hd: the strict yes. hk, hsm: as
`K6MemberIs.decide_iff` asks; `due_of_front'` has the same end without them. hp: the member passes
its test on the plan. -/
theorem due_of_front {same : S → S → Bool} {a : Place} {blk : Block S Claim}
    (Mb : K6MemberIs Wp 24 same a blk) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (hp : blk.planOk = true)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (Sound.below blk).decide s rs gs = .ok s')
    (A : K6DueFront N Wp lay6 cs shape dS Lp M arrs pl s) (St : Sound.Stated) (Lk : Link S Claim)
    (B : K6DuePub arr N Wp lay6 num cs shape dS Lp M arrs pl St Lk)
    (small : S → Option K9.Read) :
    ∃ aK' cU, RecordDue arr N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) St (K9.statesOfLink Lk)
      (K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk) s' aK' cU := by
  have hv : (if VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
      then blk.decide s rs gs else .error "a word is not below the prime") = .ok s' := hd
  split at hv
  · rename_i hok
    obtain ⟨hbare, hstart⟩ := (Mb.decide_iff hk hsm s s' rs gs).1 hv
    have K : K6Keeps s s' := Honest.k6_keeps_of_member Mb hv
    have hOn : K6On Wp s := by
      obtain ⟨ms, bS, name, hS, hla⟩ := Mb
      exact k6On_of_start hS ((IM.alone_planOk hla).symm.trans hp) hstart A.left
    have hbel :
        (Sound.below (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24)).decide s rs gs = .ok s' := by
      show (if VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
        then (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24).decide s rs gs
        else .error "a word is not below the prime") = .ok s'
      rw [if_pos hok]
      exact hbare
    obtain ⟨f1, f2, f3, f4⟩ := four_behind Wp 24 _ Mb.bare s s' rs gs hbel hOn (p8K6 Wp 24)
      A.noTables A.wide 24 4 3 Lk B.states small
    obtain ⟨aK, cU, ⟨r1, r2, r3, r4, r6, r7, r8⟩, hF, F0, hF0⟩ := recordRest_keeps K A.fold A.sentIs
      A.fresh A.book B.seats St B.stated A.lookLeft
    have hKk := K.kept Wp
    have e0 : (seatAt Wp.hS (readsOf Wp)).ledger s = F0 := by
      show s.fork?.getD {} = F0
      rw [hF0]
      rfl
    have e1 : (seatAt Wp.hS (readsOf Wp)).ledger s' = aK.F := by
      show s'.fork?.getD {} = aK.F
      rw [hF]
      rfl
    have hW' := Came.wellLaid_later A.left.1 hKk.1
    have hLn := hKk.1.ns
    rw [e1] at hW' hLn
    rw [e0] at hLn
    have hmf : aK.F.mf.size ≤ Wp.H.ns := by
      have h1 := hW'.2.2
      have h2 := A.ns F0 hF0
      omega
    exact ⟨aK, cU, r1, r2,
      dataSeated_of_laid arr N Wp (N.sent 24 0) aK num lay6 B.laid r2 B.named r3, r4, hmf, f1, f2,
      r6, r7, f3, f4, r8⟩
  · cases hv

/-- **AND BEHIND A YES OF ITS STEP.** -/
theorem due_of_step {same : S → S → Bool} {a : Place} {blk : Block S Claim}
    (Mb : K6MemberIs Wp 24 same a blk) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (hp : blk.planOk = true)
    {ft n : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hstep : (Sound.below blk).step ft s rs cols = .ok (s', n))
    (A : K6DueFront N Wp lay6 cs shape dS Lp M arrs pl s) (St : Sound.Stated) (Lk : Link S Claim)
    (B : K6DuePub arr N Wp lay6 num cs shape dS Lp M arrs pl St Lk)
    (small : S → Option K9.Read) :
    ∃ aK' cU, RecordDue arr N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) St (K9.statesOfLink Lk)
      (K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk) s' aK' cU := by
  obtain ⟨gs, hd⟩ := Came.step_decide ft (Sound.below blk) s rs cols s' n hstep
  exact due_of_front Mb hk hsm hp hd A St Lk B small

/-- **ALL TWELVE BEHIND AN ACCEPTANCE OF THE MEMBER's DECISION, WITHOUT hk AND hsm.**
`due_of_front`'s proof, line by line, but for one: the way down from the member's acceptance to the
bare sub-protocol's is `K6MemberIs.decide_down`, which asks neither. -/
theorem due_of_front' {same : S → S → Bool} {a : Place} {blk : Block S Claim}
    (Mb : K6MemberIs Wp 24 same a blk) (hp : blk.planOk = true)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (Sound.below blk).decide s rs gs = .ok s')
    (A : K6DueFront N Wp lay6 cs shape dS Lp M arrs pl s) (St : Sound.Stated) (Lk : Link S Claim)
    (B : K6DuePub arr N Wp lay6 num cs shape dS Lp M arrs pl St Lk)
    (small : S → Option K9.Read) :
    ∃ aK' cU, RecordDue arr N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) St (K9.statesOfLink Lk)
      (K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk) s' aK' cU := by
  have hv : (if VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
      then blk.decide s rs gs else .error "a word is not below the prime") = .ok s' := hd
  split at hv
  · rename_i hok
    obtain ⟨hbare, hstart⟩ := Mb.decide_down hv
    have K : K6Keeps s s' := Honest.k6_keeps_of_member Mb hv
    have hOn : K6On Wp s := by
      obtain ⟨ms, bS, name, hS, hla⟩ := Mb
      exact k6On_of_start hS ((IM.alone_planOk hla).symm.trans hp) hstart A.left
    have hbel :
        (Sound.below (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24)).decide s rs gs = .ok s' := by
      show (if VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
        then (blockAt Wp.hS (readsOf Wp) (workOf Wp) 24).decide s rs gs
        else .error "a word is not below the prime") = .ok s'
      rw [if_pos hok]
      exact hbare
    obtain ⟨f1, f2, f3, f4⟩ := four_behind Wp 24 _ Mb.bare s s' rs gs hbel hOn (p8K6 Wp 24)
      A.noTables A.wide 24 4 3 Lk B.states small
    obtain ⟨aK, cU, ⟨r1, r2, r3, r4, r6, r7, r8⟩, hF, F0, hF0⟩ := recordRest_keeps K A.fold A.sentIs
      A.fresh A.book B.seats St B.stated A.lookLeft
    have hKk := K.kept Wp
    have e0 : (seatAt Wp.hS (readsOf Wp)).ledger s = F0 := by
      show s.fork?.getD {} = F0
      rw [hF0]
      rfl
    have e1 : (seatAt Wp.hS (readsOf Wp)).ledger s' = aK.F := by
      show s'.fork?.getD {} = aK.F
      rw [hF]
      rfl
    have hW' := Came.wellLaid_later A.left.1 hKk.1
    have hLn := hKk.1.ns
    rw [e1] at hW' hLn
    rw [e0] at hLn
    have hmf : aK.F.mf.size ≤ Wp.H.ns := by
      have h1 := hW'.2.2
      have h2 := A.ns F0 hF0
      omega
    exact ⟨aK, cU, r1, r2,
      dataSeated_of_laid arr N Wp (N.sent 24 0) aK num lay6 B.laid r2 B.named r3, r4, hmf, f1, f2,
      r6, r7, f3, f4, r8⟩
  · cases hv

/-- **AND BEHIND AN ACCEPTANCE OF ITS STEP, WITHOUT hk AND hsm.** -/
theorem due_of_step' {same : S → S → Bool} {a : Place} {blk : Block S Claim}
    (Mb : K6MemberIs Wp 24 same a blk) (hp : blk.planOk = true)
    {ft n : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hstep : (Sound.below blk).step ft s rs cols = .ok (s', n))
    (A : K6DueFront N Wp lay6 cs shape dS Lp M arrs pl s) (St : Sound.Stated) (Lk : Link S Claim)
    (B : K6DuePub arr N Wp lay6 num cs shape dS Lp M arrs pl St Lk)
    (small : S → Option K9.Read) :
    ∃ aK' cU, RecordDue arr N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) St (K9.statesOfLink Lk)
      (K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk) s' aK' cU := by
  obtain ⟨gs, hd⟩ := Came.step_decide ft (Sound.below blk) s rs cols s' n hstep
  exact due_of_front' Mb hp hd A St Lk B small

#print axioms stateIsPlan_keeps
#print axioms recordRest_keeps
#print axioms due_of_front
#print axioms due_of_step
#print axioms due_of_front'
#print axioms due_of_step'

end VerifiableInference.Desc.Kinds.Head.Law.AtFold
