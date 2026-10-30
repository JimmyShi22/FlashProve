-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6WayUp.lean.
WHAT IT IS NOT. No accept is shown here: every statement carries an accept from one sub-protocol to
another. That the IOP as written in Lean seats the member in the form K6MemberIs is a premise here
(paid at its own first chain in Law/K6WayUpAtSeat.lean). Nothing on soundness, on completeness or on
hiding.
WHAT IT IS. THE WAY UP, AND DOWN, BETWEEN THE OUTPUT HEAD's BARE SUB-PROTOCOL (K6; blockOf W l,
Stored/HeadSeatAt.lean: the one of which the laws of this folder speak) AND THE MEMBER AS THE IOP AS
WRITTEN IN LEAN SEATS IT: the seated constant (seatedClaims W l ms, Stored/HeadAddsAtS.lean) behind
the guard on the mark of failure, under a name, at an address, behind the driver's guard on the
reply (IM.LaidAlone, IMR/SeatForm.lean). It imports library files alone.
THE POINT. The library has the two halves as "if and only if": seated_step_iff (Law/SeatedBack.lean)
and IM.step_alone | IM.yes_alone (IMR/SeatForm.lean). The second asks "no mark behind" and "the
guard accepts". An accept of the bare sub-protocol pays both by itself: it turns "where the chain
stands" and nothing else, and there is no mark in front (Came.decide_record, Law/RowPromise.lean).
SO THE ONE CLAUSE THAT IS LEFT BETWEEN THE TWO ACCEPTS IS THE STATE's OWN TEST ON THE REQUEST,
startOk W s.
  blockOf_at, readsOf_at   where the plan names the array of reads: blockOf's value, and the
                    library's reader of that number.
  decide_leaves     CONDITIONAL on an accept of the bare decision: no mark behind; the part "out",
                    the reply in it, is as in front.
  seated_decide_iff the seated constant's decision accepts just where the bare one does and the
                    test on the request accepts.
  member_decide_iff, member_step_iff   CONDITIONAL on the member's form, on hk and on hsm: the
                    member's decision, and its step, accept just where the bare sub-protocol's does
                    and that test accepts: to the same state, with the same count of columns.
  member_decide_down, member_step_down   THE HALF "DOWN" BY ITSELF: CONDITIONAL on the member's form
                    ALONE: where the member accepts, the bare sub-protocol accepts and that test
                    accepts: at every address and every guard.
  member_decide_iff', member_step_iff'   the two "if and only if" WITHOUT hk: CONDITIONAL on the
                    member's form and on hsm.
  member_rounds, member_want   CONDITIONAL on the member's form: its declared rounds are the bare
                    sub-protocol's; it is owed no column.
  laidAlone_of_term the term of Desc/Sound/K6Tied.lean's seated_of_term, at the driver's own test
                    on places, is of that form. No caller so far.
  K6MemberIs        the premises on the member as one definition; .bare, .decide_iff, .step_iff,
                    .decide_down, .step_down, .decide_iff', .step_iff', .rounds, .want: the same
                    laws at it, at the library's readers readsOf W and workOf W (Law/RowRides.lean).
                    .plan: CONDITIONAL on the member's form: where the member passes its test on the
                    plan, the kind's own test on the plan and the test on the laid numbers accept.
LETTERS. same: the guard's test: a letter, under hsm: it accepts where the reply is as it was (at
ProofFile.sameReply: P4.same_of_eq). a: the address, under hk: not K7's. WHAT HANGS ON THE TWO: hsm IS
SPENT FOR THE HALF "UP" ALONE, and there off K7's address alone; hk IS ASKED BY THE TWO ELDER "IF
AND ONLY IF" (each in two forms: four lemmas) AND IS NOT NEEDED: at K7's address the library has the
twin IM.yes_alone_K7; THE HALF "DOWN" WANTS NEITHER. In K6MemberIs the list ms, the seated constant
bS and the name stand under "there is": bS is pinned by its own equation.
CALLED: seated_step_iff, IM.step_alone, IM.yes_alone, IM.alone_rounds, seatedClaims_some,
tested_decide, seated_claims, seatedClaims_plan, IM.alone_planOk, Came.decide_record,
Came.step_decide, blockAt_rounds, groups_none; for the eight younger laws: IM.alone_underR,
IM.yes_alone_K7, IM.step_iff (IMR/SeatForm.lean), step_under (Desc/Sound/SeatGuardChain.lean).
TYPED ANEW, AND WHY: seated_decide_iff: the library has that pair at the step alone; at the decision
it has seated_across (Desc/Sound/K6Tied.lean), which runs one way and hides the block between.

-/
import Mathlib
import Johnson.IMR.SeatForm
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Desc.Sound.SeatNarrows
import Johnson.Desc.Kinds.Law.SeatedBack
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.SeatedRuns
import Johnson.Desc.Kinds.Law.K06HonestStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block OpenedColumn Place KindName Claim)
open VerifiableInference.Desc.First (S)


/-- Where the plan names the array of reads, blockOf's value is blockAt at the public numbers. -/
theorem blockOf_at {W : OnBytes.Model.Verify.Public} {iU3 : Nat}
    (hi : W.H.tl.ix.U.getD 2 none = some iU3) (l : Nat) :
    blockOf W l = some (blockAt W.hS iU3 (workOf W) l) := by
  unfold blockOf
  rw [hi]
  rfl

/-- The library's reader of that number (Law/RowRides.lean), at the same premise. -/
theorem readsOf_at {W : OnBytes.Model.Verify.Public} {iU3 : Nat}
    (hi : W.H.tl.ix.U.getD 2 none = some iU3) : readsOf W = iU3 := by
  unfold readsOf
  rw [hi]
  rfl

/-- An accept of the bare decision leaves no mark, and leaves the part «out» (the reply in it). -/
theorem decide_leaves {W : OnBytes.Model.Verify.Public} {l : Nat} {bU : Block S Unit}
    (hU : blockOf W l = some bU) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : bU.decide s rs gs = .ok s') :
    s'.failed = none ∧ s'.out = s.out := by
  unfold blockOf at hU
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hU
  obtain ⟨o, F1, X, Q, _, _, hf, rfl⟩ := Came.decide_record _ _ _ _ hd
  exact ⟨hf, rfl⟩

/-- The seated constant's decision against the bare one's. -/
theorem seated_decide_iff {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {bS : Block S Claim} (hS : seatedClaims W l ms = some bS) {bU : Block S Unit}
    (hU : blockOf W l = some bU) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    bS.decide s rs gs = .ok s' ↔ bU.decide s rs gs = .ok s' ∧ startOk W s = true := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some hS
  unfold blockClaims at h0
  obtain ⟨iU3, hi, rfl⟩ := Option.map_eq_some_iff.mp h0
  rw [blockOf_at hi l] at hU
  obtain rfl : blockAt W.hS iU3 (workOf W) l = bU := Option.some.inj hU
  -- the decision does not read the claims' maker: the two sub-protocols' decisions are one term
  exact tested_decide _ _ _ _ s s' rs gs

section Member

variable {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)} {bS : Block S Claim}
  {bU : Block S Unit} {same : S → S → Bool} {b : Block S Claim} {name : String} {a : Place}

/-- THE WAY UP AND DOWN, AT THE DECISION. -/
theorem member_decide_iff (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok s' ↔ bU.decide s rs gs = .ok s' ∧ startOk W s = true := by
  rw [IM.yes_alone hla hk, seated_decide_iff hS hU]
  constructor
  · rintro ⟨h, _, _⟩
    exact h
  · intro h
    obtain ⟨hf, ho⟩ := decide_leaves hU h.1
    exact ⟨h, hf, hsm s s' (congrArg (·.reply) ho)⟩

/-- THE WAY UP AND DOWN, AT THE STEP. -/
theorem member_step_iff (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) :
    b.step ft s rs cols = .ok (s', n) ↔
      bU.step ft s rs cols = .ok (s', n) ∧ startOk W s = true := by
  rw [IM.step_alone hla hk, seated_step_iff hS hU]
  constructor
  · rintro ⟨h, _, _⟩
    exact h
  · intro h
    obtain ⟨gs, hd⟩ := Came.step_decide ft bU s rs cols s' n h.1
    obtain ⟨hf, ho⟩ := decide_leaves hU hd
    exact ⟨h, hf, hsm s s' (congrArg (·.reply) ho)⟩

/-- THE WAY DOWN, AT THE DECISION: at every address and at every guard. CONDITIONAL on the member's
form: where the member's decision accepts, so does the bare sub-protocol's, to the same state, and
the state's own test on the request accepts. -/
theorem member_decide_down (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    bU.decide s rs gs = .ok s' ∧ startOk W s = true :=
  (seated_decide_iff hS hU s s' rs gs).1 ((IM.alone_underR hla).2 s rs gs s' hd)

/-- THE WAY DOWN, AT THE STEP: at every address and at every guard. CONDITIONAL on the member's
form. -/
theorem member_step_down (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {n : Nat} (hs : b.step ft s rs cols = .ok (s', n)) :
    bU.step ft s rs cols = .ok (s', n) ∧ startOk W s = true :=
  (seated_step_iff hS hU ft s s' rs cols n).1
    (VerifiableInference.Desc.step_under (IM.alone_underR hla) hs)

/-- THE WAY UP AND DOWN, AT THE DECISION, AT EVERY ADDRESS: `member_decide_iff` without its premise
on the address. At K7's address the guard on the reply is not asked (IM.yes_alone_K7). -/
theorem member_decide_iff' (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok s' ↔ bU.decide s rs gs = .ok s' ∧ startOk W s = true := by
  by_cases hk : a.kind = KindName.K7
  · rw [IM.yes_alone_K7 hla hk, seated_decide_iff hS hU]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      exact ⟨h, (decide_leaves hU h.1).1⟩
  · exact member_decide_iff hS hU hla hk hsm s s' rs gs

/-- THE WAY UP AND DOWN, AT THE STEP, AT EVERY ADDRESS: `member_step_iff` without its premise on the
address. -/
theorem member_step_iff' (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) :
    b.step ft s rs cols = .ok (s', n) ↔
      bU.step ft s rs cols = .ok (s', n) ∧ startOk W s = true := by
  by_cases hk : a.kind = KindName.K7
  · rw [IM.step_iff (Q := fun _ t => t.failed = none) (IM.alone_rounds hla)
      (fun s rs gs t => IM.yes_alone_K7 hla hk s t rs gs) ft s s' n rs cols,
      seated_step_iff hS hU]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      obtain ⟨gs, hd⟩ := Came.step_decide ft bU s rs cols s' n h.1
      exact ⟨h, (decide_leaves hU hd).1⟩
  · exact member_step_iff hS hU hla hk hsm ft s s' rs cols n

/-- The member's declared rounds are the bare sub-protocol's. -/
theorem member_rounds (hS : seatedClaims W l ms = some bS) (hU : blockOf W l = some bU)
    (hla : IM.LaidAlone same b bS name a) : b.rounds = bU.rounds := by
  rw [IM.alone_rounds hla]
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some hS
  unfold blockClaims at h0
  obtain ⟨iU3, hi, rfl⟩ := Option.map_eq_some_iff.mp h0
  rw [blockOf_at hi l] at hU
  obtain rfl : blockAt W.hS iU3 (workOf W) l = bU := Option.some.inj hU
  rfl

/-- The member is owed no column. -/
theorem member_want (hS : seatedClaims W l ms = some bS)
    (hla : IM.LaidAlone same b bS name a) (ft : Nat) (rs : List Fmt.RoundView) : b.want ft rs = [] := by
  obtain ⟨iU3, hi, _⟩ := seated_claims hS
  unfold Block.want
  rw [member_rounds hS (blockOf_at hi l) hla, blockAt_rounds, groups_none]
  rfl

end Member

/-- The term of Desc/Sound/K6Tied.lean's seated_of_term, at the driver's own test on places, is of
the form of IMR/SeatForm.lean. -/
theorem laidAlone_of_term (same : S → S → Bool) (bS : Block S Claim) (n : String) :
    IM.LaidAlone same
      (Block.guarded same VerifiableInference.Desc.First.hearsReply
        { VerifiableInference.Desc.markGuard bS with name := n }) bS n bS.place := by
  unfold IM.LaidAlone
  rfl

/-! ## The three premises as one -/

/-- **b IS K6's MEMBER AS THE IOP AS WRITTEN IN LEAN SEATS IT**: the seated constant at some list
«before», alone, under some name at the address a, behind the mark's guard and the guard same. A
definition: a premise's form. Nothing is claimed of it. -/
def K6MemberIs (W : OnBytes.Model.Verify.Public) (l : Nat) (same : S → S → Bool) (a : Place)
    (b : Block S Claim) : Prop :=
  ∃ (ms : List (Nat × Nat)) (bS : Block S Claim) (name : String),
    seatedClaims W l ms = some bS ∧ IM.LaidAlone same b bS name a

section One

variable {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
  {b : Block S Claim}

/-- Where the member is there, so is the bare sub-protocol, at the library's two readers. -/
theorem K6MemberIs.bare (M : K6MemberIs W l same a b) :
    blockOf W l = some (blockAt W.hS (readsOf W) (workOf W) l) := by
  obtain ⟨ms, bS, name, hS, _⟩ := M
  obtain ⟨iU3, hi, _⟩ := seated_claims hS
  rw [readsOf_at hi]
  exact blockOf_at hi l

theorem K6MemberIs.decide_iff (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok s' ↔
      (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s' ∧ startOk W s = true := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_decide_iff hS hU hla hk hsm s s' rs gs

theorem K6MemberIs.step_iff (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) :
    b.step ft s rs cols = .ok (s', n) ↔
      (blockAt W.hS (readsOf W) (workOf W) l).step ft s rs cols = .ok (s', n) ∧
        startOk W s = true := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_step_iff hS hU hla hk hsm ft s s' rs cols n

/-- THE WAY DOWN, AT THE DECISION, FROM THE MEMBER's FORM ALONE. -/
theorem K6MemberIs.decide_down (M : K6MemberIs W l same a b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s' ∧ startOk W s = true := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_decide_down hS hU hla hd

/-- THE WAY DOWN, AT THE STEP, FROM THE MEMBER's FORM ALONE. -/
theorem K6MemberIs.step_down (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hs : b.step ft s rs cols = .ok (s', n)) :
    (blockAt W.hS (readsOf W) (workOf W) l).step ft s rs cols = .ok (s', n) ∧
      startOk W s = true := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_step_down hS hU hla hs

/-- `K6MemberIs.decide_iff` without its premise on the address. -/
theorem K6MemberIs.decide_iff' (M : K6MemberIs W l same a b)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok s' ↔
      (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s' ∧ startOk W s = true := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_decide_iff' hS hU hla hsm s s' rs gs

/-- `K6MemberIs.step_iff` without its premise on the address. -/
theorem K6MemberIs.step_iff' (M : K6MemberIs W l same a b)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) :
    b.step ft s rs cols = .ok (s', n) ↔
      (blockAt W.hS (readsOf W) (workOf W) l).step ft s rs cols = .ok (s', n) ∧
        startOk W s = true := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_step_iff' hS hU hla hsm ft s s' rs cols n

theorem K6MemberIs.rounds (M : K6MemberIs W l same a b) :
    b.rounds = (blockAt W.hS (readsOf W) (workOf W) l).rounds := by
  have hU := M.bare
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_rounds hS hU hla

theorem K6MemberIs.want (M : K6MemberIs W l same a b) (ft : Nat) (rs : List Fmt.RoundView) :
    b.want ft rs = [] := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact member_want hS hla ft rs

/-- Where the member passes its test on the plan: both halves of the seated constant's. -/
theorem K6MemberIs.plan (M : K6MemberIs W l same a b) (hp : b.planOk = true) :
    (parOf W.hS (workOf W)).ok = true ∧ laidOk W = true := by
  obtain ⟨ms, bS, name, hS, hla⟩ := M
  exact seatedClaims_plan hS (by rw [← IM.alone_planOk hla]; exact hp)

end One

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readsOf_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.decide_leaves
#print axioms VerifiableInference.Desc.Kinds.Head.Law.seated_decide_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_decide_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_step_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_decide_down
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_step_down
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_decide_iff'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_step_iff'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_rounds
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_want
#print axioms VerifiableInference.Desc.Kinds.Head.Law.laidAlone_of_term
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.bare
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.decide_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.step_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.decide_down
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.step_down
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.decide_iff'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.step_iff'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.rounds
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.want
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs.plan
