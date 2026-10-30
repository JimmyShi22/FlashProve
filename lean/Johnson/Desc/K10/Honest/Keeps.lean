-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Keeps.lean: THE CLOSING OF A SEGMENT (K10): WHAT A YES OF ITS MEMBER
LEAVES AS IT WAS, AND HOW WHAT IT TURNS HAS TURNED: one sentence on the first chain's state in
front of the member and behind it, with the lemmas that pay it. Lemmas on the verifier's own text;
no honest side's frame in them; none of the library's goals. It imports no file of this folder.

NO PREMISE BUT THE YES: not the facts on the record in front (`CloseBase`,
Johnson/Desc/K10/Honest/Base.lean), not the rounds' shape: what is said is what the decision's
text gives for nothing.

  `CloseKeeps`   at the kind's own record (what is owed, the frame, the statement).
                 IN FRONT: nothing was owed; the frame's link has a shape (L) and a group of the
                 request (Gq); the frame's next step was "a later moment or the closing" and its
                 moment the number of L's moments; the frame named a mask's oracle message (number
                 m); the statement had the frame's group (G); all clauses of the ground's test for
                 beginning a test on that group held (`beginRunL`,
                 Johnson/Desc/First/Base/Ground.lean: the group is there, no test has begun, it
                 has a member, every member is there), and, at the statement with that test begun,
                 all clauses of its test for spending m as a mask (`spendAsMaskL`: the message is
                 there, not sampled, its shape counts no answer, not spent before).
                 BEHIND: nothing is owed; the frame is the one in front but for four fields: the
                 single rows (of which nothing is said here), no mask, the link's number one more,
                 the next step the first of a link; the statement is the one in front with the
                 test on G begun (the members' ledgers are closed; the group is marked as under
                 test and has no open row any more) and m marked as spent as a mask
  `K10Turns`     at the first chain's state: `CloseKeeps` of the two states' records as the
                 chain's own `recOf` reads them, and the state behind is the state in front with
                 that record laid back by the chain's own `putRec`. ("Nothing was owed" is of the
                 record: `recOf` reads "0 rows are owed" as nothing.)
  `K10Keeps`     THE CLAUSE: `K10Turns`, AND THE STATE BEHIND BEARS NO MARK OF FAILURE
  `close_keeps`  a yes of the block's decision at the kind's own record gives `CloseKeeps`
  `closing_turns`   a yes of the lifted block's decision gives `K10Turns` (the bare block tests no
                 mark)
  `member_keeps`  THE PAYER: a yes of the lifted block under the description's wrapper on the mark
                 of failure, under any name, gives `K10Keeps`
  `guarded_keeps` THE PAYER under the driver's guard on the seat too, at any test and any places
  `keeps_unmarked`   no mark behind, and none in front
  `turns_six`, `keeps_six`   written out: the book, the roots, the mark of failure, what the chain
                 puts out and the request are as they were; nothing is owed
  `keeps_beside`  every reader of the state that does not see what these blocks write (`K9.Beside`,
                 Johnson/Desc/First/Batch/Law/Keeps.lean) reads the same behind as in front
  `keeps_st`      what follows for the statement, by the library's own laws: its codes, its number
                 of oracle messages, every oracle message's shape and sample rows, and every other
                 group are as they were; the frame's group is marked as under test and has no open
                 row any more
  `keeps_link`, `keeps_moves`   the live frame's link number is one more; so the sentence holds of
                 no state and itself

Limits. WHICH BLOCK IS THE MEMBER: THE CLAUSE IS PAID for the lifted block under `guardMark` with
any name, and under `Block.guarded` over that, at any test on the seat and any test on the place:
both at the description's own type of claims. For the bare lifted block, general in the type of
claims, `K10Turns` alone is paid: it tests no mark. NOT PAID TO THE LETTER: the description's lot
lays the block at another type of claims and retypes it (`Block.retype`, Johnson/Desc/Block.lean,
which keeps the decision), and the driver writes the place anew: a caller meets both by unfolding.
That the first chain lays just these, in this order, at the closing's place, alone, is the
library's own law, under premises and at one hash (`IM.close_of`, Johnson/IMR/CloseSeat.lean;
`LPFK10.k10_sits`, Johnson/LPFK10R/Sits.lean); the clause is paid at that very block in
Johnson/Desc/K10/Honest/KeepsSeat.lean. WHERE THE DESCRIPTION's MAKERS JOIN A BLOCK OF THE KIND
"frame" BEHIND A PLACE's BLOCK (`chainBy`, Johnson/Desc/ProofFile/Frames1.lean) the state behind
the joined block is another, and the sentence need not hold of it. WHAT `putRec` TURNS OF THE
STATE's NINE FIELDS: the statement and what is owed, as the record says; inside an open segment
(`S.link?` yields one: not in the head's front, nor at the chain's last places) the frame in that
segment's own copy of the calls' state, and nothing else of the field `here`; else the frame in
the field `check`, and nothing else of it: read in `putRec`, `putLive`, `putLink`; the sentence
holds it as an equation; laws of the library that open it: `recOf_putRec`
(First/Close/Law/LensAt.lean), `putRec_standOf`, `putRec_link` (First/Close/Law/ShapeBehind.lean),
`S.live_putLive`, `S.check_putLive` (First/Close/Law/LaysLive.lean), `S.fork_putLive`,
`S.look_putLive` (First/StateLedger.lean). `keeps_st` is some of what follows for the statement: a
ledger that is no member's stays (`behind_ledger`, First/Close/Law/LedgerBehind.lean);
`behind_extends`, `behind_inOrder` (First/Close/Law/StBehind.lean). What the single rows are:
Johnson/Desc/K10/Honest/Fits.lean (`yes_left`), from the yes alone; in the library's words
`closing_inv2` (First/Close/Law/Whole.lean). BESIDE THIS FILE THE LIBRARY HOLDS, off the same yes:
`K10Step` (First/Close/Law/AsksOfMg.lean: it gives `K10Turns`: SeatYes.lean), `closing_keeps`
(First/Close/Law/Leaves.lean: `turns_six`'s six, from the lifted block's yes), `closeFrame_lays`
(First/Close/Law/Lays.lean: the frame behind), `k10_rides`, `k10_rides_more`
(First/Close/Law/RidesBehind.lean, RidesMore.lean: what rides, clause by clause, some of it not
named here). Members: Johnson/Desc/K10/Honest/KeepsToy.lean. Nothing on soundness, completeness or
hiding of the protocol.

-/
import Johnson.Desc.First.Close.Law.Leaves
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.Desc.First.Close.Law.CloseMeans
import Johnson.Desc.First.Close.Law.KindDecide
import Johnson.Desc.First.Close.Law.LensAt
import Johnson.Desc.First.Batch.Law.Keeps
import Johnson.Desc.ProofFile.Law.MarkGuard
import Johnson.Desc.SeatGuard
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)

/-- **What a yes says of the record in front, and what it leaves and turns, at the kind's own
record.** Nine clauses on the record in front; the tenth gives the record behind. -/
def CloseKeeps (s s' : Rec) : Prop :=
  ∃ (L : Params.ReqLink) (Gq : ReqGroup) (G : Group) (m : Nat) (rows : SingleRows),
    s.owed = none ∧ s.frame.shape.link[s.frame.link]? = some L ∧
    s.frame.groups[s.frame.link]? = some Gq ∧
    s.frame.next = .laterOrClose ∧ s.frame.moment = reqMoments L ∧
    s.frame.mask = some m ∧ s.st.groups[s.frame.group]? = some G ∧
    (∀ c ∈ Ground.beginRunL s.st s.frame.group, c.2 = true) ∧
    (∀ c ∈ Ground.spendAsMaskL (Slice.begun s.st s.frame.group G) m, c.2 = true) ∧
    s' = ⟨none,
      { s.frame with rows := rows, mask := none, link := s.frame.link + 1, next := .first },
      spent (Slice.begun s.st s.frame.group G) m⟩

/-- What a yes of the lifted block leaves and turns, at the first chain's state. -/
def K10Turns (t t' : S) : Prop :=
  CloseKeeps (K9.recOf t) (K9.recOf t') ∧ t' = K9.putRec t (K9.recOf t')

/-- **What a yes of the member leaves and turns, at the first chain's state**: and the state
behind bears no mark of failure. -/
def K10Keeps (t t' : S) : Prop :=
  K10Turns t t' ∧ t'.failed = none

/-- What a yes of the frame's closing gives. -/
theorem closeFrame_keeps {s : Rec} {es : List Fmt.Entry} {rs : List Fmt.RoundView}
    {x : ReqFrame × Statement} (hx : closeFrame s.owed s.frame s.st es rs = .ok x) :
    CloseKeeps s ⟨none, x.1, x.2⟩ := by
  obtain ⟨G, m, e1, e2, e3⟩ := closeFrame_st hx
  obtain ⟨h0, L, k2, Gq, k3, k4, rows, hc, hf⟩ := (closeFrame_iff _ _ _ _ _ x.1 x.2).1 hx
  obtain ⟨_, _, _, _, _, _, m', hm, _, _, _, hbat, _, hfold⟩ := hc
  obtain ⟨b1, input, d, b2, _, _, _, _, _, rfl, rfl⟩ := hbat
  obtain ⟨_, _, _, _, _, _, _, _, _, _, f5, _⟩ := hfold
  obtain rfl : m = m' := Option.some.inj (e1.symm.trans hm)
  have hd : d.st = Slice.begun s.st s.frame.group G := by
    unfold Ground.beginRunP at b2
    have hb : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true :=
      List.all_eq_true.2 b1
    have ht : (onSt s.st).st.groups[s.frame.group]? = some G := e2
    rw [if_pos hb, ht] at b2
    exact (congrArg (fun y => y.2.st) (Option.some.inj b2)).symm
  refine ⟨L, Gq, G, m, rows, h0, k2, k3, k4.1, k4.2, e1, e2, b1, hd ▸ f5, ?_⟩
  rw [e3, hf]

/-- A yes of the block's decision, at the kind's own record. -/
theorem close_keeps {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    CloseKeeps s s' := by
  obtain ⟨x, hx, rfl⟩ := (kind_decide_iff P s s' rs gs).1 h
  exact closeFrame_keeps hx

/-- What the chain's reading reads off what its writing wrote, where nothing is owed. -/
theorem recOf_put (t : S) (f : ReqFrame) (st : Statement) :
    K9.recOf (K9.putRec t ⟨none, f, st⟩) = ⟨none, f, st⟩ := by
  obtain ⟨h1, h2⟩ := recOf_putRec t ⟨none, f, st⟩
  show (⟨K9.owedOf (K9.putRec t ⟨none, f, st⟩), (K9.recOf (K9.putRec t ⟨none, f, st⟩)).frame,
    (K9.recOf (K9.putRec t ⟨none, f, st⟩)).st⟩ : Rec) = _
  rw [h1, h2]
  rfl

/-- A yes of the lifted block's decision, without the wrapper on the mark. -/
theorem closing_turns {Cl : Type} {P : Par} {t t' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K9.closing (Cl := Cl) P).decide t rs gs = .ok t') :
    K10Turns t t' := by
  obtain ⟨x, hx, rfl⟩ := closing_writes P t t' rs gs h
  unfold K10Turns
  rw [recOf_put]
  exact ⟨closeFrame_keeps hx, rfl⟩

/-- **Written out**: five fields of the state are as they were; nothing is owed. -/
theorem turns_six {t t' : S} (h : K10Turns t t') :
    t'.book = t.book ∧ t'.roots = t.roots ∧ t'.failed = t.failed ∧ t'.out = t.out ∧
      t'.req = t.req ∧ t'.rowsOwed = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := h.1
  have k := putRec_keeps t (K9.recOf t')
  rw [← h.2, e] at k
  exact k

theorem keeps_six {t t' : S} (h : K10Keeps t t') :
    t'.book = t.book ∧ t'.roots = t.roots ∧ t'.failed = t.failed ∧ t'.out = t.out ∧
      t'.req = t.req ∧ t'.rowsOwed = none := turns_six h.1

/-- No mark of failure, behind or in front. -/
theorem keeps_unmarked {t t' : S} (h : K10Keeps t t') : t'.failed = none ∧ t.failed = none :=
  ⟨h.2, (turns_six h.1).2.2.1 ▸ h.2⟩

/-- **Every reader that does not see what these blocks write reads the same.** -/
theorem keeps_beside {α : Type} {f : S → α} (hf : K9.Beside f) {t t' : S} (h : K10Keeps t t') :
    f t' = f t := by
  rw [h.1.2]
  exact K9.putRec_keeps hf t _

/-- **THE PAYER**: a yes of the lifted block under the description's wrapper on the mark of failure,
under any name. -/
theorem member_keeps {P : Par} (n : String) {t t' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ({ ProofFile.guardMark (K9.closing P) with name := n } : Block S ProofFile.Cl).decide t rs gs =
      .ok t') :
    K10Keeps t t' := by
  obtain ⟨h1, h2⟩ :=
    ProofFile.Law.guardMark_yes.1 (show (ProofFile.guardMark (K9.closing P)).decide t rs gs = _ from h)
  exact ⟨closing_turns h1, h2⟩

/-- **THE PAYER under the driver's guard on the seat too**: at any test `same` and any places `but`
(the first chain's: `ProofFile.sameReply`, `First.hearsReply`). -/
theorem guarded_keeps {P : Par} (n : String) (same : S → S → Bool) (but : Place → Bool) {t t' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (({ ProofFile.guardMark (K9.closing P) with name := n } : Block S ProofFile.Cl).guarded same
      but).decide t rs gs = .ok t') :
    K10Keeps t t' := by
  unfold Block.guarded at h
  simp only at h
  split at h
  · exact member_keeps n h
  · obtain ⟨u, hu, hv⟩ := ok_bind h
    unfold seatSame at hv
    split at hv
    · obtain rfl := Except.ok.inj hv
      exact member_keeps n hu
    · cases hv

/-- **What follows for the statement**, by the library's own laws on the statement behind a
closing. -/
theorem keeps_st {s s' : Rec} (h : CloseKeeps s s') :
    s'.st.codes = s.st.codes ∧ s'.st.oracles.size = s.st.oracles.size ∧
      (∀ o : Nat, (s'.st.oracles[o]?).map (fun x : OnBytes.Oracle => x.shape) =
        (s.st.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) ∧
      (∀ o : Nat, (s'.st.oracles[o]?).map (fun x : OnBytes.Oracle => x.sampleRows) =
        (s.st.oracles[o]?).map fun x : OnBytes.Oracle => x.sampleRows) ∧
      (∀ g' : Nat, g' ≠ s.frame.group → s'.st.groups[g']? = s.st.groups[g']?) ∧
      ∃ G, s.st.groups[s.frame.group]? = some G ∧
        s'.st.groups[s.frame.group]? = some { G with inRun := true, rows := #[] } := by
  obtain ⟨_, _, G, m, rows, _, _, _, _, _, _, hG, _, _, rfl⟩ := h
  exact ⟨behind_codes _ _ _ _, behind_size _ _ _ _, behind_shape _ _ _ _, behind_samples _ _ _ _,
    fun g' hg => behind_group_ne _ _ _ _ g' hg, G, hG, behind_group _ _ _ _ hG⟩

/-- The live frame's link number is one more. -/
theorem keeps_link {t t' : S} (h : K10Keeps t t') :
    (K9.recOf t').frame.link = (K9.recOf t).frame.link + 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := h.1.1
  rw [e]

/-- **The sentence holds of no state and itself.** -/
theorem keeps_moves (t : S) : ¬ K10Keeps t t := fun h => by
  have := keeps_link h
  omega

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.close_keeps
#print axioms ProofFile.Honest.K10.YesFree.closing_turns
#print axioms ProofFile.Honest.K10.YesFree.keeps_six
#print axioms ProofFile.Honest.K10.YesFree.keeps_unmarked
#print axioms ProofFile.Honest.K10.YesFree.keeps_beside
#print axioms ProofFile.Honest.K10.YesFree.member_keeps
#print axioms ProofFile.Honest.K10.YesFree.guarded_keeps
#print axioms ProofFile.Honest.K10.YesFree.keeps_st
#print axioms ProofFile.Honest.K10.YesFree.keeps_moves
