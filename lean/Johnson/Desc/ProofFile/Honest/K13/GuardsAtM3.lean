-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/GuardsAtM3.lean: kind K13, the members' batching: THE NINE GUARDS
(`K13Guards`, Debts.lean of this folder) UNDER THE THREAD's SENTENCE IN FRONT OF THE KIND's MEMBER,
AT THE LIBRARY's OWN PARAMETERS (`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean): ONE STATEMENT
A GUARD, FOR EACH WHOLE GUARD THAT IS SHOWN HERE; what is left here, as one structure; the nine
together; and what acceptance then costs. Statements with their proofs: calls of the library's facts
at reached states and of its written numbers. THE FULL SIZE ALONE, AT THE HASH `OnBytes.secondHashFunction`
ALONE. The words thread and border are explained in the head of Honest/Thread/Thr.lean.

SIX OF THE NINE ARE SHOWN, five from the hypothesis h and the thread alone:
  fin, waits: out of the public form (`k13_form_front`, FromThread.lean): `k13_guard_form_at`.
  taken: `k13_guard_taken`: by TakenAtM3.lean, WITH ITS INEQUALITY SHOWN: `k13_room_at`: the fresh
    ledger has 255 free entries (`m3_free0`), the matrix 2 ^ 18 columns (`m3_kCol`): 37 + 13 ≤ 255.
  msg: on the plan alone: `k13_guard_msg_at`.
  lin: `k13_guard_lin_at`: the state's codes are the plan's at every reached state without a mark
    (`Meaning.K2.recAll_all`, Johnson/IMR/AtReach.lean); the test accepts at the written numbers
    (`linOk_written`, by Lean's kernel; `linOk_rejects`: it can reject).
  reply: `k13_guard_reply`: at every thread's parameters: FROM A PREMISE: the thread gives that the
    reply held is the one asked (`ReplyRides`, FromThread.lean): IT SPEAKS OF ONE VALUE THAT IS SENT
    IN THE CLEAR (`replyPart`, Honest/K7.lean: no coin; of its input it reads the instance alone).
THREE ARE LEFT HERE: `K13GuardsLeft`: count (the pile has the plan's number of rows: `m3_rows`:
  thirteen; `m3_rows_taken`: the library's count `takenAt` at 355 is that number too; the thread's
  file Honest/Thread/Riders.lean has a form for it, `riderPile`), fit and form (the library's two
  tests on the shapes of the pile's rows and of the index masks' message). GuardsLeft.lean of this
  folder cuts the three into clauses and shows what of them can be shown there. SHOWN IN FILES THAT
  IMPORT THIS ONE: count, whole, from h and the thread alone (`k13_count_at`, CountAtM3.lean); the
  clause on the message's shape (`k13_indexShape_at`, IndexShapeAtM3.lean).
`k13_guards_stand_at`: the nine at one stand. `k13_guards_at`: **the nine, from h, `ReplyRides` at
  355 and `K13GuardsLeft` under the thread.**
`k13_accepted_left_at`: **so `Accepted` at 355, at every `fall`: from h, the kind's half's place
  among the thread's halves, `ReplyRides` at 355 and `K13GuardsLeft` under the thread.**
`k13_accepted_at`: the same from `K13Seated` (Seated.lean of this folder), of whose fifteen fields
  it spends four.

Where the written numbers come from. In the goals' scope, where the proof file's value is laid, a
test that pins the made plan accepts (`P5J.pins_of_laid`, Johnson/Goal/Skeleton/PinsOfLaid.lean),
and then the first chain's parameters, as read back, are the written ones (`first_written_in_scope`,
Johnson/Goal/Numbers/MadeInScope.lean: `m3_written`). The two terms for the fresh ledger's free
count are one number where a public test accepts (`P1L20.free0_is`, Johnson/P1L20R/Free0Is.lean),
and it accepts under h (`P5J.startB_at_head`, Johnson/P5J/StartAtHead.lean); the count at the
written numbers is 255 by Lean's kernel (`LT28.K11Tests.free_full`,
Johnson/Desc/Sound/K11Tests/LettersSevenInScope.lean).

What is not claimed. That the hypothesis h can be met. That the thread holds at any run.
`ReplyRides`, and the three guards that are left, at any thread. Anything at a thread with other
parameters, but for `k13_guard_reply`. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.TakenAtM3
import Johnson.Desc.ProofFile.Honest.K13.Seated
import Johnson.P1L20R.Free0Is
import Johnson.P5J.StartAtHead
import Johnson.P5J.Cols13Paid
import Johnson.P5J.NumAtHead
import Johnson.K11R.CondOfTwo
import Johnson.IMR.AtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K1 (free0Of gpOf)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (dOf msgs_at)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (FirstWritten proofSizedFull)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope sends_in_scope)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters lettersAt Script WtF)

/-! ## 1 The plan's numbers, under the hypothesis h -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- The first chain's parameters, as read back, are the written ones. -/
theorem m3_written : FirstWritten Zp.first :=
  first_written_in_scope h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1

include h in
/-- The fresh ledger of the index masks' message has 255 free entries. -/
theorem m3_free0 : free0Of Zp.first (gpOf Zp) = 255 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have e := P1L20.free0_is O (P5J.startB_at_head h.toAtMg)
  rw [O.first, K11.indexNo_four h, LT28.K11Tests.codes_in_scope h.scope h.laid.pub hy,
    msgs_at (congrArg Prod.fst (sends_in_scope h.scope h.laid.pub hy)),
    LT28.K11Tests.free_full] at e
  exact e

include h in
/-- The committed matrix has 2 ^ 18 columns. -/
theorem m3_kCol : h.𝔇.P13.lin.kCol = 18 := by
  have e := P5J.AtMg.cols13 h.toAtMg
  exact Nat.pow_right_injective (Nat.le_refl 2) (e.trans (by decide +kernel))

include h in
/-- The plan's number of rows that the batching expects is thirteen. (That so many rows lie on the
pile at a state is the guard "count", which is not shown here.) -/
theorem m3_rows : h.𝔇.P13.rows = 13 := (m3_written h).2.2.2.1

include h in
/-- It equals the library's count `takenAt` at 355: AN EQUATION OF TWO NUMBERS THAT ARE BOTH 13: no
tie by meaning is shown. -/
theorem m3_rows_taken : h.𝔇.P13.rows = P1L20.takenAt 355 := (m3_rows h).trans m3_takenAt.symm

include h in
/-- **The inequality between public numbers**: what the batching takes and the thirteen entries of
the library's count find room in the fresh ledger. -/
theorem k13_room_at : Batt.masksOf h.𝔇.P13.lin.kCol + 13 ≤ free0Of Zp.first (gpOf Zp) := by
  rw [m3_kCol h, m3_free0 h]
  decide

set_option maxRecDepth 100000 in
/-- The library's test on the shape with the codes accepts at the written numbers. -/
theorem linOk_written : linOk proofSizedFull.codes proofSizedFull.batch.shape = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test: at the same numbers with a mask code that the codes do not have it rejects. -/
theorem linOk_rejects : linOk proofSizedFull.codes
    { proofSizedFull.batch.shape with ownMaskCode := proofSizedFull.codes.mask.size } = false := by
  decide +kernel

include h in
/-- **THE GUARD "msg"**: on the plan alone. -/
theorem k13_guard_msg_at : ∃ msg, linMessageW h.𝔇.P13.lin = some msg := by
  show ∃ msg, linMessageW Zp.first.lin = some msg
  rw [(m3_written h).2.1]
  cases e : linMessageW proofSizedFull.batch.shape with
  | some msg => exact ⟨msg, rfl⟩
  | none =>
    have q := P5J.w_msgs_written
    rw [e] at q
    cases q

end

/-! ## 2 A guard that a sentence of the thread gives, at every thread's parameters -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **THE GUARD "reply"**, where the thread gives that the reply held is the one asked. The guard
wants less than this premise says: that a reply is held, not which. -/
theorem k13_guard_reply {b : Nat} {asked : Xi → E} (hY : ReplyRides L b asked) (P : Where)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    (hT : Thr L.thread b k s m En) : (!P.reply || s.out.reply.isSome) = true := by
  have e : s.out.reply = some (asked m.st.input.x) := hY k s m En hT
  rw [e]
  simp

end

/-! ## 3 The guards under the thread at border 355 -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE GUARDS "fin" AND "waits"**, and no mark of failure: out of the public form. -/
theorem k13_guard_form_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    s.failed = none ∧ (∃ f, s.here = .fin f) ∧ s.noneWaits = true :=
  k13_form_front (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) m3_place
    hT.2.2.1

/-- **THE GUARD "taken": NO PREMISE ON NUMBERS IS LEFT**: `k13_guard_taken_at` (TakenAtM3.lean) with
its inequality shown (`k13_room_at`). At the library's own parameters, as that one. -/
theorem k13_guard_taken {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    ∃ t, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf h.𝔇.P13.lin.kCol) = some t :=
  k13_guard_taken_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps (k13_room_at h)
    hT

/-- **THE GUARD "lin"**: the state's codes are the plan's at every reached state without a mark; the
test accepts at the written numbers. -/
theorem k13_guard_lin_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    linOk s.st.codes h.𝔇.P13.lin = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hc := (Meaning.K2.recAll_all h.scope h.reads O (P5J.flat_ok h.toAtMg)
    (k13_reach_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
    (k13_guard_form_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT).1).codes
  rw [hc]
  show linOk Zp.first.codes Zp.first.lin = true
  rw [(m3_written h).1, (m3_written h).2.1]
  exact linOk_written

/-- **WHAT IS LEFT OF THE NINE GUARDS**: a count and two tests on shapes, of the pile that other
sub-protocols have laid: three clauses of `K13Guards`, to the sign. A premise's form: nothing is
claimed of it. -/
structure K13GuardsLeft (P : Where) (s : S) : Prop where
  count : s.out.pending.length = P.rows
  fit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true
  form : Batt.fits P.lin.kCol s.out.pending = true

/-- **THE NINE GUARDS AT ONE STAND**: from h and the thread there; hy: the guard "reply"; hl: what
is left. -/
theorem k13_guards_stand_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En)
    (hy : (!h.𝔇.P13.reply || s.out.reply.isSome) = true) (hl : K13GuardsLeft h.𝔇.P13 s) :
    K13Guards h.𝔇.P13 s :=
  have hF := k13_guard_form_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT
  { fin := hF.2.1
    reply := hy
    count := hl.count
    fit := hl.fit
    waits := hF.2.2
    form := hl.form
    taken := k13_guard_taken h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT
    lin := k13_guard_lin_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT
    msg := k13_guard_msg_at h }

/-- **THE NINE GUARDS UNDER THE THREAD AT BORDER 355**: from h; that the thread gives the reply; and
what is left. -/
theorem k13_guards_at {asked : ProofFile.Inst → E}
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      asked)
    (hLeft : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En → K13GuardsLeft h.𝔇.P13 s) :
    ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En → K13Guards h.𝔇.P13 s :=
  fun k s m En hT =>
    k13_guards_stand_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT
      (k13_guard_reply _ hY _ hT) (hLeft k s m En hT)

/-- **THE MEMBER IS ACCEPTED, at every `fall`**: from the structure `K13Seated` (Seated.lean of this
folder) at these parameters and what is left of the guards: the reply's sentence is the structure's
own. OF THE STRUCTURE's FIFTEEN FIELDS FOUR ARE SPENT: place, member, isAtM3, and ridesIs at 355.
What acceptance costs at these parameters: `k13_accepted_left_at`. -/
theorem k13_accepted_at {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {rd : ProofFile.InstPub × TS → WtF →
      VerifiableInference.Desc.K13.Law.Wit OnBytes.Slice.GE h.𝔇.P13.lin.matrixRows
        h.𝔇.P13.lin.kCol}
    {asked : ProofFile.Inst → E} {R : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop}
    (hSeat : K13Seated (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      weights pile h.𝔇.P13 Unit rd asked R)
    (hLeft : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En → K13GuardsLeft h.𝔇.P13 s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      355 :=
  k13_seated_accepted hSeat
    (k13_guards_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hSeat.reply hLeft)
    fall

/-- **WHAT ACCEPTANCE COSTS AT THESE PARAMETERS**: h; hH: the kind's half stands at the member's
place among the thread's halves; hY: the thread gives the reply; hLeft: what is left of the guards.
None of the three ties of ExchangeAtM3.lean is asked. -/
theorem k13_accepted_left_at {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {asked : ProofFile.Inst → E}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (hs.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      asked)
    (hLeft : ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En → K13GuardsLeft h.𝔇.P13 s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      355 :=
  k13_thread_accepted (Cl' := Unit)
    (k13_atK13_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hH)
    (fun blk hb _ s _ _ hT rs gs t' q =>
      (k13_memberIs_at h).forth blk hb s rs gs t'
        (k13_guard_form_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT).1 q)
    (k13_guards_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hY hLeft) fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m3_written
#print axioms ProofFile.Honest.K13.m3_free0
#print axioms ProofFile.Honest.K13.m3_kCol
#print axioms ProofFile.Honest.K13.m3_rows
#print axioms ProofFile.Honest.K13.k13_room_at
#print axioms ProofFile.Honest.K13.linOk_written
#print axioms ProofFile.Honest.K13.k13_guard_msg_at
#print axioms ProofFile.Honest.K13.k13_guard_reply
#print axioms ProofFile.Honest.K13.k13_guard_form_at
#print axioms ProofFile.Honest.K13.k13_guard_taken
#print axioms ProofFile.Honest.K13.k13_guard_lin_at
#print axioms ProofFile.Honest.K13.k13_guards_stand_at
#print axioms ProofFile.Honest.K13.k13_guards_at
#print axioms ProofFile.Honest.K13.k13_accepted_at
#print axioms ProofFile.Honest.K13.m3_rows_taken
#print axioms ProofFile.Honest.K13.linOk_rejects
#print axioms ProofFile.Honest.K13.k13_accepted_left_at
