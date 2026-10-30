-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReaderReadsK5.lean: CONDITIONAL: AT EVERY STAND IN FRONT OF THE
MEMBER AT AN ATTENTION SEGMENT's OWN ROUNDS (kind K5) THE READER OF THE SEGMENT's MASK ROW RETURNS,
UNDER A SLOT BELOW THE PLAN's NUMBER OF SLOTS, WHAT THE WITNESS's MESSAGE WITH THE MASK ROW HOLDS
THERE, AT EVERY WITNESS; so, under one hypothesis on the Script, the premise's form `ReaderReads`
(Honest/Law/Rule/TiesFall.lean) holds at that member. Statements with their proofs; no definition.

  `masks_head`         CONDITIONAL: the library's test `masksUpTo` says yes up to the plan's number
                       of slots; the message with the mask row has one mask row
  `maskRoom_head`      CONDITIONAL: `MaskRoom` (Honest/K5/Law/ScriptQRaw.lean) at the plan's number
                       of slots comes down to ONE inequality on public numbers: hroom
  `room_of_free`       CONDITIONAL: hroom from "the number of slots is at most the mask row's free
                       entries" (`Send.freeMaskEntries`, OnBytes/Iop/Send.lean) at one mask row
                       and one answer
  `reads_msg_K5`       CONDITIONAL: the reader's value under ν is the witness's message number
                       `maskNo5`, mask table, row 0, place ν
  `readerReads_K5_T`   CONDITIONAL: **`ReaderReads` T (`Thr` T b) …**, T A VARIABLE
  `readerReads_K5`     CONDITIONAL: the same at the first chain's letters as they are laid
                       (`lettersHead`, Honest/Thread/FirstHead.lean)

THE PREMISES OF `readerReads_K5_T`, ALL OF THEM. h: the library's hypothesis on the public input
(`P5J.AtMgA`) · R : `K5AtT` (Honest/K5/Law/AtT.lean): what eight of T's letters are · hg: g is below
12 · Pl: the group's plan · hx: the place of the segment's lookup on the calls · hw: the reading wt
of the thread's witness is the Script's · Rm : `MaskRoom` at the plan's number of slots · hv: what
T's letter `valid` holds of meets Vd · hN: N is at most the number of challenges heard at the border
in front of the member · hQ: AT EVERY INPUT THAT MEETS Vd AND EVERY LIST OF AT LEAST N CHALLENGES,
CUT WHERE THE MESSAGE TURNS NO MORE (`Script.fixedMsg`), the Script's message number `maskNo5`
holds, in its mask table, row 0, at every place ν below the plan's number of slots, the reading of
rowOf (ownC k) ν. THESE THREE GUARDS ARE THOSE OF THE FRAME's FORM `OwnMsgs`
(Honest/Thread/ScriptLots.lean) AND OF `ESymsRaw` (CellsQRaw.lean): so hQ asks no more than a lot of
that form gives (`hQ_of_ownMsgs`, Honest/K5/Law/ReaderReadsOwn.lean), and no more than `ReaderReads`
spends: at a stand `Thr` has the input valid and the challenges heard. Vd, N, rowOf and ownC are
letters. At `lettersHead` R, hw and hv fall: R by `k5AtT_thrAt` (Honest/K5/Law/AtT.lean), hw and hv
by unfolding.

The road. A stand gives a reached state without a mark that meets the promise in front of the member
(`reach_T`, `onAt_T`, Honest/K5/Law/DebtsT.lean). There the library's tie of the two readings by
address holds at any list of forms whose slots lie below the plan's number (`addrTie_front_fs`,
Johnson/Desc/K5/Honest/Law/AddrTieFs.lean): it is taken at the list of one form that names the one
slot ν, so NOTHING IS ASKED OF THE LEDGER. The reading by address is the message's entry
(`val_mask`, Honest/K5/Law/ScriptQRaw.lean). What it is for. `ReaderReads` is a premise of the laws
on the mask's tie (Honest/Law/Rule/). IT IS SHOWN HERE AT THE SLOTS BELOW THE PLAN's NUMBER, which
may be fewer than the mask row's free entries: so it serves the form that is general in the set of
slots (`maskTieOn_whole`, Honest/Law/Rule/TiesLen.lean), whose premise hN then asks that the
member's slots lie below the plan's number.

Limits. Conditional. hQ IS SHOWN OF NO SCRIPT, AND hroom AT NO PLAN: the library's test `masksUpTo`
gives only that the plan's number of slots is at most the mask code's message length; hroom asks one
place more, for the answer's pad (`padB`, Johnson/Desc/SeatAt.lean, which is typed at one answer).
By `room_of_free` it follows from: the plan's number of slots is at most the free entries of one
mask row at one answer. Below the plan's number of slots alone: of the mask row's further entries
nothing is said. Where `Thr` T has no member the statements say nothing. h is a hypothesis of every
statement that names it. At the library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQAt
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQRaw
import Johnson.Desc.ProofFile.Honest.K5.Law.AtHeadLetters
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Aff Reading)
open OnBytes.Maker (WholeD)
open Johnson.Pack (pMask)
open VerifiableInference.Desc (Block Place Strs Chain)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg masksUpTo)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT dataQ seatTab)
open H2K5.Door (seatAll k5CondAt_at_head tiePubCells_all)
open H2K5.Honest (addrTie_front_fs)
open ProofFile.Honest.FirstThread (Script WtF honest lettersHead)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The library's test on the seats of mask entries says yes up to the plan's number of slots, and
the message with the mask row has one mask row. CONDITIONAL: under the hypothesis h; g is below 12;
the group's plan; the place of the lookup on the calls. -/
theorem masks_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    masksUpTo h.𝔇.sent x₁ a.ns = true ∧
      ∀ (k : Nat) (hk : k < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
        maskMsg h.𝔇.sent x₁.link = some k →
        ((sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).get ⟨k, hk⟩).1.maskRows = 1 := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨-, p2, -, p4⟩ :=
    tiePubCells_all h hg ea hx ((k5CondAt_at_head h hL).each g hg a x₁ ea hx).cells
  exact ⟨p2, p4⟩

/-- The inequality, from the library's count of a mask row's free entries at one mask row and one
answer. CONDITIONAL: the message length is not 0; ns is at most that count. -/
theorem room_of_free {ns ell : Nat} (h1 : 1 ≤ ell)
    (hf : ns ≤ OnBytes.Send.freeMaskEntries 1 ell 1) : ns + 1 ≤ ell := by
  unfold OnBytes.Send.freeMaskEntries at hf
  have hc : ((1 : Nat) == 0 || decide (ell < 1)) = false := by
    rw [Bool.or_eq_false_iff]
    exact ⟨rfl, decide_eq_false (by omega)⟩
  rw [if_neg (by rw [hc]; exact Bool.false_ne_true)] at hf
  omega

/-- **`MaskRoom` COMES DOWN TO ONE INEQUALITY.** CONDITIONAL: as `masks_head`; hm: kM is the number
of the message with the mask row; hroom: the plan's number of slots and one place more have room in
the mask code's message length. -/
theorem maskRoom_head {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM)
    (hroom : a.ns + 1 ≤
      (pMask h.𝔇.sent.codes ((sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).get ⟨kM, hk⟩).1).ell) :
    MaskRoom h.𝔇.sent h.𝔇.l3.rad x₁ kM hk a.ns 1 :=
  ⟨hm, (masks_head h hg ea hx).2 kM hk hm, Nat.le_refl 1, hroom⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : VerifiableInference.Desc.First.Item → T.ι} {pb : T.P → ProofFile.InstPub}
  {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- **WHAT THE READER RETURNS UNDER A SLOT, AT A STAND IN FRONT OF THE MEMBER**, at every witness w.
CONDITIONAL: under the hypothesis h and `K5AtT`; g is below 12; the plan's facts; the place of the
lookup on the calls; `MaskRoom`; `Thr` at the stand; pt is the open segment's part; ν is below the
plan's number of slots. -/
theorem reads_msg_K5 (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {nA : Nat}
    (Rm : MaskRoom h.𝔇.sent h.𝔇.l3.rad x₁ kM hk a.ns nA) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} (hT : Thr T (borderOf g) k s m En)
    {pt : VerifiableInference.Desc.K9.Part} (hpt : segAt? s = some pt) (w : WtF) {ν : Nat}
    (hν : ν < a.ns) :
    (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w)).mask ν =
      w.msg (maskNo5 h x₁ kM hk) true 0 ν := by
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨blk, _, hb, _, _⟩ := k5_member h hg
  have hr := reach_T h R (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  have A := addrTie_front_fs h hL hg Pl.plan hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) hr hu hon hpt w (fs5 ν 1) fun f hf z hz => by
      obtain ⟨j, hj, ez⟩ := fs5_slots hf hz
      omega
  have t := A.mask (slotsForm ν 1) (List.mem_singleton.2 rfl) (ν + 0, zeroE)
    (List.mem_map.2 ⟨0, List.mem_range.2 Nat.one_pos, rfl⟩ :
      (ν + 0, zeroE) ∈ (List.range 1).map fun j => (ν + j, zeroE))
  exact t.symm.trans (val_mask (masks_head h hg Pl.plan hx).1 Rm (seatAll h x₁) h.𝔇.arr w hν)

/-- **`ReaderReads` AT THE KIND's MEMBER, T A VARIABLE.** CONDITIONAL: every premise stands, by
name, in the file's head. -/
theorem readerReads_K5_T
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁)
    (hw : ∀ k v hd, wt (T.wit k v hd) = Q.wit k v hd) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {nA : Nat}
    (Rm : MaskRoom h.𝔇.sent h.𝔇.l3.rad x₁ kM hk a.ns nA)
    {Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop} {N : Nat} (hv : ∀ v, T.valid v → Vd v)
    (hN : N ≤ T.front + roundsTo T.bs (borderOf g)) {d : Due} (rowOf : Cs d → Nat → E)
    (ownC : Coins Bk → Cs d)
    (hQ : ∀ k v (hd : List Fmt.Drawn) ν, Vd v → N ≤ hd.length → ν < a.ns →
      Q.msg (maskNo5 h x₁ kM hk) k v (hd.take (Q.fixedMsg (maskNo5 h x₁ kM hk))) true 0 ν =
        Reading.gl.val (rowOf (ownC k) ν)) :
    ReaderReads T (Thr T (borderOf g)) segAt?
      (fun pt _ _ v ν =>
        (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))).mask ν)
      Reading.gl.val (fun k _ _ ν => rowOf (ownC k) ν) (· < a.ns) := by
  intro k s m En hT pt hpt ds ν hν
  show (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
    (wt (T.wit k m.st.input (m.st.heard ++ ds))))).mask ν = _
  rw [hw]
  exact (reads_msg_K5 h R hg Pl hx Rm hT hpt _ hν).trans
    (hQ k _ _ ν (hv _ hT.2.2.2.2.2.2) (heard_enough hN hT ds) hν)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **`ReaderReads` AT THE KIND's MEMBER, AT THE LETTERS AS THEY ARE LAID.** CONDITIONAL: under the
hypothesis h; g is below 12; the group's plan; the place of the lookup on the calls; `MaskRoom`; hQ.
-/
theorem readerReads_K5 {g : Nat} (hg : g < 12) {a : OnBytes.Attention.Plan} (Pl : PlanAt Zp g a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {nA : Nat}
    (Rm : MaskRoom h.𝔇.sent h.𝔇.l3.rad x₁ kM hk a.ns nA) {N : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g)) {d : Due} (rowOf : Cs d → Nat → E)
    (ownC : Coins Bk → Cs d)
    (hQ : ∀ k v (hd : List Fmt.Drawn) ν, Vd v → N ≤ hd.length → ν < a.ns →
      Q.msg (maskNo5 h x₁ kM hk) k v (hd.take (Q.fixedMsg (maskNo5 h x₁ kM hk))) true 0 ν =
        Reading.gl.val (rowOf (ownC k) ν)) :
    ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
      (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread (borderOf g)) segAt?
      (fun pt _ _ v ν =>
        (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) pt (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)).mask ν)
      Reading.gl.val (fun k _ _ ν => rowOf (ownC k) ν) (· < a.ns) :=
  readerReads_K5_T h
    (k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg)
    Q hg Pl hx (fun _ _ _ => rfl) Rm (fun _ hv => hv.2) hN rowOf ownC hQ

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.masks_head
#print axioms ProofFile.Honest.K5.room_of_free
#print axioms ProofFile.Honest.K5.maskRoom_head
#print axioms ProofFile.Honest.K5.reads_msg_K5
#print axioms ProofFile.Honest.K5.readerReads_K5_T
#print axioms ProofFile.Honest.K5.readerReads_K5
