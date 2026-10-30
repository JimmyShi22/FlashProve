-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskNos.lean: THE MESSAGE WITH A SEGMENT's MASK ROW BEARS, IN
THE WITNESS, THE PLAN's NUMBER OF (the segment, its number in the segment's own list); SO THE
MESSAGES WITH TWO SEGMENTS' MASK ROWS BEAR TWO NUMBERS: `MaskNosApart h` (AgreeK5.lean in this
folder) IS PAID; AND K5's OWN LOTS AGREE WITH ONE ANOTHER UNDER THE HEAD ALONE. CONDITIONAL: under
the hypothesis h, the library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean).
On public data, but for the three last. Two definitions with code; fourteen theorems: six general,
two closed facts by evaluation in Lean's kernel, six under h.

Main names:
  `maskNo5_is_num`: **THE TIE**: where `maskMsg` names member kM of the list of x₁'s link:
    `maskNo5 h x₁ kM hk = P5J.At.num Zp x₁.link mi`, at an own message mi of that link.
  `maskNosApart_head`: **THE PAYMENT**: `MaskNosApart h`.
  `k5Lots_agree_head`, `k5_msgsAgree_head`, `k5_agree_cut_head`: AgreeK5.lean's three tops without
    their premise hAp.
  `P6T.key_of_call`: the seat that the planner's list has for a member behind the kept ones bears
    the key of the link's own message of that number. `P6T.maskMsg_some`: the member that `maskMsg`
    names stands behind the kept ones, at an own message of the link.
  `P6T.maskSeatsB D ps psAll`: A TEST WITH CODE: at every link with a message with mask rows the
    planner's list ps has a seat for that member, and in psAll its tree and tenant are first held by
    a seat of its key. `maskSeatsB_congr`: it reads D at its shape alone. `maskSeats_gives`.
  `P6T.maskSeats_written`: THE CLOSED FACT: it accepts at the library's written shape and seats.
  `P6T.one_mask_written`: at the written shape each link has JUST ONE own message with mask rows.
  `maskSeats_head`: so it does at the head's own.

How. By unfolding, under the head: `maskNo5` is `At.arr Zp` at the tree and tenant that
`P6T.seatCallsT` (Johnson/P5T/SeatsAt.lean) reads off the first chain's seats. The test gives the
seat p and the first holder of its tree and tenant among all three chains' seats, with p's key; the
key is (0, link, mi) by `key_of_call`; so `arrOf` there is `numOfPlan`: `P5T.arrOf_is_num`
(Johnson/P5T/NumOfPlan.lean). The payment: `AtMg.num_apart` (NumsCover.lean in this folder). The
bridge to the written lists: `AtMg.seats_written`, `AtMg.shape_written`
(Johnson/HB/LLHARD/MaskSeatWritten.lean).

Limits. OF THE MESSAGE THAT `maskMsg` NAMES ALONE: the first of the link's OWN messages with mask
rows: at the written shape there is just one (`one_mask_written`; no theorem here carries that to
the head). Of a message with a mask row that is no link's own nothing is said. That the verifier's
side reads K5's slots in the message that `maskMsg` names is not proved here: `val_mask`
(ScriptQRaw.lean in this folder). Which member of the chain sends that message is not said. Of what
the message holds nothing is said. AGAINST THE OTHER KINDS' LOTS NOTHING IS PROVED: AgreeK5.lean's
Limits stand but for hAp. h IS A HYPOTHESIS: it has a member at the library's written copy of the
full-size public files (`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean),
which is tied to the package's files by no theorem: ONE EXAMPLE. The two closed facts have been
checked by Lean's own kernel alone. The file stands over LotsK5.lean, a working form, and over the
frame's ScriptLots.lean: neither lies in a seal. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AgreeK5
import Johnson.Desc.ProofFile.Honest.K5.Law.NumsCover
import Johnson.P5T.SeatsAt
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P6T
open P5T
open VerifiableInference.Desc.First.Look (Sent keptAt bornAt messagesAt)
open VerifiableInference.Desc.First.Att.P (maskMsg)

/-- **The seat that the planner's list has for a member behind the kept ones bears the key of the
link's own message of that number.** -/
theorem key_of_call {ps : List PSeat} {D : Sent} {l j : Nat} {p : PSeat}
    (h : callAt ps D l j = some p) (hj : keptN D l ≤ j) : keyOf p = (0, l, j - keptN D l) := by
  have hc := List.find?_some h
  unfold isCall at hc
  rw [Bool.and_eq_true, if_neg (Nat.not_lt.2 hj)] at hc
  have h1 := eq_of_beq hc.1
  have h2 := eq_of_beq hc.2
  unfold keyOf
  rw [h1, h2]

/-- **The member that `maskMsg` names stands behind the kept ones, at an own message of the
link.** -/
theorem maskMsg_some {D : Sent} {l kM : Nat} (hm : maskMsg D l = some kM) :
    ∃ (Lk : OnBytes.Params.ReqLink) (mi : Nat), D.shape.link[l]? = some Lk ∧
      mi < Lk.messages.length ∧ kM = keptN D l + mi := by
  unfold maskMsg at hm
  obtain ⟨mi, hmi, rfl⟩ := Option.map_eq_some_iff.1 hm
  obtain ⟨hlt, -, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hmi
  unfold messagesAt at hlt
  cases hq : D.shape.link[l]? with
  | none =>
    rw [hq] at hlt
    exact absurd hlt (by simp)
  | some Lk =>
    rw [hq] at hlt
    exact ⟨Lk, mi, rfl, hlt, rfl⟩

/-- `isCall` reads D at its shape alone. -/
theorem isCall_congr {D D' : Sent} (e : D.shape = D'.shape) : isCall D = isCall D' := by
  funext l j p
  unfold isCall keptN keptAt bornAt
  rw [e]

/-- `maskMsg` reads D at its shape alone. -/
theorem maskMsg_congr {D D' : Sent} (e : D.shape = D'.shape) : maskMsg D = maskMsg D' := by
  funext i
  unfold maskMsg messagesAt keptAt
  rw [e]

/-- **The test**: at every link whose list has a message with mask rows, the planner's list has a
seat for that member, and in the list psAll its tree and tenant are first held by a seat of its
key. -/
def maskSeatsB (D : Sent) (ps psAll : List PSeat) : Bool :=
  (List.range D.shape.link.length).all fun l =>
    match maskMsg D l with
    | none => true
    | some kM => (callAt ps D l kM).any fun p =>
        (psAll.find? fun q => q.j == p.j && q.t == p.t).map keyOf == some (keyOf p)

/-- The test reads D at its shape alone. -/
theorem maskSeatsB_congr {D D' : Sent} (e : D.shape = D'.shape) (ps psAll : List PSeat) :
    maskSeatsB D ps psAll = maskSeatsB D' ps psAll := by
  unfold maskSeatsB callAt
  rw [e, isCall_congr e, maskMsg_congr e]

/-- **What the test gives.** -/
theorem maskSeats_gives {D : Sent} {ps psAll : List PSeat} (h : maskSeatsB D ps psAll = true)
    {l kM : Nat} (hl : l < D.shape.link.length) (hm : maskMsg D l = some kM) :
    ∃ p p₀, callAt ps D l kM = some p ∧
      (psAll.find? fun q => q.j == p.j && q.t == p.t) = some p₀ ∧ keyOf p₀ = keyOf p := by
  unfold maskSeatsB at h
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  simp only [hm] at h1
  cases hc : callAt ps D l kM with
  | none => simp [hc] at h1
  | some p =>
    rw [hc, Option.any_some] at h1
    obtain ⟨p₀, hp₀, hk₀⟩ := Option.map_eq_some_iff.1 (eq_of_beq h1)
    exact ⟨p, p₀, rfl, hp₀, hk₀⟩

/-- A record with the written shape; its three other fields are read by nothing here. -/
def sentShape : Sent := ⟨default, VerifiableInference.Desc.ReqLit.shapeFull, default, #[]⟩

set_option maxRecDepth 1000000 in
/-- **At the library's written shape and seats the test accepts.** By evaluation in Lean's
kernel. -/
theorem maskSeats_written : maskSeatsB sentShape psFull seatsAllFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written shape each link has just one own message with mask rows.** By evaluation in
Lean's kernel. -/
theorem one_mask_written :
    (VerifiableInference.Desc.ReqLit.shapeFull.link.all fun Lk =>
      (Lk.messages.filter fun m => m.shape.maskRows != 0).length == 1) = true := by decide +kernel

end P6T

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open ProofFile.Honest.FirstThread (MsgLot LotsAgree MsgsAgree Agree2)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

include h in
/-- **The test accepts at the head's own shape and seats.** CONDITIONAL: under the hypothesis h. -/
theorem maskSeats_head :
    P6T.maskSeatsB (P5J.At.sentAt Zp) (P5J.At.pseats Zp) (P5J.At.pseatsAll Zp) = true := by
  have e1 : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.seats_written.1
  have e2 : P5J.At.pseatsAll Zp = P5T.seatsAllFull := h.toAtMg.seats_written.2.1
  have e3 : (P5J.At.sentAt Zp).shape = P6T.sentShape.shape := h.toAtMg.shape_written
  rw [e1, e2, P6T.maskSeatsB_congr e3]
  exact P6T.maskSeats_written

/-- **THE MESSAGE WITH A SEGMENT's MASK ROW BEARS THE PLAN's NUMBER OF (the segment, its number in
the segment's own list).** CONDITIONAL: under the hypothesis h; `maskMsg` names member kM. -/
theorem maskNo5_is_num {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length}
    (hm : maskMsg h.𝔇.sent x₁.link = some kM) :
    ∃ (Lk : OnBytes.Params.ReqLink) (mi : ℕ), Zp.first.shape.link[x₁.link]? = some Lk ∧
      mi < Lk.messages.length ∧ maskNo5 h x₁ kM hk = P5J.At.num Zp x₁.link mi := by
  have hm' : maskMsg (P5J.At.sentAt Zp) x₁.link = some kM := hm
  obtain ⟨Lk, mi, hl, hmi, rfl⟩ := P6T.maskMsg_some hm'
  obtain ⟨p, p₀, hc, hf, hk0⟩ := P6T.maskSeats_gives (maskSeats_head h)
    (List.getElem?_eq_some_iff.1 hl).1 hm'
  have key := P6T.key_of_call hc (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at key
  refine ⟨Lk, mi, hl, hmi, ?_⟩
  have es : P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) x₁.link
      (P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi) = (p.j, p.t) := by
    unfold P6T.seatCallsT
    rw [hc]
    rfl
  show P5J.At.arr Zp (P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) x₁.link
      (P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi)).1
    (P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) x₁.link
      (P6T.keptN (P5J.At.sentAt Zp) x₁.link + mi)).2 = _
  rw [es]
  exact P5T.arrOf_is_num _ p.j p.t x₁.link mi p₀ hf (hk0.trans key)

/-- **THE MESSAGES WITH TWO SEGMENTS' MASK ROWS BEAR TWO NUMBERS IN THE WITNESS.** CONDITIONAL:
under the hypothesis h. -/
theorem maskNosApart_head : MaskNosApart h := by
  intro x₁ x₁' kM kM' hk hk' hm hm' e
  obtain ⟨Lk, mi, hl, hmi, e1⟩ := maskNo5_is_num h (hk := hk) hm
  obtain ⟨-, mi', -, -, e2⟩ := maskNo5_is_num h (hk := hk') hm'
  exact (h.toAtMg.num_apart hl hmi (e1.symm.trans (e.trans e2))).1

variable {h}

/-- **ANY TWO OF K5's LOTS AGREE.** CONDITIONAL: under the hypothesis h alone. -/
theorem k5Lots_agree_head {S : Sz} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : ℕ → MsgAddr → Option (ℕ × ℕ)} {heard : ℕ → MsgAddr → ℕ}
    {Z5 : ℕ → OnBytes.Attention.Plan → Seat5} {L L' : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (H : IsK5Lot h S rd seat heard Z5 L) (H' : IsK5Lot h S rd seat heard Z5 L') : Agree2 L L' :=
  k5Lots_agree (maskNosApart_head h) H H'

/-- **A LIST OF K5's LOTS AGREES IN ITSELF.** CONDITIONAL: under the hypothesis h alone. -/
theorem k5_msgsAgree_head {S : Sz} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : ℕ → MsgAddr → Option (ℕ × ℕ)} {heard : ℕ → MsgAddr → ℕ}
    {Z5 : ℕ → OnBytes.Attention.Plan → Seat5} {ml₅ : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    (hm : ∀ L ∈ ml₅, IsK5Lot h S rd seat heard Z5 L) : MsgsAgree ml₅ :=
  k5_msgsAgree (maskNosApart_head h) hm

/-- **WHAT IS LEFT OF "AGREE" FOR ONE OF K5's LOTS IS AGAINST THE OTHERS' LOTS ALONE.** CONDITIONAL:
under the hypothesis h alone. -/
theorem k5_agree_cut_head {S : Sz} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : ℕ → MsgAddr → Option (ℕ × ℕ)} {heard : ℕ → MsgAddr → ℕ}
    {Z5 : ℕ → OnBytes.Attention.Plan → Seat5}
    {ml₅ rest : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    (hm : ∀ L ∈ ml₅, IsK5Lot h S rd seat heard Z5 L) {L : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (hL : IsK5Lot h S rd seat heard Z5 L) : LotsAgree (ml₅ ++ rest) L ↔ LotsAgree rest L :=
  k5_agree_cut (maskNosApart_head h) hm hL

end ProofFile.Honest.K5

#print axioms P6T.key_of_call
#print axioms P6T.maskMsg_some
#print axioms P6T.isCall_congr
#print axioms P6T.maskMsg_congr
#print axioms P6T.maskSeatsB_congr
#print axioms P6T.maskSeats_gives
#print axioms P6T.maskSeats_written
#print axioms P6T.one_mask_written
#print axioms ProofFile.Honest.K5.maskSeats_head
#print axioms ProofFile.Honest.K5.maskNo5_is_num
#print axioms ProofFile.Honest.K5.maskNosApart_head
#print axioms ProofFile.Honest.K5.k5Lots_agree_head
#print axioms ProofFile.Honest.K5.k5_msgsAgree_head
#print axioms ProofFile.Honest.K5.k5_agree_cut_head
