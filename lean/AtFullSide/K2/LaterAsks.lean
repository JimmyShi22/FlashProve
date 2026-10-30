-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/LaterAsks.lean: the two later senders of a segment, as a code switch reads them: the
form LaterSenders (JoinSenders.lean) at the joined Script.

1. A segment's group has two members behind its first sending: message 0 of the link's "reads" and
   message 0 of its "digits". Each is sent by a job of the kind K1, and the switch that closes the
   segment lays that member anew from the stretch that it carries.
2. rowsR_of_asRow: K1.rowsR lays at a data d what it lays at d as the switch reads it, whole rows.
3. join_msg_any: the tie of a job of a fit list holds at every N.
4. later_public, later_carried: what the public tests of LaterFacts.lean give.
5. shared_at_job: SharedAsks at a job of a fit list, from facts on that job.
6. later_sender, later_senders: the end.

Limits. The head, the opening, the maker's return and hJ are hypotheses. hI and hR tie the reader
wit to the input and to the readers of the closing. hlen says that the challenges heard reach the
switch. The limits of LaterFacts.lean stand. The form stands at one run's coins and says what is
written where. The full size and the format's second hash function alone.
-/
import AtFullSide.K2.JoinSenders
import AtFullSide.K2.LaterFacts
import AtFullSide.K2.FillingsAtLinkOne
import AtFullSide.K2.HeardAtSwitches
import AtFullSide.K2.JoinFitFull
import AtFullSide.K2.LendAtPure
import AtFullSide.K2.MsgsAtLinkOne
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingLast
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtClosing
import Johnson.Desc.ProofFile.Honest.Thread.JoinAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (parL noL placeL)
open VerifiableInference.Desc.K2.Honest (Left)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (layoutFull)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3.Fit (seatsW seats_at_head first_at_head)
open OnBytes.SendSim.Seat (wJobs)
open ProofFile.Honest
open ProofFile.Honest.K1 (hin_msgs_of_agree)
open ProofFile.Honest.FirstThread (Others TreeLot JoinFit OwnMsgs Script byNo headJl joinMl joinPl joinQ
  joinTl join_tie_k1_fit k1Jobs byNo_at_head ofLots_ownMsgs)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open P5J (AtMgA CellsM F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open AtFullSide.K14 (rawAheadW rawSegW)

/-! ## 1 Rows at two data -/

/-- A disjunction whose first member is true. -/
theorem or_left_true {a b c : Bool} (h : a = true) : (a || b || c) = true := by
  subst h
  rfl

/-- The negation of what is false. -/
theorem not_of_false {a : Bool} (h : a = false) : (!a) = true := by
  subst h
  rfl

/-- A main entry over the extension field reads of the data the one element there. -/
theorem rowsR_mainE_data (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data data' : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride))
    (n r j : Nat)
    (hv : (match data n r j with
        | some (.inr x) => x
        | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
        | none => (0 : Cb.Gl.E)) =
      (match data' n r j with
        | some (.inr x) => x
        | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
        | none => (0 : Cb.Gl.E))) :
    (K1.rowsR P ride data c n).mainE r j = (K1.rowsR P ride data' c n).mainE r j := by
  simp only [K1.rowsR]
  split
  · rfl
  · split
    · rfl
    · exact hv

/-- Where the rows are over the extension field, the entries over the base field are 0. -/
theorem rowsR_mainF_over (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride)) {n : Nat}
    (hE : ((shapeAt P n).mainDeg == 3) = true) (r j : Nat) :
    (K1.rowsR P ride data c n).mainF r j = 0 := by
  simp only [K1.rowsR]
  split
  · rfl
  · rename_i hn
    exact absurd (or_left_true hE) hn

/-- Where the rows are over the base field, the entries over the extension field are 0. -/
theorem rowsR_mainE_under (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride)) {n : Nat}
    (hE : ((shapeAt P n).mainDeg == 3) = false) (r j : Nat) :
    (K1.rowsR P ride data c n).mainE r j = 0 := by
  simp only [K1.rowsR]
  split
  · rfl
  · rename_i hn
    exact absurd (or_left_true (not_of_false hE)) hn

/-- Over the extension field: an entry as a row takes it is what K1.rowsR reads there. -/
theorem asRow_true (o : Option (Cb.Gl.F ⊕ Cb.Gl.E)) :
    asRow true o = (match o with
      | some (.inr x) => x
      | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
      | none => (0 : Cb.Gl.E)) := by
  cases o with
  | none => exact zeroG_eq
  | some v =>
    cases v with
    | inl x => exact K1.asE_inl x
    | inr x => rfl

/-- **K1.rowsR lays at data what it lays at data', where data is data' as a row takes it**: whole
rows of the message n. -/
theorem rowsR_of_asRow {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option K1.Ride}
    {data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)}
    (data' : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) {c : Cs (K1.dueR P ride)} {n : Nat}
    (h : ∀ r j, data n r j = asShared (shapeAt P n)
      (fun r j => asRow ((shapeAt P n).mainDeg == 3) (data' n r j)) r j) :
    K1.rowsR P ride data c n = K1.rowsR P ride data' c n := by
  by_cases hE : ((shapeAt P n).mainDeg == 3) = true
  · refine rows_ext _ _ (funext fun r => funext fun j => ?_) (funext fun r => funext fun j => ?_)
      rfl rfl rfl rfl
    · refine rowsR_mainE_data P ride data data' c n r j ?_
      rw [h r j]
      unfold asShared
      rw [if_pos hE]
      show asRow ((shapeAt P n).mainDeg == 3) (data' n r j) = _
      rw [hE]
      exact asRow_true _
    · rw [rowsR_mainF_over P ride data c hE r j, rowsR_mainF_over P ride data' c hE r j]
  · have h0 : ((shapeAt P n).mainDeg == 3) = false := Bool.eq_false_iff.2 hE
    refine rows_ext _ _ (funext fun r => funext fun j => ?_) (funext fun r => funext fun j => ?_)
      rfl rfl rfl rfl
    · rw [rowsR_mainE_under P ride data c h0 r j, rowsR_mainE_under P ride data' c h0 r j]
    · refine rowsR_mainF_data P ride data data' c n r j ?_
      rw [h r j]
      unfold asShared
      rw [if_neg hE]
      show (asRow ((shapeAt P n).mainDeg == 3) (data' n r j)).c0 = _
      rw [h0]
      exact asRow_c0 _

/-- **The closing's own data at a message of another kind's sender** are that sender's filling, as a
row takes it. -/
theorem own_is_row (S₀ : Sz) (Zp : ProofFile.Pub) (G : ProofFile.Ground) (x : ProofFile.Inst) (R : Readers)
    {segs : List SegmentPub} {p : SwitchPlace} {hd : List Fmt.Drawn} {s i : Nat} {a : MsgAddr}
    {b : Bool} (ha : p.addrs s i = some a)
    (hb : (((((segs[s]?).map fun (y : SegmentPub) => y.ownShapes (s == 0)).getD []).getD i
      {}).mainDeg == 3) = b)
    (hk : a.sender.place.kind ≠ .K2) (r j : Nat) :
    lotOwn segs p (withSwitchData S₀ (K1.lotData S₀) Zp G x) R hd s i r j =
      asRow b ((K1.lotData S₀ Zp G x).at_ R hd a r j) := by
  show ownBy _ _ p.addrs _ _ s i r j = _
  unfold ownBy
  rw [ha]
  show asRow (((((segs[s]?).map fun (y : SegmentPub) => y.ownShapes (s == 0)).getD []).getD i
    {}).mainDeg == 3) _ = _
  rw [hb, (with_other_kind S₀ (K1.lotData S₀) Zp G x a hk).2.2.2.2.1 R hd r j]

/-! ## 2 The tie at every N -/

section Tie
variable {Bk : ProverCoinCounts} {Wl Xi X Cells Tok : Type} {bs : List (Block S ProofFile.Cl)} {front : Nat}
  {arr : Nat → Nat → Nat} {seats : List (Nat × Nat)} {wit : Wl → K1.PlaceIn Xi} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xi) X)} {O : Others Bk Wl}

/-- **K1's tie on a message at a fit list, at every N.** join_tie_k1_fit states it at the job's own
number of challenges; a lot's text does not read N. -/
theorem join_msg_any (F : JoinFit bs front arr seats wit own₀ jobs O) (cells : Wl → Cells)
    (tok : Wl → Tok) (Vd : Wl → Prop) (N : Nat) {x : Nat × K1.SendJob (K1.PlaceIn Xi) X}
    (hx : x ∈ jobs) {n : Nat} (hn : n < x.2.P.sent.size) :
    OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N
      (arr (K1.seatAtMember bs x.1 x.2.P n).1 (K1.seatAtMember bs x.1 x.2.P n).2)
      (front + roundsTo bs x.1) (K1.msgTxt 0 wit x.2 own₀ n) := by
  have hin := hin_msgs_of_agree (bs := bs) (front := front) (arr := arr) (wit := wit) (own₀ := own₀)
    (jobs := jobs) (ml := joinMl bs front arr wit own₀ jobs O)
    (fun _ hL => List.mem_append.2 (Or.inl hL)) F.msgs hx
  have hL := hin ⟨arr (K1.seatAtMember bs x.1 x.2.P n).1 (K1.seatAtMember bs x.1 x.2.P n).2,
    front + roundsTo bs x.1, K1.msgTxt 0 wit x.2 own₀ n⟩
    (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  exact ofLots_ownMsgs bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) hL.1 hL.2 Vd N

end Tie

/-! ## 3 What the public tests give -/

/-- What the first test's yes gives. -/
theorem later_public {p : SwitchPlace} (hp : p ∈ placesW) {Sg : SegmentPub}
    (hS : segsW[p.link - 1]? = some Sg) {q : Nat} (hq : q < 2) :
    p.link - 1 < 25 ∧
    p.addrs (p.link - 1) (laterOwnNo (p.link - 1) Sg q) =
      some (laterAddr (p.link - 1) (q == 1) 0) ∧
    ((Sg.ownShapes (p.link - 1 == 0)).getD (laterOwnNo (p.link - 1) Sg q) {}).mainDeg =
      (shapeAt (placeL (p.link - 1) (q == 1)) 0).mainDeg ∧
    (placeL (p.link - 1) (q == 1)).place.kind ≠ .K2 ∧
    0 < (placeL (p.link - 1) (q == 1)).sent.size ∧
    heardAll (seatsW "U3") (seatsW "BZ") layoutFull heardRngW
      (laterAddr (p.link - 1) (q == 1) 0) ≤ roundsCutW (noL (p.link - 1) (q == 1)) ∧
    roundsCutW (noL (p.link - 1) (q == 1)) ≤ roundsCutW (switchNo p) := by
  have t : laterOk 0 0 p q = true :=
    List.all_eq_true.1 (List.all_eq_true.1 laterW.1 p hp) q (List.mem_range.2 hq)
  unfold laterOk at t
  rw [hS] at t
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩ := t
  exact ⟨t1, t2, t3, t4, t5, t6, t7⟩

/-- What the second test's yes gives. -/
theorem later_carried {p : SwitchPlace} (hp : p ∈ placesW) {Sg : SegmentPub}
    (hS : segsW[p.link - 1]? = some Sg) {q : Nat} (hq : q < 2) :
    entryRunIs ((rawAheadW.filter fun e => e.spender == ⟨p.place, 0⟩).filter fun e => !e.once)
      (((segsW.take (p.link - 1)).map (·.messages)).sum + ((Sg.sent.headD #[]).size - 1) + 1 + q)
      ⟨(placeL (p.link - 1) (q == 1)).place, 0⟩
      (K1.startR (placeL (p.link - 1) (q == 1)) (K1.rideOf none) 0)
      (K1.dueMsg (placeL (p.link - 1) (q == 1)).codes (shapeAt (placeL (p.link - 1) (q == 1)) 0)
        (K1.rideOf none 0)) = true := by
  have t : laterCarried rawAheadW 0 p = true := List.all_eq_true.1 laterCarriedW p hp
  unfold laterCarried at t
  rw [hS] at t
  simp only [Option.any_some] at t
  exact List.all_eq_true.1 t q (List.mem_range.2 hq)

/-! ## 4 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Tr X₀ X Y X₂ Cells Tok : Type}

/-- How far the joined filling has heard, by the written seats. -/
theorem heard_at_later (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (S₀ : Sz) (x : ProofFile.Inst) (a : MsgAddr) (b : Nat)
    (t : heardAll (seatsW "U3") (seatsW "BZ") layoutFull heardRngW a ≤ b) :
    (withSwitchData S₀ (K1.lotData S₀) Zp Bs.G₀ x).heardAt a ≤ b := by
  refine Nat.le_trans (heard_le S₀ Zp Bs.G₀ x a) ?_
  rw [seats_at_head h O.blank "U3", seats_at_head h O.blank "BZ",
    (first_at_head h O.blank).2.2, roundNumbers_entries, entries_at_head h.toAtMg O]
  exact t

/-- **The later job stands in the joined list at its number.** -/
theorem later_job_mem (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) {m : Nat} (hm : m < 25)
    (d : Bool) :
    (noL m d, headJl (X := Y) Zp Bs.G₀ no Dt m d) ∈
      byNo cF.blocksInOrder (K1.lotJobs (X := Y) no Dt Zp Bs.G₀ ++ wJobs (X := Y) no Dd Zp Bs.G₀) := by
  show _ ∈ byNo cF.blocksInOrder (k1Jobs (X := Y) no Dt Dd Zp Bs.G₀)
  rw [byNo_at_head h O no Dt Dd]
  exact K1.mem_k1MembersW.2 (Or.inl (K1.mem_k1Members.2 (Or.inr ⟨m, hm, d, rfl⟩)))

/-- **SharedAsks at a job of a fit list.** The number b bears the job J. hJd: its data read the lot's
filling at its own address. he, t1, t2, t3: the book's entry. hdat: the closing's own data are that
filling as a row takes it. hf1, hf2: the filling has heard no more than stands in front of the job,
and that many challenges have been heard. -/
theorem shared_at_job {Bk : ProverCoinCounts} {bs : List (Block S ProofFile.Cl)} {seats : List (Nat × Nat)}
    {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst} {own₀ : Y}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn ProofFile.Inst) Y)}
    {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (F : JoinFit bs 0 (P5J.At.arr Zp) seats wit own₀ jobs Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → Cells) (tok : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat) (w : Local W₀ Rc ProofFile.Inst Tr)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (hI : (wit w).x = w.x)
    (hR : (wit w).R = readers w) (S₀ : Sz) (G : ProofFile.Ground) {b n ix : Nat}
    {P₀ : VerifiableInference.Desc.K1.Par} {ρ₀ : Nat → Option K1.Ride}
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) Y} (hx : (b, J) ∈ jobs) (hP : P₀ = J.P)
    (hρ : ρ₀ = J.ride)
    (hJd : ∀ (v : K1.PlaceIn ProofFile.Inst) (fr : Front Y) (n r j : Nat), J.data v fr n r j =
      (K1.lotData S₀ Zp G v.x).at_ v.R fr.heard ⟨⟨J.P.place, 0⟩, n⟩ r j)
    (hn : n < J.P.sent.size) {p : SwitchPlace} {e : Ahead}
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[ix]? = some e)
    (t1 : e.owner = ⟨J.P.place, 0⟩) (t2 : e.start = K1.startR J.P J.ride n)
    (t3 : e.count = K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n)) (k : Coins Bk)
    {dat : Nat → Nat → Cb.Gl.E} {hd : List Fmt.Drawn} (ds : List Fmt.Drawn)
    (hdat : dat = fun r j => asRow ((shapeAt J.P n).mainDeg == 3)
      ((K1.lotData S₀ Zp G w.x).at_ (readers w) hd ⟨⟨J.P.place, 0⟩, n⟩ r j))
    (hf1 : (K1.lotData S₀ Zp G w.x).heardAt ⟨⟨J.P.place, 0⟩, n⟩ ≤ 0 + roundsTo bs b)
    (hf2 : 0 + roundsTo bs b ≤ hd.length) :
    ∃ (cs : Cs (K1.dueR J.P J.ride)) (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)),
      SharedAsks Zp bs P₀ ρ₀ b n ix 0 p k dat
        (joinQ bs 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd N w (hd ++ ds) wit J own₀ cs e
        dataK (0 + roundsTo bs b) := by
  subst hP hρ
  have hco : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = K1.dueR J.P J.ride := F.coins (b, J) hx
  have hcov : K1.bookCovers Bk 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true := by
    unfold K1.bookCovers
    rw [hco]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨cs, hcut⟩ := Option.isSome_iff_exists.1
    ((K1.lentCut_isSome k 0 (by omega) ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride)).trans hcov)
  have ht : ((hd ++ ds).take (0 + roundsTo bs b)).take
      ((K1.lotData S₀ Zp G w.x).heardAt ⟨⟨J.P.place, 0⟩, n⟩) =
      hd.take ((K1.lotData S₀ Zp G w.x).heardAt ⟨⟨J.P.place, 0⟩, n⟩) := by
    rw [List.take_take, Nat.min_eq_left hf1]
    exact List.take_append_of_le_length (Nat.le_trans hf1 hf2)
  refine ⟨cs, fun n' => asShared (shapeAt J.P n') dat, rfl, rfl, hcut, he, t1, t2, t3, rfl, ?_, ?_, ?_⟩
  · exact join_msg_any (x := (b, J)) F cells tok Vd N hx hn
  · exact (join_tie_k1_fit F cells tok Vd hx).2 n hn
  · refine rowsR_of_asRow (J.data (wit w)
      { heard := (hd ++ ds).take (0 + roundsTo bs b), own := own₀, seen := .bare [] }) fun r j => ?_
    have e₁ : (fun r j => asRow ((shapeAt J.P n).mainDeg == 3) (J.data (wit w)
        { heard := (hd ++ ds).take (0 + roundsTo bs b), own := own₀, seen := .bare [] } n r j)) =
        dat := by
      rw [hdat]
      funext r j
      rw [hJd, hI, hR]
      exact congrArg (asRow _) (at_of_take _ _ _ ht r j)
    exact congrArg (fun f => asShared (shapeAt J.P n) f r j) e₁.symm

/-- h, O, hA, hJ, hO, hI, hR, hp AND hlen ARE PREMISES. **ONE LATER SENDER OF THE SEGMENT THAT THE
SWITCH p CLOSES, AT THE JOINED SCRIPT.** -/
theorem later_sender (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hI : (wit w).x = w.x) (hR : (wit w).R = readers w) {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zp Bs.G₀) (k : Coins A.B)
    (hd ds : List Fmt.Drawn) (hlen : roundsTo cF.blocksInOrder (switchNo p) ≤ hd.length)
    {kk : Nat → Except String ProofFile.Honest.K2.Stretch}
    {y' : Option (Left × List OnBytes.OracleShape) × Nat} {Sg : SegmentPub}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ w.x)
      (readers w) hd) hd kk ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none = .ok y')
    (hS : (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg) {q : Nat} (hq : q < 2) :
    SharedAt Zp cF.blocksInOrder (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                          wJobs (X := Y) no Dd Zp Bs.G₀))
      (parL Zp Bs.G₀ (p.link - 1) (q == 1)) (K1.rideOf none) (noL (p.link - 1) (q == 1)) 0
      (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) p k
      (lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ w.x) (readers w) hd (0 + (p.link - 1))
          ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
      (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth)
      Vd N w (hd ++ ds) wit own₀ := by
  have hB := pure_book_written h hA
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hsegs := segments_at_head h.toAtMg O
  have hSW := hS
  rw [hsegs] at hSW
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := later_public hpW hSW hq
  -- the closing's count, and that a fold stands in front
  have e4 : y'.2 = 0 + (((segmentsOf Zp Bs.G₀).take (p.link - 1)).map (·.messages)).sum :=
    closingFrom_next freshTable _ _ _ _ 0 0 none y' hy'
  have hlt : p.link - 1 < (segmentsOf Zp Bs.G₀).length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hS
    cases hS
  have e5 := closingFrom_isSome freshTable _ _ _ _ 0 0 none y' hy'
  have hIdx : laterOwnNo (p.link - 1) Sg q =
      ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q) := by
    unfold laterOwnNo
    by_cases hz : p.link - 1 = 0
    · rw [hz] at e5
      have e6 : y'.1.isSome = false := e5
      have hs : (y'.1.map (·.1)).isSome = false := by
        cases hv : y'.1 with
        | none => rfl
        | some v =>
          simp [hv] at e6
      have hn : ¬ (y'.1.map (·.1)).isSome = true := fun hc => by
        rw [hs] at hc
        cases hc
      rw [if_pos hz, if_neg hn]
    · have hne : ((segmentsOf Zp Bs.G₀).take (p.link - 1)).isEmpty = false := by
        cases hc : (segmentsOf Zp Bs.G₀).take (p.link - 1) with
        | nil =>
          have hl := congrArg List.length hc
          rw [List.length_take, List.length_nil] at hl
          omega
        | cons a l => rfl
      rw [hne] at e5
      have e6 : y'.1.isSome = true := e5
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 e6
      have hs : (y'.1.map (·.1)).isSome = true := by
        simp [hv]
      rw [if_neg hz, if_pos hs]
  rw [hIdx] at t2 t3
  -- the job
  obtain ⟨J, hJe⟩ : ∃ J : K1.SendJob (K1.PlaceIn ProofFile.Inst) Y,
      J = headJl Zp Bs.G₀ no (K1.lotData Sz.ref) (p.link - 1) (q == 1) := ⟨_, rfl⟩
  have hx : (noL (p.link - 1) (q == 1), J) ∈
      byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀) := by
    subst hJe
    exact later_job_mem h O no (K1.lotData Sz.ref) Dd t1 (q == 1)
  have hP : parL Zp Bs.G₀ (p.link - 1) (q == 1) = J.P := by
    subst hJe
    exact K1.parL_later Zp Bs.G₀ _ _
  have hρ : K1.rideOf none = J.ride := by
    subst hJe
    rfl
  have hJd : ∀ (v : K1.PlaceIn ProofFile.Inst) (fr : Front Y) (n r j : Nat), J.data v fr n r j =
      (K1.lotData Sz.ref Zp Bs.G₀ v.x).at_ v.R fr.heard ⟨⟨J.P.place, 0⟩, n⟩ r j := by
    subst hJe
    intro v fr n r j
    rfl
  have hPw : J.P = placeL (p.link - 1) (q == 1) := hP.symm.trans (K1.parL_written h O _ _)
  have hn : 0 < J.P.sent.size := by
    rw [hPw]
    exact t5
  have hk : J.P.place.kind ≠ .K2 := by
    rw [hPw]
    exact t4
  -- the book's entry
  have eA : A.B.ahead = rawAheadW := ahead_at_book h hB
  have tc := later_carried hpW hSW hq
  have hix : y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q =
      ((segsW.take (p.link - 1)).map (·.messages)).sum + ((Sg.sent.headD #[]).size - 1) + 1 + q := by
    rw [e4, hsegs, Nat.zero_add]
  rw [← eA, ← hix] at tc
  obtain ⟨e, he, u1, u2, u3⟩ := entryRunIs_gives tc
  rw [← hPw] at u1 u2 u3
  rw [hρ] at u2 u3
  -- the data
  have ha : p.addrs (0 + (p.link - 1))
      ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q) = some ⟨⟨J.P.place, 0⟩, 0⟩ := by
    rw [Nat.zero_add, hPw]
    exact t2
  have hb : ((((((segmentsOf Zp Bs.G₀)[0 + (p.link - 1)]?).map
      fun (y : SegmentPub) => y.ownShapes (0 + (p.link - 1) == 0)).getD []).getD
      ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q) {}).mainDeg == 3) =
      ((shapeAt J.P 0).mainDeg == 3) := by
    rw [hsegs, Nat.zero_add, hSW]
    show (((Sg.ownShapes (p.link - 1 == 0)).getD
      ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q) {}).mainDeg == 3) = _
    rw [t3, hPw]
  have hdat : lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ w.x) (readers w) hd (0 + (p.link - 1))
      ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q) =
      fun r j => asRow ((shapeAt J.P 0).mainDeg == 3)
        ((K1.lotData Sz.ref Zp Bs.G₀ w.x).at_ (readers w) hd ⟨⟨J.P.place, 0⟩, 0⟩ r j) :=
    funext fun r => funext fun j => own_is_row Sz.ref Zp Bs.G₀ w.x (readers w) ha hb hk r j
  have hf1 : (K1.lotData Sz.ref Zp Bs.G₀ w.x).heardAt ⟨⟨J.P.place, 0⟩, 0⟩ ≤
      0 + roundsTo cF.blocksInOrder (noL (p.link - 1) (q == 1)) := by
    rw [← (with_other_kind Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ w.x ⟨⟨J.P.place, 0⟩, 0⟩ hk).1]
    refine heard_at_later h O Sz.ref w.x _ _ ?_
    rw [Nat.zero_add, roundsTo_at_head h O, hPw]
    exact t6
  have hf2 : 0 + roundsTo cF.blocksInOrder (noL (p.link - 1) (q == 1)) ≤ hd.length := by
    rw [Nat.zero_add, roundsTo_at_head h O]
    exact Nat.le_trans t7 (by
      rw [← roundsTo_at_head h O (switchNo p)]
      exact hlen)
  -- the list is fit
  have F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth := by
    subst hO
    exact joinFit_full h O hA no (K1.lotData Sz.ref) Dd 0 wit own₀ _ readers rest ch Jt hJ own₂ n₀
      ok codes sh sh₁ rest₂
  obtain ⟨cs, dataK, B⟩ := shared_at_job (n := 0) F cellsQ tokQ Vd N w readers hI hR Sz.ref Bs.G₀ hx hP
    hρ hJd hn he u1 u2 u3 k ds hdat hf1 hf2
  unfold SharedAt
  exact ⟨(noL (p.link - 1) (q == 1), J), hx, rfl, cs, e, dataK, B⟩

/-- h, O, hA, hJ, hO, hI, hR, hp AND hlen ARE PREMISES. **THE THIRD LIMB OF JoinAsks, WITH THE JOBS
NAMED, AT THE JOINED SCRIPT.** -/
theorem later_senders (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hI : (wit w).x = w.x) (hR : (wit w).R = readers w) {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zp Bs.G₀) (k : Coins A.B)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hd ds : List Fmt.Drawn)
    (hlen : roundsTo cF.blocksInOrder (switchNo p) ≤ hd.length) :
    LaterSenders Zp Bs cF (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀))
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers p k c
      (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth)
      Vd w hd ds wit own₀ := by
  intro p₀ _ _ _ y' Sg hy hS q hq
  exact later_sender h O hA no Dd cellsQ tokQ wit own₀ readers rest ch Jt hJ own₂ n₀ ok codes sh sh₁
    rest₂ Oth hO Vd _ w hI hR hp k hd ds hlen hy hS hq

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.rowsR_of_asRow
#print axioms AtFullSide.K2.own_is_row
#print axioms AtFullSide.K2.join_msg_any
#print axioms AtFullSide.K2.later_public
#print axioms AtFullSide.K2.later_carried
#print axioms AtFullSide.K2.heard_at_later
#print axioms AtFullSide.K2.later_job_mem
#print axioms AtFullSide.K2.shared_at_job
#print axioms AtFullSide.K2.later_sender
#print axioms AtFullSide.K2.later_senders
