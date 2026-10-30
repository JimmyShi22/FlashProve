-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/FiveAtScript.lean: the closing of a segment (K10): its five statements at every member of the kind, at the first chain's thread with the script of the base
prover (`firstScriptAt`, AtFullSide/K1/FirstScript.lean), at the base filling, with the letters of the records at their values.

  `partsAt`, `threadAt`, `readersAt`, `rowsAt`   the values
  `last_written`      each written place of the code switch sends more messages than its kept copies and one
  `tie_switch_at`, `fresh_switch_at`, `tie_later_at`, `tie_open_at`, `fresh_open_at`   the records at these values
  `threeLeft_switch_at`, `threeLeft_zero_at`   `ThreeLeftFirst` at a segment into which a code switch leads, and at the first segment
  **`kindTen_five_of_left`**, **`kindTen_five_at_script`**   the five statements at every member of the kind

WHAT STAYS NAMED. Closes A, the public test on the closings; hCopy, the message of a kept copy.

Limits. The head at the return and the maker's return are premises. That a run stands at a border is not shown. No property of a prover or a protocol is proved here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchThreeLeft
import Johnson.Desc.ProofFile.Honest.K10.Pay.KindTenPlaces
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchRideAt
import AtFullSide.K10.MadePaid
import AtFullSide.K10.ShrHead
import AtFullSide.K10.XchAtBookFirst
import AtFullSide.K10.XchGJobs
import AtFullSide.K10.ScriptSwitch
import AtFullSide.K10.ScriptShared
import AtFullSide.K10.ScriptRows
import AtFullSide.K10.ScriptVars
import AtFullSide.K10.ScriptHeard
import AtFullSide.K10.XchHeardAt
import AtFullSide.K1.FirstScript
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K1 (noL)
open OnBytes.HonestTrace (Sz)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread ProofFile.Honest.K10
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.K1 (firstScriptAt witB jobTwoAt jobLaterAt seatAtMember readersB)
open ProofFile.Honest.K2 (SwitchPlace switchSent segmentsOf switchPlaces lotClosingAt switchMsgOff switchPadTxt firstSender)
open ProofFile.Honest.K2.Law (placesW)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Each written place of the code switch sends more messages than its kept copies and one. -/
theorem last_written : (placesW.all fun p =>
    decide (p.sizes.target.kept.size + 1 < (switchSent p.sizes p.others).size)) = true := by
  decide +kernel

/-- The place that the written list finds at a link is of that link. -/
theorem link_of_find {l : Nat} {pS : SwitchPlace} (h : placesW.find? (·.link == l) = some pS) : pS.link = l :=
  beq_iff_eq.1 (List.find?_some (p := fun x : SwitchPlace => x.link == l) h)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- The thread's two parts at the base prover's script. -/
abbrev partsAt (head : HeadAtReturn files A) (numbers : FallNumbers) : FirstThreadParts A :=
  ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩

/-- The thread. -/
abbrev threadAt (head : HeadAtReturn files A) (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) :=
  firstThread head (partsAt head numbers) input

/-- The readers. -/
abbrev readersAt (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Readers :=
  fun v => ⟨v.trace, matrixInput.weights A.Z v.w₀, v.rc⟩

/-- The rows' data. -/
abbrev rowsAt (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) : RowDataOf ProofFile.Inst := widerRows Sz.ref A.Z A.G

section
variable (head : HeadAtReturn files A)
  (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
  (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

include made in
/-- **The five statements at every member of the kind**, from the three premises at each closing. -/
theorem kindTen_five_of_left (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat} {member : Block TS ProofFile.Cl}
    (atNumber : head.firstChain.blocksInOrder[b]? = some member) (ofTheKind : member.place.kind = .K10)
    (Left : ∀ l, l < 25 → ∀ p Qc blk, Tied head.firstChain A.Z l p Qc blk →
      ThreeLeftFirst matrixInput Sz.ref head (partsAt head numbers) input Said l Qc blk) :
    FiveAtBorder (threadAt head numbers input) Said fall b := by
  obtain ⟨l, hl, rfl⟩ := kindTen_only_at_borders head.head atNumber ofTheKind
  exact k10_five_first matrixInput OnBytes.secondHashFunction Sz.ref openHonest made head _ input l hl hSaid fall (Left l hl)

variable {l : Nat} {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}

include made in
/-- Rows are laid at every valid input. -/
theorem rows_laid_at (hC : Closes A) {pS : SwitchPlace} (hP : pS ∈ switchPlaces A.Z A.G) :
    ∀ c v hd, (threadAt head numbers input).valid v →
      ∃ V, K2.switchRowsLaid (rowsAt A) (readersAt A) (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS c v hd = .ok V :=
  fun c v hd hv => rows_laid_of head.head made hC hP c v hv.2.1 hd

include made in
/-- **The record on the switch's sending**, at these values. -/
theorem tie_switch_at (Td : Tied head.firstChain A.Z l pw Qc blk) (h1 : 1 ≤ l) (hC : Closes A) {pS : SwitchPlace}
    (hpw : placesW.find? (·.link == l) = some pS)
    (hCopy : ∀ n, n + 1 < (switchSent pS.sizes pS.others).size → firstSender pS n = false →
      OwnMsgs (partsAt head numbers).script (threadAt head numbers input).valid (fxAt head.firstChain pS)
        (P5J.At.arr A.Z (seatSw A.Z pS n).1 (seatSw A.Z pS n).2) (fxAt head.firstChain pS)
        (switchMsgOff 0 (rowsAt A) (readersAt A) (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS n)) :
    TieBySwitch (threadAt head numbers input) (partsAt head numbers).script A.Z (readersAt A) (rowsAt A) A.G Said l Qc blk
      (threadAt head numbers input).valid A.G.first.layout (segmentsOf A.Z A.G) pS (fxAt head.firstChain pS)
      (fxAt head.firstChain pS) (seatSw A.Z pS) := by
  have hP : pS ∈ switchPlaces A.Z A.G := by
    rw [places_first head]
    exact List.mem_of_find?_eq_some hpw
  have hlink : pS.link = l := link_of_find hpw
  have hD1 : ∀ (ξ : ProofFile.Inst) (i m : Nat) (a : MsgAddr), pS.addrs i m = some a → i < l →
      (rowsAt A ξ).heardAt a ≤ fxAt head.firstChain pS := by
    obtain ⟨Bs, base, O⟩ := head.head.laid.opened
    have eG : A.G = Bs.G₀ := (base_ground_atPure O.made made rfl).symm
    intro ξ i m a hpa hi
    have hP' : pS ∈ switchPlaces A.Z Bs.G₀ := eG ▸ hP
    have e := heard_at_switch_head head.head O Sz.ref hP' hlink ξ i m a hpa hi
    show (widerRows Sz.ref A.Z A.G ξ).heardAt a ≤ _
    rw [eG]
    exact e
  refine tieBySwitch_head head.head A.H _ _ _ _ _ _ _ _ _ _ input _ _ _ Said Td h1 (segments_first head) hP hpw _ (Nat.le_refl _)
    ?_ ?_ (tie_switch_first head Td hP hlink) (front_switch_first head Td hP hlink) (handed_first head hP)
    (rows_laid_at head made numbers input hC hP) hD1 fun ξ m hm => heard_zero_first head.head made hP ξ m hm
  · intro n hn
    cases hf : firstSender pS n with
    | false => exact hCopy n hn hf
    | true =>
      obtain ⟨qs, -, e1, -, -, -⟩ := seat_of_switch head.head made hP (by omega : n < _)
      have es : seatSw A.Z pS n = (qs.j, qs.t) := by
        unfold seatSw
        rw [e1]
        rfl
      rw [es]
      exact msgs_of_switch head.head made _ _ hP (by omega) hf e1
  · intro n hn
    obtain ⟨qs, -, e1, -, -, -⟩ := seat_of_switch head.head made hP (by omega : n < _)
    have es : seatSw A.Z pS n = (qs.j, qs.t) := by
      unfold seatSw
      rw [e1]
      rfl
    rw [es]
    exact pads_of_switch head.head made _ hP (by omega) e1

include made in
/-- **The record on the fresh mask at a code switch**, at these values. -/
theorem fresh_switch_at (Td : Tied head.firstChain A.Z l pw Qc blk) (h1 : 1 ≤ l) (hC : Closes A) {pS : SwitchPlace}
    (hpw : placesW.find? (·.link == l) = some pS) :
    FreshBySwitch (threadAt head numbers input) (partsAt head numbers).script A.Z (readersAt A) (rowsAt A) Said l Qc blk
      (threadAt head numbers input).valid (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS (fxAt head.firstChain pS)
      (fxAt head.firstChain pS) (seatSw A.Z pS ((switchSent pS.sizes pS.others).size - 1)).1
      (seatSw A.Z pS ((switchSent pS.sizes pS.others).size - 1)).2 := by
  have hmem : pS ∈ placesW := List.mem_of_find?_eq_some hpw
  have hP : pS ∈ switchPlaces A.Z A.G := by
    rw [places_first head]
    exact hmem
  have hlink : pS.link = l := link_of_find hpw
  have hlast : pS.sizes.target.kept.size + 1 < (switchSent pS.sizes pS.others).size :=
    of_decide_eq_true (List.all_eq_true.1 last_written pS hmem)
  have hn : (switchSent pS.sizes pS.others).size - 1 < (switchSent pS.sizes pS.others).size := by omega
  obtain ⟨qs, -, e1, -, -, -⟩ := seat_of_switch head.head made hP hn
  have es : seatSw A.Z pS ((switchSent pS.sizes pS.others).size - 1) = (qs.j, qs.t) := by
    unfold seatSw
    rw [e1]
    rfl
  refine freshBySwitch_head head.head A.H _ _ _ _ _ _ _ _ _ _ input _ _ A.G Said Td h1 hpw _ (Nat.le_refl _)
    (vars_of_tied head.head Td hpw) ?_ ?_ (fresh_switch_first head Td hP hlink) (handed_first head hP)
    (rows_laid_at head made numbers input hC hP)
  · rw [es]
    exact msgs_of_switch head.head made _ _ hP hn (first_last pS hlast) e1
  · rw [es]
    exact pads_of_switch head.head made _ hP hn e1

include made in
/-- **The record on a later moment's sending**, at these values. -/
theorem tie_later_at (Td : Tied head.firstChain A.Z l pw Qc blk) (d : Bool) {c lo : Nat} (hpos : shrPosLater l = some c)
    (hlo : lo = c + (if d then 1 else 0))
    (book : ∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum + (lo + n)]? = some e ∧
      e.owner = ⟨(jobLaterAt Sz.ref A.Z A.G l d).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobLaterAt Sz.ref A.Z A.G l d).P (jobLaterAt Sz.ref A.Z A.G l d).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobLaterAt Sz.ref A.Z A.G l d).P (jobLaterAt Sz.ref A.Z A.G l d).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobLaterAt Sz.ref A.Z A.G l d).P (jobLaterAt Sz.ref A.Z A.G l d).ride).e) :
    TieByShared (threadAt head numbers input) (partsAt head numbers).script A.Z (readersAt A) (rowsAt A) A.G Said l Qc blk
      (threadAt head numbers input).valid (witB matrixInput A.Z) (jobLaterAt Sz.ref A.Z A.G l d) ()
      (0 + roundsTo head.firstChain.blocksInOrder (noL l d)) (0 + roundsTo head.firstChain.blocksInOrder (noL l d)) lo 1
      (seatAtMember head.firstChain.blocksInOrder (noL l d) (jobLaterAt Sz.ref A.Z A.G l d).P) := by
  have hblk : head.firstChain.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt head.head (List.getElem?_eq_some_iff.1 hblk).1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  obtain ⟨hpos0, hpub⟩ := public_later (S := Sz.ref) head.head made hl d
  have hn1 : ∀ n, n < 1 → n < (jobLaterAt Sz.ref A.Z A.G l d).P.sent.size := fun n hn => by omega
  refine tieByShared_later_head head.head A.H _ _ _ _ _ _ _ _ _ _ input _ _ _ Said Td (segments_first head)
    (first_params head).1 (first_params head).2 _ d _ _ (by cases d <;> rfl) () hpos hlo
    (fun n hn => (ties_of_later head.head made _ hl d (hn1 n hn)).1)
    (fun n hn => (ties_of_later head.head made _ hl d (hn1 n hn)).2) book
    (fun n hn => (hpub n (hn1 n hn)).1) (fun n hn => (hpub n (hn1 n hn)).2.1) (fun n hn => (hpub n (hn1 n hn)).2.2)
    (later_cut_first head Sz.ref hl d) ?_
  intro k s m En ds y cols s' St n hn ca a nn hL
  exact data_job_later head.head made hl d hQ hpos hlo (step_heard_le rfl St (shr_noL_le l d)) hn ca a nn hL

include made in
/-- **The record on the first segment's opening**, messages 0, 1, 2, at these values. -/
theorem tie_open_at (Td : Tied head.firstChain A.Z 0 pw Qc blk) :
    TieByShared (threadAt head numbers input) (partsAt head numbers).script A.Z (readersAt A) (rowsAt A) A.G Said 0 Qc blk
      (threadAt head numbers input).valid (witB matrixInput A.Z) (jobTwoAt Sz.ref A.Z A.G) ()
      (0 + roundsTo head.firstChain.blocksInOrder 2) (0 + roundsTo head.firstChain.blocksInOrder 2) 0 3
      (seatAtMember head.firstChain.blocksInOrder 2 (jobTwoAt Sz.ref A.Z A.G).P) := by
  have hQ : Qc.link = 0 := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hsz : 3 < (jobTwoAt Sz.ref A.Z A.G).P.sent.size := by
    rw [plan_two head.head made]
    decide +kernel
  refine tieByShared_open_head head.head A.H _ _ _ _ _ _ _ _ _ _ input _ _ _ Said Td (segments_first head)
    (first_params head).1 (first_params head).2 _ _ _ rfl ()
    (fun n hn => (ties_of_opening head.head made _ (by omega)).1)
    (fun n hn => (ties_of_opening head.head made _ (by omega)).2) (tie_two_first head Td Sz.ref rfl)
    (fun n hn => (public_opening head.head made hn).1) (fun n hn => (public_opening head.head made hn).2.1)
    (fun n hn => (public_opening head.head made hn).2.2) (two_cut_first head Sz.ref) ?_
  intro k s m En ds y cols s' St n hn ca a nn hL
  exact data_job_open head.head made hQ (step_heard_le rfl St (by decide)) hn ca a nn hL

include made in
/-- **The record on the first segment's fresh mask**, at these values. -/
theorem fresh_open_at (Td : Tied head.firstChain A.Z 0 pw Qc blk) :
    FreshByShared (threadAt head numbers input) (partsAt head numbers).script A.Z Said 0 Qc blk
      (threadAt head numbers input).valid (witB matrixInput A.Z) (jobTwoAt Sz.ref A.Z A.G) ()
      (0 + roundsTo head.firstChain.blocksInOrder 2) (0 + roundsTo head.firstChain.blocksInOrder 2) 3
      (seatAtMember head.firstChain.blocksInOrder 2 (jobTwoAt Sz.ref A.Z A.G).P 3).1
      (seatAtMember head.firstChain.blocksInOrder 2 (jobTwoAt Sz.ref A.Z A.G).P 3).2 := by
  have hsz : 3 < (jobTwoAt Sz.ref A.Z A.G).P.sent.size := by
    rw [plan_two head.head made]
    decide +kernel
  have hk := (zero_of_tied head.head Td).1
  have hF := fresh_opening (S := Sz.ref) head.head made
  exact freshByShared_head head.head A.H _ _ _ _ _ _ _ _ _ _ input Said Td (first_params head).1 (first_params head).2 _ _ _ rfl ()
    (ties_of_opening head.head made _ hsz).1 (ties_of_opening head.head made _ hsz).2 (fresh_two_first head Td Sz.ref rfl)
    (hF.2.2.2 Qc.k (by omega)) (two_cut_first head Sz.ref)
    (ride_at_stand head.head A.H _ _ _ _ _ _ _ _ _ _ input Said Td _ hF.1 hk)

include made in
/-- **`ThreeLeftFirst` at a segment into which a code switch leads.** -/
theorem threeLeft_switch_at (Td : Tied head.firstChain A.Z l pw Qc blk) (h1 : 1 ≤ l) (hl : l < 25) (hC : Closes A)
    {pS : SwitchPlace} (hpw : placesW.find? (·.link == l) = some pS)
    (hCopy : ∀ n, n + 1 < (switchSent pS.sizes pS.others).size → firstSender pS n = false →
      OwnMsgs (partsAt head numbers).script (threadAt head numbers input).valid (fxAt head.firstChain pS)
        (P5J.At.arr A.Z (seatSw A.Z pS n).1 (seatSw A.Z pS n).2) (fxAt head.firstChain pS)
        (switchMsgOff 0 (rowsAt A) (readersAt A) (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS n)) :
    ThreeLeftFirst matrixInput Sz.ref head (partsAt head numbers) input Said l Qc blk := by
  have hP : pS ∈ switchPlaces A.Z A.G := by
    rw [places_first head]
    exact List.mem_of_find?_eq_some hpw
  have hlink : pS.link = l := link_of_find hpw
  have hpos : shrPosLater l = some ((switchSent pS.sizes pS.others).size - 1) := by
    unfold shrPosLater
    rw [if_neg (by omega), hpw]
    rfl
  have hb := tie_moment_first head Td Sz.ref hP hlink hl
  refine threeLeft_at_switch
    (fun St _ Hb _ _ => made_first_paid matrixInput OnBytes.secondHashFunction openHonest made head (partsAt head numbers) input l Said Td St Hb _)
    (tie_switch_at head made numbers input Said Td h1 hC hpw hCopy)
    (tie_later_at head made numbers input Said Td false hpos (by simp) hb.1)
    (tie_later_at head made numbers input Said Td true hpos (by simp) hb.2)
    ?_ (fresh_switch_at head made numbers input Said Td h1 hC hpw)
  intro k s m En ds y cols s' St D Hb
  obtain ⟨hr, hf, -, -⟩ := stand_reached head.head A.H _ _ _ _ _ _ _ _ _ _ input Td St
  exact switch_count_at head.head h1 hl hpw hr hf Hb.there

include made in
/-- **`ThreeLeftFirst` at the first segment.** -/
theorem threeLeft_zero_at (Td : Tied head.firstChain A.Z 0 pw Qc blk) :
    ThreeLeftFirst matrixInput Sz.ref head (partsAt head numbers) input Said 0 Qc blk := by
  have hb := tie_moment_zero head Td Sz.ref rfl
  have hpos : shrPosLater 0 = some 3 := rfl
  exact threeLeft_at_first
    (fun St _ Hb _ _ => made_first_paid matrixInput OnBytes.secondHashFunction openHonest made head (partsAt head numbers) input 0 Said Td St Hb _)
    (tie_open_at head made numbers input Said Td)
    (tie_later_at head made numbers input Said Td false hpos (by simp) hb.1)
    (tie_later_at head made numbers input Said Td true hpos (by simp) hb.2)
    (shr_hcount_head head.head A.H _ _ _ _ _ _ _ _ _ _ input Said Td)
    (fresh_open_at head made numbers input Said Td)

include made in
/-- **The five statements at every member of the kind, at the script of the base prover.** -/
theorem kindTen_five_at_script (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat} {member : Block TS ProofFile.Cl}
    (atNumber : head.firstChain.blocksInOrder[b]? = some member) (ofTheKind : member.place.kind = .K10) (hC : Closes A)
    (hCopy : ∀ (l : Nat) (pS : SwitchPlace), 1 ≤ l → l < 25 → placesW.find? (·.link == l) = some pS →
      ∀ n, n + 1 < (switchSent pS.sizes pS.others).size → firstSender pS n = false →
      OwnMsgs (partsAt head numbers).script (threadAt head numbers input).valid (fxAt head.firstChain pS)
        (P5J.At.arr A.Z (seatSw A.Z pS n).1 (seatSw A.Z pS n).2) (fxAt head.firstChain pS)
        (switchMsgOff 0 (rowsAt A) (readersAt A) (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) pS n)) :
    FiveAtBorder (threadAt head numbers input) Said fall b := by
  refine kindTen_five_of_left head made numbers input Said hSaid fall atNumber ofTheKind fun l hl p Qc blk Td => ?_
  by_cases h0 : l = 0
  · subst h0
    exact threeLeft_zero_at head made numbers input Said Td
  · have h1 : 1 ≤ l := by omega
    obtain ⟨pS, -, hpw, -⟩ := pub_at h1 hl
    exact threeLeft_switch_at head made numbers input Said Td h1 hl hC hpw (hCopy l pS h1 hl hpw)

end

end AtFullSide.K10

#print axioms AtFullSide.K10.last_written
#print axioms AtFullSide.K10.link_of_find
#print axioms AtFullSide.K10.kindTen_five_of_left
#print axioms AtFullSide.K10.rows_laid_at
#print axioms AtFullSide.K10.tie_switch_at
#print axioms AtFullSide.K10.fresh_switch_at
#print axioms AtFullSide.K10.tie_later_at
#print axioms AtFullSide.K10.tie_open_at
#print axioms AtFullSide.K10.fresh_open_at
#print axioms AtFullSide.K10.threeLeft_switch_at
#print axioms AtFullSide.K10.threeLeft_zero_at
#print axioms AtFullSide.K10.kindTen_five_at_script
