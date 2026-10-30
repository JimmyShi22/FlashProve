-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RecordAtFill.lean: THE SHARED "SENDING" (the kind K1): THE
RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean) AT THE 51 REAL MEMBERS OF THE FIRST CHAIN
(number 2; each link's "reads" and "digits"), AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT A FILLING P THAT
IS A LETTER. Four theorems; no definition.

WHY. A law that is nailed to one filling says nothing at the next wider one. HERE THE FILLING IS A
LETTER, WITH TWO PREMISES ON ITS LOTS: hex: the filling holds K1's lot (a lot whose halves are
lotHalves wit no Dt) · ho: every other lot's halves stand at places of other kinds, or at places of
the kind K1 that bear no link. The letters wit, no, Dt are lotHalves' own. The types W₀, Rc, Tr, X₀,
X and the sender's own state own₀ are letters too.

  - k1Seated_two_fill, k1Seated_fifty_fill: ten fields are paid (half by k1_first_fill,
    k1_reads_fill, k1_digits_fill: Honest/K1/Law/HalfAtFill.lean); member and nine are handed on.
  - k1Seated_two_fill_no, k1Seated_fifty_fill_no: under eno : no = lotNo secondHashFunction A.Z: firstNo is paid
    too (firstNo_atPure, FirstNoAtPure.lean: general in the filling): member and eight are handed
    on.

This file's text is made by program.

`K1Seated` is had here only under the head, a returned prover, two premises on the lots and THE
TIE; here THE TIE is shown at no Script that a run has. At the first Script, under the head and a
returned prover alone: `k1Seated_first` (AtFullSide/K1/FirstScript.lean). AND HERE MORE THAN THE TIE
IS HANDED ON: member and nine fields in the first two laws, member and eight in the other two; msgs
and pads, THE TIE, are among them in all four. NOT IN FRONT OF A LAW OVER COINS.

Limits. UNDER h (the library's head: A HYPOTHESIS). AN IMPLICATION: no filling is proved to meet hex
and ho here (at widerFillAt: hex_wider, and ho_wider under WiderKinds,
Honest/K1/Law/LotAtWider.lean; at the base prover's filling, with no hypothesis: hex_base, ho_base,
AtFullSide/K1/RecordAtBase.lean). THE FULL SIZE; the format's second hash function. Nothing on any
property.
AN IDLE WAY. L.valid is "v = w and Vd v": at Vd := fun _ => False it holds of nothing: msgs and
pads, which speak at the thread's valid inputs, are then met for nothing, and the record that
follows binds nothing at any input.
msgs AND pads ARE PROVED OF NO SCRIPT: no Script is shown that meets them at ProofFile's real letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstNoAtPure
import Johnson.Desc.ProofFile.Honest.K1.Law.HalfAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.Prover.Send (shapeAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **NUMBER 2, AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT A FILLING THAT HOLDS K1's LOT**: ten fields are
paid; member and nine are handed on. -/
theorem k1Seated_two_fill (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G) {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = placeJob (K1.firstPar A.G.first (K1.gpOf A.Z)) (no ⟨1, some 0, 1, .K1⟩)
      (firstFold A.G.first) (Dt A.Z A.G))
    {blk : Block TS ProofFile.Cl}
    (member : L.bs[2]? = some blk)
    (fits : sendFits J.P J.ride = true)
    (oneAns : answersAtMostOne J.P = true)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (firstNo : L.N.msgsAt (some J.P.place) = J.first)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 2)
        ((P5J.At.arr Zp) (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2)
        (L.thread.front + roundsTo L.bs 2) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2
        (fun k _ => padTxt 0 J n k))
    (seats : ∀ x, x ∈ pinsAtSort L.N .opening ↔ ∃ n, n < J.P.sent.size ∧
      (shapeAt J.P n).answers ≠ 0 ∧ x = seatAtMember L.bs 2 J.P n)
    (numbered : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      seatAtMember L.bs 2 J.P n ∈ (P5J.At.seats Zp) ∧
        (P5J.At.seats Zp).idxOf (seatAtMember L.bs 2 J.P n) = J.first + n)
    (sits : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      (∃ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2) ∧
      ∀ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2 →
        (x.1.l.get x.2).1 = shapeAt J.P n) :
    K1Seated L 2 blk wit J own₀ .opening (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec 0 J.P) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hP : J.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp) := by
    rw [hJ]
    show K1.firstPar A.G.first (K1.gpOf A.Z) = _
    rw [eZ, eG]
  refine k1Seated_two_of h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL O hP member ?_ fits ?_
    oneAns hasCoins firstNo msgs pads seats numbered sits
  · rw [hL, hJ]
    exact k1_first_fill hA wit no Dt hex ho
  · rw [hJ]
    intro v fr fr' e
    simp only [placeJob, e]

/-- **EACH OF THE FIFTY, AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT A FILLING THAT HOLDS K1's LOT**: link
l's "reads" (d = false) and "digits" (d = true): ten fields are paid; member and nine are handed on.
-/
theorem k1Seated_fifty_fill (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G) {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {l : ℕ} (hl : l < 25) (d : Bool) {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)
      (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt A.Z A.G))
    {blk : Block TS ProofFile.Cl} {sort : K1Sort}
    (member : L.bs[(K1.noL l d)]? = some blk)
    (fits : sendFits J.P J.ride = true)
    (oneAns : answersAtMostOne J.P = true)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (firstNo : L.N.msgsAt (some J.P.place) = J.first)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs (K1.noL l d))
        ((P5J.At.arr Zp) (seatAtMember L.bs (K1.noL l d) J.P n).1 (seatAtMember L.bs (K1.noL l d)
            J.P n).2)
        (L.thread.front + roundsTo L.bs (K1.noL l d)) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs (K1.noL l d) J.P n).1 (seatAtMember L.bs (K1.noL l d)
          J.P n).2
        (fun k _ => padTxt 0 J n k))
    (seats : ∀ x, x ∈ pinsAtSort L.N sort ↔ ∃ n, n < J.P.sent.size ∧
      (shapeAt J.P n).answers ≠ 0 ∧ x = seatAtMember L.bs (K1.noL l d) J.P n)
    (numbered : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      seatAtMember L.bs (K1.noL l d) J.P n ∈ (P5J.At.seats Zp) ∧
        (P5J.At.seats Zp).idxOf (seatAtMember L.bs (K1.noL l d) J.P n) = J.first + n)
    (sits : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      (∃ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs (K1.noL l d) J.P n).1
            (seatAtMember L.bs (K1.noL l d) J.P n).2) ∧
      ∀ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs (K1.noL l d) J.P n).1
            (seatAtMember L.bs (K1.noL l d) J.P n).2 →
        (x.1.l.get x.2).1 = shapeAt J.P n) :
    K1Seated L (K1.noL l d) blk wit J own₀ sort (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) (K1.radRec (3 * l + (if d then 2 else 1)) J.P) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨Xl, reads, digits, hX, hN⟩ := pieces_inScope h.scope h.reads O hl
  rw [← eG] at hX hN
  have hP : J.P = K1.parL Zp Bs.G₀ l d := by
    rw [hJ, parL_later]
    show K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1) = _
    rw [eZ, eG]
  refine k1Seated_fifty_of h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL O hl d hP member ?_ fits
    ?_ oneAns hasCoins firstNo msgs pads seats numbered sits
  · rw [hL, hJ]
    cases d with
    | true => exact k1_digits_fill hA wit no Dt hex ho hX hN
    | false => exact k1_reads_fill hA wit no Dt hex ho hX hN
  · rw [hJ]
    intro v fr fr' e
    simp only [laterJobAt, placeJob, e]

/-- **NUMBER 2, AT THE EARLIER HASH**: firstNo is paid too: eleven paid; member and EIGHT are handed
on. -/
theorem k1Seated_two_fill_no (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (eno : no = lotNo OnBytes.secondHashFunction A.Z) {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = placeJob (K1.firstPar A.G.first (K1.gpOf A.Z)) (no ⟨1, some 0,
        1, .K1⟩)
      (firstFold A.G.first) (Dt A.Z A.G))
    {blk : Block TS ProofFile.Cl}
    (member : L.bs[2]? = some blk)
    (fits : sendFits J.P J.ride = true)
    (oneAns : answersAtMostOne J.P = true)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 2)
        ((P5J.At.arr Zp) (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2)
        (L.thread.front + roundsTo L.bs 2) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2
        (fun k _ => padTxt 0 J n k))
    (seats : ∀ x, x ∈ pinsAtSort L.N .opening ↔ ∃ n, n < J.P.sent.size ∧
      (shapeAt J.P n).answers ≠ 0 ∧ x = seatAtMember L.bs 2 J.P n)
    (numbered : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      seatAtMember L.bs 2 J.P n ∈ (P5J.At.seats Zp) ∧
        (P5J.At.seats Zp).idxOf (seatAtMember L.bs 2 J.P n) = J.first + n)
    (sits : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      (∃ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2) ∧
      ∀ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2 →
        (x.1.l.get x.2).1 = shapeAt J.P n) :
    K1Seated L 2 blk wit J own₀ .opening (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec 0 J.P) :=
  k1Seated_two_fill h hA wit no Dt hex ho Q test carryX item n₁ n₂ b₀ Vd Rd Kp w own₀ hL hJ member
      fits oneAns hasCoins
    (by rw [hL, hJ, eno]; exact firstNo_atPure h hA ps_two) msgs pads seats numbered sits

/-- **EACH OF THE FIFTY, AT THE EARLIER HASH**: the like. -/
theorem k1Seated_fifty_fill_no (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (eno : no = lotNo OnBytes.secondHashFunction A.Z) {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {l : ℕ} (hl : l < 25) (d : Bool) {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)
      (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt A.Z A.G))
    {blk : Block TS ProofFile.Cl} {sort : K1Sort}
    (member : L.bs[(K1.noL l d)]? = some blk)
    (fits : sendFits J.P J.ride = true)
    (oneAns : answersAtMostOne J.P = true)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs (K1.noL l d))
        ((P5J.At.arr Zp) (seatAtMember L.bs (K1.noL l d) J.P n).1 (seatAtMember L.bs (K1.noL l d)
            J.P n).2)
        (L.thread.front + roundsTo L.bs (K1.noL l d)) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs (K1.noL l d) J.P n).1 (seatAtMember L.bs (K1.noL l d)
          J.P n).2
        (fun k _ => padTxt 0 J n k))
    (seats : ∀ x, x ∈ pinsAtSort L.N sort ↔ ∃ n, n < J.P.sent.size ∧
      (shapeAt J.P n).answers ≠ 0 ∧ x = seatAtMember L.bs (K1.noL l d) J.P n)
    (numbered : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      seatAtMember L.bs (K1.noL l d) J.P n ∈ (P5J.At.seats Zp) ∧
        (P5J.At.seats Zp).idxOf (seatAtMember L.bs (K1.noL l d) J.P n) = J.first + n)
    (sits : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      (∃ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs (K1.noL l d) J.P n).1
            (seatAtMember L.bs (K1.noL l d) J.P n).2) ∧
      ∀ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs (K1.noL l d) J.P n).1
            (seatAtMember L.bs (K1.noL l d) J.P n).2 →
        (x.1.l.get x.2).1 = shapeAt J.P n) :
    K1Seated L (K1.noL l d) blk wit J own₀ sort (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) (K1.radRec (3 * l + (if d then 2 else 1)) J.P) :=
  k1Seated_fifty_fill h hA wit no Dt hex ho Q test carryX item n₁ n₂ b₀ Vd Rd Kp w own₀ hL hl d hJ
      member fits oneAns
      hasCoins
    (by rw [hL, hJ, eno]; exact firstNo_atPure h hA (K1.place_fifty l hl d)) msgs pads seats
        numbered sits

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Seated_two_fill
#print axioms ProofFile.Honest.K1.k1Seated_fifty_fill
#print axioms ProofFile.Honest.K1.k1Seated_two_fill_no
#print axioms ProofFile.Honest.K1.k1Seated_fifty_fill_no
