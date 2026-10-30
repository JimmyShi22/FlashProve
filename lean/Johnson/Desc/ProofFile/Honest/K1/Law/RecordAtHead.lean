-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RecordAtHead.lean: THE RECORD OF PREMISES K1Seated
(Honest/K1/Seated.lean) AT ProofFile's LETTERS AT THE LIBRARY's HEAD (lettersHead,
Honest/Thread/FirstHead.lean): WHICH OF ITS TWENTY FIELDS ARE PAID THERE BY WHAT LIES, AND WHICH ARE
HANDED ON. Five theorems; no definition. IT DOES NOT SAY THAT THE RECORD IS MET: eleven fields and
member stay premises.

The form. Each theorem binds L with hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w:
an equation that a caller meets by rfl: no premise on the world: it stands so that every field that
is handed on can be written at L, TO THE LETTER OF THE RECORD's OWN TEXT (cut by program out of
Seated.lean), with arr, seats₀, ms at the real table's P5J.At.arr Zp, P5J.At.seats Zp, P5J.At.ms Zp
Z.lay (Johnson/P5J/LettersAt.lean). h: the library's head: A HYPOTHESIS. H, Q, wit, J and the rest:
bound letters.

  - k1Seated_at_head: at any member b: UNDER hcodes : J.P.codes = P5J.At.cs Zp and seventeen fields
    of the record: K1Seated L b …. PAID: treesNo (treesNo_atN, TreesNoTold.lean, under the field
    placeAt) · ans (lettersHead's pin is ansJT at the table's codes, numbers, reader of samples and
    members) · rowM (mgAll_row, Johnson/Desc/Sound/MgAll.lean).
  - codes_at_head: the codes of the description's own ground are the table's.
  - ps_two: the written list of places has ⟨1, some 0, 1, K1⟩ at number 2: by evaluation in the
    kernel.
  - k1Seated_two_of: UNDER O (the description opened: out of h.laid.opened), hP : J.P = K1.firstPar
    Bs.G₀.first (K1.gpOf Zp), member, and ELEVEN fields: half · fits · heardOnly · oneAns · hasCoins
    · firstNo · msgs · pads · seats · numbered · sits: K1Seated L 2 … at the sort "opening" and the
    radii K1.radRec 0 J.P. PAID BESIDE THE THREE: placeAt (ps_two) · shape, isSend, books
    (k1_two_inScope, MemberInScope.lean) · port (port_first, PiecesAndPort.lean, with hc_atAll,
    hs_atAll, Johnson/Desc/K1/Law/TestsAtAll.lean, at pin1_atAll,
    Johnson/Desc/K1/Law/PinsAtHead.lean).
  - k1Seated_fifty_of: UNDER O, hl : l < 25, hP : J.P = K1.parL Zp Bs.G₀ l d, member and the same
    eleven: K1Seated L (K1.noL l d) … at the radii K1.radRec (3 l + 1) J.P ("reads") or K1.radRec (3
    l + 2) J.P ("digits"). placeAt by place_fifty (Johnson/Desc/K1/Law/CallsE.lean); the others by
    k1_fifty_inScope, port_later, parL_later.

Mind. rad: the record ties it to nothing; here it is the written record's radii. sort stays free at
the fifty: the field seats, which alone reads it, is handed on. The record's field firstNo (the
number of the job's first message) is a namesake of the library's firstNo (the number 2 of the
opening in the flat list).

Limits. THE TIE (msgs, pads) IS A PREMISE ON THE LETTER Q. fits, oneAns, hasCoins, firstNo, seats,
numbered, sits: public; paid by nobody at these letters. half and heardOnly hang on the prover's own
record and on the job: not here. hP: that a prover's job has the plan of the description's own
ground is not said here. W's sending is not here. IT STANDS OVER FILES OF ProofFile's THAT ARE ON NO SEAL.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seated
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberInScope
import Johnson.Desc.ProofFile.Honest.K1.Law.PiecesAndPort
import Johnson.Desc.ProofFile.Honest.K1.Law.TreesNoTold
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Desc.K1.Law.CallsE

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
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {b : Nat} {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
  {J : SendJob (PlaceIn ProofFile.Inst) X} {own₀ : X} {sort : K1Sort} {rad : ℕ → ℕ}

/-- **AT lettersHead, AT ANY MEMBER**: treesNo, ans and rowM are paid; the other seventeen fields
are handed on in the record's own text. -/
theorem k1Seated_at_head
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (hcodes : J.P.codes = P5J.At.cs Zp)
    (member : L.bs[b]? = some blk)
    (placeAt : L.ps[b]? = some J.P.place)
    (shape : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (half : (L.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (isSend : K1.IsSend J.P (fun s : S => s.st) blk)
    (books : ∀ s s' r₁ r₂ gs, blk.decide s [r₁, r₂] gs = .ok s' →
      K1.Booked J.P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (fits : sendFits J.P J.ride = true)
    (heardOnly : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr')
    (oneAns : answersAtMostOne J.P = true)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (firstNo : L.N.msgsAt (some J.P.place) = J.first)
    (port : K1.condPort J.P rad = true)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs b)
        ((P5J.At.arr Zp) (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2)
        (L.thread.front + roundsTo L.bs b) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2
        (fun k _ => padTxt 0 J n k))
    (seats : ∀ x, x ∈ pinsAtSort L.N sort ↔ ∃ n, n < J.P.sent.size ∧
      (shapeAt J.P n).answers ≠ 0 ∧ x = seatAtMember L.bs b J.P n)
    (numbered : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      seatAtMember L.bs b J.P n ∈ (P5J.At.seats Zp) ∧
        (P5J.At.seats Zp).idxOf (seatAtMember L.bs b J.P n) = J.first + n)
    (sits : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
      (∃ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2) ∧
      ∀ x ∈ (P5J.At.ms Zp Z.lay),
          SitsAt x (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2 →
        (x.1.l.get x.2).1 = shapeAt J.P n) :
    K1Seated L b blk wit J own₀ sort (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) rad := by
  subst hL
  refine { member := member, placeAt := placeAt, shape := shape, half := half, isSend := isSend,
           books := books, fits := fits, heardOnly := heardOnly, oneAns := oneAns,
           hasCoins := hasCoins, firstNo := firstNo, treesNo := treesNo_atN Zp cF placeAt,
           port := port, msgs := msgs, pads := pads, seats := seats, ans := ?_,
           numbered := numbered, sits := sits, rowM := fun _ => rfl }
  rw [hcodes]
  rfl

/-- The codes of the head's own ground are the table's. -/
theorem codes_at_head {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) : Bs.G₀.first.codes =
          P5J.At.cs Zp := by
  rw [O.first]
  rfl

/-- The written list of places has the opening's place at number 2. -/
theorem ps_two : P5J.At.ps[2]? = some ⟨1, some 0, 1, .K1⟩ := by decide +kernel

/-- **AT NUMBER 2, AT THE HEAD's OWN GROUND**: eight fields are paid; member and eleven are handed
on. -/
theorem k1Seated_two_of
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (hP : J.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
    (member : L.bs[2]? = some blk)
    (half : (L.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (fits : sendFits J.P J.ride = true)
    (heardOnly : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr')
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
  have hm : cF.blocksInOrder[2]? = some blk := by rw [hL] at member; exact member
  obtain ⟨h1, h2, h3⟩ := k1_two_inScope h.scope h.reads O hm
  have hp1 := K1.pin1_atAll h
  refine k1Seated_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL
    (by rw [hP]; exact codes_at_head O) member (by rw [hL, hP]; exact ps_two)
    (by rw [hP]; exact h1) half (by rw [hP]; exact h2) (by rw [hP]; exact h3) fits heardOnly oneAns
    hasCoins firstNo
    (by rw [hP]; exact port_first _ _ (K1.hc_atAll h O hp1) (K1.hs_atAll h O hp1))
    msgs pads seats numbered sits

/-- **AT THE FIFTY, AT THE HEAD's OWN GROUND**: the like. -/
theorem k1Seated_fifty_of
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {l : ℕ} (hl : l < 25) (d : Bool) (hP : J.P = K1.parL Zp Bs.G₀ l d)
    (member : L.bs[(K1.noL l d)]? = some blk)
    (half : (L.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (fits : sendFits J.P J.ride = true)
    (heardOnly : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr')
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
  have hm : cF.blocksInOrder[K1.noL l d]? = some blk := by rw [hL] at member; exact member
  obtain ⟨h1, h2, h3⟩ := k1_fifty_inScope h.scope h.reads O hl d hm
  have hp1 := K1.pin1_atAll h
  refine k1Seated_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL
    (by rw [hP, parL_later]; exact codes_at_head O) member
    (by rw [hL, hP, parL_later]; exact K1.place_fifty l hl d)
    (by rw [hP]; exact h1) half (by rw [hP]; exact h2) (by rw [hP]; exact h3) fits heardOnly oneAns
    hasCoins firstNo
    (by
      rw [hP, parL_later]
      exact port_later _ _ (K1.hc_atAll h O hp1) (K1.hs_atAll h O hp1) hl _
        (by cases d; exact Or.inl rfl; exact Or.inr rfl))
    msgs pads seats numbered sits

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Seated_at_head
#print axioms ProofFile.Honest.K1.codes_at_head
#print axioms ProofFile.Honest.K1.ps_two
#print axioms ProofFile.Honest.K1.k1Seated_two_of
#print axioms ProofFile.Honest.K1.k1Seated_fifty_of
