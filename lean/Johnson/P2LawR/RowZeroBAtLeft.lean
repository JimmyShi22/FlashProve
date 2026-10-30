-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RowZeroBAtLeft.lean: THE FIELD row0B OF THE STRUCTURE
`AtMgA.LastLeft` (Johnson/P5J/L0/LastFreeT.lean), TO THE SIGN [its text taken by program out of a
text of this project that is not in this repository; it is own3_at_top's binder row0B at that
structure's 25 letters, by two programs], FROM RowZeroBAtHead.lean's row0B_at_head. One theorem: one
call, two rewrites by equations of letters (Johnson/P2LawR/LettersAgreeC.lean,
LettersAgreeD.lean), and unfolding.

WHAT IS LAID IN THE CALL (eleven letters that row0B_at_head leaves free): D := D.at frS.P.T.a ·
seats := At.seats Zp · oNo := Sh.oNo A · ms₂ := Sh.ms A · decT₂ := Sh.decT₂ A O' · stOf · bookOf ·
Pm₀ := Sh.pm A O' · Ns := Fence.numbersSh … · decT := fun _ _ => none · c₀' := At.c₀ (A :=
h.toAtMg.shPlan, O' := h.toAtMg.shOpen h.𝔇).
THE TWO REWRITES: M₁_is : mgAll h.𝔇 mgBase = h.toAtMg.mq h.𝔇 (by mgAt_is_mq,
Johnson/P5J/RowsAtMg.lean) · open_is : openAll h (eCodes_at h) = h.toAtMg.shOpen h.𝔇 (the two makes
of the shared table's open letters part in Mg₁ and in smp₁, neither by unfolding): five letters hang
on it: N₁ · get · ms₁ · Rc · MS.
WHAT LEAN MUST TAKE BY UNFOLDING: G · arr · Cells · links, and the description (F0T … | FL …) in S₃
and in pieceZeroAt (each shown alone by rfl in LettersAgreeC.lean) · X (X_is, LettersAgreeD.lean) ·
the description in extsLast (shown by nobody alone) · Tok (one name); and the like in hB3 and hP,
which are stated here at that structure's letters.
THREE HYPOTHESES: the head h · hB3 · hP (that structure's own hP, to the sign).
IS IT EMPTY? NO MEMBER: as Johnson/P2LawR/RowZeroBAtHead.lean's head says. Nothing on soundness.

-/
import Johnson.P2LawR.RowZeroBAtHead
import Johnson.P2LawR.LettersAgreeD
import Johnson.P5J.L0.LastFreeT

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

/-- **The field row0B of AtMgA.LastLeft, to the sign.** -/
theorem row0B_at_left {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF} {Zp :
                  ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x :
                              VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D r' Zp Np cF x) (dB : RDT) (dt : List
                              RDT) (r : Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid) (hB3 : ∀ p,
                              h.toAtMg.rc p → ((L0.getL o Zp Np cF) p).2.failed = none →
                              VerifiableInference.Desc.K12.Door.atFirstBook 0 ((L0.getL o Zp Np cF) p).2 = true ∧ bookFitsB
                              ((L0.getL o Zp Np cF) p).2.book = true ∧ ((L0.getL o Zp Np cF) p).2.book.place.size = ((L0.getL
                              o Zp Np cF) p).2.st.oracles.size) (hP : PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a)
                              (F0T o Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay) (Sh.ms h.toAtMg.shPlan) (At.N Zp cF)
                              (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0,
                              0) (0, 0)) fullLinks (First.flatPlaces true fullLinks true) r ((At.N Zp cF).treesAt none) 0 1
                              (vAt Zp (At.N Zp cF)) Ld) :
    RowZeroOwed (tiedNumbers (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU
    h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))) (tiedMeaning (L0.getL o Zp Np cF)
    (h.toAtMg.mq h.𝔇) (meaningSigS (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpSt (p14At
    Zp).codes (Sh.oNo h.toAtMg.shPlan) stSh) (Sh.ms h.toAtMg.shPlan) (Sh.decT₂ h.toAtMg.shPlan
    (h.toAtMg.shOpen h.𝔇)) (Sh.mg h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)))) (⟨rowsOpen (p14At
    Zp).codes (At.arr Zp) (D.at frS.P.T.a).t₁ (D.at frS.P.T.a).t₂⟩ : MeaningL (F0T o Zp Np cF).S₃
    (Wit (CellsM numsFull) At.Tok MsgT)) (promSigS (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At
    Zp).codes (Sh.oNo h.toAtMg.shPlan) stSh) (Sh.ms h.toAtMg.shPlan) (fun s : St => s.st) (fun s :
    St => shiftBook (Sh.nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).lo s.book) (Sh.pm
    h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇))) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS
    ((L0.getL o Zp Np cF) q).2) (endedX (Sh.X h.toAtMg.shPlan 12))) (fun q y => ocEnd (L0.getL o Zp
    Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks (First.flatPlaces true fullLinks true) q y ∧
    h.toAtMg.rc q) (pieceZeroAt (F0T o Zp Np cF) (D.at frS.P.T.a) (c0 Zp) (restCap (extsLast (Tok :=
    At.Tok) (F0T o Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpLast
    (p14At Zp).codes (smpNamed (p14At Zp).codes (At.seats Zp)) (smpSt (p14At Zp).codes (Sh.oNo
    h.toAtMg.shPlan) stSh) (L0.getL o Zp Np cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU
    h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0))) (fun _ _ => none) At.c₀ (mineOf
    (At.ms Zp Z.lay) (Sh.ms h.toAtMg.shPlan) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan)
    (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan) (0, 0) (0, 0)))))) := by
  have k := P2Law.row0B_at_head h (D.at frS.P.T.a) (At.seats Zp) (Sh.oNo h.toAtMg.shPlan) dB dt
    (Sh.ms h.toAtMg.shPlan) (Sh.decT₂ h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)) (fun s : St => s.st)
    (fun s : St => shiftBook (Sh.nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)).lo s.book)
    (Sh.pm h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇))
    (Fence.numbersSh (Sh.t₁ h.toAtMg.shPlan) (Sh.layU h.toAtMg.shPlan) (Sh.layO h.toAtMg.shPlan)
      (0, 0) (0, 0)) r Ld (fun _ _ => none) At.c₀ hB3 hP
  rw [P2Law.LettersC.M₁_is h, P2Law.LettersC.open_is h] at k
  exact k

end P5J

#print axioms P5J.row0B_at_left
