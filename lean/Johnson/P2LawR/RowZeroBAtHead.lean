-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RowZeroBAtHead.lean: THE CLOSED JOIN: row0B, THE LAST TABLE's PREMISE ON ROW
0's PIECE (`own3_at_top` | `own3_at_end`, LLT25), AT THE CLOSED LETTERS OF THE COMPOSED MEANING AND
OF THE SHARED TABLE's CONSTANT, UNDER THE ONE HEAD h : P5J.AtMgA …: FROM `rowZeroOwed_atHead`
(Johnson/Desc/AtSeats/RowZeroAtHead.lean: the tight form). One theorem: five calls.


AT WHICH LETTERS. A := planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF) · O := openAll h (eCodes_at
h) · mk := ProofFile.pureRoad.links · Z N c := Zp Np cF · M₁ := mgAll h.𝔇 mgBase · G := h.𝔇.G · arr :=
h.𝔇.arr · get | N₁ | ms₁ | Rc := O.get | O.N₁ | O.ms₁ | O.R · MS := Sh.mg A O · links :=
Sound.linksFull · X := Sh.X A 12. STILL LETTERS: D (the last table's data: PlanOk₃'s dataIs says
whose; the head's own D₀ is another letter) · seats · oNo · ms₂ · decT₂ · stOf · bookOf · Pm₀ · Ns ·
dB · dt · r · Ld · decT · c₀'. OF rowZeroOwed_atHead's TWELVE PREMISES, TEN FALL: hr · rows
(P2LawR/RowZeroBForm.lean; rowsOpen) · hI · hV · omega (PlanOk₃'s sampled, iIn, wIn, omega) · hsh ·
hseat (Johnson/P2R0R/XWAtSh.lean, off PlanOk₃) · hm · hent · hten
(P2LawR/OmegaMemberAtSh.lean; withU returns off PlanOk₃'s planOk; Sh.t₁ A = D.t₁ by ht₁_of_first).
THREE HYPOTHESES: TWO OF THE TWELVE STAY: the head h · hB3 (three tests with code on every last
state of the first chain of which O.R holds and that bears no mark: atFirstBook 0 · bookFitsB · as
many places as oracle messages); AND ONE COMES: hP : PlanOk₃ …, which own3_at_top asks anyway. The
codes: h.𝔇.cs is A.Q.codes by Sh.eCodes_at h, not by rfl: the form's lemma takes the codes as a
letter and goes by substitution: nothing is carried by hand. Ns is a letter: that x's seat is
Ns.tenant .oOmega is said by no premise; at Ns := numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) … it
is memSh_seat. X stands at planAt … (seatF …), G at h.𝔇.G, the head at F0T …:
F0T = seatF … by rfl (Sh.f0T_is). A raised limit stands in this file (maxRecDepth 40000),
as in the file that it calls.
IS IT EMPTY? NO MEMBER: that the head, hB3 and hP can be met together is shown by nobody. The full
size alone. Nothing on soundness.
-/
import Johnson.Desc.AtSeats.RowZeroAtHead
import Johnson.P2LawR.Own3EndAtSh
import Johnson.P2R0R.XWAtSh
import Johnson.P2R0R.SizedIsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat Fo.Peel
    Cb Johnson.Pack
open Iop Prob _root_.Run
open LLT25
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (vecAt)
open VerifiableInference.Desc.K1 (shapeAt)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq gLaid parO omegaShapes_pos)
open _root_.Desc.K14.Law.Sh (planAt)
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.mem Sh.mg secondAt)
open _root_.Desc.K14.Law.Sh (seatF openAll eCodes_at)
open P5J (AtMgA colsAt)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

/-- **row0B at the closed letters, under the head.** -/
theorem row0B_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r₀ : LPFD.Full.RunPF} {Zp
                  : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x₀ :
                              VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D₀ r₀ Zp Np cF x₀) (D : WholeD) (seats
                              : List (ℕ × ℕ)) (oNo : Mem → ℕ) (dB : RDT) (dt : List RDT) (ms₂ : List Mem) (decT₂ : (ℕ → Option
                              (ℕ × List UInt64)) → St → Option (CellsQ numsFull.rows (colsAt numsFull))) (stOf : St →
                              OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (Ns : NumbersS) (r :
                              Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid) (decT : (ℕ → Option (ℕ × List
                              UInt64)) → (((FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).XiPub × (FL o ProofFile.pureRoad.links
                                    Zp (seatK Zp Np) Np cF).S₁ × St) × (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).S₃) → Option
                              (CellsQ numsFull.rows (colsAt numsFull))) (c₀' : CellsQ numsFull.rows (colsAt numsFull)) (hB3 :
                              ∀ p, (openAll h (eCodes_at h)).R p → ((openAll h (eCodes_at h)).get p).2.failed = none →
                              VerifiableInference.Desc.K12.Door.atFirstBook 0 ((openAll h (eCodes_at h)).get p).2 = true ∧
                              bookFitsB ((openAll h (eCodes_at h)).get p).2.book = true ∧ ((openAll h (eCodes_at h)).get
                              p).2.book.place.size = ((openAll h (eCodes_at h)).get p).2.st.oracles.size) (hP : PlanOk₃ o
                              ProofFile.pureRoad.links Zp Np cF D h.𝔇.G h.𝔇.arr dB dt (openAll h (eCodes_at h)).ms₁ ms₂ (openAll h
                                    (eCodes_at h)).N₁ Ns Sound.linksFull (First.flatPlaces true Sound.linksFull true) r ((openAll h
                                    (eCodes_at h)).N₁.treesAt none) 0 1 (vAt Zp (openAll h (eCodes_at h)).N₁) Ld) :
    RowZeroOwed (tiedNumbers (openAll h (eCodes_at h)).N₁ Ns) (tiedMeaning (openAll h (eCodes_at
    h)).get (mgAll h.𝔇 mgBase) (meaningSigS (p14At Zp).codes h.𝔇.G h.𝔇.arr (smpSt (p14At Zp).codes
    oNo stSh) ms₂ decT₂ (Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h
    (eCodes_at h))))) (⟨rowsOpen (p14At Zp).codes h.𝔇.arr D.t₁ D.t₂⟩ : MeaningL (FL o
    ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).S₃ (Wit (CellsQ numsFull.rows (colsAt numsFull))
          P5J.At.Tok MsgT)) (promSigS (p14At Zp).codes h.𝔇.G (smpSt (p14At Zp).codes oNo stSh) ms₂ stOf
          bookOf Pm₀) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS ((openAll h (eCodes_at h)).get
          q).2) (endedX (Sh.X (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) 12))) (fun q y => ocEnd
          (openAll h (eCodes_at h)).get (openAll h (eCodes_at h)).N₁ (mgAll h.𝔇 mgBase) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ (openAll h (eCodes_at h)).R q) (pieceZeroAt
          (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF) D (c0 Zp) (restCap (extsLast (Tok :=
                P5J.At.Tok) (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF) D (p14At Zp).codes h.𝔇.G h.𝔇.arr
                (smpLast (p14At Zp).codes (smpNamed (p14At Zp).codes seats) (smpSt (p14At Zp).codes oNo stSh)
                (openAll h (eCodes_at h)).get Ns) decT c₀' (mineOf (openAll h (eCodes_at h)).ms₁ ms₂ (openAll h
                (eCodes_at h)).N₁ Ns)))) := by
  obtain ⟨-, b2, -⟩ := Book.blocksOk_of_planOk _ hP.planOk
  have hf : OkD.AtC.front2 Zp.p.chains = true :=
    Book.first_ok_retype (Cl' := Cl) (seatK Zp Np).chain b2
  have b2' : blocksOk ((_root_.Desc.K14.chainOf Zp.p.chains
      (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last).retype :
      Chain St Cl).blocksInOrder = true := b2
  obtain ⟨u, -, -, hU, -, -⟩ :=
    Book.can_of_back (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q (fun b hb =>
      Book.back_ok_retype _ b2' b (List.mem_append_left _ hb))
  have ht := ht₁_of_first (seatF o Zp Np (secondAt Zp Np) cF) o ProofFile.pureRoad.links Zp Np cF D
    hP.dataIs hP.planOk rfl
  obtain ⟨hm, hent, hten⟩ :=
    omega_member_at (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) D.t₁ ht hU _ rfl
  have e : h.𝔇.cs = (p14At Zp).codes := eCodes_at h
  have hx := P2R0.xW_at_plan (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))
    (openAll h (eCodes_at h)) hP
  have hSZ := P2R0.hSZ_of h.laid.pub hf
  have hPw : h.𝔇.P13.lin.w = (p14At Zp).S.w := by
    show (VerifiableInference.Desc.K13.whereOf Zp).lin.w = _
    rw [hSZ]
    rfl
  exact row0B_of_form seats oNo o ProofFile.pureRoad.links Zp Np cF D h.𝔇.G h.𝔇.arr
    (openAll h (eCodes_at h)).get (openAll h (eCodes_at h)).ms₁ ms₂ decT₂ (mgAll h.𝔇 mgBase)
    (Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))) stOf bookOf
    Pm₀ (openAll h (eCodes_at h)).N₁ Ns Sound.linksFull
    (Sh.X (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) 12) decT c₀'
    (openAll h (eCodes_at h)).R h.𝔇.cs e
    (fun ds back r' hr => rowZeroOwed_atHead h (smpSt h.𝔇.cs oNo stSh) ms₂ decT₂ stOf bookOf Pm₀ Ns
      (c2 Np).rounds ⟨rowsOpen h.𝔇.cs h.𝔇.arr D.t₁ D.t₂⟩ D.t₁ D.t₂ (D.t₁ + D.t₂) ds back r' hr
      (of_decide_eq_true (List.all_eq_true.1 hP.sampled _ hP.iIn))
      (of_decide_eq_true (List.all_eq_true.1 hP.sampled _ hP.wIn)) hP.omega
      (fun _ _ _ hw => by rw [e] at hw; exact hw)
      (hPw.trans hx.2.symm) hB3 hx.1 _ hm hent hten)

end P2Law

#print axioms P2Law.row0B_at_head
