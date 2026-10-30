-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RowZeroBOfSh.lean: THE JOIN: row0B, THE LAST TABLE's PREMISE ON ROW 0's PIECE
AS `own3_at_top` HAS IT (Johnson/LLT25R/LastTop.lean), FROM `rowZeroOwed_atZ_sh`
(Johnson/Flat/Last/RowZeroAtShX.lean): AT THE ONE X OF THE LAST TABLE: Sh.X (planAt Z N G) 12. One
theorem: three calls.


AT WHICH LETTERS. M₁ := mgAll 𝔇 Mg · G := 𝔇.G · arr := 𝔇.arr · Cells := CellsQ rows₀ cols₀ ·
links := Sound.linksFull · X := Sh.X (planAt Z N 𝔇.G) 12 · the rounds R := (c2 N).rounds · t₁, t₂,
base := D.t₁, D.t₂, D.t₁ + D.t₂ · lay₀ := linLayW 𝔇.cs 𝔇.P13.lin · mem := Sh.mem (planAt Z N 𝔇.G)
· x := Omega's member memSh … .oOmega at the shared table's constant's letters.
THE THREE CALLS. P2LawR/RowZeroBForm.lean (the four equations of form) · P2LawR/OmegaMemberAtSh.lean
(hm, hent, hten) · rowZeroOwed_atZ_sh.
OF ITS EIGHTEEN PREMISES, ELEVEN FALL HERE: hr (the form's lemma hands it) · rows (the
last table's ML.rows IS that sentence: rowsOpen) · hlay (lay₀ is put in) · hlin and hl (K14's second
part's own test on the plan, from PlanOk₃'s planOk) · hI, hV and omega (PlanOk₃'s sampled, iIn, wIn,
omega) · hm, hent and hten. SEVEN STAY, BY NAME: hSZ · h13 · hMg ·
hsh · hseat · hB · hdot; AND THREE COME: hcs : 𝔇.cs = (p14At Z).codes · ht₁ : 𝔇.G's first chain
tells of D.t₁ trees · hP : PlanOk₃ …, WHICH own3_at_top ASKS ANYWAY.
IS IT EMPTY? NO MEMBER: that the ten premises can be met together at the real Z is shown by nobody.
hSZ is a fact on Z (two fields of ProofFile.Pub). hB stands under Rc and "no mark" alone: Rc itself must
give it. hdot has no promise in front: it can be met only where MS.dot is made to be that sentence.
𝔇.N against N₁, and that xW is a member of mineOf …, is said by no premise. hP's field planTreeO
speaks of 𝔇.G: which description 𝔇 has is for whoever closes 𝔇. Nothing on soundness.
-/
import Johnson.P2LawR.RowZeroBForm
import Johnson.P2LawR.OmegaMemberAtSh
import Johnson.Flat.Last.RowZeroAtShX
import Johnson.Desc.Book.ToldShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

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
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.mem)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

/-- **row0B from `rowZeroOwed_atZ_sh` at the layer of the one X.** -/
theorem row0B_of_sh {Tok P₀ Xi : Type} {rows₀ cols₀ nR : ℕ} {X₀ : OnBytes.Model.Verify.Public}
    (seats : List (ℕ × ℕ)) (oNo : Mem → ℕ) (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N :
          H2U.Places4) (c : Chain S Cl) (D : WholeD) (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀) (Mg :
          Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (dB : RDT) (dt : List RDT) (get : (FL o mk Z
          (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S) (ms₁ ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀)) (MS : MeaningS St
    ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁) (Wit (CellsQ rows₀ cols₀)
    Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning
    St) (N₁ : Numbers) (Ns : NumbersS) (r : Fmt.M1.Stage → ℕ) (Ld :
    VerifiableInference.Desc.K12.Door.Laid) (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z
    (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃)
    → Option (CellsQ rows₀ cols₀)) (c₀' : CellsQ rows₀ cols₀) (Rc : (FL o mk Z (seatK Z N) N
    c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Prop) (hP : PlanOk₃ o mk Z N c D 𝔇.G 𝔇.arr dB dt ms₁
    ms₂ N₁ Ns Sound.linksFull (First.flatPlaces true Sound.linksFull true) r (N₁.treesAt none) 0 1
    (vAt Z N₁) Ld) (hcs : 𝔇.cs = (p14At Z).codes) (ht₁ : (oraclesOf 𝔇.G.first.blocksInOrder).length = D.t₁)
    (hSZ : (VerifiableInference.Desc.K13.whereOf Z).lin = (P2Third.lastPar Z).S) (h13 : 𝔇.P13 =
    VerifiableInference.Desc.K13.whereOf Z) (hMg : Mg.more = {}) (xW : Mem) (hsh : 𝔇.P13.lin.w =
    (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = 𝔇.N.w) (hB : ∀ q, Rc q → (get q).2.failed = none
    → NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧ ∀ o, o < (get q).2.st.oracles.size →
    ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r) (hdot : ∀ q (s : St) y w, DotEq (P2Third.lastPar
    Z).S.matrixRows (P2Third.lastPar Z).S.kCol (gLaid 𝔇.P13 get q) (omLast 𝔇.arr (Sh.mem (planAt Z N
    𝔇.G)) (planAt Z N 𝔇.G).Q (Sh.sentU (planAt Z N 𝔇.G)) w) (s.loc.psiSh.map
    OnBytes.Model.Reading.gl.val) (vecAt (linLayW 𝔇.cs 𝔇.P13.lin) (xW.1.l.get xW.2).1 (wTab 𝔇.cs
    𝔇.arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (mgAll 𝔇 Mg) (meaningSigS (p14At Z).codes 𝔇.G
    𝔇.arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes 𝔇.arr D.t₁
    D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (promSigS
    (p14At Z).codes 𝔇.G (smpSt (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
    N).rounds (fun q => firstOfS (get q).2) (endedX (Sh.X (planAt Z N 𝔇.G) 12))) (fun q y => ocEnd
    get N₁ (mgAll 𝔇 Mg) Sound.linksFull (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
    (pieceZeroAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z
    (seatK Z N) N c) D (p14At Z).codes 𝔇.G 𝔇.arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes
    seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns)))) := by
  obtain ⟨-, b2, b3⟩ := Book.blocksOk_of_planOk _ hP.planOk
  have k := Book.first_ok_retype (Cl' := Cl) (P2Third.secondSeatOf Z N).chain b3
  have k' : ((planAt Z N 𝔇.G).Q.codes.lengthsOk &&
      linOk (planAt Z N 𝔇.G).Q.codes (planAt Z N 𝔇.G).Q.par.S &&
      Third.plainArm (planAt Z N 𝔇.G).Q.par.S) = true := k
  simp only [Bool.and_eq_true] at k'
  have b2' : blocksOk ((_root_.Desc.K14.chainOf Z.p.chains (planAt Z N 𝔇.G).Q
      (VerifiableInference.Desc.K12.Seat.tests N) VerifiableInference.Desc.K12.Seat.last).retype :
      Chain St Cl).blocksInOrder = true := b2
  obtain ⟨u, -, -, hU, -, -⟩ := Book.can_of_back (planAt Z N 𝔇.G).Q
    (fun b hb => Book.back_ok_retype _ b2' b (List.mem_append_left _ hb))
  obtain ⟨hm, hent, hten⟩ := omega_member_at (planAt Z N 𝔇.G) D.t₁ ht₁ hU _ rfl
  exact row0B_of_form seats oNo o mk Z N c D 𝔇.G 𝔇.arr get ms₁ ms₂ decT₂ (mgAll 𝔇 Mg) MS stOf bookOf
    Pm₀ N₁ Ns Sound.linksFull (Sh.X (planAt Z N 𝔇.G) 12) decT c₀' Rc 𝔇.cs hcs
    (fun ds back r' hr => rowZeroOwed_atZ_sh 𝔇 Mg get (smpSt 𝔇.cs oNo stSh) ms₂ decT₂ MS stOf bookOf
      Pm₀ N₁ Ns Z N 𝔇.G hSZ h13 (c2 N).rounds (Sh.mem (planAt Z N 𝔇.G))
      ⟨rowsOpen 𝔇.cs 𝔇.arr D.t₁ D.t₂⟩ D.t₁ D.t₂ (D.t₁ + D.t₂) ds back r' hr Rc hMg
      (of_decide_eq_true (List.all_eq_true.1 hP.sampled _ hP.iIn))
      (of_decide_eq_true (List.all_eq_true.1 hP.sampled _ hP.wIn)) hP.omega
      (fun _ _ _ h => by rw [hcs] at h; exact h) xW _ rfl hsh hseat hB _ hm hent hten k'.1.2
      k'.1.1 hdot)

end P2Law

#print axioms P2Law.row0B_of_sh
