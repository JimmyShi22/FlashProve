-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtShXPlan.lean: ROW 0's DEBT OF THE LAST TABLE AT THE LAYER OF Sh.X
(planAt Z N G) 12 (Johnson/Flat/Last/RowZeroAtShX.lean: rowZeroOwed_atZ_sh), WITH hl AND hlin PAID
BY THE SUB-PROTOCOL's OWN TEST ON ITS PUBLIC PARAMETERS. Two theorems.

Why (on rowZeroOwed_atZ_sh): hl and hlin need no pin: they are the
first two conjuncts of the block's own test on the plan: (batchLinearConstraintsSecondPart p).planOk = p.codes.lengthsOk
&& linOk p.codes p.S && plainArm p.S; so F.planOk = true pays both at every live Z. A
payer that rides on Written, so on the pins, is dearer than need be.


  hl_hlin_of_second    the two, off (batchLinearConstraintsSecondPart p).planOk = true (second_planOk: rfl).
  rowZeroOwed_atZ_shP  **the top with hsec : (batchLinearConstraintsSecondPart (P2Third.lastPar Z)).planOk = true in the
                       place of hlin and hl**: (P2Third.lastPar Z).codes | .S are (planAt Z N
                       G).Q.codes | .Q.par.S by unfolding. LEFT: hSZ · h13 · hr · hMg · hI · hV ·
                       omega · rows · hlay · hsh · hseat · hB · hm · hent · hten · hsec · hdot.
What is not claimed. NO MEMBER. All that RowZeroAtShX.lean does not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtShX
import Johnson.Goal.Numbers.K14SecondAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Fo.Peel Cb
open Johnson.Pack
open Iop Prob _root_.Run
open OnBytes.Means (Words)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf vecAt wSitsMore wSits_open_all placeSeal)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq omegaOf gLaid WSits hW_at_ocEnd)

open VerifiableInference.Desc.K1 (shapesOf shapeAt)
open _root_.Desc.K14 (P14 withOmega)
open _root_.Desc.K14.Law (XK XK_iff codY_of_codX codY_iff omWK rdK omegaTie wordsSh_is shape_omega
  omegaInRange_of_lengths parO)


open _root_.Desc.K14.Law (withOmega_pos omegaShapes_pos ShPlan XW_iff shape_omega)
open _root_.Desc.K14.Law.Sh (planAt)
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.Y)

open VerifiableInference.Desc.Third (batchLinearConstraintsSecondPart second_planOk secondB)

/-- The sub-protocol's own test on its public parameters gives the two. -/
theorem hl_hlin_of_second {Cl : Type} (p : P₁₄) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).planOk = true) :
    p.codes.lengthsOk = true ∧ linOk p.codes p.S = true := by
  rw [second_planOk] at h
  unfold secondB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

/-- **Row 0's debt at the layer of Sh.X … 12, the two tests on the codes and the shape by the
sub-protocol's own test.** -/
theorem rowZeroOwed_atZ_shP {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ} {X₀ :
    OnBytes.Model.Verify.Public} {Fr : Frame} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀) (Mg :
    Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (get : P × S₁ → P₀ × First.S) (smp₂ : St → (s
    : Sending) → (i : Fin s.l.length) → Option ((sigOf 𝔇.cs s.l).om i).Smp) (ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀)) (MS : MeaningS St
    (P × S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St →
    OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (Z : ProofFile.Pub) (N :
          H2U.Places4) {Xi' : Type} (G : FileDescription Xi') (hSZ : (VerifiableInference.Desc.K13.whereOf
                 Z).lin = (P2Third.lastPar Z).S) (h13 : 𝔇.P13 = VerifiableInference.Desc.K13.whereOf Z) (R :
                 List Fmt.DeclaredRound) (mem : ℕ → Option Mem) (ML : MeaningL S₃ (Wit (CellsQ rows₀ cols₀) Tok
                     MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (r : Rest (ckP .two) Fr ((P × S₁
                            × St) × S₃) (Wit (CellsQ rows₀ cols₀) Tok MsgT) ds) (hr : ∀ a τ w, r.ext a τ w = w) (Rc : P ×
                            S₁ → Prop) (hMg : Mg.more = {}) (hI : N₁.index.1 < base) (hV : N₁.w.1 < base) (omega :
                            (Ns.tenant .oOmega).1 < base) (rows : ∀ b w, onOcX Fr 𝔇.cs 𝔇.G 𝔇.arr get smp₂ ms₂ decT₂
                            (mgAll 𝔇 Mg) MS stOf bookOf Pm₀ N₁ Ns (P2Third.lastPar Z) R (Sh.X (planAt Z N G) 12) (fun q y
                            => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull (First.flatPlaces true Sound.linksFull true) q y
                            ∧ Rc q) 1 b → ML.rows b.1.2 w → ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t
                            ∧ ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i (OnBytes.Means.wordsOn t.st
                            (tabAt (P2Third.lastPar Z).codes 𝔇.arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book)
                            t.st w))) (xW : Mem) (lay₀ : VectorLay) (hlay : lay₀ = linLayW 𝔇.cs 𝔇.P13.lin) (hsh :
                            𝔇.P13.lin.w = (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = 𝔇.N.w) (hB : ∀ q, Rc q → (get
                            q).2.failed = none → NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧ ∀ o, o < (get
                            q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r) (x : Mem) (hm : mem
                            (Sh.sentU (planAt Z N G)).size = some x) (hent : (x.1.l.get x.2).1 = shapeAt (parO (planAt Z N
                            G).Q) ⟨0, (omegaShapes_pos (planAt Z N G).Q)⟩) (hten : x.1.seat x.2 = (t₁ + ((planAt Z N
                            G).Q.par.toGPar.firstTree + ((Sh.layU (planAt Z N G)).shapes.size + (Sh.layO (planAt Z N
                            G)).tree.getD 0 0)), (Sh.layO (planAt Z N G)).part.getD 0 0)) (hsec :
                            (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Cl) (P2Third.lastPar Z)).planOk = true) (hdot
                                                   : ∀ q (s : St) y w, DotEq (P2Third.lastPar Z).S.matrixRows (P2Third.lastPar Z).S.kCol (gLaid
                                                   𝔇.P13 get q) (omLast 𝔇.arr mem (planAt Z N G).Q (Sh.sentU (planAt Z N G)) w)
                                                   (s.loc.psiSh.map OnBytes.Model.Reading.gl.val) (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab 𝔇.cs
                                                   𝔇.arr xW w)) → MS.dot q s y w) : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (mgAll 𝔇
                                                   Mg) (meaningSigS 𝔇.cs 𝔇.G 𝔇.arr smp₂ ms₂ decT₂ MS)) ML (promSigS 𝔇.cs 𝔇.G smp₂ ms₂ stOf
                                                   bookOf Pm₀) (besideL (fillZ (P2Third.lastPar Z) R fun q => (get q).2) (Sh.X (planAt Z N G)
                                                   12)) (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull (First.flatPlaces true
                                                   Sound.linksFull true) q y ∧ Rc q) (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl)
                                                   (P2Third.lastPar Z)) base ds back r) :=
  rowZeroOwed_atZ_sh 𝔇 Mg get smp₂ ms₂ decT₂ MS stOf bookOf Pm₀ N₁ Ns Z N G hSZ h13 R mem ML t₁ t₂
      base
    ds back r hr Rc hMg hI hV omega rows xW lay₀ hlay hsh hseat hB x hm hent hten
    (hl_hlin_of_second _ hsec).2 (hl_hlin_of_second _ hsec).1 hdot

end VerifiableInference.OnPublicFiles.Last
