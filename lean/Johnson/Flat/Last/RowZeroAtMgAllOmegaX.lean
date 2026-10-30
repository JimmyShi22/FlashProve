-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtMgAllOmegaX.lean: ROW 0's DEBT OF THE LAST TABLE AT mgAll 𝔇 Mg, AT THE
LAYER OF ANY TEST X' THAT GIVES THE SHARED LEDGER's OWN TEST AT ITS LAST BORDER (xkLast). One
theorem: a joining.

Why. rowZeroOwed_mgAll_omega (Johnson/Flat/Last/RowZeroAtMgAllOmega.lean)
stands at the layer
besideL (fillZ …) xkLast…; the last table lays ONE test for four of its premises, the
shared table's constant's Sh.X A 12, which is xkLast's test WITH the last chain's door's tests:
another term, so another statement. The top beneath (rowZeroOwed_mgAll_full) is general in the
layer's test.

  rowZeroOwed_mgAll_omegaX  rowZeroOwed_mgAll_omega's text with X' in xkLast…'s place (three
                            places) and one premise more: hX' : ∀ d, X' d = true → xkLast … d =
                            true.
What is not claimed. All that RowZeroAtMgAllOmega.lean does not claim. NO MEMBER. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtMgAllFull
import Johnson.Flat.Last.RowZeroOmega

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


/-- **Row 0's debt at the layer of any test that gives the ledger's own.** -/
theorem rowZeroOwed_mgAll_omegaX {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ}
    {X₀ : OnBytes.Model.Verify.Public} {Fr : Frame} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf 𝔇.cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀))
    (MS : MeaningS St (P × S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (p : P₁₄) (R : List Fmt.DeclaredRound) (mem : ℕ → Option Mem) (Q : P14)
    (sentU : Array OracleNotice) (layU layO : TreeLay) (h0 : 0 < (shapesOf (parO Q)).length)
    (sU sS : OracleShape) (Y : ℕ → St → Bool) (X' : St → Bool)
    (hX' : ∀ d, X' d = true → xkLast Q sentU layU layO h0 sU sS Y d = true)
    (ML : MeaningL S₃ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit (CellsQ rows₀ cols₀) Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (Rc : P × S₁ → Prop)
    (hMg : Mg.more = {})
    (hI : N₁.index.1 < base) (hV : N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base)
    (rows : ∀ b w,
      onOcX Fr 𝔇.cs 𝔇.G 𝔇.arr get smp₂ ms₂ decT₂ (mgAll 𝔇 Mg) MS stOf bookOf Pm₀ N₁ Ns p R
        X'
        (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
        1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes 𝔇.arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay)
    (hS : 𝔇.P13.lin = p.S)
    (hlay : lay₀ = linLayW 𝔇.cs 𝔇.P13.lin) (hsh : 𝔇.P13.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = 𝔇.N.w)
    (hB : ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (hp : p.S = Q.par.S) (hOm : 0 < (withOmega Q.S).size) (x : Mem)
    (hm : mem sentU.size = some x) (hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hlin : linOk Q.codes Q.par.S = true) (hl : Q.codes.lengthsOk = true)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid 𝔇.P13 get q) (omLast 𝔇.arr mem Q sentU w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab 𝔇.cs 𝔇.arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mgAll 𝔇 Mg) (meaningSigS 𝔇.cs 𝔇.G 𝔇.arr smp₂ ms₂ decT₂ MS))
      ML (promSigS 𝔇.cs 𝔇.G smp₂ ms₂ stOf bookOf Pm₀)
      (besideL (fillZ p R fun q => (get q).2) X')
      (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_mgAll_full 𝔇 Mg get smp₂ ms₂ decT₂ MS stOf bookOf Pm₀ N₁ Ns p R X' ML t₁ t₂ base ds
    back r hr Rc hMg hI hV omega rows xW lay₀ _ hS hlay hsh hseat hB
    (fun d w hd => hO_of_XK 𝔇.arr mem Q sentU layU layO h0 sU sS Y p hp hOm t₁ x hm hent hten hlin
        hl
      d w (hX' d hd)) hdot

end VerifiableInference.OnPublicFiles.Last
