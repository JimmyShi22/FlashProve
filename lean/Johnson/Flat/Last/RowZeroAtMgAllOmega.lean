--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Last/RowZeroAtMgAllOmega.lean: ROW 0's DEBT OF THE LAST TABLE AT THE FIRST TABLE's
COMPOSED MEANING mgAll 𝔇 Mg, AT THE FULL LIST, WITH "Omega's two readers agree" (hO) PAID BY A
CALL: the composed meaning of the first table and the shared chain's ledger stand in one module.
One theorem: a joining.

  rowZeroOwed_mgAll_omega  rowZeroOwed_mgAll_full (Johnson/Flat/Last/RowZeroAtMgAllFull.lean) at
                           the layer X := xkLast … (the shared ledger's own test XK at its last
                           border) and omW := omLast …, with hO := hO_of_XK
                           (Johnson/Flat/Last/RowZeroOmega.lean). IN hO's PLACE: h0 · hp · hOm ·
                           hm · hent · hten · hlin · hl: facts on the public parameters.
What is not claimed. That the layer's promise at border 0 is earned (the door's half is another
. NO MEMBER. All that the two files named do not claim. No soundness.

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


/-- **Row 0's debt at the composed meaning, at the full list, at the layer of the shared ledger's
own test: Omega's two readers tied by calls.** -/
theorem rowZeroOwed_mgAll_omega {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ}
    {X₀ : OnBytes.Model.Verify.Public} {Fr : Frame} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf 𝔇.cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀))
    (MS : MeaningS St (P × S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (p : P₁₄) (R : List Fmt.DeclaredRound) (mem : ℕ → Option Mem) (Q : P14)
    (sentU : Array OracleNotice) (layU layO : TreeLay) (h0 : 0 < (shapesOf (parO Q)).length)
    (sU sS : OracleShape) (Y : ℕ → St → Bool)
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
        (xkLast Q sentU layU layO h0 sU sS Y)
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
      (besideL (fillZ p R fun q => (get q).2) (xkLast Q sentU layU layO h0 sU sS Y))
      (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_mgAll_full 𝔇 Mg get smp₂ ms₂ decT₂ MS stOf bookOf Pm₀ N₁ Ns p R _ ML t₁ t₂ base ds
    back r hr Rc hMg hI hV omega rows xW lay₀ _ hS hlay hsh hseat hB
    (hO_of_XK 𝔇.arr mem Q sentU layU layO h0 sU sS Y p hp hOm t₁ x hm hent hten hlin hl) hdot

end VerifiableInference.OnPublicFiles.Last
