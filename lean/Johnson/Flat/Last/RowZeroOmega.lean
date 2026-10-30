-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroOmega.lean: THE LEDGER OF THE SHARED CHAIN AND ROW 0 OF THE LAST CHAIN MEET
IN ONE MODULE: "Omega's two readers agree" (hO of rowZeroOwed_ties | _sits,
Johnson/Flat/Last/RowZeroBeside.lean | RowZeroWSits.lean) BY CALLS, at the layer X := the shared
ledger's own test XK at its last border. Two abbreviations, two theorems: a joining.

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger. RowZeroAtMgAllOmegaX.lean calls hO_of_XK.
LETTERS  RowZeroWSits'; the shared ledger's Q · sentU · layU · layO · sU · sS · Y · mem.

  xkLast …          the layer's test: XK … 12 d (Johnson/Desc/K14/Law/LedgerNineTen.lean).
  omLast …          the fixed reader of Omega: omWK at o_omega's number by the public parameters
                    (Johnson/Desc/K14/Law/LedgerOne.lean).
  hO_of_XK          **hO, to the letter**, at these two. THE CALLS: XK_iff · codY_of_codX · omegaTie
                    (Johnson/Desc/K14/Law/OmegaTie.lean) ·
                    omegaInRange_of_lengths (Johnson/Desc/K14/Law/InRange.lean) ·
                    wordsSh_is (rfl).
  rowZeroOwed_omega **row 0's debt**: rowZeroOwed_sits with hO so paid. IN ITS PLACE: hp (the last
                    chain's shape is the shared chain's) · hOm · hm · hent · hten (the member at
                    o_omega's number: its entry and its seat by the public parameters) · hlin · hl
                    (two tests on the public codes): omega_of_XK's own.
What is not claimed. That the layer's promise at border 0 is earned: the door's half is another
file's (sh₃_at_pub_X, Johnson/Desc/Last/ShapeDoorWithX.lean), not called here. NO MEMBER. All that
RowZeroWSits.lean does not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroWSits
import Johnson.Desc.K14.Law.LedgerLastPaid
import Johnson.Desc.K14.Law.LedgerReaderAt
import Johnson.Desc.K14.Law.OmegaTie

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

/-- The layer's test: the shared ledger's own, at its last border. -/
abbrev xkLast (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (h0 : 0 < (shapesOf (parO Q)).length) (sU sS : OracleShape) (Y : ℕ → St → Bool) : St → Bool :=
  fun d => XK Q sentU layU layO (sU, shapeAt (parO Q) ⟨0, h0⟩, sS, Y) sentU.size 12 d

/-- The fixed reader of Omega, at o_omega's number by the public parameters. -/
abbrev omLast {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem) (Q : P14)
    (sentU : Array OracleNotice) : Wit Cells Tok MsgT → ℕ → GE :=
  fun w y => omWK Q.codes arr mem (rdK Q.codes) sentU.size Q w y

/-- **Omega's two readers agree wherever the shared ledger's test says yes at its last border.** -/
theorem hO_of_XK {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem) (Q : P14)
    (sentU : Array OracleNotice) (layU layO : TreeLay) (h0 : 0 < (shapesOf (parO Q)).length)
    (sU sS : OracleShape) (Y : ℕ → St → Bool) (p : P₁₄) (hp : p.S = Q.par.S)
    (hOm : 0 < (withOmega Q.S).size) (t₁ : ℕ) (x : Mem) (hm : mem sentU.size = some x)
    (hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hlin : linOk Q.codes Q.par.S = true) (hl : Q.codes.lengthsOk = true) :
    ∀ (d : St) (w : Wit Cells Tok MsgT), xkLast Q sentU layU layO h0 sU sS Y d = true →
      ∀ y < p.S.matrixRows,
        omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y =
          omLast arr mem Q sentU w y := by
  intro d w hX y hy
  obtain ⟨g1, g2, g3, _⟩ := (XK_iff Q sentU.size _ sentU layU layO 12 d).1 hX
  have hY := codY_of_codX Q 12 12 d g2
  have hc : d.st.codes = Q.codes := ((codY_iff Q 12 d).1 hY).resolve_left (by omega)
  rw [hp] at hy ⊢
  rw [← wordsSh_is]
  exact omegaTie arr mem Q sentU layU layO d hOm h0 sentU.size rfl g1 hY g3 t₁ w x hm hent hten
    (fun y hy => by
      rw [hc, hent, shape_omega Q h0]
      exact omegaInRange_of_lengths Q.codes Q.par.S hl hlin y hy) y hy

/-- **Row 0's debt at the layer of the ledger's own test, Omega's two readers tied by calls.** -/
theorem rowZeroOwed_omega {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
    (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound)
    (mem : ℕ → Option Mem) (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (h0 : 0 < (shapesOf (parO Q)).length) (sU sS : OracleShape) (Y : ℕ → St → Bool)
    (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (sampled : sampledBelow base N₁ ((openSets links (First.flatPlaces true links true)
      (start links))[(First.flatPlaces true links true).length]?.getD []) = true)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onSigX Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀ N₁
        Ns links p R (xkLast Q sentU layU layO h0 sU sS Y) 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (hS : Pw.lin = p.S)
    (hA : ((none, "K13.wSits") : First.MoreName) ∉ (Mg₁.more.rows links placeSeal).drops)
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
      (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (hp : p.S = Q.par.S) (hOm : 0 < (withOmega Q.S).size) (x : Mem)
    (hm : mem sentU.size = some x) (hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hlin : linOk Q.codes Q.par.S = true) (hl : Q.codes.lengthsOk = true)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omLast arr mem Q sentU w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀)
      (besideL (fillZ p R fun q => (get q).2) (xkLast Q sentU layU layO h0 sU sS Y))
      (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_sits cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀
    N₁ Ns links p R _ ML t₁ t₂ base ds back r hr sampled omega pins rows xW lay₀ _ hS hA hlay hsh
    hseat hB (hO_of_XK arr mem Q sentU layU layO h0 sU sS Y p hp hOm t₁ x hm hent hten hlin hl) hdot

end VerifiableInference.OnPublicFiles.Last
