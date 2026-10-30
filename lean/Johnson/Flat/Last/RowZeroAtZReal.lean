--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Last/RowZeroAtZReal.lean: ROW 0's DEBT OF THE LAST TABLE AT mgAll 𝔇 Mg, AT Z, UNDER
THE PLANNER's WRITTEN SIZING AT THE RELEASE's OWN TYPED SHAPE: the two tests on the codes and the
shape (hl: the codes' lengths are powers of two · hlin: the shape fits the codes) BY CALLS. Four
theorems.

  second_of_real   at the typed shape x₀ (realSized = some (x₀, codesFull2)) the last chain's test
                   on the public parameters accepts: real_test2
                   (Johnson/Goal/Numbers/K14SecondAt.lean: the kernel), opened.
  hl_of_written · hlin_of_written  at Q := p14Of Z.p.chains bp, by W.codes and W.shape.
  rowZeroOwed_atZ_real  rowZeroOwed_atZ (Johnson/Flat/Last/RowZeroAtZ.lean) with these two laid
                        in. A COROLLARY: the row's statement stays the tight form
                        rowZeroOwed_atZ_tight, which asks hl and hlin themselves. LEFT: W · hx ·
                        h13 · hr · hMg · hI · hV · omega · rows · hlay · hsh · hseat · hB · hm ·
                        hent · hten · hdot.
What is not claimed. That Written Z x₀ holds at a Z in scope (another file's). NO MEMBER. No
soundness.

-/
import Johnson.Flat.Last.RowZeroAtZ
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


open _root_.Desc.K14.Law (Written lin_last_of_written last_shared)
open _root_.Desc.K14 (p14Of)

open _root_.Desc.K14.Law (withOmega_pos omegaShapes_pos)

open VerifiableInference.Desc.Third (secondB real_test2)
open _root_.Johnson.G (codesFull2)

/-- The last chain's test on the public parameters accepts at the typed shape. -/
theorem second_of_real {x₀ : LinSized}
    (hx : VerifiableInference.Desc.K1.realSized = some (x₀, codesFull2)) :
    codesFull2.lengthsOk = true ∧ linOk codesFull2 x₀.shape = true := by
  have h := real_test2
  rw [hx, Option.any_some] at h
  unfold secondB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

theorem hl_of_written {Z : ProofFile.Pub} {x₀ : LinSized} (W : Written Z x₀)
    (hx : VerifiableInference.Desc.K1.realSized = some (x₀, codesFull2)) (bp : List (ℕ × ℕ)) :
    (p14Of Z.p.chains bp).codes.lengthsOk = true := by
  show Z.p.chains.made.sized.proof.codes.lengthsOk = true
  rw [W.codes]
  exact (second_of_real hx).1

theorem hlin_of_written {Z : ProofFile.Pub} {x₀ : LinSized} (W : Written Z x₀)
    (hx : VerifiableInference.Desc.K1.realSized = some (x₀, codesFull2)) (bp : List (ℕ × ℕ)) :
    linOk (p14Of Z.p.chains bp).codes (p14Of Z.p.chains bp).par.S = true := by
  show linOk Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch.shape = true
  rw [W.codes, W.shape]
  exact (second_of_real hx).2

/-- **Row 0's debt at Z under the planner's written sizing at the release's own typed shape**: the
two tests on the codes and the shape by the kernel. -/
theorem rowZeroOwed_atZ_real {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ}
    {X₀ : OnBytes.Model.Verify.Public} {Fr : Frame} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf 𝔇.cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀))
    (MS : MeaningS St (P × S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (Z : ProofFile.Pub) (x₀ : LinSized) (W : Written Z x₀)
    (hx : VerifiableInference.Desc.K1.realSized = some (x₀, codesFull2)) (bp : List (ℕ × ℕ))
    (h13 : 𝔇.P13 = VerifiableInference.Desc.K13.whereOf Z) (R : List Fmt.DeclaredRound)
    (mem : ℕ → Option Mem)
    (sentU : Array OracleNotice) (layU layO : TreeLay)
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
      onOcX Fr 𝔇.cs 𝔇.G 𝔇.arr get smp₂ ms₂ decT₂ (mgAll 𝔇 Mg) MS stOf bookOf Pm₀ N₁ Ns
          (P2Third.lastPar Z) R
        (xkLast (p14Of Z.p.chains bp) sentU layU layO (omegaShapes_pos (p14Of Z.p.chains bp)) sU
            sS Y)
        (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
        1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt (P2Third.lastPar Z).codes 𝔇.arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree)
                b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay)
    (hlay : lay₀ = linLayW 𝔇.cs 𝔇.P13.lin) (hsh : 𝔇.P13.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = 𝔇.N.w)
    (hB : ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (x : Mem)
    (hm : mem sentU.size = some x) (hent : (x.1.l.get x.2).1 = shapeAt (parO (p14Of Z.p.chains
        bp)) ⟨0, (omegaShapes_pos (p14Of Z.p.chains bp))⟩)
    (hten : x.1.seat x.2 =
      (t₁ + ((p14Of Z.p.chains bp).par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hdot : ∀ q (s : St) y w,
      DotEq (P2Third.lastPar Z).S.matrixRows (P2Third.lastPar Z).S.kCol (gLaid 𝔇.P13 get q)
          (omLast 𝔇.arr mem (p14Of Z.p.chains bp) sentU w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab 𝔇.cs 𝔇.arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mgAll 𝔇 Mg) (meaningSigS 𝔇.cs 𝔇.G 𝔇.arr smp₂ ms₂ decT₂ MS))
      ML (promSigS 𝔇.cs 𝔇.G smp₂ ms₂ stOf bookOf Pm₀)
      (besideL (fillZ (P2Third.lastPar Z) R fun q => (get q).2) (xkLast (p14Of Z.p.chains bp)
          sentU layU layO (omegaShapes_pos (p14Of Z.p.chains bp)) sU sS Y))
      (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) (P2Third.lastPar Z)) base ds back r) :=
  rowZeroOwed_atZ 𝔇 Mg get smp₂ ms₂ decT₂ MS stOf bookOf Pm₀ N₁ Ns Z x₀ W bp h13 R mem sentU layU
    layO sU sS Y ML t₁ t₂ base ds back r hr Rc hMg hI hV omega rows xW lay₀ hlay hsh hseat hB x hm
    hent hten (hlin_of_written W hx bp) (hl_of_written W hx bp) hdot

end VerifiableInference.OnPublicFiles.Last
