-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtShX.lean: ROW 0's DEBT OF THE LAST TABLE AT mgAll 𝔇 Mg, AT THE PUBLIC
PARAMETERS OFF Z, AT THE LAYER OF THE SHARED TABLE's CONSTANT's OWN TEST Sh.X (planAt Z N G) 12:
the ONE test that the last table lays for four of its premises. Two theorems.

  xkLast_of_ShX       Sh.X A 12 d = true gives the shared ledger's own test at its last border
                      (xkLast) at the constant's letters: Sh.X is that test WITH the last chain's
                      door's tests (XW_iff); the shape of Omega's message by shape_omega. (The two
                      are NOT one term: "rfl" is refused.)
  rowZeroOwed_atZ_sh  **THE ROW's STATEMENT AT THAT LAYER, IN THE TIGHT FORM**:
                      rowZeroOwed_mgAll_omegaX (Johnson/Flat/Last/RowZeroAtMgAllOmegaX.lean) at p
                      := P2Third.lastPar Z · Q := (planAt Z N G).Q · sentU | layU | layO := Sh's ·
                      sU := Q.S.fold.u · sS := Q.S.sharedSplit · Y := Sh.Y · X' := Sh.X (planAt Z
                      N G) 12. hX' by xkLast_of_ShX · hp by rfl · h0 | hOm by
                      Johnson/Desc/K14/Law/OmegaHasMsg.lean · hS from hSZ. LEFT: hSZ · h13 · hr ·
                      hMg · hI · hV · omega · rows · hlay · hsh · hseat · hB · hm · hent · hten ·
                      hlin · hl · hdot.
What is not claimed. NO MEMBER. All that RowZeroAtMgAllOmega.lean does not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtMgAllOmegaX
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.K14.Law.OmegaHasMsg
import Johnson.Desc.ProofFile.Lot.LastChainFour

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

/-- The constant's test at border 12 gives the ledger's own. -/
theorem xkLast_of_ShX {Xi' : Type} (A : ShPlan Xi') (d : St) (h : Sh.X A 12 d = true) :
    xkLast A.Q (Sh.sentU A) (Sh.layU A) (Sh.layO A) (omegaShapes_pos A.Q) A.Q.S.fold.u
      A.Q.S.sharedSplit (Sh.Y A) d = true := by
  have h1 := ((XW_iff A.Q (Sh.sentU A) (Sh.layU A) (Sh.layO A)
    (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Sh.Y A) (Sh.sentU A).size A.p 12 d).1 h).1
  show XK A.Q (Sh.sentU A) (Sh.layU A) (Sh.layO A)
    (A.Q.S.fold.u, shapeAt (parO A.Q) ⟨0, omegaShapes_pos A.Q⟩, A.Q.S.sharedSplit, Sh.Y A)
    (Sh.sentU A).size 12 d = true
  rw [shape_omega]
  exact h1

/-- **Row 0's debt at Z, at the layer of the shared table's constant's own test.** -/
theorem rowZeroOwed_atZ_sh {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ} {X₀ :
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
                            G)).tree.getD 0 0)), (Sh.layO (planAt Z N G)).part.getD 0 0)) (hlin : linOk (planAt Z N
                            G).Q.codes (planAt Z N G).Q.par.S = true) (hl : (planAt Z N G).Q.codes.lengthsOk = true) (hdot
                            : ∀ q (s : St) y w, DotEq (P2Third.lastPar Z).S.matrixRows (P2Third.lastPar Z).S.kCol (gLaid
                            𝔇.P13 get q) (omLast 𝔇.arr mem (planAt Z N G).Q (Sh.sentU (planAt Z N G)) w)
                            (s.loc.psiSh.map OnBytes.Model.Reading.gl.val) (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab 𝔇.cs
                            𝔇.arr xW w)) → MS.dot q s y w) : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (mgAll 𝔇
                            Mg) (meaningSigS 𝔇.cs 𝔇.G 𝔇.arr smp₂ ms₂ decT₂ MS)) ML (promSigS 𝔇.cs 𝔇.G smp₂ ms₂ stOf
                            bookOf Pm₀) (besideL (fillZ (P2Third.lastPar Z) R fun q => (get q).2) (Sh.X (planAt Z N G)
                            12)) (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull (First.flatPlaces true
                            Sound.linksFull true) q y ∧ Rc q) (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl)
                            (P2Third.lastPar Z)) base ds back r) :=
  rowZeroOwed_mgAll_omegaX 𝔇 Mg get smp₂ ms₂ decT₂ MS stOf bookOf Pm₀ N₁ Ns (P2Third.lastPar Z) R
      mem
    (planAt Z N G).Q (Sh.sentU (planAt Z N G)) (Sh.layU (planAt Z N G)) (Sh.layO (planAt Z N G))
    (omegaShapes_pos _) (planAt Z N G).Q.S.fold.u (planAt Z N G).Q.S.sharedSplit (Sh.Y (planAt Z N
        G))
    (Sh.X (planAt Z N G) 12) (xkLast_of_ShX (planAt Z N G)) ML t₁ t₂ base ds back r hr Rc hMg hI
        hV omega
    rows xW lay₀ (by rw [h13]; exact hSZ) hlay hsh hseat hB rfl (withOmega_pos _) x hm
    hent hten hlin hl hdot

end VerifiableInference.OnPublicFiles.Last
