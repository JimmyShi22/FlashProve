-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtMgAllFull.lean: ROW 0's DEBT OF THE LAST TABLE AT THE FIRST TABLE's
COMPOSED MEANING mgAll 𝔇 Mg, AT THE FULL LIST OF SEGMENTS: the two premises of rowZeroOwed_mgAll
(Johnson/Flat/Last/RowZeroAtMgAll.lean) that are tests on the table alone, by the kernel. Four
theorems.

Why. Where Mg's own list of extra public tests is empty, mgAll's list is the CLOSED
term mgMore (mgAll_more_closed, Johnson/Desc/Sound/MgAllAt.lean): it does not hang on 𝔇. So "the
test K13.wSits is open at the first table's last border" is a closed sentence at a written list of
segments.

  linksOk_full          the full list of segments is lawful: the kernel.
  wSits_open_mgMore     "K13.wSits" is open at the last border, at mgMore, at the full list: the
                        kernel.
  wSits_open_mgAll      so at mgAll 𝔇 Mg, where Mg.more = {}.
  rowZeroOwed_mgAll_full  **the debt**: LEFT: hr · hMg · hI · hV · omega · rows · hS · hlay · hsh ·
                        hseat · hB · hO · hdot.
What is not claimed. That Mg.more = {} at the base meant. The small list. NO MEMBER. All that
RowZeroAtMgAll.lean does not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtMgAll
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Sound.AtDriver

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

open VerifiableInference.Desc.First (Pub pubSets More)
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.K13.Law (EvalLaid laidOf_ok evalLaid_open_all wSitsItem)
open _root_.Desc.K14.Law (DotOmAt JointFour hEL_four hW_four)

open VerifiableInference.Desc.First (linksOk)
open VerifiableInference.Desc.K13.Law (endTests_all)

open VerifiableInference.Desc.First (linksOk)
open _root_.Desc.K14.Law (JointFour)


set_option maxRecDepth 1000000 in
/-- The full list of segments is lawful. -/
theorem linksOk_full : linksOk Sound.linksFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- "K13.wSits" is open at the first table's last border, at the composed meaning's closed list. -/
theorem wSits_open_mgMore :
    ((First.pubSets mgMore Sound.linksFull (First.flatPlaces true Sound.linksFull true))[
      (First.flatPlaces true Sound.linksFull true).length]?.getD []).contains wSitsItem = true := by
  decide +kernel

/-- So at the composed meaning, where Mg's own list is empty. -/
theorem wSits_open_mgAll {P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ}
    {X₀ : OnBytes.Model.Verify.Public} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (h : Mg.more = {}) :
    wSitsItem ∈ (First.pubSets (mgAll 𝔇 Mg).more Sound.linksFull
      (First.flatPlaces true Sound.linksFull true))[
        (First.flatPlaces true Sound.linksFull true).length]?.getD [] := by
  rw [mgAll_more_closed 𝔇 Mg h]
  exact List.contains_iff_mem.1 wSits_open_mgMore

/-- **Row 0's debt at the composed meaning, at the full list of segments**: the two tests on the
table by the kernel. -/
theorem rowZeroOwed_mgAll_full {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ}
    {X₀ : OnBytes.Model.Verify.Public} {Fr : Frame} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf 𝔇.cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀))
    (MS : MeaningS St (P × S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (ML : MeaningL S₃ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit (CellsQ rows₀ cols₀) Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (Rc : P × S₁ → Prop)
    (hMg : Mg.more = {})
    (hI : N₁.index.1 < base) (hV : N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base)
    (rows : ∀ b w,
      onOcX Fr 𝔇.cs 𝔇.G 𝔇.arr get smp₂ ms₂ decT₂ (mgAll 𝔇 Mg) MS stOf bookOf Pm₀ N₁ Ns p R X
        (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
        1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes 𝔇.arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit (CellsQ rows₀ cols₀) Tok MsgT → ℕ → GE)
    (hS : 𝔇.P13.lin = p.S)
    (hlay : lay₀ = linLayW 𝔇.cs 𝔇.P13.lin) (hsh : 𝔇.P13.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = 𝔇.N.w)
    (hB : ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (hO : ∀ (d : St) (w : Wit (CellsQ rows₀ cols₀) Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared 𝔇.arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid 𝔇.P13 get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab 𝔇.cs 𝔇.arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mgAll 𝔇 Mg) (meaningSigS 𝔇.cs 𝔇.G 𝔇.arr smp₂ ms₂ decT₂ MS))
      ML (promSigS 𝔇.cs 𝔇.G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
          (First.flatPlaces true Sound.linksFull true) q y ∧ Rc q)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_mgAll 𝔇 Mg get smp₂ ms₂ decT₂ MS stOf bookOf Pm₀ N₁ Ns Sound.linksFull p R X ML t₁ t₂
    base ds back r hr Rc linksOk_full hI hV omega rows xW lay₀ omW hS
    (wSits_open_mgAll 𝔇 Mg hMg) hlay hsh hseat hB hO hdot

end VerifiableInference.OnPublicFiles.Last
