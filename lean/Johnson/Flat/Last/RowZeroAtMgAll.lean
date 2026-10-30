-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtMgAll.lean: ROW 0's DEBT OF THE LAST TABLE AT THE FIRST TABLE's
COMPOSED MEANING: mgAll 𝔇 Mg (Johnson/Desc/Sound/MgAll.lean:
the reference form). Two theorems.

Why. Every law in row 0's files had the first table's meaning as a letter Mg₁ under premises on it
(J : JointFour; three equations of fields). A law at a letter says something only where the
premises are met. Here they are met at the one term that is the reference form, by the word of the
tables' files.

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger, at the composed meaning.
         rowZeroOwed_mgAll is called in Johnson/Flat/Last/RowZeroAtMgAllFull.lean.

  jointFour_mgAll    **the four clauses hold at mgAll 𝔇 Mg**, at cs G arr smp₁ ms₁ := 𝔇's, Pw :=
                     𝔇.P13, wSeat := 𝔇.N.w and the reader by the state's own book: pin · wrow ·
                     evalLaid by rfl; "K13.wSits" by wSitsC_eq | wSeatC_eq
                     (Johnson/Desc/K13/Law/FillK13Laws.lean).
  rowZeroOwed_mgAll  **the debt**: rowZeroOwed_reached (Johnson/Flat/Last/RowZeroOc.lean) there: J
                     by jointFour_mgAll; the three equations by MgAll.lean's own mgAll_decodes |
                     mgAll_shown | mgAll_noColl. NO PREMISE ON THE FIRST TABLE's MEANING IS LEFT
                     BUT h3 (the test "K13.wSits" is open at the first table's last border, at
                     mgAll's own list of extra public tests). LEFT: hr · hl₀ · hI · hV · omega ·
                     rows · hS · h3 · hlay · hsh · hseat · hB · hO · hdot.
What is not claimed. 𝔇, Mg, N₁, links and the later tables' fillings are letters still: NO
MEMBER. h3 at mgAll's door. That Rc can be earned. JointSays' fifth clause (pileOne) at mgAll: it
does not close by rfl, and row 0 does not spend it. No soundness.

-/
import Johnson.Flat.Last.RowZeroOc
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.K13.Law.FillK13Laws

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

/-- **The four clauses hold at the composed meaning.** -/
theorem jointFour_mgAll {P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ} {X₀ : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) :
    JointFour 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes 𝔇.arr (seatBy noFirst a.2.book) a.2.st w) 𝔇.P13 𝔇.N.w
      (mgAll 𝔇 Mg) :=
  ⟨rfl, rfl, fun _ => rfl, fun a => by
    rw [← VerifiableInference.Desc.K13.Law.wSitsC_eq, ← VerifiableInference.Desc.K13.Law.wSeatC_eq]
    rfl⟩

/-- **Row 0's debt at the composed meaning of the first table, with "reached" beside the first
chain's last promise.** -/
theorem rowZeroOwed_mgAll {Cl : Type} {P S₁ P₀ Tok Xi : Type} {rows₀ cols₀ nR : ℕ}
    {X₀ : OnBytes.Model.Verify.Public} {Fr : Frame} (𝔇 : MgData Xi P₀ Tok rows₀ cols₀ nR X₀)
    (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf 𝔇.cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ rows₀ cols₀))
    (MS : MeaningS St (P × S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (ML : MeaningL S₃ (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit (CellsQ rows₀ cols₀) Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (Rc : P × S₁ → Prop)
    (hl₀ : linksOk links = true)
    (hI : N₁.index.1 < base) (hV : N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base)
    (rows : ∀ b w,
      onOcX Fr 𝔇.cs 𝔇.G 𝔇.arr get smp₂ ms₂ decT₂ (mgAll 𝔇 Mg) MS stOf bookOf Pm₀ N₁ Ns p R X
        (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) links (First.flatPlaces true links true) q y ∧ Rc q)
        1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes 𝔇.arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit (CellsQ rows₀ cols₀) Tok MsgT → ℕ → GE)
    (hS : 𝔇.P13.lin = p.S)
    (h3 : wSitsItem ∈ (First.pubSets (mgAll 𝔇 Mg).more links
      (First.flatPlaces true links true))[(First.flatPlaces true links true).length]?.getD [])
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
      (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) links (First.flatPlaces true links true) q y ∧ Rc q)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_reached 𝔇.cs 𝔇.G 𝔇.arr get 𝔇.smp smp₂ 𝔇.ms ms₂ decT₂ 𝔇.P13 𝔇.N.w (mgAll 𝔇 Mg) MS stOf
    bookOf Pm₀ N₁ Ns links p R X ML t₁ t₂ base ds back r hr (jointFour_mgAll 𝔇 Mg) Rc 𝔇.decT
    (mgAll_decodes 𝔇 Mg) (mgAll_shown 𝔇 Mg) (mgAll_noColl 𝔇 Mg) hl₀ hI hV omega rows xW lay₀ omW hS
    h3 hlay hsh hseat hB hO hdot

end VerifiableInference.OnPublicFiles.Last
