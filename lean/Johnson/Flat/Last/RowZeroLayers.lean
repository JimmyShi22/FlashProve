-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroLayers.lean: ROW 0's DEBT OF THE LAST CHAIN's LEDGER WITH THE FIRST TABLE's
MEANING A LETTER: at any Mg₁ that meets the table's files' JointSays
(Johnson/Desc/Sound/PointAtLayers.lean: five equations of fields), in place of the named term
mg1Joint, which nobody composes. One abbreviation, two theorems.

Why. Different files lay the meaning's fields in layers, each field once; the meaning of record is a
composed term (mgAll). A law at mg1Joint is a law at a term that stands in no composition. The law
at "LIN point" is re-said so (point_leadsB_layers, PointAtLayers.lean); this is the like for row 0.

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger, at the composed meaning.
         rowZeroOwed_layers is called in Johnson/Flat/Last/RowZeroLetter.lean.
LETTERS  RowZeroBeside's, with Mg₁ itself where mg1W … Mg₁ stood.

  onLetX               the table's promise at border k, at the letter, at the layer besideL … X.
  rowZeroOwed_layers   **the debt.** OF J TWO CLAUSES ARE SPENT: wrow (the link ev: by rewriting)
                       and evalLaid (through hEL_layers (PointAtLayers.lean), by hEL_four, at
                       evalLaid_open_all). LEFT: J · hOc (the first chain's last promise reads the
                       strings below base: at mg1Joint it came of the test sampled; at a letter it
                       is asked outright) · hr · omega · pins · rows · dot.
  rowZeroOwed_beside'  rowZeroOwed_beside's statement again, as an instance: the named filling meets
                       J (jointSays_mg1Joint), and hOc comes of sampled: A CONTROL ON THE FORM.
What is not claimed. J at the composed term: untried (three of the five are
equations of functions: files that lay the same sentence in other words fail J). NO MEMBER. All
that RowZeroBeside.lean does not claim. No soundness.
J is JointFour (Johnson/Flat/Last/JointFour.lean): the table's files'
JointSays without its clause pileOne, which no law here spends and which does not close at the
composed meaning; the letter matC has left with it. JointSays.four gives J to whoever has the
five.

-/
import Johnson.Flat.Last.RowZeroBeside
import Johnson.Flat.Last.JointFour

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
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start Pub pubSets More)
open VerifiableInference.Desc.Third (S₃ P₁₄ firstOfS)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok vecAt wSitsMore
  evalLaid_open_all)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt DotEq omegaOf gLaid WSits hEL_at_ocEnd)

open _root_.Desc.K14.Law (JointFour JointSays.four hEL_four jointSays_mg1Joint)

/-- The table's promise at border k, at a letter for the first table's meaning, at the layer. -/
abbrev onLetX {P S₁ P₀ Cells Tok Xi : Type} (Fr : Frame) (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT))
    (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St)
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound)
    (X : St → Bool) (k : ℕ) (a : ((P × S₁ × St) × S₃) × Fr.E.Str) : Prop :=
  onQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
    (ocEnd get N₁ Mg₁ links (First.flatPlaces true links true)) k a

/-- **Row 0's debt at the layer, at a letter for the first table's meaning.** -/
theorem rowZeroOwed_layers {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
    (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Pw : Where) (wSeat : ℕ × ℕ)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (J : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat Mg₁)
    (hOc : OcReadsBelow base (ocEnd get N₁ Mg₁ links (First.flatPlaces true links true)))
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onLetX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns links p R X 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (dot : ∀ a w,
      onLetX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns links p R X 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (ocEnd get N₁ Mg₁ links (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) := by
  obtain ⟨m1, m2, m3⟩ := make_pieceOf (P := P) (S₁ := S₁) (S₂ := St) (Cl := Cl) p base ds back r hr
  have dn := fun k a h => ((onQ₃_beside (Fr := Fr) (tiedNumbers N₁ Ns)
    (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
    (ocEnd get N₁ Mg₁ links (First.flatPlaces true links true)) X k a).1 h)
  exact rowZeroOwed_of_left (rowZeroLeft_atWords (rowZeroAtWords_of_public
    (Cl₀ := Unit) (Pw := Pw) (cs := p.codes) (lo := base) (arr := arr) (t₁ := t₁) (t₂ := t₂)
    (fs := fun q => (get q).2)
    { wrap := m1, hand := m2, idle := m3
      ocBelow := hOc
      lo_le := Nat.le_refl _
      tree := readsTree_sig cs G arr smp₂ ms₂ decT₂ stOf bookOf MS Pm₀
      omegaBelow := omega
      pins := pins
      started := fun a ha => started_fillZ (dn 0 a ha).1
      weights := fun a ha => weights_fillZ (dn 0 a ha).1
      names := fun a ha => names_fillZ (dn 0 a ha).1
      placed := fun a ha => placed_fillZ (dn 0 a ha).1
      tenant := fun a ha => by
        obtain ⟨e, he, ht⟩ := tenant_fillZ (dn 0 a ha).1
        rw [sharedOfEnd_ended _ e he] at ht
        exact ht
      laid := fun a ha =>
        hEL_four J get N₁ links _
          (evalLaid_open_all Mg₁.more links) _ _ ha.1 ha.2.1
      shape := fun a s' ha hy _ =>
        Bool.and_eq_true_iff.2 ⟨shape_fillZ (dn 0 a ha).1 hy, (dn 0 a ha).2⟩
      codes := fun b hb => codes_fillZ (dn 1 b hb).1
      rows := rows
      ev := fun a w _ h => by
        show Mg₁.wrow _ _ _
        rw [J.wrow]
        exact h
      dot := dot }))

/-- A control on the form: rowZeroOwed_beside's statement, as an instance. -/
theorem rowZeroOwed_beside' {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
    (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
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
        Ns links p R X 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (dot : ∀ a w,
      onSigX Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀ N₁
        Ns links p R X 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_layers cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat
    (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) MS stOf bookOf Pm₀ N₁ Ns links p R X ML t₁ t₂
    base ds back r hr (jointSays_mg1Joint cs G arr smp₁ ms₁ _ _ Pw wSeat matC Mg₁ decT₁).four
    (ocEnd_readsBelow_sig cs G arr smp₁ ms₁ decT₁
      (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) get base N₁ links _ sampled)
    omega pins rows dot

end VerifiableInference.OnPublicFiles.Last
