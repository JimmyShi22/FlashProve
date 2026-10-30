-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroBeside.lean: A TEST ON THE SHARED CHAIN's LAST RECORD LAID BESIDE THE LAST
TABLE's BOOK-KEEPING (besideL PL X: shape k q e s && X e: Johnson/Desc/Last/BesideL.lean): ROW 0's
DEBT OVER IT: so that what a link needs of that record is had INSIDE the promise. One abbreviation,
three theorems.

Why. Row 0's link dot wants "Omega's two readers agree" (hO of dot_of_ties,
Johnson/Flat/Last/RowZeroDot.lean). omegaTie (Johnson/Desc/K14/Law/OmegaTie.lean) gives that from
tests on the shared chain's last record e. The last table's promise (onL,
Johnson/Desc/Last/BordersLast.lean) holds of e only Omega's "no collision" and PL.shape k q e s. So
the tests are laid into the shape. e does not turn along the last chain (a piece of it hands on what
was handed): so the conjunct rides for nothing.

OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger, at PL := besideL (fillZ …) X. Nobody calls it.
LETTERS  RowZeroAtPlaces'; X : St → Bool.

  onSigX                the table's promise at border k, at the fillings that lie, at the layer.
  rowZeroOwed_beside    **row 0's debt at the layer.** LEFT: hr · sampled · omega · pins · rows ·
                        dot: the last two asked INSIDE THE LAYER's PROMISE: with X e in hand.
  dot_beside            the link dot from its ties, at the layer: hO is asked with X e in hand.
  rowZeroOwed_ties      **the two together**: dot has left; in its place: hS · hW · hO · hdot.
What is not claimed. THAT THE LAYER's PROMISE AT BORDER 0 IS EARNED: the last chain's door owes
X e beside what it owes already: from the shared chain's last promise. That the ledger's other three
rows stand at the layer: each is to be lifted (its piece hands on what was handed). NO MEMBER. All
that RowZeroAtPlaces.lean and RowZeroDot.lean do not claim. No soundness.

-/
import Johnson.Flat.Last.RowZeroDot
import Johnson.Desc.Last.BesideL

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

/-- The table's promise at border k, at the fillings that lie, at the layer. -/
abbrev onSigX {P S₁ P₀ Cells Tok Xi : Type} (Fr : Frame) (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool) (k : ℕ)
    (a : ((P × S₁ × St) × S₃) × Fr.E.Str) : Prop :=
  onQ₃ (tiedNumbers N₁ Ns)
    (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
    (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
      (First.flatPlaces true links true)) k a

/-- **Row 0's debt at the layer.** -/
theorem rowZeroOwed_beside {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
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
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) := by
  obtain ⟨m1, m2, m3⟩ := make_pieceOf (P := P) (S₁ := S₁) (S₂ := St) (Cl := Cl) p base ds back r hr
  have dn := fun k a h => ((onQ₃_beside (Fr := Fr) (tiedNumbers N₁ Ns)
    (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
    (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
      (First.flatPlaces true links true)) X k a).1 h)
  exact rowZeroOwed_of_left (rowZeroLeft_atWords (rowZeroAtWords_of_public
    (Cl₀ := Unit) (Pw := Pw) (cs := p.codes) (lo := base) (arr := arr) (t₁ := t₁) (t₂ := t₂)
    (fs := fun q => (get q).2)
    { wrap := m1, hand := m2, idle := m3
      ocBelow := ocEnd_readsBelow_sig cs G arr smp₁ ms₁ decT₁
        (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) get base N₁ links _ sampled
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
        hEL_at_ocEnd cs G arr smp₁ ms₁ decT₁ _ _ Pw wSeat matC Mg₁ get N₁ links _
          (evalLaid_open_all (Mg₁.more.merge wSitsMore) links) _ _ ha.1 ha.2.1
      shape := fun a s' ha hy _ =>
        Bool.and_eq_true_iff.2 ⟨shape_fillZ (dn 0 a ha).1 hy, (dn 0 a ha).2⟩
      codes := fun b hb => codes_fillZ (dn 1 b hb).1
      rows := rows
      ev := fun _ _ _ h => h
      dot := dot }))

/-- **The link dot from its ties, at the layer**: hO is asked with the test's yes in hand. -/
theorem dot_beside {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pw : Where) (wSeat : ℕ × ℕ)
    (matC : Cells → ℕ → ℕ → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (t₁ : ℕ) (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE)
    (hS : Pw.lin = p.S)
    (hW : ∀ q y D,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
      (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D)
    (hO : ∀ (d : St) (w : Wit Cells Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    ∀ a w,
      onSigX Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀ N₁
        Ns links p R X 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w := by
  intro a w ha h
  obtain ⟨ha', hx⟩ := (onQ₃_beside _ _ _ _ _ X 0 a).1 ha
  have hL : EvalLaid Pw (get (a.1.1.1, a.1.1.2.1)).2 :=
    hEL_at_ocEnd cs G arr smp₁ ms₁ decT₁ _ _ Pw wSeat matC Mg₁ get N₁ links _
      (evalLaid_open_all (Mg₁.more.merge wSitsMore) links) _ _ ha.1 ha.2.1
  obtain ⟨D, hD, _⟩ := laidOf_ok hL
  exact hdot _ _ _ _ (dotEq_of_dotOmAt (gLaid_is_gOfS Pw get _ hL) (hO _ w hx)
    (wTie cs arr xW lay₀ p Pw get hS _ D hL hD (hW _ _ D ha.1 ha.2.1 hD)
      (started_first (started_fillZ ha')) w) h)

/-- **Row 0's debt at the layer, the link dot paid from its ties.** -/
theorem rowZeroOwed_ties {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
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
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE) (hS : Pw.lin = p.S)
    (hW : ∀ q y D,
      ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true) q y →
      (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D)
    (hO : ∀ (d : St) (w : Wit Cells Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (ocEnd get N₁ (mg1W cs G arr smp₁ ms₁ decT₁ Pw wSeat matC Mg₁) links
        (First.flatPlaces true links true))
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_beside cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf
    Pm₀ N₁ Ns links p R X ML t₁ t₂ base ds back r hr sampled omega pins rows
    (dot_beside cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ Pw wSeat matC Mg₁ MS stOf bookOf Pm₀ N₁
      Ns links p R X t₁ xW lay₀ omW hS hW hO hdot)

end VerifiableInference.OnPublicFiles.Last
