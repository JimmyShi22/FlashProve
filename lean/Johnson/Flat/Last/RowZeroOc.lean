-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroOc.lean: ROW 0's DEBT OF THE LAST CHAIN's LEDGER WITH TWO LETTERS: Mg₁
(the first table's meaning, under the table's files' JointSays) AND Oc (the condition that the
first chain hands on to the two later chains), under two clauses: hIs
(Oc gives the first chain's last promise ocEnd …) and hBelow (Oc reads the oracles' strings below
the piece's base). One abbreviation, five theorems: the forms of rowZeroOwed_layers | dot_letter |
hW_letter | rowZeroOwed_letter | rowZeroOwed_reads (Johnson/Flat/Last/RowZeroLayers.lean |
RowZeroLetter.lean | RowZeroReads.lean), cut by program off these files, with Oc where ocEnd …
stood.

Why. The two later tables are counted at "ocEnd … ∧ reached": the
names that only carry a fact on the verifier's state leave the first table's door, and such a fact
is had of REACHED states, not from the promise. So every premise here that speaks of the first
chain's last state (hB; the links rows and dot; hW) is fenced by Oc, not by ocEnd: at Oc := fun q
y => ocEnd … q y ∧ Rc q it is asked with Rc q in hand. Here the three links stand at Oc, not at
ocEnd: weaker premises.


OBJECT, FIELD as in Johnson/Flat/Last/RowZeroAtSig.lean.
USER     the field row0 of the last chain's ledger, at its letter Oc. rowZeroOwed_reached is
         called in Johnson/Flat/Last/RowZeroAtMgAll.lean, rowZeroOwed_oc in
         Johnson/LLT25R/LastRowZero.lean.

  onOcX                 the table's promise at border k, at the two letters, at the layer.
  rowZeroOwed_oc        the debt: LEFT: hr · J · hIs · hBelow · omega · pins · rows · dot.
  dot_oc · hW_oc        the link dot from its ties; "W sits" at the ruled reader: hB under Oc.
  rowZeroOwed_ocLetter  the debt with dot so paid: LEFT: hr · J · hIs · hBelow · omega · pins ·
                        rows · hS · h3 · hlay · hsh · hseat · hB · hO · hdot.
  rowZeroOwed_reached   **the instance at Oc := fun q y => ocEnd … q y ∧ Rc q** (Rc a letter): hIs
                        by make; hBelow and pins by calls (ocEnd_readsBelow_eq · endTests_all ·
                        pins_letter); hB IS ASKED OF REACHED STATES ALONE: ∀ q, Rc q → no mark →
                        …. LEFT: hr · J · hd · hsn · hn · hl₀ · hI · hV · omega · rows · hS · h3 ·
                        hlay · hsh · hseat · hB · hO · hdot.
What is not claimed. That Rc can be earned; J and the three equations at the composed meaning; h3
at its door. NO MEMBER. All that the three files named above do not claim. No soundness.
J is JointFour (Johnson/Flat/Last/JointFour.lean): the table's files'
JointSays without its clause pileOne, which no law here spends and which does not close at the
composed meaning; the letter matC has left with it. JointSays.four gives J to whoever has the
five.

-/
import Johnson.Flat.Last.RowZeroReads

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

/-- The table's promise at border k, at the two letters, at the layer. -/
abbrev onOcX {P S₁ P₀ Cells Tok Xi : Type} (Fr : Frame) (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT))
    (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St)
    (N₁ : Numbers) (Ns : NumbersS) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (Oc : P × S₁ → Strs → Prop) (k : ℕ) (a : ((P × S₁ × St) × S₃) × Fr.E.Str) : Prop :=
  onQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X) Oc k a

/-- **Row 0's debt at the layer, at letters for the first table's meaning and for the condition that
the first chain hands on.** -/
theorem rowZeroOwed_oc {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
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
    (Oc : P × S₁ → Strs → Prop)
    (hIs : ∀ q y, Oc q y → ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y)
    (hBelow : OcReadsBelow base Oc)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onOcX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns p R X Oc 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (dot : ∀ a w,
      onOcX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns p R X Oc 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      Oc
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) := by
  obtain ⟨m1, m2, m3⟩ := make_pieceOf (P := P) (S₁ := S₁) (S₂ := St) (Cl := Cl) p base ds back r hr
  have dn := fun k a h => ((onQ₃_beside (Fr := Fr) (tiedNumbers N₁ Ns)
    (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
    Oc X k a).1 h)
  exact rowZeroOwed_of_left (rowZeroLeft_atWords (rowZeroAtWords_of_public
    (Cl₀ := Unit) (Pw := Pw) (cs := p.codes) (lo := base) (arr := arr) (t₁ := t₁) (t₂ := t₂)
    (fs := fun q => (get q).2)
    { wrap := m1, hand := m2, idle := m3
      ocBelow := hBelow
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
          (evalLaid_open_all Mg₁.more links) _ _ (hIs _ _ ha.1) ha.2.1
      shape := fun a s' ha hy _ =>
        Bool.and_eq_true_iff.2 ⟨shape_fillZ (dn 0 a ha).1 hy, (dn 0 a ha).2⟩
      codes := fun b hb => codes_fillZ (dn 1 b hb).1
      rows := rows
      ev := fun a w _ h => by
        show Mg₁.wrow _ _ _
        rw [J.wrow]
        exact h
      dot := dot }))

/-- **The link dot from its ties, at the two letters.** -/
theorem dot_oc {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame} (cs : OnBytes.Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
    (Pw : Where) (wSeat : ℕ × ℕ)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
    (links : List ModelPart) (p : P₁₄) (R : List Fmt.DeclaredRound) (X : St → Bool)
    (t₁ : ℕ) (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE)
    (J : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat Mg₁)
    (Oc : P × S₁ → Strs → Prop)
    (hIs : ∀ q y, Oc q y → ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y)
    (hS : Pw.lin = p.S)
    (hW : ∀ q y D, Oc q y →
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
      onOcX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns p R X Oc 0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w := by
  intro a w ha h
  obtain ⟨ha', hx⟩ := (onQ₃_beside _ _ _ _ _ X 0 a).1 ha
  have hL : EvalLaid Pw (get (a.1.1.1, a.1.1.2.1)).2 :=
    hEL_four J get N₁ links _
      (evalLaid_open_all Mg₁.more links) _ _ (hIs _ _ ha.1) ha.2.1
  obtain ⟨D, hD, _⟩ := laidOf_ok hL
  exact hdot _ _ _ _ (dotEq_of_dotOmAt (gLaid_is_gOfS Pw get _ hL) (hO _ w hx)
    (wTie cs arr xW lay₀ p Pw get hS _ D hL hD (hW _ _ D ha.1 ha.2.1 hD)
      (started_first (started_fillZ ha')) w) h)

/-- **"W sits" at the ruled reader, at the two letters**: hB is asked under Oc. -/
theorem hW_oc {P S₁ P₀ Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem)
    (Pw : Where) (wSeat : ℕ × ℕ)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (N₁ : Numbers) (links : List ModelPart) (xW : Mem)
    (lay₀ : VectorLay)
    (J : JointFour cs G arr smp₁ ms₁ (fun a => a.2.st)
      (fun a w => tabAt a.2.st.codes arr (seatBy noFirst a.2.book) a.2.st w) Pw wSeat Mg₁)
    (h3 : wSitsItem ∈ (First.pubSets Mg₁.more links
      (First.flatPlaces true links true))[(First.flatPlaces true links true).length]?.getD [])
    (Oc : P × S₁ → Strs → Prop)
    (hIs : ∀ q y, Oc q y → ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y)
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y, Oc q y → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r) :
    ∀ q y D, Oc q y → (get q).2.failed = none → laidOf Pw (get q).2 = some D →
      WSits (Cells := Cells) (Tok := Tok) cs arr xW lay₀ (fun q => (get q).2.st)
        (fun q w => tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w)
        q D := by
  intro q y D ho hm hD
  have W := hW_four J get N₁ links _ xW lay₀
    (fun q => (get q).2.st) (fun q w => tabByPlace cs arr (get q).2 w)
    h3 (fun _ => rfl) hlay
    (fun p w n j t sh => tabByPlace_book cs arr (get p).2 w n j t sh) hsh hseat q y D (hIs q y ho)
    hm hD
  obtain ⟨hN, hF, hP⟩ := hB q y ho hm
  obtain ⟨x, hx, _⟩ := W.there
  have hst : D.st = (get q).2.st := W.st
  rw [hst] at hx
  have hlt : D.w < (get q).2.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  obtain ⟨r, hr⟩ := hP D.w hlt
  have hs := seatFirst_place (get q).2.book hN hF D.w r hr
  have hc : (get q).2.st.codes = cs := by rw [← hst]; exact W.codes
  refine { W with tab := fun w => ?_ }
  rw [← W.tab w]
  show tabAt (get q).2.st.codes arr (seatBy noFirst (get q).2.book) (get q).2.st w D.w =
    tabByPlace cs arr (get q).2 w D.w
  unfold Sound.tabAt tabByPlace
  rw [hs, hr, hx, hc]

/-- **Row 0's debt at the two letters, its link dot paid from its ties and "W sits" by calls.** -/
theorem rowZeroOwed_ocLetter {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
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
    (Oc : P × S₁ → Strs → Prop)
    (hIs : ∀ q y, Oc q y → ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y)
    (hBelow : OcReadsBelow base Oc)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (rows : ∀ b w,
      onOcX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns p R X Oc 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE) (hS : Pw.lin = p.S)
    (h3 : wSitsItem ∈ (First.pubSets Mg₁.more links
      (First.flatPlaces true links true))[(First.flatPlaces true links true).length]?.getD [])
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q y, Oc q y → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (hO : ∀ (d : St) (w : Wit Cells Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      Oc
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_oc cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat Mg₁ MS stOf bookOf Pm₀ N₁ Ns
    links p R X ML t₁ t₂ base ds back r hr J Oc hIs hBelow omega pins rows
    (dot_oc cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat Mg₁ MS stOf bookOf Pm₀ N₁ Ns
      links p R X t₁ xW lay₀ omW J Oc hIs hS
      (hW_oc cs G arr get smp₁ ms₁ Pw wSeat Mg₁ N₁ links xW lay₀ J h3 Oc hIs hlay hsh hseat
        hB)
      hO hdot)

/-- **Row 0's debt where the first chain hands on its last promise WITH "reached" beside it**: the
two "reads below" paid by calls; hB is asked of reached states alone. -/
theorem rowZeroOwed_reached {Cl : Type} {P S₁ P₀ Cells Tok Xi : Type} {Fr : Frame}
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
    (Rc : P × S₁ → Prop)
    (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (hd : Mg₁.decodes = decodesOf decT₁) (hsn : Mg₁.shown = shownJT cs G ms₁)
    (hn : Mg₁.noColl = noCollJT cs G smp₁ ms₁) (hl₀ : linksOk links = true)
    (hI : N₁.index.1 < base) (hV : N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base)
    (rows : ∀ b w,
      onOcX Fr cs G arr get smp₂ ms₂ decT₂ Mg₁ MS stOf bookOf Pm₀ N₁ Ns p R X
        (fun q y => ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y ∧ Rc q) 1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (xW : Mem) (lay₀ : VectorLay) (omW : Wit Cells Tok MsgT → ℕ → GE) (hS : Pw.lin = p.S)
    (h3 : wSitsItem ∈ (First.pubSets Mg₁.more links
      (First.flatPlaces true links true))[(First.flatPlaces true links true).length]?.getD [])
    (hlay : lay₀ = linLayW cs Pw.lin) (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hseat : xW.1.seat xW.2 = wSeat)
    (hB : ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r)
    (hO : ∀ (d : St) (w : Wit Cells Tok MsgT), X d = true → ∀ y < p.S.matrixRows,
      omegaOf d.loc (linLayOmega d.st.codes p.S) (wordsShared arr t₁ d.st d.book w) y = omW w y)
    (hdot : ∀ q (s : St) y w,
      DotEq p.S.matrixRows p.S.kCol (gLaid Pw get q) (omW w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → MS.dot q s y w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ p R fun q => (get q).2) X)
      (fun q y => ocEnd get N₁ Mg₁ links (First.flatPlaces true links true) q y ∧ Rc q)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) :=
  rowZeroOwed_ocLetter cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Pw wSeat Mg₁ MS stOf bookOf Pm₀ N₁
    Ns links p R X ML t₁ t₂ base ds back r hr J _ (fun _ _ h => h.1)
    (fun q y y' hc hl h =>
      ⟨ocEnd_readsBelow_eq cs G smp₁ ms₁ decT₁ Mg₁ hd hsn hn get base N₁ links _
        (endTests_all links hl₀ base N₁ hI hV).1 q y y' hc hl h.1, h.2⟩)
    omega (pins_letter cs G arr get smp₁ smp₂ ms₁ ms₂ decT₂ Mg₁ MS N₁ Ns ML base J.pin hI hV omega)
    rows xW lay₀ omW hS h3 hlay hsh hseat (fun q _ h => hB q h.2) hO hdot

end VerifiableInference.OnPublicFiles.Last
