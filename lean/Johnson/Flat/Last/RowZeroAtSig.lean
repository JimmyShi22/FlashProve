-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroAtSig.lean: ROW 0's DEBT OF THE LAST CHAIN's LEDGER (RowZeroOwed,
Johnson/Flat/Last/LastOnePage.lean) AT THE FILLINGS THAT LIE: the table's files' fillings by
signature (tiedNumbers · tiedMeaning get (meaningSig …) (meaningSigS …) · promSigS … · ocEnd …), the
book-keeping fillZ (ShapeRowZero.lean), and the maker's own piece of K14's second part: FROM TWO
TESTS, ONE CONDITION ON THE PINS, ONE CONDITION ON THE FIRST CHAIN's LAST PROMISE AND THREE LINKS TO
LETTERS. One abbreviation, two theorems: a joining of files of Johnson/Desc/Sound/,
Johnson/Desc/Third/Law/, Johnson/Flat/Last/. Three EQUATIONS
of letters would ask more than row 0 spends, and dotIs is not payable at the table's files' own
filling of the shared table's dot (mgPoint, Johnson/Desc/Sound/PointAtFilling.lean: the same DotEq,
Omega and W read by other terms). So: three implications inside the promise, and hEL.

OBJECT   as in Johnson/Desc/Third/Law/Row0AtFillZ.lean and Row0Make.lean.
USER     the field row0 of LastLeft (Johnson/LLT25R/LastLedger.lean): the
         conclusion is that field's type at hand := fun q => firstOfS (get q).2, ended := fun d =>
         (Desc.K14.ended d).map sharedOfEnd (so fillAt … hand ended is fillZ), the shared seat K14's
         own (so the shared chain's record is St), p := p14At Z, R := (c2 N).rounds, and the piece
         pieceZeroAt … (c0 Z) …, which is pieceOf (heldZero p) (D.t₁ + D.t₂) … by its text. NOT
         JOINED HERE: this file does not import Johnson/LLT25R/LastLedger.lean.
LETTERS  the table's files' cs G arr get smp₁ smp₂ ms₁ ms₂ (two lists of members: the first
         table's; the shared table's) decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links ps · ML · p R Pw
         t₁ t₂ · base ds back r.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  onSig … k            the table's promise at border k at these fillings: an abbreviation.
  dotEq_of_dotOmAt     DotOmAt gives (Dot)'s equation at any other readers of Omega and of W that
                       agree with its own as far as the two sums run: what the link dot is made of
                       at mgPoint's dot.
  rowZeroOwed_atSig    **the debt.** PAID INSIDE: the make (make_pieceOf) · ocBelow
                       (ocEnd_readsBelow_sig, from the test sampled) · tree (readsTree_sig) · the
                       seven public fields at fillZ · laid (from hEL: Oc and "no mark" stand in the
                       promise). LEFT, AS PREMISES: hr (the cut's extractor at number 0 is the
                       identity) · sampled · omega (the ledger's own two tests) · pins (the ledger's
                       pinsRead) · hEL (TO THE LETTER the conclusion of
                       hEL_at_ocEnd, Johnson/Desc/Sound/JointFilling.lean: there from one test on
                       the first table, at M₁ := its mg1Joint) · rows · ev · dot.
What is not claimed. NO MEMBER: no statement inside the promise at border 0 is shown at
these fillings. Outside "the record is the start's" the readers w₁Of and gOfS fall back on 0 and
on no weights in silence: a dot that is filled by dotI … is read at every border of the shared
chain at which dot lies open: that something was handed there is the shared table's promise's
matter. hEL_at_ocEnd is not called here: it is in Johnson/Flat/Last/RowZeroAtJoint.lean. All that
Row0AtFillZ.lean does not claim. No soundness of a verifier.

-/
import Johnson.Desc.Sound.ReadsBelowAt
import Johnson.Desc.Third.Law.Row0AtFillZ
import Johnson.Desc.Third.Law.Row0Make
import Johnson.Flat.Last.RowZeroPays

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
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid WRow)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt DotEq omegaOf)

/-- DotOmAt gives (Dot)'s equation at any other readers of Omega and of W that agree with its own as
far as the two sums run. -/
theorem dotEq_of_dotOmAt {S : LinShape} {g g' : Nat → GE} {d : St} {m : Words GE}
    {V V' om' : Nat → GE} (hg : g' = g)
    (hO : ∀ y < S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes S) m y = om' y)
    (hV : ∀ c < 2 ^ S.kCol, V c = V' c) (h : DotOmAt S g d m V) :
    DotEq S.matrixRows S.kCol g' om' (d.loc.psiSh.map OnBytes.Model.Reading.gl.val) V' := by
  subst hg
  exact dotEq_congr _ _ _ _ _ _ _ _ hO hV h

section
variable {P S₁ P₀ Cells Tok Xi : Type} (Fr : Frame) (cs : OnBytes.Codes)
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (get : P × S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St (P × S₁) (Wit Cells Tok MsgT))
  (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St)
  (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (p : P₁₄) (R : List Fmt.DeclaredRound)

/-- The table's promise at border k, at the fillings that lie. -/
abbrev onSig (k : ℕ) (a : ((P × S₁ × St) × S₃) × Fr.E.Str) : Prop :=
  onQ₃ (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
    (ocEnd get N₁ (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) links ps) k a

variable {Fr}

/-- **Row 0's debt at the fillings that lie.** -/
theorem rowZeroOwed_atSig {Cl : Type} (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (Pw : Where)
    (t₁ t₂ base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (r : Rest (ckP .two) Fr ((P × S₁ × St) × S₃) (Wit Cells Tok MsgT) ds)
    (hr : ∀ a τ w, r.ext a τ w = w)
    (sampled : sampledBelow base N₁ ((openSets links ps (start links))[ps.length]?.getD []) = true)
    (omega : (Ns.tenant .oOmega).1 < base)
    (pins : PinsReadBelow (S₃ := S₃) (tiedNumbers N₁ Ns)
      (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML base)
    (hEL : ∀ q y, ocEnd get N₁ (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) links ps q y →
      (get q).2.failed = none → EvalLaid Pw (get q).2)
    (rows : ∀ b w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links ps p R
        1 b →
      ML.rows b.1.2 w →
      ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
        ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
          (OnBytes.Means.wordsOn t.st
            (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w)))
    (ev : ∀ a w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links ps p R
        0 a →
      WRow Pw (get (a.1.1.1, a.1.1.2.1)).2
        (wordsFirst arr (get (a.1.1.1, a.1.1.2.1)).2.st (get (a.1.1.1, a.1.1.2.1)).2.book w) →
      M₁.wrow (get (a.1.1.1, a.1.1.2.1)) (strsOf Fr a.2) w)
    (dot : ∀ a w,
      onSig Fr cs G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links ps p R
        0 a →
      DotOmAt p.S (gOfS (get (a.1.1.1, a.1.1.2.1)).2) a.1.1.2.2
        (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w)
        (wvW arr p (fun q => (get q).2) (a.1.1.1, a.1.1.2.1) w) →
      MS.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w) :
    RowZeroOwed (tiedNumbers N₁ Ns)
      (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
      ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillZ p R fun q => (get q).2)
      (ocEnd get N₁ (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) links ps)
      (pieceOf (heldZero (P := P × S₁ × St) (Cl := Cl) p) base ds back r) := by
  obtain ⟨m1, m2, m3⟩ := make_pieceOf (P := P) (S₁ := S₁) (S₂ := St) (Cl := Cl) p base ds back r hr
  exact rowZeroOwed_of_left (rowZeroLeft_atWords (rowZeroAtWords_of_public
    (rowZeroPublic_atFillZ (Cl₀ := Unit) (R := R) (Pw := Pw) (lo := base) (arr := arr) (t₁ := t₁)
      (t₂ := t₂) (fs := fun q => (get q).2)
      { wrap := m1, hand := m2, idle := m3
        ocBelow := ocEnd_readsBelow_sig cs G arr smp₁ ms₁ decT₁ M₁ get base N₁ links ps sampled
        lo_le := Nat.le_refl _
        tree := readsTree_sig cs G arr smp₂ ms₂ decT₂ stOf bookOf MS Pm₀
        omegaBelow := omega
        pins := pins
        laid := fun a ha => hEL _ _ ha.1 ha.2.1
        rows := rows
        ev := ev
        dot := dot })))

end

end VerifiableInference.OnPublicFiles.Last
