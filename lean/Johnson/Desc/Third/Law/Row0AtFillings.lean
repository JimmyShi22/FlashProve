-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0AtFillings.lean: ROW 0 OF THE LAST CHAIN's TABLE OF JOINTS WITH ALL FOUR
LINKS OF MEANING PAID: what is left is the pieces' make, five conditions "it reads below the base",
eight public conditions inside the promise, and THREE LINKS TO THE TABLE's LETTERS ML.rows, Mg.ev,
Mg.dot. One structure of Prop, two theorems: a joining of
Johnson/Desc/Third/Law/Row0AtWords.lean (reads · fence · atDot · dot · rows) and Row0Ev.lean (ev).

OBJECT   as in these two.   USER   rowZero_atWords, so eachOwn_of_rows | eachOwn_last.
LETTERS  p · Pw · cs · arr, t₁, t₂ · fs · lo · x.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  RowZeroPublic        WHAT IS LEFT, nineteen fields:
    THE MAKE           wrap · hand · idle.
    WHAT RIDES         ocBelow · lo_le · tree · omegaBelow · pins.
    PUBLIC, AT BORDER 0   started (the record is the start's of what was handed) · weights (the
                       pending rows' weights are well-formed) · names · placed · tenant · laid
                       (EvalLaid at the first chain's last record).
    PUBLIC, AT BORDER 1   shape (PL.shape 1 behind the block's own yes) · codes (the record's table
                       of codes is cs: so cs is the plan's).
    THE LETTERS        rows: ML.rows GIVES the body of rowsOpen cs arr enterOwn
                       seatOwn (Johnson/Flat/Last/LastAtArm.lean
                       [not in this library]) at seatOwn s := the seat by the
                       record's own book · ev: evI (WRow at the first chain's own words) GIVES Mg.ev
                       · dot: dotI (DotOmAt at the shared record's own words) GIVES Mg.dot. THREE
                       IMPLICATIONS, inside the promise: where a letter IS that term, the identity.
                       (Three equations would ask more than is spent, and are not payable
                       at a filling of Mg.dot that reads Omega and W by other terms.)
  rowZeroAtWords_of_public · rowZero_public   it gives RowZeroAtWords; so both conjuncts of EachOwn.
What is not claimed. NO MEMBER: nobody has shown a table, a piece and a promise at which the
nineteen hold together, nor run the public ones at an honest record. Seven of the eight public ones
are had at the filling fillZ: Johnson/Desc/Third/Law/Row0AtFillZ.lean. NOTHING TIES
Pw.lin TO p.S. That the letters, as they are filled, are what the OTHER rows of the three tables
spend (row 2 of this table: rows; the shared chain's point: ev, dot) is owed there. All that
Row0Ev.lean and Row0AtWords.lean do not claim. No soundness of a verifier; nothing on hiding.

-/
import Johnson.Desc.Third.Law.Row0Ev

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open OnBytes.Maker OnBytes.Flat Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid)
open _root_.Desc.K14 (St)
open _root_.Run.PQ (CK)

variable {P S₁ Cells Tok Cl : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (ML : MeaningL S₃ (Wit Cells Tok MsgT))
  (Pm : PromMeaning St) (PL : PromMeaningL St S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)

/-- **WHAT IS LEFT AT ROW 0 WITH THE FOUR LINKS OF MEANING PAID.** -/
structure RowZeroPublic (Cl₀ : Type) (p : P₁₄) (Pw : Where) (cs : Codes)
    (x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)) (lo : ℕ) (arr : ℕ → ℕ → ℕ)
    (t₁ t₂ : ℕ) (fs : P × S₁ → First.S) : Prop where
  wrap : YesOf (fun t : (P × S₁ × St) × S₃ => t.2) (batchLinearConstraintsSecondPart p : Block S₃ Cl₀) x.b
  hand : ∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1
  idle : ∀ a τ w, x.ext a τ w = w
  ocBelow : OcReadsBelow lo Oc
  lo_le : lo ≤ x.base
  tree : ReadsTree Mg Pm
  omegaBelow : (N.tenant .oOmega).1 < x.base
  pins : PinsReadBelow (S₃ := S₃) N Mg ML x.base
  started : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a → Started p fs a
  weights : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    ∀ r ∈ (fs (a.1.1.1, a.1.1.2.1)).rows, ∀ g ∈ r.g, g.ok = true
  names : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a → Names a.1.2
  placed : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
      q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size
  tenant : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    ∀ q : ℕ × ℕ, a.1.1.2.2.book.place[a.1.1.2.2.loc.oOmega]? = some q → q.2 = 0
  /-- the row (Eval) lies among the own group's open rows of the first chain's last record -/
  laid : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    EvalLaid Pw (fs (a.1.1.1, a.1.1.2.1))
  shape : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) (s' : S₃), onQ₃ N Mg Pm PL Oc 0 a →
    (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s') → Says p a.1.2 s' →
    PL.shape 1 (a.1.1.1, a.1.1.2.1) a.1.1.2.2 s' = true
  codes : ∀ b : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 1 b → b.1.2.st.codes = cs
  /-- ML.rows gives the body of rowsOpen cs arr enterOwn (the seat by the record's own book) -/
  rows : ∀ (b : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 1 b → ML.rows b.1.2 w →
    ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
      ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
        (OnBytes.Means.wordsOn t.st
          (tabAt cs arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w))
  /-- "(Eval) says its claim" of the first chain's own words gives Mg.ev -/
  ev : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
    evI arr Pw fs (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w →
    Mg.ev (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w
  /-- DotOmAt at the shared record's own words gives Mg.dot -/
  dot : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
    dotI p.S (fun q => gOfS (fs q)) (fun d => wordsShared arr t₁ d.st d.book) (wvW arr p fs)
      (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w →
    Mg.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w

variable {N Mg ML Pm PL Oc}

/-- **It gives what is left at the closed family.** -/
theorem rowZeroAtWords_of_public {Cl₀ : Type} {p : P₁₄} {Pw : Where} {cs : Codes}
    {x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)} {lo : ℕ} {arr : ℕ → ℕ → ℕ}
    {t₁ t₂ : ℕ} {fs : P × S₁ → First.S}
    (h : RowZeroPublic N Mg ML Pm PL Oc Cl₀ p Pw cs x lo arr t₁ t₂ fs) :
    RowZeroAtWords N Mg ML Pm PL Oc Cl₀ p x lo arr t₁ t₂ fs where
  wrap := h.wrap
  hand := h.hand
  idle := h.idle
  ocBelow := h.ocBelow
  lo_le := h.lo_le
  tree := h.tree
  omegaBelow := h.omegaBelow
  pins := h.pins
  started := h.started
  weights := h.weights
  names := h.names
  placed := h.placed
  tenant := h.tenant
  shape := h.shape
  rows := fun b w hb hr => rows_atWords arr t₁ t₂ cs b.1.2 w (h.codes b hb) (h.rows b w hb hr)
  ev := fun a w ha hr =>
    h.ev a w ha (ev_atWords Pw (h.started a ha) (h.laid a ha) (h.placed a ha) w hr)
  dot := h.dot

/-- So both conjuncts of EachOwn at row 0. -/
theorem rowZero_public {Cl₀ : Type} {p : P₁₄} {Pw : Where} {cs : Codes}
    {x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)} {lo : ℕ} {arr : ℕ → ℕ → ℕ}
    {t₁ t₂ : ℕ} {fs : P × S₁ → First.S}
    (h : RowZeroPublic N Mg ML Pm PL Oc Cl₀ p Pw cs x lo arr t₁ t₂ fs) :
    x.Own (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML) (insQ₃ 0) (outsQ₃ 0) ∧
      x.Frames (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 0) (insQ₃ 0) :=
  rowZero_atWords (rowZeroAtWords_of_public h)

end VerifiableInference.Desc.Third.Law
