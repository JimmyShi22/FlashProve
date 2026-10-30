-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0AtFillZ.lean: ROW 0 OF THE LAST CHAIN's TABLE OF JOINTS AT THE
FILLING OF THE PROMISE's BOOK-KEEPING PL := fillZ p R fs
(Johnson/Desc/Last/ShapeRowZero.lean): SEVEN OF THE EIGHT PUBLIC FIELDS OF RowZeroPublic
(Johnson/Desc/Third/Law/Row0AtFillings.lean) ARE PAID THERE, EACH BY ONE CALL of
ShapeRowZero.lean's theorems: started · weights · names · placed · tenant · shape · codes (at cs :=
p.codes). One structure of Prop, two theorems: a joining of these two files.

OBJECT   as in Row0AtFillings.lean; the test shapeAt (Johnson/Desc/Last/ShapeAt.lean), with code.
USER     rowZero_public, so eachOwn_of_rows | eachOwn_last.
LETTERS  p · R (the own test's rounds) · Pw · arr, t₁, t₂ · fs · lo · x.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  RowZeroAtFillZ       WHAT IS LEFT, twelve fields: the make (wrap · hand · idle: paid by
                       make_pieceOf, Johnson/Desc/Third/Law/Row0Make.lean, at the maker's own piece)
                       · what rides (ocBelow · lo_le · tree · omegaBelow · pins) · laid (EvalLaid at
                       the first chain's last record: no clause of shapeAt speaks of it: it comes
                       through Oc) · the three links to the letters (rows · ev · dot).
  rowZeroPublic_atFillZ   **it gives RowZeroPublic at PL := fillZ p R fs, cs := p.codes.** The
                       calls: started_fillZ · weights_fillZ · names_fillZ · placed_fillZ ·
                       tenant_fillZ (through sharedOfEnd_ended) · shape_fillZ · codes_fillZ.
  rowZero_atFillZ      so both conjuncts of EachOwn at row 0.
What is not claimed. NO MEMBER: shapeAt has been evaluated at no record. A BARE MEMBER OF THE TWELVE
WOULD BE WORTH NOTHING (at Oc := False all twelve hold): the member that counts stands at Oc := the
first chain's promise at its end, at the maker's own piece, WITH some statement inside the promise
at border 0. The promise at this filling is empty at a shape whose masks are not sent ahead
(ShapeAt.lean, limit 2): every plan that the planner makes sends them ahead
(Johnson/Desc/Last/ShapeMask.lean · Johnson/Desc/Third/Law/MasksAhead.lean, up to the verifier's own
chains); that the seat's p is read off these chains is the seat's matter. What fillZ asks at border
0 falls due upstream, at the last chain's door ((SH₃), Johnson/Desc/Sound/BordersLastQ.lean). All
that Row0AtFillings.lean and ShapeRowZero.lean do not claim. No soundness of a verifier; nothing on
hiding.

-/
import Johnson.Desc.Last.ShapeRowZero
import Johnson.Desc.Third.Law.Row0AtFillings

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
  (Pm : PromMeaning St) (Oc : P × S₁ → Strs → Prop)

/-- **WHAT IS LEFT AT ROW 0 AT THE FILLING fillZ OF THE PROMISE's BOOK-KEEPING.** -/
structure RowZeroAtFillZ (Cl₀ : Type) (p : P₁₄) (R : List Fmt.DeclaredRound) (Pw : Where)
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
  laid : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a →
    EvalLaid Pw (fs (a.1.1.1, a.1.1.2.1))
  rows : ∀ (b : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm (fillZ p R fs) Oc 1 b →
    ML.rows b.1.2 w →
    ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn b.1.2 = .ok t ∧
      ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
        (OnBytes.Means.wordsOn t.st
          (tabAt p.codes arr (seatBy (noLast t₁ t₂ b.1.2.loc.firstTree) b.1.2.book) t.st w))
  ev : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a →
    evI arr Pw fs (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w →
    Mg.ev (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w
  dot : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a →
    dotI p.S (fun q => gOfS (fs q)) (fun d => wordsShared arr t₁ d.st d.book) (wvW arr p fs)
      (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w →
    Mg.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w

variable {N Mg ML Pm Oc}

/-- **It gives RowZeroPublic at that filling.** -/
theorem rowZeroPublic_atFillZ {Cl₀ : Type} {p : P₁₄} {R : List Fmt.DeclaredRound} {Pw : Where}
    {x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)} {lo : ℕ} {arr : ℕ → ℕ → ℕ}
    {t₁ t₂ : ℕ} {fs : P × S₁ → First.S}
    (h : RowZeroAtFillZ N Mg ML Pm Oc Cl₀ p R Pw x lo arr t₁ t₂ fs) :
    RowZeroPublic N Mg ML Pm (fillZ p R fs) Oc Cl₀ p Pw p.codes x lo arr t₁ t₂ fs where
  wrap := h.wrap
  hand := h.hand
  idle := h.idle
  ocBelow := h.ocBelow
  lo_le := h.lo_le
  tree := h.tree
  omegaBelow := h.omegaBelow
  pins := h.pins
  started := fun _ ha => started_fillZ ha
  weights := fun _ ha => weights_fillZ ha
  names := fun _ ha => names_fillZ ha
  placed := fun _ ha => placed_fillZ ha
  tenant := fun a ha => by
    obtain ⟨e, he, ht⟩ := tenant_fillZ ha
    rw [sharedOfEnd_ended _ e he] at ht
    exact ht
  laid := h.laid
  shape := fun _ _ ha hy _ => shape_fillZ ha hy
  codes := fun _ hb => codes_fillZ hb
  rows := h.rows
  ev := h.ev
  dot := h.dot

/-- So both conjuncts of EachOwn at row 0. -/
theorem rowZero_atFillZ {Cl₀ : Type} {p : P₁₄} {R : List Fmt.DeclaredRound} {Pw : Where}
    {x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)} {lo : ℕ} {arr : ℕ → ℕ → ℕ}
    {t₁ t₂ : ℕ} {fs : P × S₁ → First.S}
    (h : RowZeroAtFillZ N Mg ML Pm Oc Cl₀ p R Pw x lo arr t₁ t₂ fs) :
    x.Own (onQ₃ N Mg Pm (fillZ p R fs) Oc 0) (onQ₃ N Mg Pm (fillZ p R fs) Oc 1) (meansQ₃ N Mg ML)
        (insQ₃ 0) (outsQ₃ 0) ∧
      x.Frames (onQ₃ N Mg Pm (fillZ p R fs) Oc 0) (onQ₃ N Mg Pm (fillZ p R fs) Oc 1)
        (meansQ₃ N Mg ML) (openAfter insQ₃ outsQ₃ (· ∈ startLast) 0) (insQ₃ 0) :=
  rowZero_public (rowZeroPublic_atFillZ h)

end VerifiableInference.Desc.Third.Law
