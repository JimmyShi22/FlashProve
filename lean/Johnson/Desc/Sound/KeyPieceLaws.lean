-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyPieceLaws.lean: WHAT MAKES A GIVEN PIECE GOOD BETWEEN TWO ROWS: for a piece
that a maker has cut off the written rounds' data (its block, stretch, extractor and errors are what
they are), the two ways to fill its seat: by a proved typed block, and by a tie on statements.

The setting. `goodOfRelLaw` (Johnson/Desc/Sound/KeyRelLaw.lean) speaks of the piece that a seat
makes for itself (`seatPiece`: the extractor hands the witness back; the errors are the written
counts along the seat's maps). `SeatRow.ofRows` (Johnson/Desc/Sound/KeyRowsOfPieces.lean) takes
pieces as they are given.

What is said.
  `RelAt p k G rdA A B`: for a piece p, a proved typed block k, a reading G of p's rounds as k's, a
    reading rdA of the statement in front as k's in-statement, and two rows A, B:
      fits: p's own errors bear k's along G;
      onIn, relIn: A's condition gives k's, read; k's relaxed relation, read, gives A's relation;
      step: where p's reduction puts out a' at a statement in A's condition, the transcript has an
        image at which k's verifier puts out some b'; if b' is in k's out-condition, a' is in B's;
        if B's relation holds of a', k's relaxed out-relation has a witness at b'.
  `goodOfRelAt`: then p is good between A and B.
  `relAt_of_relLaw`: `RelLaw` gives it at every piece that holds `below b` on the law's own stretch,
    with the written counts along the law's maps as its errors, whatever its extractor is.
  `goodOfQuietAt`: a piece whose block meets `QuietTie` between A and B, where B reads no tree from
    the piece's place on, is good between A and B, WHATEVER ITS ROUNDS, EXTRACTOR AND ERRORS ARE.
  `lastRow_append`, `rowsGood_append`: a list of pairs in two parts: what is asked of the whole is
    what is asked of the parts.

Limits. Rules. No piece of any description is shown good.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRelLaw
import Johnson.Desc.Sound.KeyRowsOfPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Reduction Err Shape IOR ExtSpec)
open _root_.Iop.Reduction (orOff)

variable {S Cl W : Type} {F : Frame}

/-- **A proved typed block carried at a given piece.** -/
structure RelAt (p : Piece (ckP .two) F S Cl W) {JA JB : JK} (k : BK JA JB)
    (G : S × F.E.Str → CarryS (uLT (ckP .two) p.ds) k.R.red.shape)
    (rdA : S × F.E.Str → JA.X × JA.E.Str) (A B : JointRow S F) : Prop where
  fits : ∀ a, (G a).Fits k.err p.err
  onIn : ∀ a, A.on a → JA.on (rdA a)
  relIn : ∀ a w, A.on a → JA.relR (rdA a) w → A.rel a
  step : ∀ a τ a', A.on a → p.ior.red.out a τ = some a' →
    ∃ τ' b', (G a).tr τ = some τ' ∧ k.R.red.out (rdA a) τ' = some b' ∧
      (JB.on b' → B.on a') ∧ (B.rel a' → ∃ w, JB.relR b' w)

/-- **Then the piece is good between the two rows.** -/
theorem goodOfRelAt (p : Piece (ckP .two) F S Cl W) {JA JB : JK} (k : BK JA JB)
    (G : S × F.E.Str → CarryS (uLT (ckP .two) p.ds) k.R.red.shape)
    (rdA : S × F.E.Str → JA.X × JA.E.Str) (A B : JointRow S F) (hk : k.Good)
    (hB : Nonempty JB.W) (h : RelAt p k G rdA A B) :
    (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good := by
  refine ⟨⟨pointsT (ckP .two) p.ds⟩, stageIOR_isLocal (ckP .two) p.stage p.run, ?_⟩
  exact pieceOfProved S Cl W (ckP .two) F p (JA.X × JA.E.Str) (JB.X × JB.E.Str) JA.W JB.W k.R.red G
    k.err rdA A.on JA.on (fun a _ => A.rel a) (orOff B.on (fun a _ => B.rel a)) JA.relR
    (orOff JB.on JB.relR) k.ext h.fits h.onIn
    (fun a τ a' _ ha ho hw => by
      obtain ⟨τ', b', e0, e1, e2, e3⟩ := h.step a τ a' ha ho
      rcases hw with hr | hn
      · obtain ⟨w', hw'⟩ := e3 hr
        exact ⟨τ', b', w', e0, e1, Or.inl hw', fun g => h.relIn _ _ ha g⟩
      · exact hB.elim fun w' =>
          ⟨τ', b', w', e0, e1, Or.inr fun g => hn (e2 g), fun g => h.relIn _ _ ha g⟩)
    hk.know

/-- **`RelLaw` serves every piece that holds the block with the test below the prime in front**, on
the law's own stretch, with the written counts along the law's maps as its errors: whatever its
extractor is. So a law that is stated of a seat's own piece fills a seat at a piece that a maker has
cut. -/
theorem relAt_of_relLaw (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {JA JB : JK} (k : BK JA JB) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → JA.X × JA.E.Str) (A B : JointRow S F)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → W → W) (hM : M.OK)
    (hb : viewWordsBelowPrime ⟨back, []⟩ = true) (h : RelLaw b base ds back k M rdA A B) :
    RelAt (⟨below b, base, ds, back, ext, M.err k.err⟩ : Piece (ckP .two) F S Cl W) k
      (fun _ => M.carry) rdA A B where
  fits := fun _ => M.fits hM k.err
  onIn := h.onIn
  relIn := h.relIn
  step := fun a τ a' ha ho => by
    obtain ⟨hv, ho'⟩ := Piece.below_out
      (⟨b, base, ds, back, ext, M.err k.err⟩ : Piece (ckP .two) F S Cl W) hb a a' τ ho
    obtain ⟨h1, h2, h3, h4⟩ := (Piece.out_iff
      (⟨b, base, ds, back, ext, M.err k.err⟩ : Piece (ckP .two) F S Cl W) a a' τ).1 ho'
    obtain ⟨s, y⟩ := a
    obtain ⟨s', y'⟩ := a'
    have hp : M.pass τ = true :=
      Maps.pass_of_passT M τ (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h1).1).1
    have h4' : y' = (y.1, sLeft (ckP .two) (stg F base ds) y τ) := h4
    subst h4'
    obtain ⟨b', e1, e2, e3⟩ := h.step s s' y τ ha h1 hv h2 h3
    exact ⟨M.view τ, b', M.tr_of_pass τ hp, e1, e2, e3⟩

/-- **A piece whose block costs no error.** -/
theorem goodOfQuietAt (p : Piece (ckP .two) F S Cl W) (A B : JointRow S F)
    (hnd : (F.all.map (·.no)).Nodup) (hon : ReadsBelow p.base B.on)
    (hrel : ReadsBelow p.base B.rel) (h : QuietTie p.b A B) :
    (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good :=
  goodOfRelAt p (BK.pass A.self) (fun _ => skipAll _) id A B (BK.pass_good _) ⟨()⟩
    { fits := fun _ => skipAll_fits _ _
      onIn := fun _ ha => ha
      relIn := fun _ _ _ hw => hw
      step := fun a τ a' ha ho => by
        obtain ⟨_, _, h3, h4⟩ := (Piece.out_iff p a a' τ).1 ho
        obtain ⟨s, y⟩ := a
        obtain ⟨s', y'⟩ := a'
        have h4' : y' = (y.1, sLeft (ckP .two) (stg F p.base p.ds) y τ) := h4
        subst h4'
        have e : B.on (s', (y.1, sLeft (ckP .two) (stg F p.base p.ds) y τ)) = B.on (s', y) :=
          hon s' _ _ rfl fun q hq => sLeft_old hnd p.ds p.base y τ q hq
        have e' : B.rel (s', (y.1, sLeft (ckP .two) (stg F p.base p.ds) y τ)) = B.rel (s', y) :=
          hrel s' _ _ rfl fun q hq => sLeft_old hnd p.ds p.base y τ q hq
        obtain ⟨h1, h2⟩ := h s s' y _ _ ha h3
        refine ⟨(), (s, y), skipAll_tr _ τ, rfl, fun _ => ?_, fun hr => ⟨(), ?_⟩⟩
        · rw [e]
          exact h1
        · rw [e'] at hr
          exact h2 hr }

theorem lastRow_append : ∀ (A : JointRow S F)
    (l m : List (Piece (ckP .two) F S Cl W × JointRow S F)),
    lastRow A (l ++ m) = lastRow (lastRow A l) m
  | _, [], _ => rfl
  | _, x :: l, m => lastRow_append x.2 l m

theorem rowsGood_append (εs : ℝ≥0∞) : ∀ (A : JointRow S F)
    (l m : List (Piece (ckP .two) F S Cl W × JointRow S F)),
    RowsGood εs A (l ++ m) ↔ RowsGood εs A l ∧ RowsGood εs (lastRow A l) m
  | _, [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _, x :: l, m =>
    ⟨fun h => ⟨⟨h.1, ((rowsGood_append εs x.2 l m).1 h.2).1⟩,
      ((rowsGood_append εs x.2 l m).1 h.2).2⟩,
      fun h => ⟨h.1.1, (rowsGood_append εs x.2 l m).2 ⟨h.1.2, h.2⟩⟩⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodOfRelAt
#print axioms VerifiableInference.Desc.Sound.relAt_of_relLaw
#print axioms VerifiableInference.Desc.Sound.goodOfQuietAt
#print axioms VerifiableInference.Desc.Sound.rowsGood_append
