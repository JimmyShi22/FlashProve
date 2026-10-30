-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRelLaw.lean: A PROVED TYPED BLOCK CARRIED BETWEEN TWO BORDERS OF A TABLE OF
JOINTS: the borders are conditions and relations on the carried record itself; the typed joints
stand INSIDE the seat alone.

The setting. `DecideLaw` (Johnson/Desc/Sound/KeyDecides.lean) asks an EQUATION behind a block: the
typed verifier puts out the reading of the record behind. A typed out-statement need not be a
function of the record (it may hold functions on the typed message's places where the record holds
rows of the program's type), nor the record of it. What soundness spends is less: the typed verifier
puts out SOMETHING, and the border's relation behind gives the typed relation of it.

What is said.
  `RelLaw b base ds back k M rdA A B`, for two rows A, B of whatever make (`JointRow`,
    Johnson/Desc/Sound/KeyJoints.lean; a border of a table: `JointRow.ofBorder`), a proved typed
    block k between its OWN joints, and a reading rdA of the statement in front as k's in-statement:
      onIn: A's condition gives k's, read;
      relIn: under A's condition, k's relaxed relation, read, gives A's relation;
      step: at every statement in A's condition and every transcript at which the stage's own tests
        pass, every word shown is below the prime and what is shown has the declared shape: if
        `decide` returns s', THE TYPED VERIFIER PUTS OUT SOME b' at `M.view τ`, and: if b' is in k's
        out-condition, (s', the oracles left) is in B's; if B's relation holds there, k's relaxed
        out-relation has a witness at b'.
  `goodOfRelLaw`: then the seat's piece is good between A and B: it sits as a seat `outright`
    (`SeatRow`, Johnson/Desc/Sound/KeyRows.lean): `SeatRow.related`, `related_laws`.
  `relLaw_of_decide`: `DecideLaw` is the case in which b' is the reading of the record behind.
  `QuietTie b A B`: WHAT A BLOCK OWES THAT COSTS NO ERROR: a tie on statements, no typed block:
    where `decide` returns, the statement behind is in B's condition and B's relation there gives
    A's in front. `relLaw_of_quiet`, `SeatRow.quiet`, `quiet_laws`: it sits in a row.

Limits. A rule. No block's law is shown.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Reduction Err Shape IOR ExtSpec)
open _root_.Iop.Reduction (orOff)

variable {S Cl : Type} {F : Frame}

/-- **A proved typed block carried between two rows of whatever make.** -/
structure RelLaw (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) {JA JB : JK}
    (k : BK JA JB) (M : Maps ds k.R.red.shape) (rdA : S × F.E.Str → JA.X × JA.E.Str)
    (A B : JointRow S F) : Prop where
  onIn : ∀ a, A.on a → JA.on (rdA a)
  relIn : ∀ a w, A.on a → JA.relR (rdA a) w → A.rel a
  step : ∀ (s s' : S) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds)),
    A.on (s, y) →
    sTests (ckP .two) (stg F base ds) y τ = true →
    viewWordsBelowPrime (sView (ckP .two) (stg F base ds) y τ) = true →
    Shown F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
      (sView (ckP .two) (stg F base ds) y τ).opened →
    b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened) = .ok s' →
    ∃ b', k.R.red.out (rdA (s, y)) (M.view τ) = some b' ∧
      (JB.on b' → B.on (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ))) ∧
      (B.rel (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) → ∃ w, JB.relR b' w)

/-- **Then the seat's piece is good between the two rows.** -/
theorem goodOfRelLaw (W : Type) (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {JA JB : JK} (k : BK JA JB) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → JA.X × JA.E.Str) (A B : JointRow S F) (hk : k.Good)
    (hB : Nonempty JB.W) (hM : M.OK) (hb : viewWordsBelowPrime ⟨back, []⟩ = true)
    (h : RelLaw b base ds back k M rdA A B) :
    ((seatPiece (F := F) W b base ds back k M).bk A.on B.on (fun a _ => A.rel a)
      (fun a _ => B.rel a)).Good := by
  refine ⟨⟨pointsT (ckP .two) ds⟩,
    stageIOR_isLocal (ckP .two) (seatPiece (F := F) W b base ds back k M).stage
      (seatPiece (F := F) W b base ds back k M).run, ?_⟩
  exact pieceOfProved S Cl W (ckP .two) F (seatPiece (F := F) W b base ds back k M)
    (JA.X × JA.E.Str) (JB.X × JB.E.Str) JA.W JB.W k.R.red (fun _ => M.carry) k.err rdA A.on JA.on
    (fun a _ => A.rel a) (orOff B.on (fun a _ => B.rel a)) JA.relR (orOff JB.on JB.relR) k.ext
    (fun _ => M.fits hM k.err) h.onIn
    (fun a τ a' w ha ho hw => by
      obtain ⟨hv, ho'⟩ := Piece.below_out
        (⟨b, base, ds, back, fun _ _ w => w, M.err k.err⟩ : Piece (ckP .two) F S Cl W) hb a a' τ ho
      obtain ⟨h1, h2, h3, h4⟩ := (Piece.out_iff
        (⟨b, base, ds, back, fun _ _ w => w, M.err k.err⟩ : Piece (ckP .two) F S Cl W) a a' τ).1 ho'
      obtain ⟨s, y⟩ := a
      obtain ⟨s', y'⟩ := a'
      have hp : M.pass τ = true :=
        Maps.pass_of_passT M τ (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h1).1).1
      have h4' : y' = (y.1, sLeft (ckP .two) (stg F base ds) y τ) := h4
      subst h4'
      obtain ⟨b', e1, e2, e3⟩ := h.step s s' y τ ha h1 hv h2 h3
      rcases hw with hr | hn
      · obtain ⟨w', hw'⟩ := e3 hr
        exact ⟨M.view τ, b', w', M.tr_of_pass τ hp, e1, Or.inl hw', fun g => h.relIn _ _ ha g⟩
      · exact hB.elim fun w' =>
          ⟨M.view τ, b', w', M.tr_of_pass τ hp, e1, Or.inr fun g => hn (e2 g),
            fun g => h.relIn _ _ ha g⟩)
    hk.know

/-- `DecideLaw` is the case in which what is put out is the reading of the record behind. -/
theorem relLaw_of_decide {A B : JointRow S F} (s : Seat Cl A B)
    (h : DecideLaw s.b s.base s.ds s.back s.k s.M A.rd B.rd A.inv B.inv) :
    RelLaw s.b s.base s.ds s.back s.k s.M A.rd A B where
  onIn := fun _ ha => ha.1
  relIn := fun _ w _ hw => ⟨w, hw⟩
  step := fun x x' y τ ha h1 hv h2 h3 => by
    obtain ⟨hi, ho⟩ := h x x' y τ ha.1 ha.2 h1 hv h2 h3
    exact ⟨_, ho, fun g => ⟨g, hi⟩, fun hr => hr⟩

/-- A typed block carried between two rows of whatever make, as a seat in a row. -/
def SeatRow.related {W : Type} {A Z : JointRow S F} (B : JointRow S F) (b : Block S Cl) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) {JA JB : JK} (k : BK JA JB) (M : Maps ds k.R.red.shape)
    (l : SeatRow Cl W B Z) : SeatRow Cl W A Z :=
  .outright B (seatPiece W b base ds back k M) l

theorem SeatRow.related_laws {W : Type} {A Z : JointRow S F} (B : JointRow S F) (b : Block S Cl)
    (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) {JA JB : JK} (k : BK JA JB)
    (M : Maps ds k.R.red.shape) (rdA : S × F.E.Str → JA.X × JA.E.Str) (l : SeatRow Cl W B Z)
    (εs : ℝ≥0∞) (hk : k.Good) (hB : Nonempty JB.W) (hM : M.OK) (hb : viewWordsBelowPrime ⟨back, []⟩ = true)
    (h : RelLaw b base ds back k M rdA A B) (hh : Err.Below (M.err k.err) εs)
    (hl : l.Laws εs) :
    (SeatRow.related (A := A) B b base ds back k M l).Laws εs :=
  ⟨⟨goodOfRelLaw W b base ds back k M rdA A B hk hB hM hb h, hh⟩, hl⟩

/-! ## A block that hears nothing that counts: no typed block is wanted -/

/-- The row itself as a joint on the carried record. -/
abbrev JointRow.self (A : JointRow S F) : JK := jointAt F S Unit A.on fun a _ => A.rel a

/-- **What a block owes that costs no error** (a block without a round; a block whose rounds are all
skipped): a tie on statements: at every statement in A's condition, where `decide` returns s': the
statement behind is in B's condition, and B's relation there gives A's relation in front. B reads no
tree from the block's place on: so the oracles behind may be taken as those in front. -/
def QuietTie (b : Block S Cl) (A B : JointRow S F) : Prop :=
  ∀ (s s' : S) (y : F.E.Str) rs gs, A.on (s, y) → b.decide s rs gs = .ok s' →
    B.on (s', y) ∧ (B.rel (s', y) → A.rel (s, y))

/-- **Such a block meets `RelLaw`**, at the typed block that hands the row's own statement on. -/
theorem relLaw_of_quiet (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (A B : JointRow S F) (hnd : (F.all.map (·.no)).Nodup) (hon : ReadsBelow base B.on)
    (hrel : ReadsBelow base B.rel) (h : QuietTie b A B) :
    RelLaw b base ds back (BK.pass A.self) (Maps.skips ds) id A B where
  onIn := fun _ ha => ha
  relIn := fun _ _ _ hw => hw
  step := fun s s' y τ ha _ _ _ hd => by
    have e : B.on (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) = B.on (s', y) :=
      hon s' _ _ rfl fun q hq => sLeft_old hnd ds base y τ q hq
    have e' : B.rel (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) = B.rel (s', y) :=
      hrel s' _ _ rfl fun q hq => sLeft_old hnd ds base y τ q hq
    obtain ⟨h1, h2⟩ := h s s' y _ _ ha hd
    refine ⟨(s, y), rfl, fun _ => ?_, fun hr => ⟨(), ?_⟩⟩
    · rw [e]
      exact h1
    · rw [e'] at hr
      exact h2 hr

/-- A block that costs no error, as a seat in a row. -/
def SeatRow.quiet {W : Type} {A Z : JointRow S F} (B : JointRow S F) (b : Block S Cl) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) (l : SeatRow Cl W B Z) : SeatRow Cl W A Z :=
  SeatRow.related B b base ds back (BK.pass A.self) (Maps.skips ds) l

theorem SeatRow.quiet_laws {W : Type} {A Z : JointRow S F} (B : JointRow S F) (b : Block S Cl)
    (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (l : SeatRow Cl W B Z) (εs : ℝ≥0∞)
    (hb : viewWordsBelowPrime ⟨back, []⟩ = true) (hnd : (F.all.map (·.no)).Nodup)
    (hon : ReadsBelow base B.on) (hrel : ReadsBelow base B.rel) (h : QuietTie b A B)
    (hl : l.Laws εs) : (SeatRow.quiet (A := A) B b base ds back l).Laws εs :=
  SeatRow.related_laws B b base ds back (BK.pass A.self) (Maps.skips ds) id l εs (BK.pass_good _)
    ⟨()⟩ (Maps.ok_skips ds) hb (relLaw_of_quiet b base ds back A B hnd hon hrel h)
    ((Maps.skips ds).below_err (Maps.ok_skips ds) _ (Maps.held_skips εs ds)) hl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.relLaw_of_quiet
#print axioms VerifiableInference.Desc.Sound.SeatRow.quiet_laws
#print axioms VerifiableInference.Desc.Sound.goodOfRelLaw
#print axioms VerifiableInference.Desc.Sound.relLaw_of_decide
#print axioms VerifiableInference.Desc.Sound.SeatRow.related_laws
