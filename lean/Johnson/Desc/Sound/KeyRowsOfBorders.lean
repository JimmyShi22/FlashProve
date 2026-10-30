-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRowsOfBorders.lean: ANY BORDER OF A TABLE OF JOINTS (a condition and a
relation with witnesses, on the carried record and the oracles) AS A ROW OF OURS; and a block that
is good between two such borders, with witnesses and an extractor, as a seat "outright".

The setting. A table of joints that is written over the carried record itself gives, for each
border, a condition `on` and a relation R with witnesses of one type for the file ("every open item
holds"). Johnson/Desc/Sound/KeyJoints.lean's row is a typed joint, a reading and an invariant; the
relation that the key file's rule reads at a row is "the joint's relation, read, has a witness". The
key file's named hypothesis asks soundness for a language: no witness is handed to anybody.

What is said.
  `JointRow.ofBorder on R`: the row whose joint is the border itself (`jointAt`,
    Johnson/Desc/Sound/ChainRule.lean), whose reading is the identity and whose invariant asks
    nothing. `ofBorder_on`, `ofBorder_rel`: its condition is `on`; its relation is "R has a
    witness".
  `goodShadow`: a piece that is good between two borders, WITH witnesses and whatever extractor, is
    good between the two rows: so it sits as a seat `outright` (`SeatRow`,
    Johnson/Desc/Sound/KeyRows.lean).
  `rowLe B B'`: WHAT JOINS A SEAT THAT ENDS AT B TO A SEAT THAT BEGINS AT B': B's condition gives
    B''s, and under B's condition B''s relation gives B's. `goodInto`: then a piece that is good
    into B is good into B'; `goodFrom`: and a piece that is good from B' is good from B. `rowMeets`:
    two rows that agree both ways; `rowMeets.le`, `rowMeets.ge`.

Limits. Forms. No border of any table is laid in.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Reduction Err Shape IOR ExtSpec Doomed)
open _root_.Iop.Reduction (orOff)

variable {S Cl W : Type} {F : Frame}

/-- **A border as a row.** -/
def JointRow.ofBorder (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop) : JointRow S F :=
  ⟨jointAt F S W on R, id, fun _ => True⟩

theorem ofBorder_on (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop) (a : S × F.E.Str) :
    (JointRow.ofBorder on R).on a ↔ on a :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem ofBorder_rel (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop) (a : S × F.E.Str) :
    (JointRow.ofBorder on R).rel a ↔ ∃ w, R a w :=
  Iff.rfl

/-- A piece's goodness reads of its conditions and relations only this much. -/
theorem good_congr (p : Piece (ckP .two) F S Cl W) (on₁ on₂ on₁' on₂' : S × F.E.Str → Prop)
    (R₁ R₂ R₁' R₂' : S × F.E.Str → W → Prop) (ho : ∀ a, on₂ a → on₁ a)
    (hR : ∀ a w, on₂ a → R₁ a w → R₂ a w)
    (hB : ∀ b w, orOff on₂' R₂' b w → ∃ w', orOff on₁' R₁' b w')
    (hw : ∀ a w w', R₂ a w → R₂ a w') (h : (p.bk on₁ on₁' R₁ R₁').Good) :
    (p.bk on₂ on₂' R₂ R₂').Good := by
  refine ⟨h.point, h.isLocal, fun a ha => ?_⟩
  refine Doomed.mono _ _ (fun τ hτ b w hb hw' => ?_) (h.know a (ho a ha))
  obtain ⟨w', h'⟩ := hB b w hw'
  exact hw a _ _ (hR a _ ha (hτ b w' hb h'))

/-- **Good with witnesses is good in the shadow.** -/
theorem goodShadow (p : Piece (ckP .two) F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (h : (p.bk on on' R R').Good) :
    (p.bk (JointRow.ofBorder on R).on (JointRow.ofBorder on' R').on
      (fun a _ => (JointRow.ofBorder on R).rel a)
      (fun a _ => (JointRow.ofBorder on' R').rel a)).Good :=
  good_congr p on _ on' _ R _ R' _ (fun _ h => h.1) (fun _ w _ h => ⟨w, h⟩)
    (fun b w h => h.elim (fun ⟨w', hw'⟩ => ⟨w', Or.inl hw'⟩)
      fun hn => ⟨w, Or.inr fun ho => hn ⟨ho, trivial⟩⟩)
    (fun _ _ _ h => h) h

/-- **What joins a seat that ends at the row B to a seat that begins at the row B'**: B's condition
gives B''s; under B's condition B''s relation gives B's. -/
structure rowLe (B B' : JointRow S F) : Prop where
  on : ∀ a, B.on a → B'.on a
  rel : ∀ a, B.on a → B'.rel a → B.rel a

/-- Two rows at one place are one: the conditions agree; under them the relations agree. -/
structure rowMeets (A B : JointRow S F) : Prop where
  on : ∀ a, A.on a ↔ B.on a
  rel : ∀ a, A.on a → (A.rel a ↔ B.rel a)

theorem rowMeets.le {A B : JointRow S F} (m : rowMeets A B) : rowLe A B :=
  ⟨fun a => (m.on a).1, fun a ha => (m.rel a ha).2⟩

theorem rowMeets.ge {A B : JointRow S F} (m : rowMeets A B) : rowLe B A :=
  ⟨fun a => (m.on a).2, fun a ha => (m.rel a ((m.on a).2 ha)).1⟩

/-- A piece that is good into B is good into B'. -/
theorem goodInto (p : Piece (ckP .two) F S Cl W) (A B B' : JointRow S F) (m : rowLe B B')
    (h : (p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good) :
    (p.bk A.on B'.on (fun a _ => A.rel a) (fun a _ => B'.rel a)).Good :=
  good_congr p _ _ _ _ _ _ _ _ (fun _ h => h) (fun _ _ _ h => h)
    (fun b w h => ⟨w, h.elim
      (fun hr => (Classical.em (B.on b)).elim (fun ho => Or.inl (m.rel b ho hr)) Or.inr)
      fun hn => Or.inr fun ho => hn (m.on b ho)⟩)
    (fun _ _ _ h => h) h

/-- A piece that is good from B' is good from B. -/
theorem goodFrom (p : Piece (ckP .two) F S Cl W) (B B' Z : JointRow S F) (m : rowLe B B')
    (h : (p.bk B'.on Z.on (fun a _ => B'.rel a) (fun a _ => Z.rel a)).Good) :
    (p.bk B.on Z.on (fun a _ => B.rel a) (fun a _ => Z.rel a)).Good :=
  good_congr p _ _ _ _ _ _ _ _ (fun a h => m.on a h) (fun a _ ha h => m.rel a ha h)
    (fun _ w h => ⟨w, h⟩) (fun _ _ _ h => h) h

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodShadow
#print axioms VerifiableInference.Desc.Sound.goodInto
#print axioms VerifiableInference.Desc.Sound.goodFrom
