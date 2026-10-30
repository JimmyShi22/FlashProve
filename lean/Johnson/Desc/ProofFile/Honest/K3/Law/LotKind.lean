-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LotKind.lean: the honest side of the kind "lookup" (K3). Every
half that the lookups' lot lays stands at a place of the kind K3. Theorems.

Terms. Honest/K3/GLOSSARY.md ("half", "lot", "filling", "site").

What is shown. None of the four has a hypothesis.
  `lotBy_kind`: at `lotBy row` (Honest/K3/Lot.lean), for every row.
  `rowLotAt_kind`: at `rowLotAt A` (Honest/K3/LotFilled.lean), for every filling.
  `theLot_kind`: at `theLot cells weights req` (LotFilled.lean), for all values of the lot's three
    letters. This is what was asked (see Users).
  `theLotSpec_kind`: the same at the lot with the specification's summands.

How the proof goes. The lot lays one half for each site, at the site's own place (the text of
`lotBy`); a site's place is of the kind K3: the first conjunct of `spot_of_site`
(Honest/K3/Law/LotOfSite.lean).

Users. On an ask from the frame's side (Honest/Frame.lean). That side has a lemma on which half is
found at a place in the first chain's halves. One of its hypotheses, "no other lot has a half at a
place of my kind", no kind's files can show alone. The ask is, of each kind whose lot
stands in a filling, one lemma, in the form of a worked example
`replyLot_kind (Z G) : ∀ x ∈ replyLot.halves Z G, x.place.kind = .K7`; of the lookup's files at
`K3.theLot id id req`. The ask says besides that a lot which lays halves of two kinds should say
which two. The lookups' lot lays halves of one kind: that is what `theLot_kind` says. The form
follows the ask, a text of this project, not in this tree, which quotes it. It was not compared
with the files that hold the lemma and the worked example. Honest/K3/Law/Keep/LotInstKeepLaw.lean
[not in this library] and Honest/K3/Law/Thread/LotInstFind.lean import this file.

Imported. Beneath this file lie, among others:
  the frame's files: Honest/BookOf, Honest/ForKinds, Honest/Sum;
  the files on the chain's shape: Honest/Side, Honest/Law/Cut,
    Honest/Law/Play;
  the files on the masked sumcheck's laws: Honest/SumLaw/Law, LawEnds, Statement, Terms;
  a file on a member at a lot's place: Honest/Member/AtLot;
  under Johnson/HonestTrace/: FromCells, LookAtDigits, LookDefs and
    DigitsAtTrace.

Limits. The statements hold at every public part, also where the list of sites is empty: there they
say nothing. Nothing is said on whether a half is there, on what a half holds, or on the other lots.
The lots that lay a half only where a test accepts (`theLotFit` and its like,
Honest/K3/SeatFits.lean) are not spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.K3.LotFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (KindName)

variable {V W X W₀ Rc Xi Tr : Type}

/-- **Every half of `lotBy row` stands at a place of the kind K3**, for every row. -/
theorem lotBy_kind (row : Site → List (Part V W X)) (Z : Pub) (G : Ground) :
    ∀ x ∈ (lotBy row).halves Z G, x.place.kind = KindName.K3 := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact (spot_of_site Z s hs).1

/-- The same at `rowLotAt A`, for every filling. -/
theorem rowLotAt_kind (A : Pub → Fill W) (Z : Pub) (G : Ground) :
    ∀ x ∈ (rowLotAt (V := V) (X := X) A).halves Z G, x.place.kind = KindName.K3 :=
  lotBy_kind _ Z G

/-- **Every half of the lookups' lot stands at a place of the kind K3.** -/
theorem theLot_kind (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    ∀ x ∈ (theLot (Rc := Rc) (X := X) cells weights req).halves Z G,
      x.place.kind = KindName.K3 :=
  rowLotAt_kind _ Z G

/-- The same at the specification's summands. -/
theorem theLotSpec_kind (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    ∀ x ∈ (theLotSpec (Rc := Rc) (X := X) cells weights req).halves Z G,
      x.place.kind = KindName.K3 :=
  rowLotAt_kind _ Z G

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.lotBy_kind
#print axioms ProofFile.Honest.K3.Law.rowLotAt_kind
#print axioms ProofFile.Honest.K3.Law.theLot_kind
#print axioms ProofFile.Honest.K3.Law.theLotSpec_kind
