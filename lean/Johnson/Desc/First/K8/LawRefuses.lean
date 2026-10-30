-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRefuses.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE LAW'S PREMISE
"THE STATE'S VALUE HAS THE PLACE'S NUMBERS" NEED NOT BE PROMISED: WHERE IT FAILS THE BLOCK OF THE
DRAW SAYS NO.

The law `k08_rowT` (Johnson/Desc/First/K8/LawTable.lean) takes `PlaceRec p tl0`
(Johnson/Desc/First/K8/LawPlace.lean): the public value tl0 has the place's number of matrices,
their numbers of columns and rows, the number of combinations and the tables' shapes. Since the
law's letters are taken off the statement in front, tl0 is the state's own value. The block tests
just these five numbers on the state, whatever is drawn. So at a statement where they fail nothing
is owed.
  `placeRec_of_decide`: a yes of the block's decision gives `PlaceRec` at the state's value.
  `goodIn_of_refuses`: a piece that puts nothing out at the statements of a condition has
    `Piece.GoodIn` there, whatever the promise and the relations. General.
  `goodIn_where_or_refuses`: **by cases on a proposition: the law where it holds; a refusal where it
    fails.** General.
Statements and proofs.
Limits. Rules over letters but for the first. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawPlace
import Johnson.Desc.Sound.GoodIn
import Iop.Compose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model

/-- A yes of the decision gives the place's numbers at the state's value. -/
theorem placeRec_of_decide {Cl : Type} (p : Par) (tl : HTailF2) (st st' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hst : st.tl? = some tl)
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide st rs gs = .ok st') : PlaceRec p tl := by
  obtain ⟨_, _, _, _, _, c4, c5, c7, c6, c8, _⟩ := decide_ok atS p st st' rs gs h
  exact ⟨by simpa [atS, hst] using c4, by simpa [atS, hst] using c5, by simpa [atS, hst] using c7,
    by simpa [atS, hst] using c6, by simpa [atS, hst] using c8⟩

end VerifiableInference.Desc.First.K8

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- Where a piece puts nothing out, nothing is owed. -/
theorem goodIn_of_refuses (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop)
    (h : ∀ a τ b, on a → p.ior.red.out a τ = some b → False) : p.GoodIn on on' R R' :=
  fun a ha => Doomed.of_forall _ _ fun τ b hb => (h a τ b ha hb).elim

/-- **The law where a proposition holds; a refusal where it fails.** -/
theorem goodIn_where_or_refuses (p : Piece C F S Cl W) (Q : Prop) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (h1 : Q → p.GoodIn on on' R R')
    (h2 : ¬ Q → ∀ a τ b, on a → p.ior.red.out a τ = some b → False) : p.GoodIn on on' R R' := by
  by_cases hQ : Q
  · exact h1 hQ
  · exact goodIn_of_refuses p on on' R R' (h2 hQ)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.First.K8.placeRec_of_decide
#print axioms VerifiableInference.Desc.Sound.goodIn_of_refuses
#print axioms VerifiableInference.Desc.Sound.goodIn_where_or_refuses
