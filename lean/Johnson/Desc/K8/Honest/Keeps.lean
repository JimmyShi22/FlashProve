-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/Keeps.lean: THE SMALLNESS TEST: WHAT THE STEP OF THE KIND's OWN MEMBER, AT
WHICH THE MATRIX IS DRAWN, LEAVES OF THE VERIFIER's STATE AS IT WAS, AND HOW WHAT IT TURNS MAY HAVE
TURNED: one sentence on the state in front (s) and the state behind (s'), with the lemmas that pay
it from a yes of the member's own decision, and what follows from it. Lemmas on the verifier's own
text; none of the library's goals.

  `K8Keeps s s'`     in front the state holds data tl of the test: its list of tables is closed, no
                     matrix has been drawn; no row is owed a count; AND s' IS s WITH tl LAID BACK,
                     TWO OF ITS FIELDS TURNED: the drawn matrix `cfF` and the matrices' first
                     columns `cfFirst`. It names no place's numbers and no round
THE PAYERS, each from a yes:
  `keeps_of_means`   from the library's `MeansAtS` (Johnson/Desc/First/K8/HearMeans.lean)
  `keeps_of_decide`  from a yes of the decision of the draw's block `approximateRangeProofDrawKind atS p`
  `keeps_of_whole`   from a yes of the decision of the kind, whole (`K8.whole p`)
  `keeps_of_seats`   from a yes of the decision of a block c that is seated over the draw's block
                     (`Seats c (approximateRangeProofDrawKind atS p)`, Johnson/Desc/First/K8/LawSeated.lean): there, besides,
                     no mark stands behind
WHAT FOLLOWS:
  `K8Keeps.leaves`   every reading of the state that `S.putTl` leaves has one value in front and
                     behind
  `K8Keeps.rest`     so: the chain's statement, the book of trees, the count of roots, what is owed,
                     the mark, the state of the calls, what was put out, the request
  `K8Keeps.fork`     so: the ledger
  `K8Keeps.tl`       the test's data behind are those in front but for the two fields
NO DEVICE. NO TACTIC THAT SEARCHES.
Limits. From a yes alone. What the two fields hold behind is not said here: `MeansAtS` says it, at
a place's numbers and a round. Of the runs that the kind's block states (claims, after) nothing:
they are run at two later members.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.K8.HearMeans
import Johnson.Desc.First.K8.LawLeaves
import Johnson.Desc.First.K8.LawSeated
import Johnson.Desc.First.K8.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8

/-- **What the draw's member leaves, and how what it turns may have turned.** -/
def K8Keeps (s s' : S) : Prop :=
  ∃ (tl : HTailF2) (cf : Array Int) (first : Array Nat), s.tl? = some tl ∧ tl.funClosed = true ∧
    (s.rowsOwed = none ∨ s.rowsOwed = some 0) ∧ tl.cfF.size = 0 ∧ tl.foldDrawn = 0 ∧
    s' = s.putTl { tl with cfF := cf, cfFirst := first }

/-! ## The payers -/

theorem keeps_of_means {p : Par} {s s' : S} {r : Fmt.RoundView} (h : MeansAtS p s r s') :
    K8Keeps s s' := by
  obtain ⟨tl, h1, h2, h3, ⟨h4, h5⟩, -, -, -, -, -, e⟩ := h
  exact ⟨tl, _, _, h1, h2, h3, h4, h5, e⟩

theorem keeps_of_decide {Cl : Type} (p : Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s') :
    K8Keeps s s' := by
  obtain ⟨r, rfl⟩ := decide_one atS p s s' rs gs h
  exact keeps_of_means ((decide_atS_iff p s s' r gs).1 h)

theorem keeps_of_whole (p : ParW) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (whole p).decide s rs gs = .ok s') :
    K8Keeps s s' :=
  keeps_of_decide (Cl := Claim) p.toPar (rs := rs) (gs := gs) h

theorem keeps_of_seats {Cl : Type} {p : Par} {c : Block S Cl} (hc : Seats c (approximateRangeProofDrawKind atS p))
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : c.decide s rs gs = .ok s') : K8Keeps s s' ∧ s'.failed = none :=
  ⟨keeps_of_decide p ((hc.2 s rs gs s').1 h).1, ((hc.2 s rs gs s').1 h).2⟩

/-! ## What follows -/

theorem K8Keeps.leaves {α : Type} (f : S → α) (hf : ∀ (s : S) (tl : HTailF2), f (s.putTl tl) = f s)
    {s s' : S} (h : K8Keeps s s') : f s' = f s := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  exact hf s _

theorem K8Keeps.rest {s s' : S} (h : K8Keeps s s') :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.roots = s.roots ∧ s'.rowsOwed = s.rowsOwed ∧
      s'.failed = s.failed ∧ s'.check = s.check ∧ s'.out = s.out ∧ s'.req = s.req := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  exact putTl_rest s _

theorem K8Keeps.fork {s s' : S} (h : K8Keeps s s') : s'.fork? = s.fork? :=
  h.leaves S.fork? putTl_fork

theorem K8Keeps.tl {s s' : S} (h : K8Keeps s s') :
    ∃ (tl : HTailF2) (cf : Array Int) (first : Array Nat), s.tl? = some tl ∧
      s'.tl? = some { tl with cfF := cf, cfFirst := first } := by
  obtain ⟨tl, cf, first, h1, -, -, -, -, rfl⟩ := h
  exact ⟨tl, cf, first, h1, tlP_lawful.get_set s _ tl h1⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_of_means
#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_of_decide
#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_of_whole
#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_of_seats
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.leaves
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.rest
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.fork
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.tl
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps
