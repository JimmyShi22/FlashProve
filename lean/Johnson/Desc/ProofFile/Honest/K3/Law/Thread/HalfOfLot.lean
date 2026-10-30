-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HalfOfLot.lean: the honest side of the kind "lookup"
(K3). Conditional: the search at a site's place finds the half of the lookups' lot, general in the
lot; and at the lots that are seated: `theLot` (Honest/K3/LotFilled.lean), whose row depends on the
public part, and `theLotFit` (Honest/K3/SeatFits.lean), which filters it. One definition; theorems.

Terms. Honest/K3/GLOSSARY.md: see there half, lot, site, summand and seated filling. In this file:
ls is a list of lots; the gathered halves are `firstOf Z Gr ls` (Honest/Frame.lean).

What is shown.
  `half_of_lot`: general in the lot: a half of a lot of the list is found by the search at its
    place.
  `seatAt`, `seatAt_place`: the seated row at a site, at the summands and the reader of the input
    that `theLot` sets there: they read the public part. Its place is the site's.
  `mem_theLot`, `half_theLot`: that half stands among the halves of `theLot`; so the search finds
    it.
  `mem_theLotFit`, `half_theLotFit`: the same at `theLotFit`, where its tests accept.
  `half_theLot_ok`, `half_theLotFit_ok`: the same from the frame's own test that no place has two
    halves.
Why: the theorems of Honest/K3/Law/Thread/SitePays.lean on the half at a site take a lot of the form
`lotBy row` (Honest/K3/Lot.lean), with row a function of the site alone. The lots that are seated
are no such terms: so these theorems are true and cannot be called there. Their proofs read of the
lot two things alone: it stands in the list of lots; the half stands among its halves at the public
part.

Hypotheses that remain.
  `hl`: the lot stands in the list of lots.
  `hs`: s is a site of the public part.
  `hn`, `ht`: no two of the gathered halves share a place; or, in the last two theorems, the frame's
    list of places with two halves is empty (`twice`, Frame.lean).
  `hx`: (in `half_of_lot`) the half stands among the lot's halves at the public part.
  `h1`, `h2`, `hm`, `hf`: (at `theLotFit`) the four hypotheses of Honest/K3/Law/SeatFitsLaw.lean:
    the table of places can be read; there is a site for every address; the letter made accepts;
    `k3Fits` (Honest/K3/SeatFits.lean) accepts at every site.

Imported: Honest/Frame.lean.

Users. Honest/K3/Law/Thread/HalfAtSite.lean [not in this library] calls `half_theLot_ok` and
`half_theLotFit_ok`; Honest/K3/Law/Thread/SitesOnce.lean and Honest/K3/Law/Keep/LotsSame.lean
[not in this library] import this file too.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
The lots at the specification's summands are not spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PlacesOnce
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatFitsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block)

/-! ## 1 General in the lot -/

/-- **A half of a lot of the list is found by the search at its place.** Conditional on the lot
standing in the list of lots; the half standing among its halves at the public part; and no two of
the gathered halves sharing a place. -/
theorem half_of_lot {V W X : Type} (Z : Pub) (Gr : Ground) (ls : List (HLot V W X))
    (L : HLot V W X) (hl : L ∈ ls) (x : Placed V W X) (hx : x ∈ L.halves Z Gr)
    (hn : ((firstOf Z Gr ls).map (·.place)).Nodup) :
    (firstOf Z Gr ls).find? (fun h => h.place == x.place) = some x :=
  find_once _ x (List.mem_flatMap.2 ⟨L, hl, hx⟩) hn

/-! ## 2 At the lots that are seated -/

section
variable {S Cl W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
  (req : Xi → OnBytes.Model.Head.Covered × Array Nat)

/-- **The seated row at a site, as `theLot` sets it**: the summands and the reader of the input are
those of the filling at the public part's sources. -/
def seatAt (Z : Pub) (s : Site) : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  proverSideOfLookupInChainAtOneOwner theReads (((fastFill (Rc := Rc) (sourcesAt cells weights req Z)).jobs s).asked)
    ((fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s) s.at_

/-- Its place is the site's. -/
theorem seatAt_place (Z : Pub) (s : Site) :
    (seatAt (Rc := Rc) (X := X) cells weights req Z s).place = s.at_.place := rfl

/-- That half stands among the halves of `theLot`. Conditional on the site. -/
theorem mem_theLot (Z : Pub) (Gr : Ground) (s : Site) (hs : s ∈ lookSites Z) :
    seatAt (Rc := Rc) (X := X) cells weights req Z s ∈
      (theLot (Rc := Rc) (X := X) cells weights req).halves Z Gr :=
  List.mem_map.2 ⟨s, hs, rfl⟩

/-- **The search at a site's place finds the half of `theLot`.** Conditional on `theLot` standing in
the list of lots; the site; and no two of the gathered halves sharing a place. No instance of these
hypotheses is exhibited in this file. -/
theorem half_theLot (Z : Pub) (Gr : Ground)
    (ls : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (hl : theLot cells weights req ∈ ls) (s : Site) (hs : s ∈ lookSites Z)
    (hn : ((firstOf Z Gr ls).map (·.place)).Nodup) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) =
      some (seatAt cells weights req Z s) :=
  half_of_lot Z Gr ls _ hl _ (mem_theLot cells weights req Z Gr s hs) hn

/-- The same from the frame's own test. Conditional on the same, with the frame's list of places
with two halves being empty. -/
theorem half_theLot_ok (Z : Pub) (Gr : Ground)
    (ls : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (hl : theLot cells weights req ∈ ls) (s : Site) (hs : s ∈ lookSites Z)
    (ht : twice (firstOf Z Gr ls) = []) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) =
      some (seatAt cells weights req Z s) :=
  half_theLot cells weights req Z Gr ls hl s hs (halves_once _ ht)

variable (bsOf : Pub → List (Block S Cl)) (made : Pub → Bool)

/-- That half stands among the halves of `theLotFit`. Conditional on the site and on the four: the
table of places can be read; a site for every address; the letter made accepts; `k3Fits` accepts at
every site. -/
theorem mem_theLotFit (Z : Pub) (Gr : Ground) (h1 : (spotsOf Z.cuts).isSome = true)
    (h2 : (lookMisses Z).isEmpty = true) (hm : made Z = true)
    (hf : ∀ s ∈ lookSites Z, k3Fits Z (bsOf Z) s = true) (s : Site) (hs : s ∈ lookSites Z) :
    seatAt (Rc := Rc) (X := X) cells weights req Z s ∈
      (theLotFit (Rc := Rc) (X := X) bsOf made cells weights req).halves Z Gr := by
  rw [theLotFit_all bsOf made cells weights req Z Gr h1 h2 hm hf]
  exact mem_theLot cells weights req Z Gr s hs

/-- **The search at a site's place finds the half of `theLotFit`, which is that of `theLot`.**
Conditional on `theLotFit` standing in the list of lots; the four; the site; and no two of the
gathered halves sharing a place. No instance of these hypotheses is exhibited in this file. -/
theorem half_theLotFit (Z : Pub) (Gr : Ground)
    (ls : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (hl : theLotFit bsOf made cells weights req ∈ ls) (h1 : (spotsOf Z.cuts).isSome = true)
    (h2 : (lookMisses Z).isEmpty = true) (hm : made Z = true)
    (hf : ∀ s ∈ lookSites Z, k3Fits Z (bsOf Z) s = true) (s : Site) (hs : s ∈ lookSites Z)
    (hn : ((firstOf Z Gr ls).map (·.place)).Nodup) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) =
      some (seatAt cells weights req Z s) :=
  half_of_lot Z Gr ls _ hl _ (mem_theLotFit cells weights req bsOf made Z Gr h1 h2 hm hf s hs) hn

/-- The same from the frame's own test. Conditional on the same, with the frame's list of places
with two halves being empty. -/
theorem half_theLotFit_ok (Z : Pub) (Gr : Ground)
    (ls : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (hl : theLotFit bsOf made cells weights req ∈ ls) (h1 : (spotsOf Z.cuts).isSome = true)
    (h2 : (lookMisses Z).isEmpty = true) (hm : made Z = true)
    (hf : ∀ s ∈ lookSites Z, k3Fits Z (bsOf Z) s = true) (s : Site) (hs : s ∈ lookSites Z)
    (ht : twice (firstOf Z Gr ls) = []) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) =
      some (seatAt cells weights req Z s) :=
  half_theLotFit cells weights req bsOf made Z Gr ls hl h1 h2 hm hf s hs (halves_once _ ht)

end

#print axioms ProofFile.Honest.K3.Law.AtThr.half_of_lot
#print axioms ProofFile.Honest.K3.Law.AtThr.seatAt_place
#print axioms ProofFile.Honest.K3.Law.AtThr.mem_theLot
#print axioms ProofFile.Honest.K3.Law.AtThr.half_theLot
#print axioms ProofFile.Honest.K3.Law.AtThr.half_theLot_ok
#print axioms ProofFile.Honest.K3.Law.AtThr.mem_theLotFit
#print axioms ProofFile.Honest.K3.Law.AtThr.half_theLotFit
#print axioms ProofFile.Honest.K3.Law.AtThr.half_theLotFit_ok

end ProofFile.Honest.K3.Law.AtThr
