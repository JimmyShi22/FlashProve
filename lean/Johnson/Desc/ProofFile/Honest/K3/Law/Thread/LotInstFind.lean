-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LotInstFind.lean: at the lookups' lot at the proof
file's own instance, and at the two lots of Honest/K3/LotInstFast.lean: every half stands at a place
of the kind K3, and the search at a site's place in the lot's own list of halves finds that site's
half. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: a site's half is `seatAt`
(Honest/K3/Law/Thread/HalfOfLot.lean).

What is shown.
  `theLotInst_kind`, `theLotFast_kind`, `theLotInstFast_kind`: `theLot_kind`
    (Honest/K3/Law/LotKind.lean) at `theLotInst` (Honest/K3/LotInst.lean), `theLotFast` and
    `theLotInstFast`. No hypothesis.
  `theLotInst_find`, `theLotFast_find`, `theLotInstFast_find`: `theLot_find`
    (Honest/K3/Law/Thread/SitesOnce.lean) at the same three. At the two lots at the instance the
    half is `seatAt` at `req := reqAt Z` (Honest/K3/WitReq.lean).

Hypotheses that remain.
  `hs`, in the last three: the site stands in `lookSites Z`.

How the proof goes. The first three are `rowLotAt_kind` (Honest/K3/Law/LotKind.lean). The last three
rewrite with `theLotInst_is`, `theLotFast_is` and `theLotInstFast_is`.

Imported, through Honest/K3/Law/Thread/SitesOnce.lean and Honest/K3/Law/LotKind.lean: the files
directly under Honest/, those under Honest/Thread/, Honest/Law/, Honest/SumLaw/ and Honest/K8/, and
Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Meant for the two hypotheses that `now_first_find` (Honest/FirstFindSixKinds.lean;
not imported) takes of each kind's lot,
where one of these three lots stands in the place of `theLot`. That the forms fit has not been tried
in Lean. Honest/K3/Law/Keep/CaseAtDesc.lean [not in this library] imports this file.

Limits. At `theLotFast` and `theLotInstFast` the half that the search finds is stated as `seatAt`,
the term whose reader is `askOf`: that is true because the lots are equal (`theLotFast_eq`,
`theLotInstFast_eq`), and says nothing on which term a program evaluates: a program that takes the
half out of these lots' lists evaluates `fastAsk` at the digits. General in the public part: nothing
is said on whether a site stands at any place. On public data and the lots' text alone.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInstFast
import Johnson.Desc.ProofFile.Honest.K3.Law.LotKind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitesOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (KindName)

variable {X W₀ Rc Xi Tr : Type}

/-- Every half of `theLotInst` stands at a place of the kind K3. -/
theorem theLotInst_kind (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    ∀ x ∈ (theLotInst (Rc := Rc) (X := X) cells weights).halves Z G,
      x.place.kind = KindName.K3 :=
  rowLotAt_kind _ Z G

/-- Every half of `theLotFast` stands at a place of the kind K3. -/
theorem theLotFast_kind (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    ∀ x ∈ (theLotFast (Rc := Rc) (X := X) cells weights req).halves Z G,
      x.place.kind = KindName.K3 :=
  rowLotAt_kind _ Z G

/-- Every half of `theLotInstFast` stands at a place of the kind K3. -/
theorem theLotInstFast_kind (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub)
    (G : Ground) :
    ∀ x ∈ (theLotInstFast (Rc := Rc) (X := X) cells weights).halves Z G,
      x.place.kind = KindName.K3 :=
  rowLotAt_kind _ Z G

end ProofFile.Honest.K3.Law

namespace ProofFile.Honest.K3.Law.AtThr

variable {X W₀ Rc Xi Tr : Type}

/-- The search at a site's place in the list of halves of `theLotInst` finds that site's half.
Conditional on the site standing in `lookSites Z`. -/
theorem theLotInst_find (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (Gr : Ground)
    (s : Site) (hs : s ∈ lookSites Z) :
    ((theLotInst (Rc := Rc) (X := X) cells weights).halves Z Gr).find?
        (fun x => x.place == s.at_.place) = some (seatAt cells weights (reqAt Z) Z s) := by
  rw [theLotInst_is]
  exact theLot_find cells weights (reqAt Z) Z Gr s hs

/-- The same at `theLotFast`. Conditional on the site standing in `lookSites Z`. -/
theorem theLotFast_find (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (Gr : Ground) (s : Site)
    (hs : s ∈ lookSites Z) :
    ((theLotFast (Rc := Rc) (X := X) cells weights req).halves Z Gr).find?
        (fun x => x.place == s.at_.place) = some (seatAt cells weights req Z s) := by
  rw [theLotFast_is]
  exact theLot_find cells weights req Z Gr s hs

/-- The same at `theLotInstFast`. Conditional on the site standing in `lookSites Z`. -/
theorem theLotInstFast_find (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub)
    (Gr : Ground) (s : Site) (hs : s ∈ lookSites Z) :
    ((theLotInstFast (Rc := Rc) (X := X) cells weights).halves Z Gr).find?
        (fun x => x.place == s.at_.place) = some (seatAt cells weights (reqAt Z) Z s) := by
  rw [theLotInstFast_is]
  exact theLotInst_find cells weights Z Gr s hs

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.theLotInst_kind
#print axioms ProofFile.Honest.K3.Law.theLotFast_kind
#print axioms ProofFile.Honest.K3.Law.theLotInstFast_kind
#print axioms ProofFile.Honest.K3.Law.AtThr.theLotInst_find
#print axioms ProofFile.Honest.K3.Law.AtThr.theLotFast_find
#print axioms ProofFile.Honest.K3.Law.AtThr.theLotInstFast_find
