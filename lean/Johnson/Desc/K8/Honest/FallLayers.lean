-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallLayers.lean: WHAT THE COUNT OF Johnson/Desc/K8/Honest/FallCount.lean ASKS OF
THE RUNS (`Gathers`), AT A FEED-FORWARD SEGMENT: THE STATEMENT, as a closed proposition, with the
definitions that it needs. DEFINITIONS. NO THEOREM. No prover.

A feed-forward segment's claims are gathered in the protocol's order
(Johnson/Desc/First/Driver/Chain.lean: orderOf .layers): the lookup on the calls: "objects",
"guests" · the layers' own: "front" · the lookup on the digits: "objects", "guests" · the smallness
test's: "K8.equations" · the layers' own: "back". Each of these lists but the ties and reads of
"K8.equations" is a function of what the verifier has heard in front of the batching draw:
  "objects"   the rows that the lookup's sumchecks left, as plain claims
  "guests"    no claim
  "front"     the forms `frontForms` at what the layers' own rounds returned and at what is shown
              under the ledger's slots (Johnson/Desc/First/Link/Law/K4Values.lean)
  the first four of "K8.equations"   `four8` (Johnson/Desc/First/Batch/Law/K8Four.lean)
  "back"      the forms `backForms`
So the plain claims' coefficients are written out here off the state in front of the draw.

Main names:
  `plainOf l`   forms as plain claims
  `coefAt l c`  the coefficients of claim number c of a list; 0 where the list has no such claim
  `layersFront gC gD lf`, `layersBack o`   the claims in front of "K8.equations" and behind it
  `layersCoef fr four bk mid`   the letter a of `Gathers`: the claims in front and the four, by their
      numbers; behind mid ties and reads, the claims behind
  **`GathersLayers`**   the statement
WHICH RUN STANDS AT WHICH ENTRY OF THE ORDER IS A PREMISE, up to a guard (every yes of the run that
stands there is a yes of the kind's own run, with the same return): `LayersTies`
(Johnson/Desc/First/Link/Law/PayLayers.lean) and the like for the two runs "objects".
Limits. At a feed-forward segment alone. The ties are premises. At a state at which one of the four
things heard is missing nothing is said.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallCount
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.Batch.BlindK3
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- Forms as plain claims. -/
def plainOf (l : List Aff) : List Claim := l.map fun f => { form := f }

/-- The coefficient of claim number c of a list on entry i of virtual row r of array t; 0 where the
list has no claim of that number. -/
def coefAt (l : List Claim) (c t r i : Nat) : Cb.Gl.E :=
  match l[c]? with
  | some cl => coefOn cl t r i
  | none => 0

/-- The claims in front of "K8.equations". gC, gD: what the lookup on the calls and the lookup on the
digits left; lf: the forms of "front". -/
def layersFront (gC gD : Forest.Heard) (lf : List Aff) : List Claim :=
  plainOf gC.rows.toList ++ plainOf lf ++ plainOf gD.rows.toList

/-- The claims behind "K8.equations". o: what the layers' own rounds returned. -/
def layersBack (o : Layer.Own) : List Claim := plainOf (K4Values.backForms o)

/-- The plain claims' coefficients by the claims' numbers. fr, four, bk: the claims in front, the
first four of "K8.equations", the claims behind; mid: how many ties and reads stand between. -/
def layersCoef (fr four bk : List Claim) (mid : Nat) (c t r i : Nat) : Cb.Gl.E :=
  if c < fr.length + 4 then coefAt (fr ++ four) c t r i
  else coefAt bk (c - (fr.length + (4 + mid))) t r i

/-- **`Gathers` at a feed-forward segment.** L: the segment; p4: the numbers of its block of the
layers' own kind. IF the runs that L's blocks state at the entries of the order stand under the
kinds' own runs; L's order is the protocol's; s stands in a feed-forward segment whose part of the
state a₀ holds what the two lookups left (gC, gD) and what the layers' own rounds returned (o); and
the forms of "front" at o and a₀'s ledger are lf: THEN the frame's function of claims meets `Gathers`
at s, with the numbers and coefficients written out off a₀. -/
def GathersLayers : Prop :=
  ∀ (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : K9.Where) (s : S)
    (a₀ : LayOwn) (gC gD : Forest.Heard) (o : Layer.Own) (lf : List Aff),
    LinkJoin.LayersTies L p4 nU →
    (∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls) →
    (∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits) →
    L.order = orderOf .layers →
    s.here = .lay a₀ →
    a₀.lookHeard = some gC → a₀.tl.heard = some gD → a₀.own = some o →
    K4Values.frontForms (!p4.k3Runs) p4.P p4.g o a₀.F = some lf →
    Gathers p (claimsInBy L.each L.hear L.order) s a₀.tl o.funs
      (layersFront gC gD lf).length 4
      (layersCoef (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (layersBack o)
        (a₀.tl.NM + (readsList a₀.tl o.funs).length))

end VerifiableInference.Desc.First.K8.Honest
