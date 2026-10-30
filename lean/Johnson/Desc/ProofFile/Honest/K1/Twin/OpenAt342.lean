-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/OpenAt342.lean: FOR THE TWINS OF THE LIBRARY's ARMS (the kind
K1), BESIDE Twin/HonestAt.lean: ONE MORE CLOSED FACT AT THE COMPOSED MEANING's TABLE OF NAMES
mgMore: "frame.sentIs" of segment 24 is open in front of the output head's reads. TYPED BY HAND. Two
theorems; no definition. PUBLIC DATA ALONE. IT STANDS IN THE LIBRARY's
NAMESPACE VerifiableInference.Desc.K1; the names are not the library's.

  - sentOpen342_mg: the library's sentOpen342 (Johnson/Desc/K1/Law/PlanesLeft6AtAll.lean) WITH
    mwMore TURNED TO mgMore AND NOT A SIGN ELSE. sentOpen342_mg_fails: its negative test, with the
    same turn. Evaluations in Lean's kernel.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: the twins that call this stand
at the meaning "honest", at which the clauses noColl, shown and decodes are True by definition: a
law at that meaning may stand beneath statements on completeness or zero knowledge only, never
beneath a statement on soundness.

Drift. If the sealed fact turns, its like here is typed anew by hand and held against it anew.

Limits. THE FULL SIZE ALONE. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.PlanesLeft6AtAll
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (sentIsB link_of_sentIs)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase linkNo onQ)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (MatsSeated)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (k1Ix)
open VerifiableInference.Desc.Sound (mgMore)

set_option maxRecDepth 1000000 in
theorem sentOpen342_mg : openB mgMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
    (.more (some 24) "frame.sentIs") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: another segment's item is not open there. -/
theorem sentOpen342_mg_fails : openB mgMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
    (.more (some 23) "frame.sentIs") = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sentOpen342_mg
#print axioms VerifiableInference.Desc.K1.sentOpen342_mg_fails
