-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormDoor.lean: THE FORM's HALF AT THE FRONT OF A PROXIMITY TEST: the letters for
saying that the front's part in the kind's block (guardedProximityTestParts.front, Johnson/Desc/K12/JoinGuarded.lean)
RETURNS ok.

What is proved of them: Johnson/Prover/Link/FormDoorLaws.lean.

Main names.
  FrontOwes p t G   A RECORD OF PREMISES on the record t in front of the test: guard (f): the plan's
    count of roots is the record's; EVERY CLAUSE OF frontL (Johnson/Desc/K12/Front.lean: nineteen,
    on the schedule as it lies in the record); AT EVERY CLAIM THAT LIES OPEN ON THE GROUP:
    RowClauses (Johnson/Desc/First/Batch/Law/DoorTests.lean: the sentences for the tests of a
    new open row, Ground.rowL); guard (p): pubOk (Johnson/Desc/K12/Law/PubOk.lean) at the record's
    codes.

Limits. frontL and pubOk are taken over WHOLE, as premises: nothing of them is unfolded. THREE OF
RowClauses' FIELDS READ VALUES: pads ("no coefficient on a pad": the words of a row's coefficient
are 0); terms and forms (Tensor.ok, OnBytes/Iop/Tensor.lean, of a term's tensor and, through
Form.fits, of each tensor of a form: each written-out variable's pair is (1, 1)): equalities of
elements on a row's coefficients, which come from drawn values: owed for all draws, by the row's
make. Its field runs reads sizes alone. Five of frontL's clauses say again what TestFront.fresh says
of the first fold's mask.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormBat
import Johnson.Desc.First.Batch.Law.DoorTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **What the front's part asks.** -/
structure FrontOwes (p : P12) (t : T12) (G : Group) : Prop where
  roots : p.nums.free = t.roots
  front : ∀ c ∈ frontL t.st t.book t.g t.mask, c.2 = true
  rows : ∀ row ∈ G.rows.toList, K9L.RowClauses t.st G row
  pub : H2K.Pub.pubOk p t.st.codes = true

end Johnson.Prover.Link
