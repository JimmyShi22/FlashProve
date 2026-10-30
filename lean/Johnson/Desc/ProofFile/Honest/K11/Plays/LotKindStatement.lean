-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotKindStatement.lean: TWO FACTS ON THE KIND's LOT OF HALVES
(`headMergeLot`, Honest/K11/Part.lean), IN THE FORMS THAT THE FRAME's GENERAL LEMMA ON "WHICH HALF
IS FOUND AT MY PLACE" ASKS OF A KIND: STATEMENTS ALONE: two definitions of propositions. NOTHING IS
PROVED IN THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

  `HeadMergeLotKind`   general in the public part and the ground: every half of the lot stands at a
                       place of the kind K11
  `HeadMergeLotFind`   under the library's head: in the lot's own list of halves the search by
                       `IM.k11Place` finds the kind's half

Limits. NO NEW CONTENT IN THE SECOND: it is the kernel of `HalfAtHead` (OfLotsStatement.lean of this
folder, a file that is not in this library) set free of the prover and of the list of lots: typed
for its form, and because it rests on far fewer files. They speak of the kind's own lot alone: THAT
NO OTHER LOT OF A FILLING LAYS A HALF AT A PLACE OF THE KIND K11, AND THAT THE LOT STANDS IN A
FILLING's LIST, ARE NOT SAID: no kind can show the first alone. claims and weights are letters. The
head is a premise of the second, at the earlier hash, at the full size: no example of it is shown
here; the library's `head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one under four
premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.K11.Exchange.AtFullStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)

/-- The statement on the kind of the lot's places. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeLotKind : Prop :=
  ∀ (W₀ Rc Tr X : Type)
    (claims : ProofFile.Pub → ProofFile.Ground → ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (Z : ProofFile.Pub) (G : ProofFile.Ground),
    ∀ x ∈ (headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights).halves Z G,
      x.place.kind = .K11

/-- The statement on the search in the lot's own list. Not proved here; a lemma's statement, none of
the library's goals. -/
def HeadMergeLotFind : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain S ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (_ : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W₀ Rc Tr X : Type) (Bs : ProofFile.PureBase)
    (claims : ProofFile.Pub → ProofFile.Ground → ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (((headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights).halves Zp Bs.G₀).find? fun g =>
      g.place == IM.k11Place) =
      some (headMergeHalf (claims Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀))

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.HeadMergeLotKind
#print axioms ProofFile.Honest.K11.HeadMergeLotFind
