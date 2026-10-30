-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ReadsArrAtAll.lean: THE FIELD hArr OF WHAT IS STILL OWED FOR KIND K1's
CONDITION (`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED
CONSTANT's HEAD, IN THE FIELD's OWN TYPE: the closed test `readsArrB` (
Johnson/Desc/K1/Law/HeadNumbersAtAll.lean: the output head's segment's list of arrays has an entry
at the number of the head's array of the reads) accepts at the public part's own list of segments
and public parameters. Statements with their proofs: calls. HOW. Another file has the law:
`reads_named_of_built` (Johnson/Desc/Kinds/Law/ReadsRoomOfBuilt.lean): behind an accept of the
public tests on the segments' structures the last segment's third vector stands in its list of
arrays under the name "U3". That the public part's built segments are such a return at the
description's own list: `planned_built`, `plain_built` (Johnson/IMR/PureJoin.lean) off
`madeOf_planned`, `pubBy_made` (MakerPublic.lean). That the head's segment is the last: the
library's `listLinksH_with`. That the third vector is array 0: `public_third`
(Johnson/Desc/Kinds/Law/ReadsNamed.lean). The road is that of `room_at_const`
(Johnson/Desc/Kinds/Law/K6BuiltAtConst.lean), line by line: said plainly.
  `reads_named_at24`: the entry itself: (24, "U3").
  `hArr_atAll`: the field. PREMISE: the head hA.
A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns. What is not claimed. That the head
can be met. Nothing on the other arrays of that list, nor on another segment's list. Nothing on
soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.HeadNumbersAtAll
import Johnson.Desc.Kinds.Law.ReadsRoomOfBuilt
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.IMR.PureJoin
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf)
open ProofFile (Cl)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place}

/-- **The entry itself.** -/
theorem reads_named_at24 (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    ((Zp.made.p.built.links.map (·.arrayOf)).getD 24 #[])[0]? = some (24, "U3") := by
  have hp : ProofFile.Plain.planned OnBytes.secondHashFunction Zl.pol Zl.KL (some Zl.lay) = .ok Zp.made.p :=
    ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made hA.laid.pub)
  obtain ⟨l₀, hl, hb⟩ := IM.plain_built (IM.planned_built hp)
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hA.scope hA.reads hA.pubOne
  have p4' : Zp.made.p.X.p4 = true := p4
  have ng' : Zp.made.p.X.NGr = 12 := ng
  unfold ProofFile.Plain.linksPlain at hl
  rw [p4'] at hl
  obtain ⟨_, _, z, _, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  have T : Zp.made.p.X.H.tl.ix.U.getD 2 none = some 0 :=
    Kinds.Head.Law.ReadsNamed.public_third hA.pubOne
  have c1 := (Kinds.Head.Law.Built.reads_named_of_built hb z e (t := 0) T).1
  rw [ng'] at c1
  exact c1

/-- **The field hArr.** -/
theorem hArr_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    readsArrB Zp.made.p.built.links (P5J.At.X Zp) = true := by
  unfold readsArrB
  rw [reads_zero hA, reads_named_at24 hA]
  rfl

end

end VerifiableInference.Desc.K1
