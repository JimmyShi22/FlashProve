-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ULayAtAll.lean: THE FIELD hUL OF WHAT IS STILL OWED FOR KIND K1's CONDITION
(`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED CONSTANT, IN THE
FIELD's OWN TYPE: at a feed-forward segment the constant's stated function is the one made of that
segment's own plan and of its own list of arrays. One statement with its proof, and one fact by
evaluation. HOW. The constant's letter uL is `uLAt` at the public parameters and
at the list's arrays (Johnson/Road/K4/ULayAt.lean): it reads the plan through the lookup
arguments' `tlAt`. In the goals' scope: the list has 25 segments (`ground_gets`); the segment's
group is half its number (`group_lay`, Johnson/Desc/K1/Law/ArmLayMats.lean);
attention stands between, and there are 12 groups (`scope_plans`): so `tlAt_lay`
(Johnson/Desc/First/Look/DigitsShapeAt.lean) gives that very plan. The arrays agree by the make.
  `lay_even`: a feed-forward segment's number is even and below 24: by evaluation.
  `hUL_atAll`: the field. PREMISES: the head hA and the opening O.

A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns.
What is not claimed. That the head or the opening can be met. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.ArmLayMats
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.First.Look.DigitsShapeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.Sound (linksFull matsOfData)
open OnBytes.Road.K4 (uLay uLAt)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)
open IM (Open)

theorem lay_even : ∀ l < 25, (linksFull[l]?).getD .layers = ModelPart.layers →
    2 * (l / 2) = l ∧ l / 2 < 12 := by decide

/-- **The field hUL.** -/
theorem hUL_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ l X hp, (linksFull[l]?).getD .layers = .layers → Bs.G₀.built[l]? = some X →
      Bs.G₀.W.G[X.g]? = some hp →
      hA.𝔇.uL l = uLay hp.tl fun _ D => matsOfData hp.tl (hA.𝔇.pubD.d3.arrayOf.getD l #[]) D := by
  intro l X hp hsub hX hG
  obtain ⟨sz, -⟩ := IM.ground_gets hA.scope hA.reads O.pub O.blank
  have hl : l < 25 := by
    rw [← sz]
    exact (Array.getElem?_eq_some_iff.1 hX).1
  obtain ⟨e, h12⟩ := lay_even l hl hsub
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hA.scope hA.reads hA.pubOne
  rw [group_lay hA.scope hA.reads O l hl hsub X hX, O.W] at hG
  have ht := First.Look.tlAt_lay (X := Zp.p.X) hG (by
    have : (Zp.p.X).NGr = 12 := ng
    omega)
  have p4' : (Zp.p.X).p4 = true := p4
  rw [p4', if_pos rfl, e] at ht
  show uLAt (P5J.At.X Zp) (P5J.At.names3 Zp) l = _
  unfold uLAt
  have ht' : First.Look.tlAt (P5J.At.X Zp) l = some hp.tl := ht
  rw [ht', Option.getD_some]
  have hn : P5J.At.names3 Zp l = hA.𝔇.pubD.d3.arrayOf.getD l #[] := by
    show ((Zp.made.p.built.links[l]?).map (·.arrayOf)).getD #[] =
      (Zp.made.p.built.links.map (·.arrayOf)).getD l #[]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rw [hn]

end VerifiableInference.Desc.K1
