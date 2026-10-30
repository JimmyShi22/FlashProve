-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/BuiltOfPub.lean: THE PLANNER's RETURN BEHIND THE
VALUE THAT verify() LAYS: the built links of the description's public part are a return of
buildLinksH (OnBytes/Model/StagesLinks.lean: the public tests on the links of a request's chain), at
the first chain's own parameters and at the links that the public parameters' plans make.

Why. Facts on public data that a law gives at every return of buildLinksH are then paid behind
proofDataAndDecisionOfPublicFiles's return, as the guard's yes is: no text need ask them again.

W below: the public parameters (the plan derived from the three public files), as the seat holds it.

OVER WHAT IT STANDS: all that Johnson/H2K5R/LawAtLaid.lean's head names.

Main names:
  `built_of_pub`: where pubPlain o returns Z: linksPlain Z.p.X returns some l₀, and buildLinksH l₀ …
    Z.first = .ok Z.p.built. From planned_built and plain_built (Johnson/IMR/PureJoin.lean), as
    inside ground_public there, with the return named.
  `link_att_ns`: where linksPlain X returns l₀ and the proof covers attention: link 2 g + 1 of l₀ is
    there and has the number of scalars of group g's plan.
  `K05_built_of_open`: **from an opening**: W is Z.p.X; the two facts of built_of_pub at W; and
    link_att_ns at every group. `K05_built_at_entry`: the same from proofDataAndDecisionOfPublicFiles's return (two lines).
In raw terms: no kind's files' Lean structure for the data beside the public parameters is imported.
EMPTY wherever proofDataAndDecisionOfPublicFiles refuses.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.LawAtLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH buildLinksH)
open VerifiableInference.Desc (Claim Block Chain FileDescription)

/-- **The built links are a return of buildLinksH.** -/
theorem built_of_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ∃ l₀, ProofFile.Plain.linksPlain Z.p.X = .ok l₀ ∧
      buildLinksH l₀ Z.p.X.NGr Z.p.X.p4 Z.p.X.layers.wsLay Z.first = .ok Z.p.built :=
  IM.plain_built (IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ))))

/-- An attention link of the plans' links has its plan's number of scalars. -/
theorem link_att_ns {X : Verify.Public} {l₀ : Array LinkH}
    (hl : ProofFile.Plain.linksPlain X = .ok l₀) (h4 : X.p4 = true) {g : ℕ} {a : Attention.Plan}
    (ha : X.A[g]? = some a) (hg : g < X.NGr) : ∃ Y, l₀[2 * g + 1]? = some Y ∧ Y.ns = a.ns := by
  unfold ProofFile.Plain.linksPlain at hl
  rw [h4] at hl
  obtain ⟨g0, -, -, p0, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  obtain ⟨-, q⟩ := p0 g _ _ (Array.getElem?_eq_getElem (by rw [g0]; exact hg))
    (by rw [Array.getElem?_map, ha]; rfl)
  exact ⟨_, q, rfl⟩

/-- **THE PLANNER's RETURN, FROM AN OPENING.** -/
theorem K05_built_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    Bs.G₀.W = Z.p.X ∧ ∃ l₀, ProofFile.Plain.linksPlain Bs.G₀.W = .ok l₀ ∧
      buildLinksH l₀ Bs.G₀.W.NGr Bs.G₀.W.p4 Bs.G₀.W.layers.wsLay Z.first = .ok Z.p.built ∧
      ∀ (g : ℕ) (a : Attention.Plan), Bs.G₀.W.p4 = true → g < Bs.G₀.W.NGr →
        Bs.G₀.W.A[g]? = some a → ∃ Y, l₀[2 * g + 1]? = some Y ∧ Y.ns = a.ns := by
  obtain ⟨-, -, eW, -, -⟩ := IM.blank_ground O.blank
  obtain ⟨l₀, hl, hb⟩ := built_of_pub O.pub
  rw [← eW] at hl hb
  exact ⟨eW, l₀, hl, hb, fun g a h4 hg ha => link_att_ns hl h4 ha hg⟩

/-- **THE PLANNER's RETURN BEHIND THE VALUE's.** -/
theorem K05_built_at_entry {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F Z Bs base₀ c A B l₀, IM.Open o pol lay KL F Z Bs base₀ c A B ∧ Bs.G₀.W = Z.p.X ∧
      ProofFile.Plain.linksPlain Bs.G₀.W = .ok l₀ ∧
      buildLinksH l₀ Bs.G₀.W.NGr Bs.G₀.W.p4 Bs.G₀.W.layers.wsLay Z.first = .ok Z.p.built ∧
      ∀ (g : ℕ) (a : Attention.Plan), Bs.G₀.W.p4 = true → g < Bs.G₀.W.NGr →
        Bs.G₀.W.A[g]? = some a → ∃ Y, l₀[2 * g + 1]? = some Y ∧ Y.ns = a.ns := by
  obtain ⟨F, Z, Bs, base₀, c, A, B, -, -, -, -, -, O⟩ := laid_opens h
  obtain ⟨eW, l₀, hl, hb, H⟩ := K05_built_of_open O
  exact ⟨F, Z, Bs, base₀, c, A, B, l₀, O, eW, hl, hb, H⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.built_of_pub
#print axioms VerifiableInference.Desc.First.Att.P.link_att_ns
#print axioms VerifiableInference.Desc.First.Att.P.K05_built_of_open
#print axioms VerifiableInference.Desc.First.Att.P.K05_built_at_entry
