-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/PublicAtEntry.lean: KIND K5: THREE TESTS ON PUBLIC DATA THAT THE
TIE BETWEEN THE KIND's LAW AND THE TABLE OF JOINTS ASKS ARE PAID BY THE RETURN OF THE VALUE THAT
verify() LAYS: no running text need ask them.

Why. An evaluated Bool is a premise until a text that the verifier runs asks it, or a law gives it.
Three of the six Bools of the tie (tiePublicB, Johnson/Desc/First/Att/K05TiePublic.lean) are laws of
every return of buildLinksH (Johnson/Desc/First/Att/K05PublicOfBuilt.lean). The planner behind the
proof file's description ends in such a return (BuiltOfPub.lean). Here the two are joined.

  `K05_public_of_open`: **from an opening, F.planOk and the door's yes**, at Ds := sentOfBuilt
    Z.first Z.p.built (the codes, shape and layout of the first chain's parameters; link by link the
    built links' lists of arrays): reqLayoutOk = true; oneMaskB Ds i = true at every i; and at every
    entry of the first chain's flat list that bears K5, with g, a, x pinned as in
    TiedAtEntry.lean: masksUpTo Ds x x.ns = true.
  `K05_public_at_entry`: the same from proofDataAndDecisionOfPublicFiles's return (two lines, over laid_opens,
    LawAtLaid.lean).
NOT HERE: the other three (the codes' lengths; symArraysB; u3PublicB). OVER WHAT IT STANDS: all that
LawAtLaid.lean's head names. EMPTY wherever proofDataAndDecisionOfPublicFiles refuses.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.BuiltOfPub
import Johnson.H2K5R.PlaceAtFlat
import Johnson.Desc.First.Att.K05PublicOfBuilt
import Johnson.Desc.First.Att.K05PlanOfPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params OnBytes.Plan
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc (Claim Block Chain FileDescription)

/-- **THREE PUBLIC TESTS, FROM AN OPENING.** -/
theorem K05_public_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hpl : F.planOk = true)
    {D : OnBytes.Maker.WholeD} (hs : ∀ t ∈ LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    reqLayoutOk Z.first.codes Z.first.shape Z.first.layout = true ∧
      (∀ i, oneMaskB (sentOfBuilt Z.first Z.p.built) i = true) ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K5 →
        ∃ (g : ℕ) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place),
        E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ Bs.G₀.W.A[g]? = some a ∧
        lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
        masksUpTo (sentOfBuilt Z.first Z.p.built) x x.ns = true := by
  obtain ⟨-, hP, Hx⟩ := K05_facts_of_open O hpl hs
  obtain ⟨-, -, eW, -, -⟩ := IM.blank_ground O.blank
  obtain ⟨l₀, hl, hb⟩ := built_of_pub O.pub
  refine ⟨layout_of_built hb, oneMask_of_built hb, fun E hE hK => ?_⟩
  obtain ⟨g, blk, a, x, h4, hg, hfl0, -, -, -, -, -, ea, hx, hlk⟩ := Hx E hE hK
  obtain ⟨sv, hfp', -, hk0, -⟩ := K05_place_at O h4 hg
  have eP : E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
    rw [← hfp', List.getElem?_map, hfl0] at hk0
    exact Option.some.inj hk0
  obtain ⟨-, -, ens, -, -⟩ := k5Plan_of_public hP h4 ea hx (Params.settingOf Bs.G₀.W.P.frame)
  have ea' := ea
  rw [eW] at h4 hg ea'
  obtain ⟨Y, hY, eY⟩ := link_att_ns hl h4 ea' hg
  exact ⟨g, a, x, eP, ea, hx, masks_of_built hb hY hlk (ens.trans eY.symm)⟩

/-- **THREE PUBLIC TESTS, PAID BY THE VALUE's RETURN.** -/
theorem K05_public_at_entry {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F Z Bs base₀ c A B, IM.Open o pol lay KL F Z Bs base₀ c A B ∧
      reqLayoutOk Z.first.codes Z.first.shape Z.first.layout = true ∧
      (∀ i, oneMaskB (sentOfBuilt Z.first Z.p.built) i = true) ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K5 →
        ∃ (g : ℕ) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place),
        E.place = ⟨1, some (2 * g + 1), 3, .K5⟩ ∧ Bs.G₀.W.A[g]? = some a ∧
        lookAt Bs.G₀.W (2 * g + 1) false = some x ∧
        masksUpTo (sentOfBuilt Z.first Z.p.built) x x.ns = true := by
  obtain ⟨F, Z, Bs, base₀, c, A, B, -, hpl, -, -, hs, O⟩ := laid_opens h
  obtain ⟨h1, h2, h3⟩ := K05_public_of_open O hpl hs
  exact ⟨F, Z, Bs, base₀, c, A, B, O, h1, h2, h3⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_public_of_open
#print axioms VerifiableInference.Desc.First.Att.P.K05_public_at_entry
