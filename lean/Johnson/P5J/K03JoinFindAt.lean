-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03JoinFindAt.lean: THE KIND "LOOKUP" (K3), AT THE TWELVE ATTENTION SEGMENTS, AT THE
COMPOSED MEANING's OWN PARAMETERS: WHAT THE LINK's SECOND SUB-PROTOCOL STATES UNDER THE NAME "join"
IS THE LOOKUP's OWN RUN AT THE CALLER's KEYS (THAT IT STATES ONE IS NOT SAID HERE). One theorem.
  `k03_joinFind_att`: ends, to the letter, in the premise hfJ of `k03_rides_dig_att`
    (Johnson/P5J/K03RidesDigAt2.lean; the lookup's files' own text in
    Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean). The statement's end is typed after that file
    and held against it by program: token for token.
AN APPLICATION: the sentence from an opening of the maker is `K05_join_of_open`
(Johnson/H2K5R/JoinAtOpen.lean: the guard already struck at "join"): here it is called at the head's
own opening; the link is the one of the chain cF (one entry of one list). WHAT STAYS A PREMISE: the
head AtMgA.
Limits. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.MgAtAll
import Johnson.H2K5R.JoinAtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Maker OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.Desc.First.Att.P (keysOfO K05_join_of_open)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **hfJ AT THE CONSTANT.** -/
theorem k03_joinFind_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ g < 12, ∀ A, (At.X Zp).A[g]? = some A →
    ∀ Lk, cF.links[2 * g + 1]? = some Lk →
    (∀ n r, (statesOfLink Lk 2).find? (fun x => x.1 == "join") = some (n, r) →
      r = VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm)
        (keysOfO A)) := by
  intro g hg A hA Lk hLk n r hf
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨Lk', e1, e2⟩ := K05_join_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) (by rw [hW]; exact hA)
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans hLk)
  rw [e2] at hf
  exact (Prod.mk.inj (Option.some.inj hf)).2.symm

end P5J

#print axioms P5J.k03_joinFind_att
