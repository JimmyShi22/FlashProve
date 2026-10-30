-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SendWFormsAtHead.lean: THE MAKES OF THE STATEMENT's ROWS BEHIND THE MEMBER AT
THE PLACE M:4 (member 356 of the flat list of the proof file's own first chain): the one small law
more that ChainF.lean asks. Under the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  **`sendW_forms_at`**: with msg what linMessageW reads off the first chain's parameters: behind a
    yes of the member at number 356 on two rounds, where W's sending's step wG returns m at the
    shape in front: formsOf t.st = rowsForms (K13.whereOf Zp) m (sendForms (wPar Zp msg) ‹the number
    of messages in front, off the shape› (formsOf s.st)): a function of the shape in front and the
    makes in front.
By sendW_at (SendWAtHead.lean), sendW_carries (Johnson/Desc/First/Shape/SendW.lean), sendW_forms
(ChainF.lean), rowsB_forms (RowsBehindWForms.lean).
Limits. Of a yes on two rounds alone: of a yes on another list nothing is said. Under wG's own
return. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). At the earlier hash OnBytes.secondHashFunction.
Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.SendWStepAtHead
import Johnson.Desc.First.Shape.RowsBehindWForms
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem sendW_forms_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (b : Block S ProofFile.Cl) (msg : Array OracleNotice),
      linMessageW Zp.first.lin = some msg ∧ cF.blocksInOrder[356]? = some b ∧
      ∀ s r₁ r₂ gs t m, b.decide s [r₁, r₂] gs = .ok t →
        wG (wPar Zp msg) (chainSh s) = some m →
        formsOf t.st = rowsForms (VerifiableInference.Desc.K13.whereOf Zp) m
          (sendForms (wPar Zp msg) (chainSh s).core.st.oracles.length (formsOf s.st)) := by
  obtain ⟨b, msg, hm, q, hy⟩ := sendW_at h
  refine ⟨b, msg, hm, q, fun s r₁ r₂ gs t m hd hw => ?_⟩
  obtain ⟨⟨m', h1, h2⟩, -, -⟩ := (hy s t [r₁, r₂] gs).1 hd
  have h1' : (VerifiableInference.Desc.K1.sendAtS (Cl := Unit) (wPar Zp msg)).decide s [r₁, r₂]
      (gs.take (VerifiableInference.Desc.K1.sendAtS (Cl := Unit) (wPar Zp msg)).openings) =
      .ok m' := h1
  obtain rfl := sendW_carries h1' hw
  rw [rowsB_forms h2, sendW_forms h1']

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sendW_forms_at
