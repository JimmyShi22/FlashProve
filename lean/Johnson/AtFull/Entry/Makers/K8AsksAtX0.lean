-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/K8AsksAtX0.lean: THE SMALLNESS TEST'S CLOSED TEST ON THE PUBLIC PART
ACCEPTS AT THE VALUE THAT THE PUBLIC PART'S MAKER RETURNS AT THE LEAN LIBRARY'S WRITTEN COPY OF THE
FULL-SIZE PUBLIC FILES (`VerifierAndGoals.storedPublicFiles`, as Ladder/Stored.lean spells it). One statement, under the
size of the layout file.

  **`k8AsksWB_zFull`** (hsz : the stored layout file has 224975 bytes) (hX : `publicOfO`, at the
    format's second hash function, returns X₀ at `VerifierAndGoals.storedPublicFiles`): `P1K8L.k8AsksWB X₀ = true`.
How. The theorem that the maker returns there (Johnson/AtFull/Public/Join.lean) names the parts of
its value by letters, each with its own maker's equation; `k8AsksWB_at`
(Johnson/AtFull/Entry/Makers/K8AsksAtMakers.lean) carries the closed facts to these letters; a maker
is a function, so X₀ is that value.

Limits. UNDER hsz, WHICH IS NOT SHOWN HERE. `VerifierAndGoals.storedPublicFiles` is three terms written in
Ladder/Stored.lean: no Lean code ties them to the repository's folder of examples; the example's
weights are synthetic. At the second hash function. The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Entry.Makers.K8AsksAtMakers
import Johnson.AtFull.Public.AtX0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (Makers opens_yFull)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (shape_at_stored)

/-- **The closed test accepts at what the public part's maker returns at the stored full-size
files.** -/
theorem k8AsksWB_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : P1K8L.k8AsksWB X₀ = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -, -,
    hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  obtain rfl := Except.ok.inj (hX'.symm.trans hX)
  refine k8AsksWB_at opens_yFull M rfl rfl ?_
  show headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines) yFull = Cond.hFull
  rw [shape_at_stored, _root_.AtFull.Public.yFull_lPd]
  rfl

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.k8AsksWB_zFull
