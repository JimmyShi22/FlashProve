-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SymsHalvesB.lean: TWO SENTENCES ON PUBLIC DATA THAT ARE OWED BENEATH THE NAMED
CONDITION OF THE SUB-PROTOCOL K1 ("at each attention segment | at each layers' segment the symbol
arrays of the segment's matrices are seated": `symsSeatedB`, Johnson/Desc/K1/Law/ArmSyms.lean, under
"for all" over the segments), EACH AS ONE TEST WITH CODE, WITH ITS LAW. Definitions (two tests) and
statements with their proofs; nothing is evaluated.

  `battB`, `hBatt_of`   the attention segments: the test, and the sentence in its own text from it
  `blayB`, `hBlay_of`   the layers' segments: the like
Each test accepts at a segment whose plan the public parameters lack, for want of a case, as the
sentence's own text does: a sheet that evaluates them counts the plans beside. No negative test is
typed here: none can be had without public parameters: they ride in the sheet
(Johnson/L25X/K1Section.lean [not in this library]).

What is not claimed. That the tests accept at any files. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmSyms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (ModelPart)

/-- At each attention segment the symbol arrays of the segment's matrices are seated. -/
def battB (arrs : Array (Array (ℕ × String))) (X : Verify.Public) (lay : ReqLayout)
    (shp : ReqShape) : Bool :=
  (List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == ModelPart.attention) || (X.A[l / 2]?).all fun Ap =>
      symsSeatedB (arrs.getD l #[]) lay shp l Ap.seam.tl

/-- At each layers' segment the symbol arrays of the segment's matrices are seated. -/
def blayB (arrs : Array (Array (ℕ × String))) (X : Verify.Public) (lay : ReqLayout)
    (shp : ReqShape) : Bool :=
  (List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == ModelPart.layers) || (X.G[l / 2]?).all fun hp =>
      symsSeatedB (arrs.getD l #[]) lay shp l hp.tl

theorem hBatt_of {arrs : Array (Array (ℕ × String))} {X : Verify.Public} {lay : ReqLayout}
    {shp : ReqShape} (h : battB arrs X lay shp = true) :
    ∀ l Ap, l < 25 → (linksFull[l]?).getD .layers = .attention → X.A[l / 2]? = some Ap →
      symsSeatedB (arrs.getD l #[]) lay shp l Ap.seam.tl = true := by
  intro l Ap hl hsub hA
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [hsub, hA] at h1
  exact h1

theorem hBlay_of {arrs : Array (Array (ℕ × String))} {X : Verify.Public} {lay : ReqLayout}
    {shp : ReqShape} (h : blayB arrs X lay shp = true) :
    ∀ l hp, l < 25 → (linksFull[l]?).getD .layers = .layers → X.G[l / 2]? = some hp →
      symsSeatedB (arrs.getD l #[]) lay shp l hp.tl = true := by
  intro l hp hl hsub hG
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [hsub, hG] at h1
  exact h1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hBatt_of
#print axioms VerifiableInference.Desc.K1.hBlay_of
