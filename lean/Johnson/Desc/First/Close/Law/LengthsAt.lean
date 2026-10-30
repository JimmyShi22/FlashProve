-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LengthsAt.lean: THE TWO EQUATIONS ON THE CODES' MESSAGE LENGTHS, WHICH
`cubeFits_of_shapes`, `names_in` AND `ties_of_shapes` (CubeOfShapes.lean, NamesOfShapes.lean,
ShapesBegun.lean, beside this file) LEAVE AS PREMISES, FROM THREE EQUATIONS ON THE STATEMENT: its
table of codes is the written one; the group's two code numbers are 0. Statements and proofs.

  `front_lengths`: at both sizes: the written table's first main code and first mask code have
    message lengths 2 to their own exponents, and these are the lengths of every group in front: by
    the kernel.
  `lengths_full`, `lengths_small`: T.codes = `codesFull2` (`codesSmall2`); G.code = 0; G.maskCode =
    0; T.groups[g]? = some G; (begun T g G).layout g = some lay; gs a group in front: 2 ^ lay.logEll
    = gs.main.ell and 2 ^ lay.logEllZk = gs.mask.ell.
  `mask_ell_full`, `mask_ell_small`: the clause "code" of K10's promise (`K10On`, OnK10.lean) at the
    mask code number 0: the statement's mask code has the stage's length.
Limits. The three equations on the statement are premises: that a verifier's state's statement has
the written table of codes is another house's fact along the fold; that a link's group bears the
code numbers 0 is not shown here (the planner's `fillLinks` lays 0 into the links' messages'
shapes: read). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayBegun
import Johnson.G.SwitchPricesLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.G
open OnBytes.LayLaw (layout_eq begun_layout)

/-- The written tables' first codes against the groups in front: by the kernel. -/
theorem front_lengths :
    (∀ gs ∈ frontFull, 2 ^ (codesFull2.base.getD 0 default).logEll = gs.main.ell ∧
      2 ^ (codesFull2.mask.getD 0 default).logEll = gs.mask.ell ∧
      (codesFull2.mask.getD 0 default).ell = gs.mask.ell) ∧
    ∀ gs ∈ frontSmall, 2 ^ (codesSmall2.base.getD 0 default).logEll = gs.main.ell ∧
      2 ^ (codesSmall2.mask.getD 0 default).logEll = gs.mask.ell ∧
      (codesSmall2.mask.getD 0 default).ell = gs.mask.ell := by
  decide +kernel

section
variable {T : Statement} {G : Group} {g : ℕ} {lay : GroupLayout}

/-- The layout's two exponents are those of the group's two codes. -/
theorem layout_exps (hG : T.groups[g]? = some G) (hL : (begun T g G).layout g = some lay) :
    lay.logEll = (T.codes.base.getD G.code default).logEll ∧
      lay.logEllZk = (T.codes.mask.getD G.maskCode default).logEll := by
  rw [begun_layout T g G hG, layout_eq T g G hG] at hL
  obtain rfl := Option.some.inj hL
  exact ⟨rfl, rfl⟩

/-- **At the full size.** -/
theorem lengths_full (hc : T.codes = codesFull2) (h0 : G.code = 0) (h1 : G.maskCode = 0)
    (hG : T.groups[g]? = some G) (hL : (begun T g G).layout g = some lay) {gs : GroupSize}
    (hgs : gs ∈ frontFull) : 2 ^ lay.logEll = gs.main.ell ∧ 2 ^ lay.logEllZk = gs.mask.ell := by
  obtain ⟨e1, e2⟩ := layout_exps hG hL
  rw [e1, e2, hc, h0, h1]
  exact ⟨(front_lengths.1 gs hgs).1, (front_lengths.1 gs hgs).2.1⟩

/-- **At the small size.** -/
theorem lengths_small (hc : T.codes = codesSmall2) (h0 : G.code = 0) (h1 : G.maskCode = 0)
    (hG : T.groups[g]? = some G) (hL : (begun T g G).layout g = some lay) {gs : GroupSize}
    (hgs : gs ∈ frontSmall) : 2 ^ lay.logEll = gs.main.ell ∧ 2 ^ lay.logEllZk = gs.mask.ell := by
  obtain ⟨e1, e2⟩ := layout_exps hG hL
  rw [e1, e2, hc, h0, h1]
  exact ⟨(front_lengths.2 gs hgs).1, (front_lengths.2 gs hgs).2.1⟩

/-- The statement's mask code number 0 has the length of every group in front. -/
theorem mask_ell_full (hc : T.codes = codesFull2) {gs : GroupSize} (hgs : gs ∈ frontFull) :
    (T.codes.mask.getD 0 default).ell = gs.mask.ell := by
  rw [hc]
  exact (front_lengths.1 gs hgs).2.2

theorem mask_ell_small (hc : T.codes = codesSmall2) {gs : GroupSize} (hgs : gs ∈ frontSmall) :
    (T.codes.mask.getD 0 default).ell = gs.mask.ell := by
  rw [hc]
  exact (front_lengths.2 gs hgs).2.2

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.front_lengths
#print axioms VerifiableInference.Desc.First.Close.lengths_full
#print axioms VerifiableInference.Desc.First.Close.lengths_small
#print axioms VerifiableInference.Desc.First.Close.mask_ell_full
