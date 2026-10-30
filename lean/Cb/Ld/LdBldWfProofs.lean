-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfProofs.lean: the proofs of Cb/Ld/LdBldWfSpec.lean's statements `bldWf_hpl`,
`bldWf_std`, `bldWf_rest2`: an assembly of Cb/Ld/LdBldWfDef.lean (what holds by the definitions and
by numbers) and Cb/Ld/LdBldWfPlace.lean (places; there too: `bldWf_where`). What is said and what is
not: the head of Cb/Ld/LdBldWfSpec.lean.

Main names (statements and hypotheses: Cb/Ld/LdBldWfSpec.lean):
  `bldWf_hpl`: `X.Room p` ⇒ the masks of all blocks at different free entries (`X.Hpl`).
  `bldWf_std`: `X.Room p` ⇒ for every hpl, the six clauses on the standard sender's data.
  `bldWf_rest2`: `X.Room p` ⇒ for every hpl, all eighteen fields of `(X.Zw hpl).Rest2 p`.
-/
import Cb.Ld.LdBldWfDef
import Cb.Ld.LdBldWfPlace

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

theorem bldWf_hpl : Spec.bldWf_hpl F E Fp := fun X _ h => bldWfP_hpl X h.injM

theorem bldWf_std : Spec.bldWf_std F E Fp := fun X _ _ hpl =>
  ⟨bldWfD_wfStd X hpl, bldWfD_wfBody X hpl, bldWfD_wfBd X hpl, fun l i => bldWfP_wfAtL X l i,
    bldWfD_wfAtB X hpl, bldWfD_wfNoPad X hpl⟩

/-- All eighteen fields of `Rest2`. -/
theorem bldWf_rest2 : Spec.bldWf_rest2 F E Fp := fun X p h hpl =>
  { val := bldWfD_val X
    describes := h.describes
    lin := bldWfD_lin X
    lks :=
      { v := bldWfD_v X h, adm := bldWfD_adm X h, mult := bldWfD_mult X h, rows := bldWfD_rows X
        supC := fun f _ b => bldWfP_supC X f b
        supR := fun f hf b => bldWfP_supR X p h f hf b }
    deg := bldWfD_deg X
    zOK := bldWfD_zOK X h
    fair := bldWfD_fair X h
    multOf := bldWfD_multOf X h
    tie := bldWfD_tie X
    lkPl := fun f hf => bldWfP_lkPl X f hf
    rdL := fun _ _ _ hS => hS
    own := bldWfP_own X
    ent := bldWfP_ent X h.injB h.injM
    inRd := fun _ _ => bldWfP_noPad X _
    rdJ := fun _ n _ => bldWfP_noPad X n
    atEq := fun l i => bldWfP_atEq X l i
    ownL := fun l i => bldWfP_ownL X l i
    apart := fun b j hj n hS => ⟨bldWfP_noPad X n, by
      cases b with
      | some l => exact fun i => bldWfP_apartL X j l hj n hS i
      | none => exact fun i => bldWfP_apartB X j (Nat.lt_succ_iff.1 hj) n hS i⟩ }

end
end Cb
