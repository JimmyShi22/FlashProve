-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskAsmPiece.lean: from a link to a piece, and to the reading of all entries.
`MJ.Link` (Cb/Ld/LdLkpMaskSp.lean) and `MJ.Piece` (Cb/Ld/LdLkpMaskKit.lean) are two bundles of
properties of one reduction with its `MJ` record; this file passes from the first to the second.

Statements and proofs. Glue for the callers of Cb/Ld/LdLkpMaskAsm.lean.

Main names, each under the hypotheses of its statement:
  `mjp_of_link`: a link started with a claim C that reads Sr only is a `Piece`
    (Cb/Ld/LdLkpMaskKit.lean) of the letters `D.narrow C`.
  `mjl_full`: the reading "the entries in Rd, the others forgotten" may be replaced by the reading
    of all entries, for a block at the base in the format `b.Plain` (Cb/Ld/LdLkpFormat.lean) that
    ends with the witness with which it began (Sr inside Rd).
  `mjp_full`: both: the form that the rules for blindness take (Cb/Ld/LdLkpFormatPiece.lean,
    Cb/Ld/LdLkpFormatBlindIdx.lean).
  `ldLkpMaskAsm_piece`: for `A.chainA`: a `Piece` with Sr = `A.srAll Dt`, Sw = `A.swAll`, reading
    all entries.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskAsmProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable {E J : Type}

theorem mjp_of_link {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {D : MJ E J R} {H : R.Honest Wi Wo} {rdi : Wi → J → E} {rdo : Wo → J → E} {Sr Sw : J → Prop}
    {C : Xi → (J → E) → Prop} (h : D.Link H rdi rdo Sr Sw C)
    (hcl : ∀ k k' x, (∀ j, Sr j → k j = k' j) → C x k → C x k') :
    (D.narrow C).Piece H rdi rdo Sr Sw :=
  ⟨h.fits, ⟨h.reads, hcl⟩, h.writes⟩

theorem mjl_full [Zero E] {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp : Type} {b : BkA K M X₁ X₂ Ex Wp}
    {D : MJ E J b.R} {msg : M → J → E} {Rd Sr Sw : J → Prop} {C : X₁ → (J → E) → Prop}
    (h : D.Link b.H (fun w => mjCut Rd (msg w.1)) (fun w => mjCut Rd (msg w.1)) Sr Sw C)
    (hp : b.Plain) (hRd : ∀ j, Sr j → Rd j) :
    D.Link b.H (fun w => msg w.1) (fun w => msg w.1) Sr Sw C :=
  mjl_forget h hp.keepsW fun w _ hj => (mjCut_of (msg w.1) (hRd _ hj)).symm

theorem mjp_full [Zero E] {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp : Type} {b : BkA K M X₁ X₂ Ex Wp}
    {D : MJ E J b.R} {msg : M → J → E} {Rd Sr Sw : J → Prop} {C : X₁ → (J → E) → Prop}
    (h : D.Link b.H (fun w => mjCut Rd (msg w.1)) (fun w => mjCut Rd (msg w.1)) Sr Sw C)
    (hp : b.Plain) (hRd : ∀ j, Sr j → Rd j)
    (hcl : ∀ k k' x, (∀ j, Sr j → k j = k' j) → C x k → C x k') :
    (D.narrow C).Piece b.H (fun w => msg w.1) (fun w => msg w.1) Sr Sw :=
  mjp_of_link (mjl_full h hp hRd) hcl

end

theorem ldLkpMaskAsm_piece (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (A : LkAsm E)
    (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type)
    (msg : M → A.J → E) (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop) (hA : A.H.lkb.Adm p)
    (hMu : A.H.MuOK Mu) (hOK : A.MaskOK Dt) (hRd : ∀ j, A.srAll Dt j → Rd j)
    (hC : ∀ st k, C st k → A.lk.inP Mu st k) (hs : MjStab C A.swAll)
    (hcl : ∀ k k' st, (∀ j, A.srAll Dt j → k j = k' j) → C st k → C st k') :
    ((A.mjChain Ex M Wp Kc msg Rd).narrow C).Piece
      (A.chainA Ex M Wp Kc msg).H (fun w => msg w.1) (fun w => msg w.1) (A.srAll Dt) A.swAll :=
  mjp_full (b := A.chainA Ex M Wp Kc msg)
    (ldLkpMaskAsm_link E p A Mu Ex M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs)
    (plain_seq
      (plain_seq (plain_head Ex M Wp Kc A.H msg) (plain_segK Ex M Wp Kc A.IK A.v' A.tK msg))
      (plain_segT Ex M Wp Kc A.Q msg))
    hRd hcl

end Cb
