-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefLkpPreZk.lean: the list "shift, lookup" of a reference segment: what zero knowledge
asks of it (`F.prog.Zk base`), beside its hypotheses (`F.prog.Hyp`), from conditions on places.
(not all hypotheses are named here: see `Spec.ldSegRef_preZk_zk`)

Definitions, statements (in `Cb.Spec`) and proofs. By packing only.

Cb/Req1/LdSegRefLkpPre.lean leaves two hypotheses: the lookup's link has the masked bundle; the
lookup reads the entries in Rd only. For E of characteristic p and `E₀.Str` nonempty, under
`F.ZkOK p Dt Rd C` (below), both follow from the item "masked messages" of the assembled lookup's
chain (Cb/Ld/LdLkpMaskAsm2.lean: `ldLkpMaskAsm2_link`), by the steps by which
Cb/Ld/LdLkpMaskLift2.lean carries it to the other read-outs: a read-out sends nothing.

Main names:
  `A.mjFp ι Dc`, `A.dmFp ι S Dc Cc rd`: the letters of the item after the read-out with a family of
    rows (`A.rdF ι`, Cb/Ld/LdLkpAsm2Fmt.lean); over a signature. `A.dmFp ..` and `F.dm Rd C` are
    `MaskData` (Ior/Masked.lean); `A.mjFp ..` is an `MJ` (Cb/Ld/LdLkpMaskChain.lean).
    `MaskData R Wi` is a structure: a type `Kc` with `kc : Wi → Kc`; a type `Xp` with
    `pub : Xi → Xp`; a finite, non-empty type `Mk` with `put : Mk → Kc → Kc`; a predicate `Cl` on
    `Xp` and `Kc`; `msg`, from `Kc`, `Xp` and the verifier's randomness ρ to plain parts; and `sim`,
    from `Xp` and ρ to distributions on plain parts.
  `mjLift_baseF`, `mjLift_liftF`: the link, and the item over a signature, for `A.baseF ι` (each
    from `h : Dc.Link (A.chainA ..).H rd rd Sr Sw Cc`).
  `baseF_sameOn`: under the hypotheses of its statement, `A.baseF ι` reads the entries in
    `A.srAll Dt` only (what the data read, and the lookup's own masks).
  `F.ZkOK p Dt Rd C`: the conditions, named: `F.OK p`; the places (`F.A.MaskOK Dt`); all that is
    read lies in Rd; C, the claim with which the item is started: it gives the lookup's exact claim,
    does not read the lookup's own masks, reads what the lookup reads only, and follows from the
    exact claim at the entries in Rd.
  The three statements: for E of characteristic p and `E₀.Str` nonempty, under `F.ZkOK p Dt Rd C`:
  `Spec.ldSegRef_preZk_goodM`: the lookup's link has the masked bundle, with the letters
    `F.dm Rd C`.
  `Spec.ldSegRef_preZk_zk`: `F.prog.Zk base`, if the fact of these letters is fresh at the start.
  `Spec.ldSegRef_preZk_carry`: a fact that is fresh at the start and changes no entry in
    `F.A.srAll Dt` (in this sense: the text of `ldQuiet`, Cb/Req1/LdSegFrontTabZk.lean) is fresh
    after the list.

Limits: this file does not say that `F.ZkOK` can be met.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefLkpPreProofs
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdLkpMaskLift2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E) {N : Type} (ι : N → A.J)

/-- the letters after the read-out with a family of rows -/
def mjFp {Ex : ExtSpec} {M Wp Kc : Type} {msg : M → A.J → E}
    (Dc : MJ E A.J (A.chainA Ex M Wp Kc msg).R) :
    MJ E A.J (A.baseF ι Ex M Wp Kc msg).R :=
  Dc.post (fun o => some (A.rdF ι o)) (ExtMap.id Ex) (A.rdF ι)

/-- The letters over a signature. -/
def dmFp (S : Sig E) {E₀ : ExtSpec} {Kc Wp : Type} {msg : S.Msg → A.J → E}
    (Dc : MJ E A.J (A.chainA E₀ S.Msg Wp Kc msg).R)
    (Cc : A.St → (A.J → E) → Prop) (rd : S.Msg × Wp → A.J → E) :
    MaskData ((A.baseF ι E₀ S.Msg Wp Kc msg).R.keep S.Smp S.ext) (S.Wit × Wp) :=
  ((((A.mjFp ι Dc).narrow Cc).data rd).keep S.Smp S.ext).mapW fun w => (S.msgs w.1, w.2)

end LkAsm2
end
end Cb.LdLkp

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem mjLift_baseF (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type)
    (msg : M → A.J → E) (Dc : MJ E A.J (A.chainA Ex M Wp Kc msg).R) (rd : M × Wp → A.J → E)
    (Sr Sw : A.J → Prop) (Cc : A.St → (A.J → E) → Prop)
    (h : Dc.Link (A.chainA Ex M Wp Kc msg).H rd rd Sr Sw Cc) :
    (A.mjFp ι Dc).Link (A.baseF ι Ex M Wp Kc msg).H rd rd Sr Sw Cc :=
  mjl_post h (fun o => some (A.rdF ι o)) (ExtMap.id Ex) (A.rdF ι) (fun o => (A.rdF ι o.1, o.2)) rd
    (fun _ => rfl) fun _ => rfl

theorem mjLift_liftF (A : LkAsm2 E) (N : Type) (ι : N → A.J) (S : Sig E) (E₀ : ExtSpec)
    (Kc Wp : Type) (msg : S.Msg → A.J → E) (Dc : MJ E A.J (A.chainA E₀ S.Msg Wp Kc msg).R)
    (rd : S.Msg × Wp → A.J → E) (Sr Sw : A.J → Prop) (Cc : A.St → (A.J → E) → Prop)
    (h : Dc.Link (A.chainA E₀ S.Msg Wp Kc msg).H rd rd Sr Sw Cc) :
    (S.liftH (A.baseF ι E₀ S.Msg Wp Kc msg).H).MM (A.dmFp ι S Dc Cc rd) := by
  have h1 := mm_keep _ _ _ _ _ _ _ _ _ S.Smp S.ext
    (mjl_mm (mjLift_baseF E A N ι E₀ S.Msg Wp Kc msg Dc rd Sr Sw Cc h))
  exact mm_mapW _ _ _ _ _ _ (S.Wit × Wp) _ (S.Wit × Wp) _ _
    (fun w : S.Wit × Wp => (S.msgs w.1, w.2))
    (fun (w : S.Wit × Wp) (o : S.Msg × Wp) => (w.1, o.2)) h1

/-- Under the hypotheses below, the lookup reads what its data read, and its own masks. -/
theorem baseF_sameOn (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) (ι : N → A.J)
    (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type)
    (msg : M → A.J → E) (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop) (hA : A.H.lkb.Adm p)
    (hMu : A.H.MuOn Mu) (hOK : A.MaskOK Dt) (hRd : ∀ j, A.srAll Dt j → Rd j)
    (hC : ∀ st k, C st k → A.lk.inP Mu st k) (hs : MjStab C A.swAll)
    (hcl : ∀ k k' st, (∀ j, A.srAll Dt j → k j = k' j) → C st k → C st k') :
    (A.baseF ι Ex M Wp Kc msg).SameOn msg (A.srAll Dt) :=
  sameOn_of_piece (ldLkpAsm2F_noOrcs E A N ι Ex M Wp Kc msg)
    (mjp_full (b := A.baseF ι Ex M Wp Kc msg)
      (mjLift_baseF E A N ι Ex M Wp Kc msg _ _ _ _ _
        (ldLkpMaskAsm2_link E p A Mu Ex M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs))
      (ldLkpAsm2F_plain E A N ι Ex M Wp Kc msg) hRd hcl)

end

namespace LdPreD
variable {E Kc : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
  {Wp : Type} (F : LdPreD E Kc S E₀ Wp)

/-- The letters of the lookup's link. -/
def dm (Rd : F.A0.J → Prop) (C : F.St × E → (F.A0.J → E) → Prop) :
    MaskData (F.s2.linkA F.jT F.lkBk).R F.s2.J.W :=
  F.A.dmFp F.ι S (F.A.mjChain E₀ S.Msg Wp Kc F.msg Rd) C fun w => mjCut Rd (F.msg w.1)

/-- The conditions. -/
structure ZkOK (p : ℕ) (Dt Rd : F.A0.J → Prop) (C : F.St × E → (F.A0.J → E) → Prop) : Prop where
  ok     : F.OK p
  places : F.A.MaskOK Dt
  inRd   : ∀ j, F.A.srAll Dt j → Rd j
  gives  : ∀ st k, C st k → F.A.lk.inP F.Mu st k
  stable : MjStab C F.A.swAll
  reads  : ∀ k k' st, (∀ j, F.A.srAll Dt j → k j = k' j) → C st k → C st k'
  from'  : ∀ st (m : F.A0.J → E), F.A.lk.inP F.Mu st m → C st (mjCut Rd m)

end LdPreD

namespace Spec
variable (E : Type) [Field E] [Fintype E]

def ldSegRef_preZk_goodM : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str] (Wp : Type)
      (F : LdPreD E Kc S E₀ Wp) (Dt Rd : F.A0.J → Prop) (C : F.St × E → (F.A0.J → E) → Prop),
    F.ZkOK p Dt Rd C → (F.s2.linkA F.jT F.lkBk).GoodM (F.dm Rd C)

def ldSegRef_preZk_zk : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str]
      (Wp : Type) (F : LdPreD E Kc S E₀ Wp) (Dt Rd : F.A0.J → Prop)
      (C : F.St × E → (F.A0.J → E) → Prop) (base : MaskFact F.s0.J.W → Prop),
    F.ZkOK p Dt Rd C → base (F.dm Rd C).fact → F.prog.Zk base

def ldSegRef_preZk_carry : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str] (Wp : Type)
      (F : LdPreD E Kc S E₀ Wp) (Dt Rd : F.A0.J → Prop) (C : F.St × E → (F.A0.J → E) → Prop)
      (base : MaskFact F.s0.J.W → Prop) (f : MaskFact F.s0.J.W),
    F.ZkOK p Dt Rd C →
    (∀ w w' m, f.kc w' = f.put m (f.kc w) →
      ∀ j, F.A.srAll Dt j → F.msg (S.msgs w'.1) j = F.msg (S.msgs w.1) j) →
    base f → F.prog.After base f

end Spec

section
variable (E : Type) [Field E] [Fintype E]

theorem ldSegRef_preZk_goodM : Spec.ldSegRef_preZk_goodM E := by
  intro p _ Kc S E₀ _ Wp F Dt Rd C h
  exact
    { base := linkA_goodB F.s2 F.jT F.lkBk
        (ldLkpAsm2F_base E p F.A F.N F.ι F.Mu E₀ Kc S.Msg Wp F.R1 F.msg h.ok.inj
          h.ok.places h.ok.adm h.ok.muOK)
      mm := mjLift_liftF E F.A F.N F.ι S E₀ Kc Wp F.msg _ _ _ _ C
        (ldLkpMaskAsm2_link E p F.A F.Mu E₀ S.Msg Wp Kc F.msg Dt Rd C h.ok.adm h.ok.muOK h.places
          h.inRd h.gives h.stable)
      claim := fun x _ w hx => h.from' x.1 (F.msg (S.msgs w.1)) hx.2.2.2 }

theorem ldSegRef_preZk_zk : Spec.ldSegRef_preZk_zk E := fun p _ Kc S E₀ _ Wp F Dt Rd C base h hb =>
  ldSegRef_pre_zk E p Kc S E₀ Wp F base (F.dm Rd C) h.ok
    (ldSegRef_preZk_goodM E p Kc S E₀ Wp F Dt Rd C h) hb

theorem ldSegRef_preZk_carry :
    Spec.ldSegRef_preZk_carry E := fun p _ Kc S E₀ _ Wp F Dt Rd C base f h hk hb =>
  ldSegRef_pre_carry E Kc S E₀ Wp F (F.A.srAll Dt)
    (baseF_sameOn E p F.A F.N F.ι F.Mu E₀ S.Msg Wp Kc F.msg Dt Rd C h.ok.adm h.ok.muOK h.places
      h.inRd h.gives h.stable h.reads)
    base f hk hb

end
end Cb
