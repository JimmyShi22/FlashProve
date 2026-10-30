-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K4/BatchKControls.lean.
THE CONTROLS.
THEY NAME T.OK AND ldOnT_ok's TWELVE PREMISES ON PURPOSE.
(c1) THE FORM: the library's record gives the thin one: five projections. (c2) NOT HOLLOW, NO LESS:
under ldOnT_ok's OWN twelve premises, at ITS OWN shape, the seven follow (the seventh by
each_pl_of_okFrom) and the thin conclusion is had THROUGH ldOnT_okK.
(c3) ONE ROAD: ldOBT_object's second conjunct from LinBK's fields fits | know: they are what the
call of ldOB_know takes.

-/
import Cb.Thin.K4.BatchK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- (c1) -/
theorem linBK_of_ok {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {O : LdOL F E}
    {N : ℕ} (T : O.LinBT N) (h : T.OK) : T.LinBK :=
  ⟨h.point, h.isLocal, h.coherent, h.fits, h.know⟩

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- (c2) -/
theorem ldOnT_okK_ofOld (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
    (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
    (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
    (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (kT : JKey LdLinP.JT) (d : O.toC.P.W0)
    (d₀ : O.P.W0) (_ya : O.toC.P.Ea.Str)
    (hFit : O.Fits on0) (hF : O.toC.P.FoldErr on0 εf) (hpy : Function.Injective O.py) (hS : Sn.OK)
    (_hA : Sn.Apart) (_hmono : ∀ U V, V ⊆ U → qa U → qa V)
    (hOk : cZ.forget.forget.OkFrom (O.toC.P.chain on0 Sn εf))
    (_hSd : cZ.forget.forget.SidesCT (O.toC.P.q5 Sn qa)) (hKB : cZ.forget.KB N O.toC.P.key6 kT)
    (_hOkV : cZ.OkFromV (O.toC.P.chainV Sn qa N on0 εf)) (hCoh : cZ.forget.Coh)
    (_hq : ∀ Jn, VT.q Jn fun _ => ∅) : (O.termT on0 Sn qa εf N cZ d d₀).LinBK :=
  ldOnT_okK F E O on0 Sn qa εf N VT cZ kT d d₀ hFit hF hpy hS hKB hCoh
    (each_pl_of_okFrom _ _ hOk)

end

/-- (c3) -/
example (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E) (N : ℕ)
    (T : O.LinBT N) (d0 : O.left.AMsg) (hd : HasDist O.Cf.C₀.G O.Cf.C₀.d)
    (he : O.Cf.eM < O.Cf.C₀.d) (h : T.OK) : LinBKnowR O.left T.Q N d0 T.P.err :=
  ldOB_know F E O T.on0 T.Q N T.ext T.P.err d0 hd he (linBK_of_ok T h).fits (linBK_of_ok T h).know

end Cb

