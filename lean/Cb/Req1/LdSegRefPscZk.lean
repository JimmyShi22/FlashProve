-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPscZk.lean: the sumcheck as a move of a segment: its masked bundle, and what it
reads.

Statements and proofs. By packing only: Cb/Ld/LdPscGood.lean (under the hypotheses of its statement,
`Spec.psc_our_goodM_sig`, the sumcheck over a signature is a masked block) and
Cb/Ld/LdLkpMaskKit.lean (the sumcheck as a piece), in the letters of Cb/Req1/LdSegRefPsc.lean.

Main names:
  `pscStage S T E₀ Wp A0 msg`: the stage before the sumcheck: the true sum claim in the
    `T.fmt.length` variables of T, beside A0.
  `pscBk_goodM`: the link of the sumcheck has the masked bundle (`IOR.GoodM`), with the letters
    `T.par.maskSig S E₀ Wp msg (T.own Rd)`; from the conditions on T (`T.VarsOK`, `T.DegX`,
    `T.DegY`, `T.ValInj`) and `T.OwnOur Rd` (own places pairwise different and in Rd; maps and
    incoming form read Rd only and no own place).
  `pscBk_ok`: under the hypotheses of its statement, so the move's zero-knowledge clause holds if
    that fact is fresh at the start.
  `sameOnW_of_piece`: if `noOrcs b.R.shape`, a piece with any reading gives "the honest run reads
    the entries in Sr only", for that reading.
  **pscBk_sameOn** the sumcheck reads the entries in Rd only: from T.VarsOK, T.DegX, T.DegY and
    T.OwnOur Rd (the first three are used only because the closed form of the honest messages is
    taken from the masked item); pscBk_carry: so, under the same conditions, it carries every later
    fact that changes no entry in Rd (hk) and is fresh at the start (`hb : base f`)

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefPsc
import Cb.Ld.LdLkpAsm2Fmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

section
variable {E : Type} [Field E] [Fintype E]

/-- The stage before the sumcheck. -/
@[reducible] def pscStage {Kc : Type} (S : Sig E) (T : PscOur E) (E₀ : ExtSpec)
    (Wp : Type) (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) : LdStage E Kc :=
  ⟨S, E × T.St, E₀, Wp, T.baseIn A0 fun w => msg w.1⟩

theorem pscBk_goodM {Kc : Type} (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop) (hV : T.VarsOK)
    (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj) (hO : T.OwnOur Rd) :
    ((pscStage S T E₀ Wp A0 msg).linkA
        (T.par.baseOut A0 fun w => msg w.1) (pscBk T E₀ S.Msg Wp Kc msg)).GoodM
      (T.par.maskSig S E₀ Wp msg (T.own Rd)) := by
  have g := psc_our_goodM_sig E S T E₀ Wp Kc A0 msg Rd hV hX hY hI hO
  have e : T.par.SumHolds = T.SumHolds :=
    funext fun x => funext fun m => propext (psc_our_sum E T x m)
  have e' : T.par.baseIn A0 (fun w : S.Msg × Wp => msg w.1) = T.baseIn A0 fun w => msg w.1 := by
    unfold PscOur.baseIn PscPar.baseIn
    rw [e]
    rfl
  rw [e'] at g
  exact ldSeg_sub_goodM E Kc (pscStage S T E₀ Wp A0 msg)
    ((pscStage S T E₀ Wp A0 msg).after (T.par.baseOut A0 fun w => msg w.1)) _ _ g

theorem pscBk_ok {Kc : Type} (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop) (hV : T.VarsOK)
    (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj) (hO : T.OwnOur Rd)
    (base : MaskFact (pscStage S T E₀ Wp A0 msg).J.W → Prop)
    (hb : base (T.par.maskSig S E₀ Wp msg (T.own Rd)).fact) :
    ((pscStage S T E₀ Wp A0 msg).mvA
      (T.par.baseOut A0 fun w => msg w.1) (pscBk T E₀ S.Msg Wp Kc msg)).chain.OkGiven base :=
  mvA_okM _ _ _ base _ (pscBk_goodM S T E₀ Wp A0 msg Rd hV hX hY hI hO) hb

end

theorem sameOnW_of_piece {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp E J : Type}
    {b : BkA K M X₁ X₂ Ex Wp} (hn : noOrcs b.R.shape) {D : MJ E J b.R} {rd : M × Wp → J → E}
    {Sr Sw : J → Prop} (hP : D.Piece b.H rd rd Sr Sw) : b.SameOnW rd Sr := by
  intro u u' x c ρ hu
  have hm : D.msg (rd u') x ρ = D.msg (rd u) x ρ := hP.reads.msg _ _ x ρ hu
  refine ⟨tr_ext_noOrcs _ hn _ _ ?_ ?_, ?_⟩
  · rw [hP.fits.mm.run, hP.fits.mm.run]
    exact hm
  · rw [Strat.rho_run, Strat.rho_run]
  · rw [hP.fits.hand, hP.fits.hand, hm]

section
variable {E : Type} [Field E] [Fintype E]

theorem pscBk_sameOn (T : PscOur E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E)
    (Rd : T.J → Prop) (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hO : T.OwnOur Rd) :
    (pscBk T Ex M Wp Kc msg).SameOn msg Rd := by
  classical
  have hO' := psc_our_own E T Rd hO
  have hP := mjp_psc E T.par Ex (M × Wp) (fun w => msg w.1) (T.own Rd) (T.own Rd) ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY) hO' hO' (by
    show T.fmt ++ [pDummy E T.DY] ≠ []
    simp)
  intro u u' x c ρ hu
  refine sameOnW_of_piece (b := pscBk T Ex M Wp Kc msg) (noOrcs_psc T.par Ex)
    hP u u' x c ρ fun j hj => ?_
  show (if Rd j then msg u'.1 j else 0) = if Rd j then msg u.1 j else 0
  have hj' : Rd j := hj
  rw [if_pos hj', if_pos hj']
  exact hu j hj'

theorem pscBk_carry {Kc : Type} (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop) (hV : T.VarsOK)
    (hX : T.DegX) (hY : T.DegY) (hO : T.OwnOur Rd)
    (base : MaskFact (pscStage S T E₀ Wp A0 msg).J.W → Prop)
    (f : MaskFact (pscStage S T E₀ Wp A0 msg).J.W)
    (hk : ∀ w w' m,
      f.kc w' = f.put m (f.kc w) → ∀ j, Rd j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j)
    (hb : base f) :
    ((pscStage S T E₀ Wp A0 msg).mvA
        (T.par.baseOut A0 fun w => msg w.1) (pscBk T E₀ S.Msg Wp Kc msg)).chain.FreshGiven
      base f :=
  mvA_carry _ _ _ (pscBk_plain T E₀ S.Msg Wp Kc msg)
    (pscBk_sameOn T E₀ S.Msg Wp Kc msg Rd hV hX hY hO) base f hk hb

end
end Cb
