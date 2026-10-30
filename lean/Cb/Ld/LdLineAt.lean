-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLineAt.lean: a form of completeness and round-by-round knowledge soundness (at the base: the
bundle `GoodAt` of Cb/Ld/LdSigLift.lean) of a sumcheck, of a step into a sumcheck followed by it, of
the reduction of two claims to one ("the line"), and of a zerocheck, each stated, under the
hypotheses below, for a fixed tuple of messages, before any code or oracle message comes in.

Statements (in `Cb.Spec`) and proofs (assemblies of what is proved elsewhere).
`GoodAt R H A B ext P` says that the reduction R, with the honest side H, leads from the base joint
A to B for each fixed tuple of messages: among its clauses, pointwise completeness from `A.rel` to
`B.rel` (`Honest.Acc`, Ior/Honest.lean), the honest prover ends with the messages with which it
began, and for every tuple m the reduction is round-by-round knowledge sound on the statements with
`A.on`, with the extractor ext m and the errors `P.err`, between the relaxed relations (`A.relR`,
`B.relR`) read at m.

Main names:
  `Spec.psc_our_goodAt`: the sumcheck with the dummy variable (`PscOur`), from the true sum claim in
    k variables to its output rows (`PscPar.OutHolds`, Cb/Ld/LdPsc.lean), if `T.VarsOK`, `T.DegX`,
    `T.DegY`, `T.ValInj`.
  `PscIn.chainAt`, `PscIn.chainAtH`, `PscIn.chainAtN`; `Spec.pscIn_psc_goodAt`: the step of
    Cb/Ld/LdZero.lean, then the sumcheck: from (all claims, and R0) to (the output rows, and R0);
    its errors, round by round: the step's one, then the sumcheck's: 1, the degrees, DY, 0; the
    extractor is the identity. Asked: `Z.Link`, `Z.Back`, `Z.ev.OK`, and the four conditions above
    of `Z.T`.
  `Spec.ldZero_psc_goodAt`: the zerocheck on the cube, then the sumcheck, if `Z.co.OK`,
    `Z.next.DegX`, `Z.next.DegY`. `Spec.ldZeroS_goodAt`, `Spec.ldZeroS_psc_goodAt`: the zerocheck
    with the first variable over a domain, if `Function.Injective Z.dom`, `Z.co.OK`; then the
    sumcheck, if also `Nonempty Z.D`, `Z.next.DegX`, `Z.next.DegY`.
  `Spec.ldLine_goodAt`, `Spec.ldLineC_goodAt`: the line (Cb/Ld/LdLine.lean): under `L.Virt`,
    `L.Form`, `L.toIn.Back`; on the two halves of a table under `C.Halves`.
These are the forms that the lifting rules take (over a signature: `Spec.sigLift_goodB`,
Cb/Ld/LdSigLift.lean; with an encoded index).

Limits: this file says nothing on zero knowledge of the sumcheck (masked messages:
Cb/Ld/LdPscZk.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZeroAt
import Cb.Ld.LdZeroSkipProofs
import Cb.Ld.LdLineProofs
import Cb.Ld.LdBattKit
import Cb.Ld.LdPscSig

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

namespace PscIn
variable {E : Type} [Field E] [Fintype E] (Z : PscIn E) (Ex : ExtSpec)

/-- The step, then the sumcheck, at the base. -/
def chainAt : IOR Z.St0 Ex Z.T.par.Out Ex := (IOR.draw Z.ev.D Z.nxX Ex).seq (Z.T.par.psc Ex)
def chainAtH (M Wp : Type) (msg : M → Z.T.J → E) : (Z.chainAt Ex).Honest (M × Wp) (M × Wp) :=
  (IOR.Honest.draw Z.ev.D Z.nxX Ex (M × Wp)).seq (Z.T.par.hon Ex fun w : M × Wp => msg w.1)
def chainAtN (Kc : Type) : IOR.Nums Kc (Z.chainAt Ex) :=
  (IOR.Nums.draw Kc Z.ev.D Z.nxX Ex Z.ev.err).seq (Z.T.par.nums Ex Kc)

end PscIn

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

def psc_our_goodAt : Prop :=
  ∀ (T : PscOur E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E),
    T.VarsOK → T.DegX → T.DegY → T.ValInj →
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1) (T.baseIn A0 fun w => msg w.1)
      (T.par.baseOut A0 fun w => msg w.1) (fun _ _ _ wp => wp) (T.par.nums Ex Kc)

def pscIn_psc_goodAt : Prop :=
  ∀ (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St0 Ex (M × Wp)) (msg : M → Z.T.J → E),
    Z.Link → Z.Back → Z.ev.OK → Z.T.VarsOK → Z.T.DegX → Z.T.DegY → Z.T.ValInj →
    GoodAt (Z.chainAt Ex) (Z.chainAtH Ex M Wp msg) (Z.relsIn R0 msg)
      (Z.T.par.baseOut (Z.ride R0) fun w => msg w.1) (fun _ _ _ wp => wp) (Z.chainAtN Ex Kc)

def ldZero_psc_goodAt : Prop :=
  ∀ (Z : ZeroCube E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St Ex (M × Wp)) (msg : M → Z.J → E),
    Z.co.OK → Z.next.DegX → Z.next.DegY →
    GoodAt (Z.toIn.chainAt Ex) (Z.toIn.chainAtH Ex M Wp msg)
      ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩
      (Z.next.par.baseOut (Z.toIn.ride R0) fun w => msg w.1)
      (fun _ _ _ wp => wp) (Z.toIn.chainAtN Ex Kc)

def ldZeroS_goodAt : Prop :=
  ∀ (Z : ZeroSkip E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St Ex (M × Wp)) (msg : M → Z.J → E),
    Function.Injective Z.dom → Z.co.OK →
    GoodAt (IOR.draw Z.toIn.ev.D Z.toIn.nxX Ex) (Honest.draw Z.toIn.ev.D Z.toIn.nxX Ex (M × Wp))
      ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩
      (Z.toIn.relsOut R0 msg) (fun _ _ _ wp => wp)
      (Nums.draw Kc Z.toIn.ev.D Z.toIn.nxX Ex Z.toIn.ev.err)

def ldZeroS_psc_goodAt : Prop :=
  ∀ (Z : ZeroSkip E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc Z.St Ex (M × Wp)) (msg : M → Z.J → E),
    Function.Injective Z.dom → Nonempty Z.D → Z.co.OK → Z.next.DegX → Z.next.DegY →
    GoodAt (Z.toIn.chainAt Ex) (Z.toIn.chainAtH Ex M Wp msg)
      ⟨fun st y w => R0.rel st y w ∧ Z.ZeroHolds st (msg w.1),
        fun a w => R0.relR a w ∧ Z.ZeroHolds a.1 (msg w.1),
        R0.on, R0.core⟩
      (Z.next.par.baseOut (Z.toIn.ride R0) fun w => msg w.1)
      (fun _ _ _ wp => wp) (Z.toIn.chainAtN Ex Kc)

def ldLine_goodAt : Prop :=
  ∀ (L : LinePar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc L.P.par.Out Ex (M × Wp)) (msg : M → L.N.J → E),
    L.Virt → L.Form → L.toIn.Back →
    GoodAt (IOR.draw L.toIn.ev.D L.toIn.nxX Ex) (Honest.draw L.toIn.ev.D L.toIn.nxX Ex (M × Wp))
      ⟨fun o y w => R0.rel o y w ∧ ∀ b, L.P.par.EHolds o (L.em (msg w.1)) (L.a b),
        fun a w => R0.relR a w ∧ ∀ b, L.P.par.EHolds a.1 (L.em (msg w.1)) (L.a b),
        R0.on, R0.core⟩
      (L.toIn.relsOut R0 msg) (fun _ _ _ wp => wp) (Nums.draw Kc L.toIn.ev.D L.toIn.nxX Ex 1)

def ldLineC_goodAt : Prop :=
  ∀ (C : LineCube E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc C.P.par.Out Ex (M × Wp)) (msg : M → C.J → E),
    C.Halves →
    GoodAt (IOR.draw C.toLine.toIn.ev.D C.toLine.toIn.nxX Ex)
      (Honest.draw C.toLine.toIn.ev.D C.toLine.toIn.nxX Ex (M × Wp))
      ⟨fun o y w => R0.rel o y w ∧ ∀ b, C.P.par.EHolds o (C.toLine.em (msg w.1)) (C.a b),
        fun a w => R0.relR a w ∧ ∀ b, C.P.par.EHolds a.1 (C.toLine.em (msg w.1)) (C.a b),
        R0.on, R0.core⟩
      (C.toLine.toIn.relsOut R0 msg) (fun _ _ _ wp => wp)
      (Nums.draw Kc C.toLine.toIn.ev.D C.toLine.toIn.nxX Ex 1)

end Spec

section Proofs
open IOR
variable (E : Type) [Field E] [Fintype E]

theorem psc_our_goodAt : Spec.psc_our_goodAt E := fun T Ex M Wp Kc A0 msg hV hX hY hI => by
  have e : T.SumHolds = T.par.SumHolds :=
    funext fun x => funext fun m => propext (psc_our_sum E T x m).symm
  unfold PscOur.baseIn
  rw [e]
  exact psc_goodAt E T.par Ex M Wp Kc A0 msg ((psc_our_ok E T).1 hV)
    (psc_our_deg E T hX hY) ((psc_our_ok E T).2 hI)

theorem pscIn_psc_goodAt :
    Spec.pscIn_psc_goodAt E := fun Z Ex M Wp Kc R0 msg hL hB hOK hV hX hY hI =>
  goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp (IOR.draw Z.ev.D Z.nxX Ex) (Z.T.par.psc Ex) _ _ _
    (Z.relsOut R0 msg) _ (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _ _
    (pscIn_goodAt E Z Ex M Wp Kc R0 msg hL hB hOK)
    (psc_our_goodAt E Z.T Ex M Wp Kc (Z.ride R0) msg hV hX hY hI) fun _ _ _ _ _ _ _ => rfl

theorem ldZero_psc_goodAt : Spec.ldZero_psc_goodAt E := by
  intro Z Ex M Wp Kc R0 msg hco hX hY
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZero_all E Z st m)
  have h := pscIn_psc_goodAt E Z.toIn Ex M Wp Kc R0 msg (ldZero_link E Z) (ldZero_back E Z)
    (ldZero_ok E Z hco) (ldZero_vars E Z).1 hX hY (ldZero_vars E Z).2
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

theorem ldZeroS_goodAt : Spec.ldZeroS_goodAt E := by
  intro Z Ex M Wp Kc R0 msg hd hco
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZeroS_all E Z st m)
  have h := pscIn_goodAt E Z.toIn Ex M Wp Kc R0 msg (ldZeroS_link E Z)
    (ldZeroS_back E Z) (ldZeroS_ok E Z hd hco)
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

theorem ldZeroS_psc_goodAt : Spec.ldZeroS_psc_goodAt E := by
  intro Z Ex M Wp Kc R0 msg hd hne hco hX hY
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZeroS_all E Z st m)
  have h := pscIn_psc_goodAt E Z.toIn Ex M Wp Kc R0 msg (ldZeroS_link E Z) (ldZeroS_back E Z)
    (ldZeroS_ok E Z hd hco) (ldZeroS_vars E Z hd hne).1 hX hY (ldZeroS_vars E Z hd hne).2
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

theorem ldLine_goodAt : Spec.ldLine_goodAt E := fun L Ex M Wp Kc R0 msg hV hF hB =>
  pscIn_goodAt E L.toIn Ex M Wp Kc R0 msg (ldLine_link E L hV hF) hB (ldLine_ok E L)

theorem ldLineC_goodAt : Spec.ldLineC_goodAt E := fun C Ex M Wp Kc R0 msg hH =>
  ldLine_goodAt E C.toLine Ex M Wp Kc R0 msg (ldLineC_virt E C hH)
    (ldLineC_form E C) (ldLineC_back E C)

end Proofs
end
end Cb
