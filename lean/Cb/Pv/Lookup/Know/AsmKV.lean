-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Know/AsmKV.lean.
Knowledge soundness of the assembled lookup, for every short sumcheck.

TWhole.ShortK and TWhole.ShortKC (Cb/G6/Letter.lean) are records of a sumcheck's verifier whose
rounds send one coefficient less, with the laws of its rounds and of its errors and, as a field, a
proof of its knowledge soundness under the library's three conditions (VarsOK, DegOK, ValInj).

States: baseK V VC: the lookup's verifier over such records; asmK_shortOK: the library's three
conditions hold at each of the lookup's own sumchecks, so no premise on the records is left;
  asmK_know: knowledge soundness, the five arguments of `Iop.Reduction.Know` (Ior/Know.lean)
    written out, for every V, VC, every joint R0 that rides along and each fixed tuple of messages;
    asmK_know_sig, asmK_know_sigT: over a signature of sampled messages.
Premises: the field's characteristic p; the library's conditions on the sizes (Adm p); padsOK; n + 1
+ 1 = 2^w, where n + 2 planes count. None reads a witness or a transcript.
Limits: a statement for every V, VC says nothing on what a verifier accepts. Records that fill the
two types: TWhole.V₀, V₀C (Cb/G6/Pick.lean; Cb/Pv/Lookup/Know/AsmKV0.lean). No honest side of this
lookup is in this file.
Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Lookup.Know.AsmK
import Cb.G6.Letter

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset Kn TWhole

section
variable {E : Type} [Field E] [Fintype E]

/-- The letter of Cb/Pv/Lookup/Know/LtK.lean out of the two records. -/
def PscLtK.ofShort (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) : PscLtK E Ex :=
  ⟨fun Y => ⟨(V Y Ex).R, (V Y Ex).ε⟩, fun Y => ⟨(VC Y Ex).R, (VC Y Ex).ε⟩⟩

/-- The lookup's verifier and its errors, over the two records. -/
noncomputable def LkAsmH.baseK (A : LkAsmH E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) {Ex : ExtSpec} : BkK A.St (TX A.St E A.J) Ex :=
  A.baseKS (PscLtK.ofShort V VC Ex)

end
end Cb.LdLkp

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Finset

section
variable (E : Type) [Field E] [Fintype E]

theorem ofShort_our (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (M Wp Kc : Type) (T : PscOur E) (msg : M → T.J → E) (hV : T.VarsOK) (hX : T.DegX)
    (hY : T.DegY) (hI : T.ValInj) : (PscLtK.ofShort V VC Ex).FullK M Wp Kc T.par msg := fun A0 =>
  (V T.par Ex).know ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY) ((psc_our_ok E T).2 hI)
    M Wp Kc A0 msg

/-- No premise on the letter is left: the library's three conditions hold at the lookup's own
sumchecks. -/
theorem asmK_shortOK (A : LkAsmH E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    A.LtK (PscLtK.ofShort V VC Ex) Wp Kc msg :=
  { tie := fun l _ =>
      have ok := tieF_ok E A.H.tie l
      ofShort_our E V VC Ex M Wp Kc _ _ ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
    keys := fun l _ =>
      have ok := ldLkpP_ok E (A.IK.setV (A.v' + 1)).DK l
      ofShort_our E V VC Ex M Wp Kc _ _ ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
    tab := fun l _ =>
      have ok := ldLkpP_ok E A.D l
      ofShort_our E V VC Ex M Wp Kc _ _ ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
    clo := fun A0 => (VC A.En.par Ex).know (endM_vars E A.En).1
      (endM_deg E A.En (instM_ok E A.IT (A.n + 1) A.oE A.wE)) (endM_vars E A.En).2 M Wp Kc A0 msg
    bit := ofShort_our E V VC Ex M Wp Kc _ _ (ldZeroP_vars E A.Bt.zc).1 (ldLkpBitP_degX E A.Bt)
      (ldLkpBitP_degY E A.Bt) (ldZeroP_vars E A.Bt.zc).2 }

/-- Knowledge soundness of the lookup, for every V, VC and R0 and each fixed tuple of messages m,
with the five arguments of `Iop.Reduction.Know` written out: condition, input relation, output
relation, extractor, errors. -/
theorem asmK_know (p : ℕ) [CharP E p] (A : LkAsmH E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true) (hF : A.n + 1 + 1 = 2 ^ A.w)
    (m : M) :
    (A.baseK V VC).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ A.lk.inR a.1 (msg m))
      (fun b wp => R0.relR (b.1.1, b.2) (m, wp) ∧ A.lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) (A.baseK V VC).e :=
  asmI_know E p A Ex Kc M Wp (PscLtK.ofShort V VC Ex) R0 msg
    (asmK_shortOK E A V VC Ex M Wp Kc msg) hA hP hF m

/-- The same over a signature, by the library's sigLift_know. -/
theorem asmK_know_sig (p : ℕ) [CharP E p] (A : LkAsmH E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Sg : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
    (R0 : Rels Kc A.St E₀ (Sg.Msg × Wp)) (msg : Sg.Msg → A.J → E)
    (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true) (hF : A.n + 1 + 1 = 2 ^ A.w) :
    ((A.baseK V VC).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over (cj R0 msg id (A.lk.inP fun _ _ => True) A.lk.inR)).on
      (Sg.over (cj R0 msg id (A.lk.inP fun _ _ => True) A.lk.inR)).relR
      (Sg.over (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) (A.baseK V VC).e :=
  asmI_know_sig E p A Sg E₀ Kc Wp (PscLtK.ofShort V VC E₀) R0 msg
    (asmK_shortOK E A V VC E₀ Sg.Msg Wp Kc msg) hA hP hF

theorem asmK_know_sigT (p : ℕ) [CharP E p] (A : LkAsmH E) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Sg : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
    (R0 : Rels Kc A.St E₀ (Sg.Msg × Wp)) (msg : Sg.Msg → A.J → E)
    (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true) (hF : A.n + 1 + 1 = 2 ^ A.w) :
    ((A.baseK V VC).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over (cj R0 msg id (fun _ _ => True) A.lk.inR)).on
      (Sg.over (cj R0 msg id (fun _ _ => True) A.lk.inR)).relR
      (Sg.over (cj R0 msg Prod.fst (fun _ _ => True) (A.lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) (A.baseK V VC).e :=
  asmK_know_sig E p A V VC Sg E₀ Kc Wp R0 msg hA hP hF

end
end Cb
