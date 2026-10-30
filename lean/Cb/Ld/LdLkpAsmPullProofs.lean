-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmPullProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsmPull.lean (the
assembled lookup with rows and mask form on the named entries only).

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names, each under the hypotheses of its statement (Cb/Ld/LdLkpAsmPull.lean):
  `ldLkpAsmN_base`: at the base: `A.baseN ι` is `BkA.Good`, that is `GoodAt`, beside any riding
    joint R0, from "every key in the table [exact: and Mu]" to "(extension of the keys at the end
    point) + (mask form at the entries named by N) = public target, and all rows hold of the entries
    named by N".
  `ldLkpAsmN_ok`: over a signature: `A.subN ι S E₀` is `SubR.OK` with ent = the entries named by N.
  `ldLkpAsmN_idx`: with an encoded index decoded by the statement: `IOR.GoodB` of
    `A.subIN ι C S msg` between the joints of Cb/Ld/LdWfIdx.lean (`idxAt`); which statements
    knowledge soundness covers: its row in the head of Cb/Ld/LdLkpAsmPull.lean.
  Conditions of these three: ι injective; `A.PlacesIn` of the range of ι; the numbers
  (`A.H.lkb.Adm p`, p the characteristic of E); `A.H.MuOK Mu`.
  `ldLkpAsmN_plain`, `ldLkpAsmN_plainI`, `ldLkpAsmN_idxStep`, `ldLkpAsmN_passes`, `ldLkpAsmN_same`:
    the formats, as in Cb/Ld/LdLkpAsmIdx.lean.
  `ldLkpAsmN_len`: every explicit part that the verifier of `A.baseN` puts out lists `A.nRows` rows.
Before them auxiliary lemmas: the pulled-back output claim says what the output claim says
(`LkAsm.outN_iff`, under ι : N → A.J injective and `A.PlacesIn` of its range); the verifier hands
the state on (`LkAsm.passN`).
How the three are got (read off the proofs): `ldLkpAsmN_base`: `LkAsm.chain_good`
(Cb/Ld/LdLkpAsmProofs.lean), carried through the read-out by `goodAt_postMap` (Cb/Ld/LdSigStep.lean)
with `LkAsm.outN_iff`; `ldLkpAsmN_ok`: `sigLift_goodB` (Cb/Ld/LdSigLiftProofs.lean) at
`ldLkpAsmN_base`; `ldLkpAsmN_idx`: `idxLift_goodB` (Cb/Ld/LdWfIdxProofs.lean) at `ldLkpAsmN_base`,
with `LkAsm.passN` and `ldLkpAsmN_plain`.

Limits: see the head of Cb/Ld/LdLkpAsmPull.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsmPull
import Cb.Ld.LdLkpSuppProofs
import Cb.Ld.LdLkpAsmIdxProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- Under `hι` and `hP`, the output claim on the named entries, at `A.rdN ι o`, holds if and only if
the output claim at `A.rd o` does. -/
theorem LdLkp.LkAsm.outN_iff (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J)
    (hι : Function.Injective ι) (hP : A.PlacesIn fun j => j ∈ Set.range ι)
    (o : A.Q.XB) (m : A.J → E) :
    A.lk.out id (A.entN ι) (A.rdN ι o) m ↔ A.lk.out id id (A.rd o) m := by
  obtain ⟨h1, h2⟩ := ldLkpSupp_out E A N ι hι hP o (A.v' + 1) (A.key (A.rd o).1 m) m
  exact and_congr h1 (and_congr h2 Iff.rfl)

/-- The verifier hands the state on. -/
theorem LdLkp.LkAsm.passN (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec)
    (M Wp Kc : Type) (msg : M → A.J → E) :
    (A.baseN ι Ex M Wp Kc msg).R.Passes id fun x' => x'.1 :=
  (((pass_head Ex M Wp Kc A.H msg).seq
    (passes_map (pass_segK Ex M Wp Kc A.IK A.v' A.tK msg) fun x => (A.b2 x).1)).seq
    (passes_map (pass_segT Ex M Wp Kc A.Q msg) fun x => (A.b2 (A.o4 x)).1)).post _ _ fun o x' e => by
      obtain rfl := Option.some.inj e
      rfl

theorem ldLkpAsmN_base : Spec.ldLkpAsmN_base E := by
  intro p _ A N _ ι Mu Ex Kc M Wp R0 msg hι hP hA hMu
  have g := A.chain_good E p Mu Ex Kc M Wp R0 msg hA hMu
  unfold BkA.Good at g ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ (A.rdN ι) g ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1,
      (A.outN_iff E N ι hι hP o _).mpr
        ((A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩)⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp ((A.outN_iff E N ι hι hP o _).mp h.2)⟩

theorem ldLkpAsmN_ok : Spec.ldLkpAsmN_ok E := by
  intro p _ A N _ ι Mu S E₀ Kc Wp R0 msg hι hP hA hMu
  exact sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (ldLkpAsmN_base E p A N ι Mu E₀ Kc S.Msg Wp R0 msg hι hP hA hMu)

theorem ldLkpAsmN_plain : Spec.ldLkpAsmN_plain E := fun A _ ι Ex M Wp Kc msg =>
  plain_postM (plain_seq
    (plain_seq (plain_head Ex M Wp Kc A.H msg) (plain_segK Ex M Wp Kc A.IK A.v' A.tK msg))
    (plain_segT Ex M Wp Kc A.Q msg)) (A.rdN ι)

theorem ldLkpAsmN_idx : Spec.ldLkpAsmN_idx E := by
  intro p _ A N _ ι Mu C S rc R0 msg hι hP hA hMu
  exact idxLift_goodB E C S Unit _ _ Unit Unit _ _ _ _ rc (fun x => rc x.1) (fun _ _ _ wp => wp) _
    (fun x y τ x' h => congrArg rc (A.passN E N ι C.E0 (C.Msg × S.Msg) Unit Unit msg x y τ x' h))
    (ldLkpAsmN_plain E A N ι C.E0 (C.Msg × S.Msg) Unit Unit msg).copies.copy
    (ldLkpAsmN_base E p A N ι Mu C.E0 Unit (C.Msg × S.Msg) Unit R0 msg hι hP hA hMu)

theorem ldLkpAsmN_plainI : Spec.ldLkpAsmN_plainI E := by
  intro A N ι C M msg
  have h := ldLkpAsmN_plain E A N ι C.E0 (C.Msg × M) Unit Unit msg
  refine ⟨h.copies, fun w x c ρ => ?_, h.budAll, fun w x => h.free (idxIn C w) x⟩
  show ((((A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).H.mapW (idxIn C) fun w o =>
        (w.1, (w.2.1, o.2))).strat
      w x c).run ρ).2.2 = w
  rw [Honest.mapW_run]

theorem ldLkpAsmN_idxStep : Spec.ldLkpAsmN_idxStep E := fun A N ι C S msg =>
  lift_idxStep S (ldLkpAsmN_plainI E A N ι C S.Msg msg)

theorem ldLkpAsmN_passes : Spec.ldLkpAsmN_passes E := fun A N ι C S msg =>
  lift_passes (b := A.baseIN ι C S.Msg msg) S (A.passN E N ι C.E0 (C.Msg × S.Msg) Unit Unit msg)

theorem ldLkpAsmN_same : Spec.ldLkpAsmN_same E := fun A N ι C S msg =>
  lift_keepsW S (ldLkpAsmN_plainI E A N ι C S.Msg msg)

theorem ldLkpAsmN_len : Spec.ldLkpAsmN_len E := by
  intro A N ι Ex M Wp Kc msg x y τ xo h
  obtain ⟨o, _, ho⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj ho]
  show ((A.rd o).2.2.map (Row.pull ι)).length = A.nRows
  rw [List.length_map]
  exact ldLkpAsm_len E A o

end
end Cb
