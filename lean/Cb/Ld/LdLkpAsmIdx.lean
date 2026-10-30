-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmIdx.lean: the assembled lookup `LkAsm` (Cb/Ld/LdLkpAsm.lean) on keys that read an
encoded index.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpAsmIdxProofs.lean.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean).
`IOR.GoodB` (Ior/Masked.lean) has among its fields completeness in the sense of `Honest.Acc`
(Ior/Honest.lean) and round-by-round knowledge soundness (`Know`, Ior/Know.lean).
At the base means between joints in which the tuple of messages is a part of the witness (`BkA`,
Cb/Ld/LdLkpTreeP.lean), before the lift over a signature (Cb/Ld/LdSigLift.lean).

The assembled lookup (Cb/Ld/LdLkpAsm.lean) is good at the base for any type of tuples
(`ldLkpAsm_base`, under the hypotheses of its statement). Here the tuples are (message of the index,
messages of the oracle messages): so keys, table side and rows may read entries of the index's
message beside entries of the messages. The index is no oracle message: it is a further oracle of
the statement, its record is in the explicit part, and its message is the decoding by the statement
(Cb/Ld/LdWfIdx.lean: `idxAt`, `idxH` and the index-lifting rule, `Spec.idxLift_goodAt`, and over a
signature `Spec.idxLift_goodB`).

Main names:
  `A.baseI C M msg`: the chain at the base with the honest side that is given the message of its
    prover encoded index (`idxH`); reduction and numbers are those of `A.baseA`.
  `A.subI C S msg`: lifted over a signature S: a lookup sub-protocol in the sense of
    Cb/Ld/LdLkp.lean (`Sub`), S' = S, further oracle: the index, further witness: the prover encoded
    index (`C.PIdx`).
  `ldLkpAsmI_good`: for any reading rc of the record off the state, any riding joint R0 on tuples
    (core and further witness of type Unit), any Mu with `A.H.MuOK Mu` (Cb/Ld/LdLkpHead.lean), under
    the conditions on numbers (`A.H.lkb.Adm p`, p the characteristic of E): `IOR.GoodB` of
    `A.subI C S msg`, between two joints.
    From (`S.over (idxAt C rc (cj R0 msg id (A.lk.inP Mu) A.lk.inR))`):
      beside what `S.over` itself asks (Cb/Ld/LdSig.lean): exact: every word is the encoding of its
        pair and every message has its sample's answers; relaxed: the decoder returns the witness's
        messages:
      exact: the index is the encoding of the prover encoded index with this record; at its message:
        R0, every key in the table, Mu.
      Relaxed: the statement decodes the index to some U; at U: R0, every key in the table.
    To
      (`S.over (idxAt C (fun x => rc x.1) (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id)))`):
      the same, with, in place of "every key in the table" and Mu (exact and relaxed alike):
        (extension of the keys at the end point) + (mask form) = public target, and all rows hold.
    Knowledge soundness covers only the statements at which the index has no collision at the
    record's seed (`C.coll`) and R0's condition holds, and samples and words of S are collision-free
    (`S.CF`) (the fields `on` of `idxAt` and of `S.over`, Cb/Ld/LdSig.lean).
  `ldLkpAsmI_plain`: the format at the base (Cb/Ld/LdLkpFormat.lean: `Plain`): the block only copies
    its oracles: it reads none, ties nothing; the honest prover ends with its witness; every budget;
    nothing withheld.
  `ldLkpAsmI_idx`, `ldLkpAsmI_passes`, `ldLkpAsmI_same`: so, over S: the index is neither read nor
    tied and is copied (`ldLkpAsmI_idx`); state and samples are handed on by the verifier
    (`ldLkpAsmI_passes`); the witness by the honest prover (`ldLkpAsmI_same`).

Notation:
  `A`: of type `LkAsm E`: the data of the assembled lookup (Cb/Ld/LdLkpAsm.lean);
  `rc`: of type `A.St → C.Rec`; `msg`: of type `C.Msg × S.Msg → A.J → E`; at the base,
    `C.Msg × M → A.J → E`;
  `R0`: a joint (`IOR.Rels`, Ior/Chain.lean);
  `cj R0 msg pr Φ ΦR`: a riding joint, and claims on the entries (Cb/Ld/LdLkpKit.lean), with the
    fields
    `rel`: `R0.rel (pr x) y w ∧ Φ x (msg w.1)`;
    `relR`: `R0.relR (pr a.1, a.2) w ∧ ΦR a.1 (msg w.1)`;
    `on`: `R0.on (pr a.1, a.2)`; `core`: `R0.core`;
  `idxAt C rc R`: the joint R on tuples (message of the index, messages), with the index decoded by
    the statement (Cb/Ld/LdWfIdx.lean);
  `A.lk.inR`: the claim, relaxed; `A.lk.inP Mu`: the claim, exact: `A.lk.inR st m ∧ Mu st m`;
    `A.lk.out`: the output claim (`Lk.inR`, `Lk.inP`, `Lk.out`, Cb/Ld/LdLkp.lean);
  `Mu`: of type `A.St → (A.J → E) → Prop`; `A.H.MuOK Mu`: what is asked of "the vector is the
    multiplicities": with it, for keys in the table, the claim after λ holds at every λ, and the
    idle positions are idle (`LkHead.MuOK`, Cb/Ld/LdLkpHead.lean);
  `A.H.lkb.Adm p`: the conditions on numbers: with B for `A.H.lkb`:
    `B.W ≤ 2 ^ B.w ∧ 2 ^ B.v < 2 ^ B.W ∧ 2 ^ B.d * (2 ^ B.W - 1) < p` (`LkB.Adm`, Cb/Ld/LdLkp.lean).

Limits: this file says nothing on zero knowledge.
By type the entries are any function msg of the tuple; that keys are linear in the index's entries
is the caller's matter.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm
import Cb.Ld.LdWfIdx
import Cb.Ld.LdLkpFormat

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

/-- The chain at the base, on tuples (message of the index, messages). -/
def baseI (C : ConfigurationWithOutOfDomainSample) (M : Type) (msg : C.Msg × M → A.J → E) :
    BkA Unit M A.St (TX A.St E A.J) C.E0 (C.PIdx × Unit) :=
  ⟨(A.baseA C.E0 (C.Msg × M) Unit Unit msg).R,
    idxH C (A.baseA C.E0 (C.Msg × M) Unit Unit msg).H,
    (A.baseA C.E0 (C.Msg × M) Unit Unit msg).P⟩

/-- Over a signature. -/
def subI (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E) :
    Sub S S C.E0 A.St A.J (C.PIdx × Unit) :=
  ⟨(A.baseI C S.Msg msg).R.keep S.Smp S.ext,
    S.liftH (A.baseI C S.Msg msg).H,
    fun _ _ w => w,
    (A.baseI C S.Msg msg).P.keep S.Smp S.ext⟩

end LkAsm
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The assembled lookup, with the index decoded by the statement. -/
def ldLkpAsmI_good : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (Mu : A.St → (A.J → E) → Prop) (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
      (rc : A.St → C.Rec) (R0 : Rels Unit A.St C.E0 ((C.Msg × S.Msg) × Unit))
      (msg : C.Msg × S.Msg → A.J → E),
    A.H.lkb.Adm p → A.H.MuOK Mu →
    GoodB (A.subI C S msg).R (A.subI C S msg).H
      (S.over (idxAt C rc (cj R0 msg id (A.lk.inP Mu) A.lk.inR)))
      (S.over (idxAt C (fun x => rc x.1) (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))))
      (A.subI C S msg).ext (A.subI C S msg).P

def ldLkpAsmI_plain : Prop :=
  ∀ (A : LkAsm E) (C : ConfigurationWithOutOfDomainSample) (M : Type) (msg : C.Msg × M → A.J → E), (A.baseI C M msg).Plain

def ldLkpAsmI_idx : Prop :=
  ∀ (A : LkAsm E) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subI C S msg).R.IdxStep

def ldLkpAsmI_passes : Prop :=
  ∀ (A : LkAsm E) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subI C S msg).R.Passes (fun x => x) (fun x => (x.1.1, x.2))

def ldLkpAsmI_same : Prop :=
  ∀ (A : LkAsm E) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E) w x c ρ,
    (((A.subI C S msg).H.strat w x c).run ρ).2.2 = w

end
end Cb.Spec
