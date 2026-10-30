-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmPull.lean: the assembled lookup `LkAsm` (Cb/Ld/LdLkpAsm.lean) with rows and mask form
on the named entries only.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpAsmPullProofs.lean.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean).
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).

Why: the interface of the lookup sub-protocol (`SubR`, `SubR.OK`, Cb/Ld/LdLkp.lean) has "rows and
mask form read only the multiplicities and masks" by type: they are forms on the entries `ent`,
named by a set N. Cb/Ld/LdLkpAsm.lean takes for N all entries J, those that the keys read among
them: there the clause is empty. Here N is any set of names with an injective ι : N → J whose range
holds all places that the data name (bits, masks: `LkAsm.PlacesIn` of Cb/Ld/LdLkpSupp.lean), and the
read-out lists rows and mask form as forms on N. So the clause says what it should: an entry outside
the range of ι (an entry of the index's message, say) is read, in the output claim (`Lk.out`), by
the keys alone.

Main names:
  `ldLkpAsmN_base`: at the base (see Cb/Ld/LdLkpAsmIdx.lean), any tuple type M, any riding joint R0:
    `A.baseN ι` is `BkA.Good`, that is `GoodAt`, from "every key in the table [exact: and Mu]" to
    "(extension of the keys at the end point) + (mask form at the entries named by N) = public
    target, and all rows hold of the entries named by N".
  `ldLkpAsmN_ok`: over a signature: `A.subN ι S E₀` is `SubR.OK` with ent = the entries named by N.
  `ldLkpAsmN_idx`: with an encoded index decoded by the statement: `IOR.GoodB` (Ior/Masked.lean) of
    `A.subIN ι C S msg` between the joints of Cb/Ld/LdWfIdx.lean (`idxAt`). Knowledge soundness
    covers only the statements at which the index has no collision at the record's seed and R0's
    condition holds, and samples and words of S are collision-free (`S.CF`, Cb/Ld/LdSig.lean), as in
    Cb/Ld/LdLkpAsmIdx.lean.
  Conditions of these three: ι injective; `A.PlacesIn` of the range of ι; the numbers
  (`A.H.lkb.Adm p`, p the characteristic of E); `A.H.MuOK Mu`.
  `ldLkpAsmN_plain`, `ldLkpAsmN_plainI`, `ldLkpAsmN_idxStep`, `ldLkpAsmN_passes`, `ldLkpAsmN_same`:
    the formats, as in Cb/Ld/LdLkpAsmIdx.lean.
  `ldLkpAsmN_len`: every explicit part that the verifier of `A.baseN` puts out lists `A.nRows` rows.

Notation:
  `A`: of type `LkAsm E`: the data of the assembled lookup (Cb/Ld/LdLkpAsm.lean);
  `R0`: a joint (`IOR.Rels`, Ior/Chain.lean);
  `msg`: of type `M → A.J → E`; over a signature, `S.Msg → A.J → E`; with an encoded index,
    `C.Msg × M → A.J → E`, over a signature `C.Msg × S.Msg → A.J → E`;
  `cj R0 msg pr Φ ΦR`: a riding joint, and claims on the entries (Cb/Ld/LdLkpKit.lean), with the
    fields
    `rel`: `R0.rel (pr x) y w ∧ Φ x (msg w.1)`;
    `relR`: `R0.relR (pr a.1, a.2) w ∧ ΦR a.1 (msg w.1)`;
    `on`: `R0.on (pr a.1, a.2)`; `core`: `R0.core`;
  `A.lk.inR`: the claim, relaxed; `A.lk.inP Mu`: the claim, exact: `A.lk.inR st m ∧ Mu st m`;
    `A.lk.out`: the output claim (`Lk.inR`, `Lk.inP`, `Lk.out`, Cb/Ld/LdLkp.lean);
  `Mu`: of type `A.St → (A.J → E) → Prop`; `A.H.MuOK Mu`: what is asked of "the vector is the
    multiplicities": with it, for keys in the table, the claim after λ holds at every λ, and the
    idle positions are idle (`LkHead.MuOK`, Cb/Ld/LdLkpHead.lean);
  `A.H.lkb.Adm p`: the conditions on numbers: with B for `A.H.lkb`:
    `B.W ≤ 2 ^ B.w ∧ 2 ^ B.v < 2 ^ B.W ∧ 2 ^ B.d * (2 ^ B.W - 1) < p` (`LkB.Adm`, Cb/Ld/LdLkp.lean);
  `idxAt C rc R`: the joint R on tuples (message of the index, messages), with the index decoded by
    the statement (Cb/Ld/LdWfIdx.lean);
  `TX St E N`: `St × MCl E N × List (Row E N)` (Cb/Ld/LdLkpTree.lean);
  `Plain`: the format at the base (`BkA.Plain`, Cb/Ld/LdLkpFormat.lean);
  `IdxStep`: a step: from (the encoded index, any oracles) to (the encoded index, any oracles);
    `Passes rc rc'`: whenever the verifier outputs x', rc' x' = rc x (Cb/Ld/LdWfPre.lean);
  `Kc`, `M`, `Wp`: of type `Type`; `Ex`, `E₀`: of type `ExtSpec`.

Limits: Four differences to a write-up of ours (lean/CREDITS.md), which writes the lookup
out, are declared: (1) to (4) below. `LkAsm2` (Cb/Ld/LdLkpAsm2.lean), Cb/Ld/LdLkpAsm2*.lean,
removes (1), (3), (4); at (2) it has the same block, `RootP.rootA`, one round, drawn earlier.
`LkAsm` (Cb/Ld/LdLkpAsm.lean) is superseded under all callers: no protocol, toy or top stands on it
any more. Its files stay because files of `LkAsm2` quote their generic parts.
   (1) Order. There the one claim on the table's products comes right after the tie, before the
       keys' grand product; here the forest's point is drawn after the keys' tree.
   (2) The forest's first point. There a line step on a map with as many parts as there are bit
       positions, counting and idle ones together (a power of two): one round; here a round of its
       own for the point (declared as ours in the head of Cb/Ld/LdLkpAsm.lean).
   (3) Idle bit positions. There the table's factor carries a public factor, 1 at the counting
       positions and 0 at the others, so the product at an idle position is 1 for all messages and
       the claim "product = 1" there needs nothing; here that claim is added after the challenge and
       rides along, true because honest bits are 0 there: a hypothesis (`H.Idle`) that falls with
       the public factor.
   (4) The table's factor. There it is closed without revealing a map (two rounds fewer, one row);
       here by the closing that reveals (two rows). This bears on what the verifier sees, so on the
       block's item "masked messages" too, not only on counts.
This file says nothing on zero knowledge.
It does not say that the places are pairwise different.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpSupp
import Cb.Ld.LdLkpAsmIdx
import Cb.Ld.LdLkpAsmMore

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E) {N : Type} (ι : N → A.J)

/-- The read-out on the named entries. -/
def rdN (o : A.Q.XB) : TX A.St E N :=
  ((A.rd o).1, (A.rd o).2.1.pull ι, (A.rd o).2.2.map (Row.pull ι))

/-- the entries named by N -/
def entN (m : A.J → E) : N → E := fun n => m (ι n)

/-- At the base. -/
def baseN (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) : BkA Kc M A.St (TX A.St E N) Ex Wp :=
  (A.chainA Ex M Wp Kc msg).postM (A.rdN ι)

/-- Over a signature. -/
def subN (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) :
    SubR S E₀ Kc A.St N Wp :=
  ⟨(A.baseN ι E₀ S.Msg Wp Kc msg).R.keep S.Smp S.ext,
    S.liftH (A.baseN ι E₀ S.Msg Wp Kc msg).H,
    fun _ _ w => w,
    (A.baseN ι E₀ S.Msg Wp Kc msg).P.keep S.Smp S.ext⟩

/-- On tuples (message of the index, messages). -/
def baseIN (C : ConfigurationWithOutOfDomainSample) (M : Type) (msg : C.Msg × M → A.J → E) :
    BkA Unit M A.St (TX A.St E N) C.E0 (C.PIdx × Unit) :=
  ⟨(A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).R,
    idxH C (A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).H,
    (A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).P⟩

def subIN (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E) :
    Sub S S C.E0 A.St N (C.PIdx × Unit) :=
  ⟨(A.baseIN ι C S.Msg msg).R.keep S.Smp S.ext,
    S.liftH (A.baseIN ι C S.Msg msg).H,
    fun _ _ w => w,
    (A.baseIN ι C S.Msg msg).P.keep S.Smp S.ext⟩

end LkAsm
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- At the base. -/
def ldLkpAsmN_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) (Kc M Wp : Type)
      (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOK Mu →
    (A.baseN ι Ex M Wp Kc msg).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg Prod.fst (A.lk.out id (A.entN ι)) (A.lk.out id (A.entN ι)))

/-- The interface, with its clause on what rows and mask form read. -/
def ldLkpAsmN_ok : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOK Mu →
    (A.subN ι S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => Mu st (msg ym.2)) R0 fun ym => A.entN ι (msg ym.2)

/-- With an encoded index decoded by the statement. -/
def ldLkpAsmN_idx : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (rc : A.St → C.Rec)
      (R0 : Rels Unit A.St C.E0 ((C.Msg × S.Msg) × Unit)) (msg : C.Msg × S.Msg → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOK Mu →
    GoodB (A.subIN ι C S msg).R (A.subIN ι C S msg).H
      (S.over (idxAt C rc (cj R0 msg id (A.lk.inP Mu) A.lk.inR)))
      (S.over (idxAt C (fun x => rc x.1)
          (cj R0 msg Prod.fst (A.lk.out id (A.entN ι)) (A.lk.out id (A.entN ι)))))
      (A.subIN ι C S msg).ext (A.subIN ι C S msg).P

def ldLkpAsmN_plain : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseN ι Ex M Wp Kc msg).Plain
def ldLkpAsmN_plainI : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (M : Type) (msg : C.Msg × M → A.J → E),
    (A.baseIN ι C M msg).Plain
def ldLkpAsmN_idxStep : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subIN ι C S msg).R.IdxStep
def ldLkpAsmN_passes : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subIN ι C S msg).R.Passes (fun x => x) (fun x => (x.1.1, x.2))
def ldLkpAsmN_same : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
      (msg : C.Msg × S.Msg → A.J → E) w x c ρ,
    (((A.subIN ι C S msg).H.strat w x c).run ρ).2.2 = w

def ldLkpAsmN_len : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec)
      (M Wp Kc : Type) (msg : M → A.J → E) x y τ xo,
    (A.baseN ι Ex M Wp Kc msg).R.out x y τ = some xo → xo.2.2.length = A.nRows

end
end Cb.Spec
