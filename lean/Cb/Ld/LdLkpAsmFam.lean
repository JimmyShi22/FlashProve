-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmFam.lean: the assembled lookup with its rows as a family of fixed size: no list is
filed.

Definitions and statements (in `Cb.Spec`). Proofs: Cb/Ld/LdLkpAsmFamProofs.lean.
The assembled lookup (data `LkAsm`, Cb/Ld/LdLkpAsm.lean) is the chain `A.chainA` (the lookup's head,
the keys' side, the table's side) followed by a read-out.
Its read-out `A.rd` maps the chain's last explicit part to (state, masked claim, list of rows)
(`TX`, Cb/Ld/LdLkpTree.lean).
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core. At the base means between joints in which the tuple of messages is a part of the witness
(`BkA`, Cb/Ld/LdLkpTreeP.lean), before the lift over a signature (Cb/Ld/LdSigLift.lean).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: the read-out of the assembled lookup (Cb/Ld/LdLkpAsm.lean, Cb/Ld/LdLkpAsmPull.lean) files its
rows in a list. By type a list has any length, so whoever reads the rows off a state later (a
batching with a fixed format, a step that only maps the explicit part) has to reject other lengths,
and the honest length becomes a clause of the exact relation (`rel`). But the read-out lists exactly
`A.nRows` rows at every last explicit part (`Spec.ldLkpAsm_len`, Cb/Ld/LdLkpAsmMore.lean). So the
rows can be filed as a family over `Fin A.nRows` at once, by another read-out of the same chain. No
step, no rejection, no clause on a length.

Main names:
  `FX St E N n`: the explicit part: (state, masked claim, a row for each i < n).
  `toFam n`: a list of rows as such a family (beyond the list's end: the row 0 = 0).
  `L.outF res ent`: the lookup's output claim for such an explicit part.
  `A.rdF ι`, `A.baseF ι` (ι : N → A.J): the read-out; the chain at the base with it: the same
    rounds, the same messages as `A.baseA` and `A.baseN ι`.
  `Spec.ldLkpAsmF_fam`: for a list of length n the two forms of the output claim say the same.
  `Spec.ldLkpAsmF_base`: under the conditions below, at the base, for any tuple type `M` and any
    joint `R0`, `A.baseF ι` is `BkA.Good`, that is `GoodAt`, from one joint to another. Both joints
    have the form `cj` (Cb/Ld/LdLkpKit.lean): each is made from `R0`, which rides along, and from
    two claims on the entries, one for the honest relation (`rel`), one for the relaxed relation
    (`relR`). The input joint: every key in the table; honest: and Mu (`H.MuOK`,
    Cb/Ld/LdLkpHead.lean). The output joint: the output claim on the family (`L.outF`), in both
    relations. The statement's conditions are those of Cb/Ld/LdLkpAsmPull.lean: ι injective;
    `A.PlacesIn` of the range of ι; `A.H.lkb.Adm p`, p the characteristic of E; `A.H.MuOK Mu`.
  `Spec.ldLkpAsmF_plain`, `Spec.ldLkpAsmF_pass`, `Spec.ldLkpAsmF_noOrcs`, `Spec.ldLkpAsmF_shape`:
    the formats (Cb/Ld/LdLkpFormat.lean; `noOrcs`: Cb/Ld/LdPscGood.lean); the shape is that of
    `A.baseA`.
  `Spec.ldLkpAsmF_supp`: forms live on N by type; pushed along ι they are 0 outside its range at all
    states: what a later masked block asks of an incoming form is then a condition on places.

Limits: this is the read-out of `LkAsm` (Cb/Ld/LdLkpAsm.lean), which is superseded under all
callers: the same read-out at `LkAsm2` (Cb/Ld/LdLkpAsm2.lean) is in Cb/Ld/LdLkpAsm2Fmt.lean
(`A.rdF`, `A.baseF`, `ldLkpAsm2F_base` to `ldLkpAsm2F_shape`), which takes `toFam` and `FX` from
this file.
This file says nothing on zero knowledge (the item of the chain before the read-out:
Cb/Ld/LdLkpMaskAsm.lean; a read-out sends nothing).
-/
import Cb.Ld.LdLkpAsmPull
import Cb.Ld.LdLkpFormatPiece

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

/-- the explicit part with a family of rows -/
abbrev FX (St E N : Type) (n : ℕ) : Type := St × MCl E N × (Fin n → Row E N)

section
variable {E St M M' N : Type} [Field E]

/-- a list of rows as a family -/
def toFam (n : ℕ) (x : TX St E N) : FX St E N n :=
  (x.1, x.2.1, fun i => x.2.2.getD i ⟨fun _ => 0, 0⟩)

/-- The output claim on a family of rows. -/
def Lk.outF (L : Lk E St M) [Fintype N] {n : ℕ} (res : M' → M) (ent : M' → N → E) :
    FX St E N n → M' → Prop := fun x m' =>
  x.2.1.Holds L.v (L.key x.1 (res m')) (ent m') ∧
  (∀ i, (x.2.2 i).Holds (ent m')) ∧
  L.more x.1 (res m')

end

noncomputable section
namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E) {N : Type} (ι : N → A.J)

/-- The read-out with a family of rows. -/
def rdF (o : A.Q.XB) : FX A.St E N A.nRows := toFam A.nRows (A.rdN ι o)

/-- At the base. -/
def baseF (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    BkA Kc M A.St (FX A.St E N A.nRows) Ex Wp :=
  (A.chainA Ex M Wp Kc msg).postM (A.rdF ι)

end LkAsm
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

def ldLkpAsmF_fam : Prop :=
  ∀ (E St M M' N : Type) [Field E] [Fintype N] (L : Lk E St M) (res : M' → M) (ent : M' → N → E)
      (n : ℕ) (x : TX St E N) (m' : M'),
    x.2.2.length = n → (L.outF res ent (toFam n x) m' ↔ L.out res ent x m')

section
variable (E : Type) [Field E] [Fintype E]

/-- The lookup at the base, its rows a family. -/
def ldLkpAsmF_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) (Kc M Wp : Type)
      (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOK Mu →
    (A.baseF ι Ex M Wp Kc msg).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg Prod.fst (A.lk.outF id (A.entN ι)) (A.lk.outF id (A.entN ι)))

def ldLkpAsmF_plain : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseF ι Ex M Wp Kc msg).Plain
def ldLkpAsmF_pass : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseF ι Ex M Wp Kc msg).R.Passes id fun x' => x'.1
def ldLkpAsmF_noOrcs : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    noOrcs (A.baseF ι Ex M Wp Kc msg).R.shape
def ldLkpAsmF_shape : Prop :=
  ∀ (A : LkAsm E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseF ι Ex M Wp Kc msg).R.shape = (A.baseA Ex M Wp Kc msg).R.shape

/-- At all states: a filed form, pushed along ι, is 0 outside the range of ι. -/
def ldLkpAsmF_supp : Prop :=
  ∀ (J N St : Type) [Fintype N] (ι : N → J) (n : ℕ) (x : FX St E N n),
    SuppIn (fun j => j ∈ Set.range ι) (pushJ ι x.2.1.mf) ∧
    ∀ i, SuppIn (fun j => j ∈ Set.range ι) (pushJ ι (x.2.2 i).cf)

end
end Cb.Spec
