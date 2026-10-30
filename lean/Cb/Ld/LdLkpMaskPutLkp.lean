-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPutLkp.lean: under `A.MaskOK Dt`, the own masks of the assembled lookup are
"overwrite the entries at named places": the places of all its sumchecks.
This file gives, for each part of the lookup argument and for the whole, the places among the
entries that, under the conditions below, `put` overwrites (`MJ.Pl`, Cb/Ld/LdLkpMaskPut.lean).

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpMaskPutLkpProofs.lean.
The assembled lookup here is `LkAsm` (Cb/Ld/LdLkpAsm.lean), superseded under all callers by `LkAsm2`
(Cb/Ld/LdLkpAsm2.lean): Cb/Ld/LdLkpMaskPutLkp2.lean has this file's statement on the whole lookup at
the data of `LkAsm2` and uses its generic parts (tie, tree, head, keys' side) as they stand.
This file uses Cb/Ld/LdLkpMaskPut.lean (`D.PutAt`, the data `D.Pl` and how they are put together)
and the `MJ` records (Cb/Ld/LdLkpMaskChain.lean) of the lookup's parts: Cb/Ld/LdLkpMaskTie.lean,
Cb/Ld/LdLkpMaskTree.lean, Cb/Ld/LdLkpMaskSeg.lean, Cb/Ld/LdLkpMaskSegT.lean,
Cb/Ld/LdLkpMaskAsm.lean.

For each of these records the data (a type of places' names, the places, "a mask value is a value
for each place") are put together as the records are:
  `D.plAt`, `D.plTie` (the tie); `D.plLev`, `D.plTree` (a tree); `H.plHead` (the head); `plSegK`
  (the keys' side); `Q.plForest`, `Q.plSegT` (the table's side: point, forest, closing, bit test);
  `A.plChain`, `A.plBase` (the whole lookup, without and with the read-out).

Main names, each from the conditions on places of the file that defines the record (`MaskOK`,
`TabOK`): the data are OK (the places are different; the own masks overwrite exactly these entries;
every family of values occurs once), and the places are the set that the same file names:
  `Spec.ldLkpPl_tie`, `Spec.ldLkpPl_tree`: the own places of the steps (levels) l ≤ n.
  `Spec.ldLkpPl_head`, `Spec.ldLkpPl_segK`: the same.
  `Spec.ldLkpPl_forest`: those of the levels below l.
  `Spec.ldLkpPl_segT`: `Q.swT`.
  `Spec.ldLkpPl_asm`: `A.MaskOK Dt` ⇒ `(A.plChain ..).OK`, and its places are `A.swAll`; the same
    for `A.plBase`.

Limits: this file says nothing on what is read. It does not say that these entries are uniform and
unseen when the lookup starts: the matter of the block that sends them.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskPut
import Cb.Ld.LdLkpMaskAsm

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

namespace TieP
variable {E : Type} [Field E] [Fintype E] (D : TieP E)

def plAt (Ex : ExtSpec) (Rd : D.J → Prop) (l : ℕ) : (D.mjAt Ex Rd l).Pl :=
  ((D.lv l).T.plJ Ex (D.eJ l) Rd).post (fun o => some (D.nxt l o)) (ExtMap.id Ex) (D.nxt l)

def plTie (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (Rd : D.J → Prop) (n : ℕ) :
    (D.mjTie Ex M Wp Kc msg Rd n).Pl :=
  MJ.Pl.chain (fun l => E × (D.lv l).T.St)
    (D.stepA Ex Wp Kc msg) (fun l => D.mjAt Ex Rd l) (fun l => D.plAt Ex Rd l) n

end TieP

namespace TreeP
variable {E : Type} [Field E] [Fintype E] (D : TreeP E)

def plLev (Ex : ExtSpec) (Rd : D.J → Prop) (l : ℕ) : (D.mjLev Ex Rd l).Pl :=
  ((D.lv l).T.plJ Ex (D.eJ l) Rd).seq
    (MJ.Pl.silent (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex fun _ _ => True)

def plTree (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (Rd : D.J → Prop) (n : ℕ) :
    (D.mjTree Ex M Wp Kc msg Rd n).Pl :=
  MJ.Pl.chain (fun l => E × (D.lv l).T.St)
    (D.levA Ex Wp Kc msg) (fun l => D.mjLev Ex Rd l) (fun l => D.plLev Ex Rd l) n

end TreeP

section
variable {E : Type} [Field E] [Fintype E]

def LkHead.plHead (H : LkHead E) (Ex : ExtSpec) (M Wp Kc : Type)
    (msg : M → H.J → E) (Rd : H.J → Prop) :
    (H.mjHead Ex M Wp Kc msg Rd).Pl :=
  (MJ.Pl.silent E (Prod.mk : H.St → E → H.St × E) Ex fun _ _ => True).seq
    ((H.tie.plTie Ex M Wp Kc msg Rd H.n).pre (fun x => some ((0 : E), x))
      (ExtMap.id Ex) fun x => ((0 : E), x))

def plSegK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec) (M Wp Kc : Type)
    (msg : M → I.J → E) (Rd : I.J → Prop) :
    (mjSegK I v' tK Ex M Wp Kc msg Rd).Pl :=
  ((I.setV (v' + 1)).DK.plTree Ex M Wp Kc msg Rd v').pre
    (fun x => some (enterK (I.setV (v' + 1)) tK x)) (ExtMap.id Ex) (enterK (I.setV (v' + 1)) tK)

end

namespace SegTab
variable {E : Type} [Field E] [Fintype E] (Q : SegTab E)

def plForest (Ex : ExtSpec) {M : Type} (Wp Kc : Type) (msg : M → Q.I.J → E) (Rd : Q.I.J → Prop) :
    (l : ℕ) → (Q.mjForest Ex Wp Kc msg Rd l).Pl
  | 0 => MJ.Pl.silent Q.R.toIn.ev.D Q.R.toIn.nxX Ex Q.R.toIn.AllHold
  | l + 1 => (plForest Ex Wp Kc msg Rd l).seq (Q.D.plLev Ex Rd l)

def plSegT (Ex : ExtSpec) {M : Type} (Wp Kc : Type) (msg : M → Q.I.J → E) (Rd : Q.I.J → Prop) :
    (Q.mjSegT Ex Wp Kc msg Rd).Pl :=
  ((Q.plForest Ex Wp Kc msg Rd Q.I.d).seq (Q.En.psc.plJ Ex (Equiv.refl _) Rd)).seq
    ((MJ.Pl.silent Q.Bt.zc.toIn.ev.D Q.Bt.zc.toIn.nxX Ex Q.Bt.zc.toIn.AllHold).seq
      (Q.Bt.zc.next.plJ Ex (Equiv.refl _) Rd))

end SegTab

namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

/-- The places of the own masks of the whole lookup. -/
def plChain (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd : A.J → Prop) :
    (A.mjChain Ex M Wp Kc msg Rd).Pl :=
  ((A.H.plHead Ex M Wp Kc msg Rd).seq (plSegK A.IK A.v' A.tK Ex M Wp Kc msg Rd)).seq
    (A.Q.plSegT Ex Wp Kc msg Rd)

def plBase (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd : A.J → Prop) :
    (A.mjBase Ex M Wp Kc msg Rd).Pl :=
  (A.plChain Ex M Wp Kc msg Rd).post (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd

end LkAsm
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpPl_tie : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (Rd Dt : D.J → Prop) (n : ℕ),
    D.MaskOK n Dt →
    (D.plTie Ex M Wp Kc msg Rd n).OK ∧
    ∀ j, (D.plTie Ex M Wp Kc msg Rd n).At j ↔ ∃ l ≤ n, D.ownAt l j

def ldLkpPl_tree : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (Rd Dt In : D.J → Prop) (n : ℕ),
    D.MaskOK n Dt In →
    (D.plTree Ex M Wp Kc msg Rd n).OK ∧
    ∀ j, (D.plTree Ex M Wp Kc msg Rd n).At j ↔ ∃ l ≤ n, D.ownAt l j

def ldLkpPl_head : Prop :=
  ∀ (H : LkHead E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → H.J → E) (Rd Dt : H.J → Prop),
    H.tie.MaskOK H.n Dt →
    (H.plHead Ex M Wp Kc msg Rd).OK ∧
    ∀ j, (H.plHead Ex M Wp Kc msg Rd).At j ↔ ∃ l ≤ H.n, H.tie.ownAt l j

def ldLkpPl_segK : Prop :=
  ∀ (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec) (M Wp Kc : Type)
      (msg : M → I.J → E) (Rd Dt In : I.J → Prop),
    (I.setV (v' + 1)).DK.MaskOK v' Dt In →
    (plSegK I v' tK Ex M Wp Kc msg Rd).OK ∧
    ∀ j, (plSegK I v' tK Ex M Wp Kc msg Rd).At j ↔ ∃ l ≤ v', (I.setV (v' + 1)).DK.ownAt l j

def ldLkpPl_forest : Prop :=
  ∀ (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E)
      (Rd Dt In : Q.I.J → Prop) (l : ℕ),
    (∀ l' < l, Q.D.MaskOK l' Dt In) →
    (Q.plForest Ex Wp Kc msg Rd l).OK ∧
    ∀ j, (Q.plForest Ex Wp Kc msg Rd l).At j ↔ ∃ l' < l, Q.D.ownAt l' j

def ldLkpPl_segT : Prop :=
  ∀ (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E) (Rd Dt In : Q.I.J → Prop),
    Q.TabOK Dt In → (Q.plSegT Ex Wp Kc msg Rd).OK ∧ ∀ j, (Q.plSegT Ex Wp Kc msg Rd).At j ↔ Q.swT j

/-- The whole lookup. -/
def ldLkpPl_asm : Prop :=
  ∀ (A : LkAsm E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd Dt : A.J → Prop),
    A.MaskOK Dt →
    ((A.plChain Ex M Wp Kc msg Rd).OK ∧ ∀ j, (A.plChain Ex M Wp Kc msg Rd).At j ↔ A.swAll j) ∧
    ((A.plBase Ex M Wp Kc msg Rd).OK ∧ ∀ j, (A.plBase Ex M Wp Kc msg Rd).At j ↔ A.swAll j)

end
end Cb.Spec
