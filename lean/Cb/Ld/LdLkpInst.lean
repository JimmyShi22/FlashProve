-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpInst.lean: the two product trees of the lookup as instances: the keys' tree and the
table's forest; what their roots and their tops say.
This file is about a lookup argument with multiplicities in bits: the products in its identity stand
at the roots (level 0) of product trees. Here the trees' data are given, and what the claims at
their roots and tops say.
The identity (the last clause of `Cb.Lkp.Mid`, Cb/Gen/LkpAlg.lean): `keyProd` = the product, over
the bit positions j < W, of `tabProd .. j` ^ 2^j; `keyProd`: the product of λ - key over the keys;
`tabProd .. j`: the product over the table of 1 + bit (λ - 1 - entry) at the bit position j.

Definitions and statements (the statements in `Cb.Spec`). Proofs: Cb/Ld/LdLkpInstProofs.lean.
The product tree of Cb/Ld/LdLkpTreeP.lean is stated for any levels U with the one condition `Step`
(an entry of level l is the product of the two entries of level l + 1 above it: last coordinate 0
and 1).
Here are the two forests of the lookup with multiplicities in bits (mathematics:
Cb/Gen/LkpAlg.lean), by the numbering of Cb/Ld/LdLkpNum.lean (coordinate i is bit i).
The data (`LkInst`):
  `X`: the states that a chain has reached when the trees begin, of any type, with readers `st` (the
    public state of the lookup) and `lam` (the first challenge);
  `key`: 2^v keys, functions of state and entries, never sent;
  `tab`: a table of 2^d entries, read off the state;
  2^w bit positions;
  `fK`, `formT`: the forms of the masked claims on the roots (on the product of the keys; on the
    products of the table), read off the state: they give the incoming forms of the two trees at
    level 0 (for the forest: combined with the equality weights at its point);
  `wK`, `cK`, `wT`, `cT`: the places of the blocks' own masks;
  `oK`, `oT`: the order of the rounds of each level: which coordinate its j-th variable is (by
    default coordinate j);
  `oE`, `oB`: the same for the w + d variables of the closing `I.endU` (Cb/Ld/LdLkpInst2.lean) and
    of the bit test `I.bitB`. `I.endB` does not read `oE`: its j-th variable is coordinate j.

Main names:
  `I.DK`: the keys' tree: one tree (g = 0) with the 2^v leaves λ - key.
  `I.DT`: the table's forest: 2^w trees, one for each bit position (the low w bits of a corner's
    number), with the 2^d leaves 1 + bit (λ - 1 - entry).
  `I.tAt`: where the bit of a corner of the cube in w + d variables stands; `I.endB`, `I.bitB`: the
    closing of the forest's top claim (Cb/Ld/LdLkpEnd.lean) and the bit test (Cb/Ld/LdLkpBit.lean)
    at these places.
  `Spec.ldLkpInst_stepK`, `Spec.ldLkpInst_stepT`: both meet the tree's one condition.
  `Spec.ldLkpInst_rootK`: level 0 of the keys' tree: the product over the keys: one of the two sides
    of the lookup's identity.
  `Spec.ldLkpInst_rootT`: level 0 of the table's forest: the product over the table at the bit
    position that the corner numbers.
  `Spec.ldLkpInst_topK`: the top of the keys' tree is a masked claim on the keys: the sum claim of
    level v holds if and only if (extension of the keys at the point) - (incoming form) = λ - target
    (a masked claim of Cb/Ld/LdLkpTree.lean, whose point lists the top bit first).
  `Spec.ldLkpInst_topT`: the top of the forest is the claim that the closing block (`I.endB`) takes:
    no step stands between them.
  `Spec.ldLkpInst_bits`: the bit test's claim at the places `I.tAt` is `Cb.Lkp.Bits`.

Limits: this file has no protocol of its own.
It says nothing on how the two roots are tied.
Which of the two indices of a bit (`bAt u j`) is the low one is a choice (the bit position).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpTreeRows
import Cb.Ld.LdLkpNum
import Cb.Ld.LdLkpEnd
import Cb.Ld.LdLkpBit

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

/-- The data. -/
structure LkInst (E : Type) [Field E] [Fintype E] where
  /-- the states that the chain has reached, and what is read off them -/
  X : Type
  St : Type
  st : X → St
  lam : X → E
  J : Type
  [finJ : Fintype J]
  v : ℕ
  d : ℕ
  w : ℕ
  key : St → (J → E) → ℕ → E
  tab : St → ℕ → E
  /-- where the bit (table entry u, position j) stands -/
  bAt : ℕ → ℕ → J
  /-- the forms of the masked claims on the roots, read off the state: on the product of the keys;
  on the products of the table -/
  fK : X → J → E
  formT : X → (Fin (w + 0) → Bool) → J → E
  /-- the places of the own masks of the levels of the two trees -/
  wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cK : ℕ → Bool → J
  wT : (l : ℕ) → PIdx (List.replicate (w + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cT : ℕ → Bool → J
  /-- the order of the rounds at each level of the keys' tree and of the table's forest
  (`TreeP.sg`, Cb/Ld/LdLkpTreeP.lean); by default the j-th variable is coordinate j -/
  oK : (l : ℕ) → Equiv.Perm (Fin (0 + l)) := fun _ => Equiv.refl _
  oT : (l : ℕ) → Equiv.Perm (Fin (w + l)) := fun _ => Equiv.refl _
  /-- the order of the rounds of the closing `endU` (Cb/Ld/LdLkpInst2.lean): its j-th variable (j
  from 0, in the order of their rounds) is coordinate oE j of the w + d; by default the j-th
  variable is coordinate j. `endB` does not read it. -/
  oE : Equiv.Perm (Fin (w + d)) := Equiv.refl _
  /-- the order of the rounds of the bit test `bitB` (`LkBit.sg`, Cb/Ld/LdLkpBit.lean): its j-th
  variable is coordinate oB j of the w + d; by default the j-th variable is coordinate j -/
  oB : Equiv.Perm (Fin (w + d)) := Equiv.refl _

attribute [instance] LkInst.finJ

namespace LkInst
variable {E : Type} [Field E] [Fintype E] (I : LkInst E)

/-- the bits, read off the entries -/
def bit (m : I.J → E) : ℕ → ℕ → E := fun u j => m (I.bAt u j)

/-- The keys' tree. -/
def DK : TreeP E where
  St0 := I.X
  J := I.J
  g := 0
  U := fun x m l => cubeLvl 0 I.v (facK (I.key (I.st x) m) (I.lam x)) l
  inc0 := fun x _ => I.fK x
  wAt := I.wK
  cAt := I.cK
  sg := I.oK

/-- The table's forest. -/
def DT : TreeP E where
  St0 := I.X
  J := I.J
  g := I.w
  U := fun x m l => cubeLvl I.w I.d (facT I.w (I.tab (I.st x)) (I.bit m) (I.lam x)) l
  inc0 := fun x ϱ j => ∑ θ, Alg.eqk ϱ θ * I.formT x θ j
  wAt := I.wT
  cAt := I.cT
  sg := I.oT

/-- where the bit of a corner stands: the low w bits of its number are the position -/
def tAt (b : Fin (I.w + I.d) → Bool) : I.J := I.bAt (numLE b / 2 ^ I.w) (numLE b % 2 ^ I.w)

/-- The closing of the forest's top claim, at the state of level d. -/
def endB (wE : PIdx (List.replicate (I.w + I.d) (pfCube E 2) ++ [pDummy E 1]) → I.J) (cE : I.J) :
    LkEnd E where
  X := (I.DT.lv I.d).T.St
  J := I.J
  k := I.w + I.d
  tAt := I.tAt
  z := (I.DT.lv I.d).pnt
  cp := fun s b =>
    I.lam ((I.DT.lv I.d).base s) - 1 - I.tab (I.st ((I.DT.lv I.d).base s)) (numLE b / 2 ^ I.w)
  inc := fun s => pushJ (I.DT.lv I.d).toJ ((I.DT.lv I.d).T.slS s)
  wAt := wE
  cAt := cE

/-- The bit test, with states of any type. -/
def bitB (Sb : Type)
    (wB : PIdx (List.replicate (I.w + I.d) (pfCube E 2) ++ [pDummy E 2]) → I.J) (cB : I.J) :
    LkBit E where
  St := Sb
  J := I.J
  k := I.w + I.d
  tAt := I.tAt
  wAt := wB
  cAt := cB
  sg := I.oB

/-- the masked claim on the keys that the top of the keys' tree states -/
def topCl (x : E × (I.DK.lv I.v).T.St) : MCl E I.J :=
  ⟨Blocks.nat fun i : Fin (0 + I.v) => (I.DK.lv I.v).pnt x.2 i.rev,
    fun j => - pushJ (I.DK.lv I.v).toJ ((I.DK.lv I.v).T.slS x.2) j,
    I.lam ((I.DK.lv I.v).base x.2) - x.1⟩

end LkInst
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp
variable (E : Type) [Field E] [Fintype E]

def ldLkpInst_stepK : Prop := ∀ I : LkInst E, I.DK.Step
def ldLkpInst_stepT : Prop := ∀ I : LkInst E, I.DT.Step

def ldLkpInst_rootK : Prop :=
  ∀ (I : LkInst E) x m θ, I.DK.U x m 0 θ = keyProd I.v (I.key (I.st x) m) (I.lam x)
def ldLkpInst_rootT : Prop :=
  ∀ (I : LkInst E) x m (θ : Fin (I.w + 0) → Bool),
    I.DT.U x m 0 θ = tabProd I.d (I.tab (I.st x)) (I.bit m) (I.lam x) (numLE θ)

/-- The top of the keys' tree is a masked claim on the keys. -/
def ldLkpInst_topK : Prop :=
  ∀ (I : LkInst E) (x : E × (I.DK.lv I.v).T.St) (m : I.J → E),
    (I.DK.lv I.v).T.SumHolds x (fun j => m ((I.DK.lv I.v).toJ j)) ↔
    (I.topCl x).Holds I.v (I.key (I.st ((I.DK.lv I.v).base x.2)) m) m

/-- The sum claim at the top of the forest is the closing block's claim. -/
def ldLkpInst_topT_iff : Prop :=
  ∀ (I : LkInst E) wE cE (x : E × (I.DT.lv I.d).T.St) (m : I.J → E),
    (I.DT.lv I.d).T.SumHolds x (fun j => m ((I.DT.lv I.d).toJ j)) ↔ (I.endB wE cE).Holds x m

/-- The tree's joint at level d is the closing block's input joint. -/
def ldLkpInst_topT : Prop :=
  ∀ (I : LkInst E) wE cE (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → I.J → E)
      (A0 : Rels Kc (I.DT.lv 0).T.St Ex (M × Wp)),
    I.DT.jtAt msg A0 I.d = (I.endB wE cE).relsIn (I.DT.ride msg A0 I.d) fun w => msg w.1

/-- The bit test's claim is that all bits are bits. -/
def ldLkpInst_bits : Prop :=
  ∀ (I : LkInst E) Sb wB cB (m : I.J → E), (I.bitB Sb wB cB).AllBits m ↔ Bits I.d I.w (I.bit m)

end Cb.Spec
