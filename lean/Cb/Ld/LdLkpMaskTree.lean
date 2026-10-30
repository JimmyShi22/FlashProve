-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskTree.lean: under the hypotheses of its statements, a product tree (or forest) of a
lookup has the item "masked messages", as a whole (`Honest.MM`, Ior/Masked.lean).
This file is about the product argument by a binary tree (Cb/Ld/LdLkpTreeP.lean), as the lookup
argument uses it.

`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `MM` is the conclusion of
`Spec.ldLkpMaskTree_mm`; `GoodM` stands in no statement of this file. (In the first two sentences
`D : MaskData ..` and `M : D.Mk` are the letters of Ior/Masked.lean; below `D : TreeP E`, and the
statement has `((D.mjTree ..).narrow (D.sumAt 0)).data ..` for that `D`.)

Definitions (with one proved lemma, `toJ_bij`), and statements (in `Cb.Spec`). Proofs:
Cb/Ld/LdLkpMaskTreeProofs.lean.
The tree (Cb/Ld/LdLkpTreeP.lean: `D : TreeP E`, `D.treeA`; a forest is 2^g such trees, `TreeP.g`):
the levels 0, .., n; each level is a sumcheck for the product of the two halves of the next level,
under equality weights, followed by a line step in which only the verifier speaks. No oracle is
sent; all masks are entries of oracle messages sent before.

The conditions on the places of the masks (`D.MaskOK n Dt In`), all on the parameters:
  `inj`: within a level, different own masks lie at different places.
  `disj`: the own masks of different levels lie at different places.
  `rd`: the levels (`D.U`) read the entries in Dt only ("the data").
  `dt`: no own mask of a level lies in the data.
  `inc`: the incoming form of level 0 reads the entries in In only (masks that an earlier block has
    left in the claim with which the tree is entered).
  `io`: no own mask of a level lies in In.
That no own mask, no datum and no entry of In blinds the answer to a sample comes in through Rd, as
in Cb/Ld/LdLkpMaskTie.lean. It cannot be said at this level.

In `Spec.ldLkpMaskTree_link` and `Spec.ldLkpMaskTree_mm` M is any tuple type, msg any reading of the
entries; `Spec.ldLkpMaskTree_sound` is stated at the tuple type `M` = D.J → E, read by the identity
(`msg`).
Rd: the entries that the reading of the chain keeps. Of Rd the statements here ask only that it
holds `D.srAt Dt In n`.

Main names:
  `Spec.ldLkpMaskTree_link`: under `D.Step` (`TreeP.Step`, Cb/Ld/LdLkpTreeP.lean),
    `D.MaskOK n Dt In`, and `D.srAt Dt In n` inside Rd:
    started with any claim C that gives the sum claim of level 0 and reads no own mask of the tree,
    the tree is a link of a chain of masked blocks (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
  `Spec.ldLkpMaskTree_mm`: under the same three premises: `Honest.MM` for the whole tree, started
    with the sum claim of level 0.
  `Spec.ldLkpMaskTree_sound`: under the hypotheses of its statement: if C gives the joint before the
    tree (`mjClOf (D.jtAt .. 0)`), then what the honest run of the tree makes of C
    (`(D.mjTree ..).sp C`; `MJ.sp`: Cb/Ld/LdLkpMaskSp.lean) gives the joint after the tree
    (`mjClOf (D.jtAt .. (n + 1))`; `mjClOf`: Cb/Ld/LdLkpMaskKit.lean).

Notation: `Ex`: the external oracles (an `ExtSpec`, Iop/InteractiveOracleProof.lean); `Wp`: the type of the further
witness; `Kc`: the type of the core; `D.J`: the finite type that names the entries; `A0`: a joint
(`Rels Kc ..`), an argument of `D.jtAt`; `mjClOf A`: the claim on entries that a joint at the base
makes (Cb/Ld/LdLkpMaskKit.lean); `MJ.narrow`: the same record with the claim `Cl'` in the place of
its own (`{ D with Cl := Cl' }`; Cb/Ld/LdLkpMaskPsc.lean); `MJ.data`: the record of Ior/Masked.lean
(`MaskData`) (Cb/Ld/LdLkpMaskChain.lean).

Limits: this file does not say that the masks are uniform and unseen when the tree starts.
It says nothing on soundness: see Cb/Ld/LdLkpTreeP.lean. (`Spec.ldLkpMaskTree_sound` speaks of the
honest run.)

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskOur
import Cb.Ld.LdLkpTreeP

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section

namespace TreeP
variable {E : Type} [Field E] [Fintype E] (D : TreeP E)

theorem toJ_bij : ∀ l, Function.Bijective (D.lv l).toJ
  | 0 => Function.bijective_id
  | _ + 1 => Function.bijective_id

/-- The entries of level l are the tree's entries. -/
def eJ (l : ℕ) : (D.lv l).T.J ≃ D.J := Equiv.ofBijective _ (D.toJ_bij l)

/-- The places of the own masks of level l. -/
def ownAt (l : ℕ) : D.J → Prop := fun j =>
  ∃ i, j = D.eJ l (Sum.elim (D.lv l).T.wAt (D.lv l).T.cAt i)

/-- The conditions on the places. -/
structure MaskOK (n : ℕ) (Dt In : D.J → Prop) : Prop where
  inj  : ∀ l ≤ n, Function.Injective (Sum.elim (D.lv l).T.wAt (D.lv l).T.cAt)
  disj : ∀ l l', l < l' → l' ≤ n → ∀ j, D.ownAt l j → ¬ D.ownAt l' j
  rd   : ∀ st m m', (∀ j, Dt j → m j = m' j) → D.U st m = D.U st m'
  dt   : ∀ l ≤ n, ∀ j, Dt j → ¬ D.ownAt l j
  inc  : ∀ st ϱ j, ¬ In j → D.inc0 st ϱ j = 0
  io   : ∀ l ≤ n, ∀ j, In j → ¬ D.ownAt l j

/-- What the messages of level l read. -/
def srAt (Dt In : D.J → Prop) (l : ℕ) : D.J → Prop := fun j => Dt j ∨ In j ∨ ∃ l' ≤ l, D.ownAt l' j

/-- The `MJ` record of level l: the sumcheck, then the line step. -/
def mjLev (Ex : ExtSpec) (Rd : D.J → Prop) (l : ℕ) :
    MJ E D.J (((D.lv l).T.par.psc Ex).seq
        (IOR.draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex)) :=
  ((D.lv l).T.mjJ Ex (D.eJ l) Rd).seq
    (MJ.silent (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex fun _ _ => True)

/-- The `MJ` record (Cb/Ld/LdLkpMaskChain.lean) of the whole tree. -/
def mjTree (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (Rd : D.J → Prop) (n : ℕ) :
    MJ E D.J (D.treeA Ex Wp Kc msg n).R :=
  MJ.chain (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg) (fun l => D.mjLev Ex Rd l) n

/-- The sum claim of level l, on the tree's entries. -/
def sumAt (l : ℕ) : E × (D.lv l).T.St → (D.J → E) → Prop := fun x k =>
  (D.lv l).T.SumHolds x fun j' => k (D.eJ l j')

end TreeP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The places, written out. -/
def ldLkpMaskTree_own : Prop :=
  ∀ (D : TreeP E) (l : ℕ) (j : D.J), D.ownAt l j ↔ (∃ i, j = D.wAt l i) ∨ ∃ b, j = D.cAt l b

/-- States: under the hypotheses below, the tree is a link of a chain of masked blocks. -/
def ldLkpMaskTree_link : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ)
      (Dt In Rd : D.J → Prop) (C : E × (D.lv 0).T.St → (D.J → E) → Prop),
    D.Step → D.MaskOK n Dt In → (∀ j, D.srAt Dt In n j → Rd j) →
    (∀ x k, C x k → D.sumAt 0 x k) → (∀ l ≤ n, MjStab C (D.ownAt l)) →
    (D.mjTree Ex M Wp Kc msg Rd n).Link (D.treeA Ex Wp Kc msg n).H (fun w => mjCut Rd (msg w.1))
      (fun w => mjCut Rd (msg w.1)) (fun j => ∃ l ≤ n, D.srAt Dt In l j)
      (fun j => ∃ l ≤ n, D.ownAt l j) C

/-- States: under the hypotheses below, the tree has the item "masked messages". -/
def ldLkpMaskTree_mm : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (n : ℕ) (Dt In Rd : D.J → Prop),
    D.Step → D.MaskOK n Dt In → (∀ j, D.srAt Dt In n j → Rd j) →
    (D.treeA Ex Wp Kc msg n).H.MM
      (((D.mjTree Ex M Wp Kc msg Rd n).narrow (D.sumAt 0)).data fun w => mjCut Rd (msg w.1))

/-- States: under the hypotheses below, what the honest run of the tree makes of a claim gives the
joint after the tree. -/
def ldLkpMaskTree_sound : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (Kc : Type) (A0 : Rels Kc (D.lv 0).T.St Ex ((D.J → E) × Unit))
      (n : ℕ) (Dt In Rd : D.J → Prop) (C : E × (D.lv 0).T.St → (D.J → E) → Prop),
    D.Step → D.MaskOK n Dt In → (∀ j, D.srAt Dt In n j → Rd j) → (∀ x k, C x k → D.sumAt 0 x k) →
    (∀ x k, C x k → mjClOf (D.jtAt (fun m => m) A0 0) x k) → (∀ l ≤ n, MjStab C (D.ownAt l)) →
    ∀ x' k, (D.mjTree Ex (D.J → E) Unit Kc (fun m => m) Rd n).sp C x' k →
      mjClOf (D.jtAt (fun m => m) A0 (n + 1)) x' k

end
end Cb.Spec
