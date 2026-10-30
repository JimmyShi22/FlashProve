-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTreeP.lean: the product tree built from the zero-knowledge sumcheck and the line step:
nothing about them is assumed.
This file is about a product argument by a binary tree: a claim on level l is reduced to a claim on
level l + 1 by one sumcheck and one step in which the verifier draws a point on a line.

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpTreePProofs.lean.
Cb/Ld/LdLkpTree.lean has the tree with the sumcheck of each level as a hypothesis, in records of its
own. Here the tree is built with the records of Cb/Ld/LdPsc.lean (`PscOur`: the sumcheck for a
polynomial summand, with a dummy last variable) and Cb/Ld/LdLine.lean (`LineCube`: two value rows
into the next sum claim), whose theorems are used.

The objects. A forest of 2^g trees; level l is a table U l on the cube of g + l variables. The
levels are functions of a public state and of the entries m : J → E of the messages; nobody sends
them.
  `TreeP`: the data: states St0, entries J, g, the levels U, the incoming form of level 0 as a
    reader `inc0` of state and point (no form stands in a state: a state with an arbitrary form
    could read a level's own masks, and the item "masked messages", which is asked at all states,
    would fail), and where the masks of level l stand among the entries: `wAt l` (the coefficients
    of the hiding polynomial), `cAt l` (one inner mask for each of the two values); and the order
    of the rounds: the j-th variable of level l is coordinate `sg l` j (`sg l`: a permutation; by
    default the identity).
  `D.Step`: the one condition: U l x = U (l+1) (x, false) · U (l+1) (x, true), for all l. (Above the
    leaves of a tree with n levels: the lower half of level l + 1 is level l, the upper half is 1.)
  `D.lv l`: the sumcheck of level l, `(D.lv l).T : PscOur`: g + l variables, the j-th with the
    equality weight at coordinate `sg l` j of the current point; summand Y₀ Y₁ on the two halves of
    level l + 1, both revealed, each under a mask of its own; degree 2 in every variable and in the
    dummy. Its state: at level 0 (state, point of g coordinates); at level l + 1 (the output of the
    sumcheck of level l, ρ): states are nested. Readers: base (the public state), pnt (the current
    point), gam (the point at which the sumcheck ended), both by coordinate, toJ, two.
  `D.cube l`: the line step after level l (`LineCube`).
  `D.ride A0 l`: what rides along at level l: the joint A0 with which the tree was entered, and the
    rows on the hiding polynomials' coefficients of all levels below l.
  `D.jtAt A0 l`: the joint at level l, at the base: the true sum claim of the level's sumcheck, and
    what rides along.
  `BkA`, `BkA.Good`, `BkA.seq`, `BkA.chain`: blocks at the base (the tuple m of messages is a part
    of the witness: `H : R.Honest (M × Wp) (M × Wp)`; Cb/Ld/LdSigLift.lean); good = `GoodAt`
    (Cb/Ld/LdSigLift.lean: knowledge sound for each fixed tuple of messages) with the identity as
    extractor.

`Cb.GoodAt` asks, of a reduction with its honest side between two joints whose witnesses pair a
value of one type M with a further witness, the clauses of `GoodB` with two differences: a further
clause `same` asks that, on every run, the honest prover's output witness carries the M-part of its
input witness unchanged; and the clause `know`, in place of `GoodB`'s, asks, for each fixed m of
type M, round-by-round knowledge soundness (`Know`) on the input joint's set of statements and at
the numbers' list of errors, as `GoodB`'s does, but between the relaxed relations at (m, ·) and with
the extractor `ext m`. `GoodB` is `IOR.GoodT` without its clause on zero knowledge. Here `GoodAt`
stands, through `BkA.Good`, as the conclusion of `Spec.ldLkpP_level` and `Spec.ldLkpP_tree`, and as
premise and conclusion of `Spec.ldLkpP_chain`; `GoodB` is the conclusion of `Spec.ldLkpP_tree_sig`.

Main names:
  `Spec.ldLkpP_chain`: the rule: if block l leads from joint l to joint l + 1, for l ≤ n, the chain
    leads from joint 0 to joint n + 1.
  `Spec.ldLkpP_sum`: what the joint says (under `D.Step`): the sum claim of level l holds if and
    only if (multilinear extension of U l at the current point) + (incoming form at the entries) =
    target.
  `Spec.ldLkpP_ok`: every level's sumcheck meets the conditions of its theorem: variables, challenge
    sets, degrees.
  `Spec.ldLkpP_halves`: (under `D.Step`) every line step meets its condition: the two revealed maps
    are the halves of the table of the next summand.
  `Spec.ldLkpP_level`: (under `D.Step`) one level leads from `D.jtAt A0 l` to `D.jtAt A0 (l + 1)`.
  `Spec.ldLkpP_tree`: the tree, at the base: under `D.Step` alone, the levels 0, .., n lead from
    `D.jtAt A0 0` to `D.jtAt A0 (n + 1)`: `GoodAt`: strings (`point`), local (`isLocal`), perfectly
    complete, nothing withheld, knowledge sound for each fixed tuple of messages, the identity
    extracts.
  `Spec.ldLkpP_tree_sig`: over a signature (`Sig`, Cb/Ld/LdSig.lean: the oracle messages of a
    statement: a finite type of names, with the data of an oracle message for each; not a digital
    signature) of oracle messages with samples, under `D.Step`: `IOR.GoodB` (above) from
    `S.over (D.jtAt A0 0)` to `S.over (D.jtAt A0 (n + 1))`.
  `Spec.ldLkpP_rounds`: rounds: the sum over the levels l ≤ n of (g + l + 3) + 1. Nothing is merged.

Limits: that the first g coordinates name the tree is a choice of this file. The new coordinate of a
line step is the last one: the top bit, if coordinate i is read as bit i.
This file says nothing on zero knowledge: the item "masked messages" of each sumcheck stands
elsewhere (Cb/Ld/LdPscZk.lean); for the chain it is not stated here; that the places `wAt l`,
`cAt l` are pairwise different and used by nothing else is not asked here.
How level 0 gets its point and its incoming form, and what is done with the claim at the top, is not
here.
Errors are the blocks' errors in a row (1; 2 for each variable; 2 of |E| - 1 for the dummy; 0; 1 for
ρ), by definition of the numbers.
The tree with one sumcheck and one line step a level is the field's; the sumcheck follows the paper
that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLine
import Cb.Ld.LdZeroAt
import Cb.Ld.LdBattKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

/-- A block at the base, with its data; the kind of explicit part may change. -/
structure BkA (K M Xi Xo : Type) (Ex : ExtSpec) (Wp : Type) where
  R : IOR Xi Ex Xo Ex
  H : R.Honest (M × Wp) (M × Wp)
  P : Nums K R

namespace BkA
variable {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type}

/-- Good: for each fixed tuple of messages; the identity extracts. -/
def Good (b : BkA K M X₁ X₂ Ex Wp) (A : Rels K X₁ Ex (M × Wp)) (B : Rels K X₂ Ex (M × Wp)) : Prop :=
  GoodAt b.R b.H A B (fun _ _ _ wp => wp) b.P

def seq (a : BkA K M X₁ X₂ Ex Wp) (b : BkA K M X₂ X₃ Ex Wp) : BkA K M X₁ X₃ Ex Wp :=
  ⟨a.R.seq b.R, a.H.seq b.H, a.P.seq b.P⟩

/-- The blocks b 0, .., b n in a row. -/
def chain (X : ℕ → Type) (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) :
    ∀ n, BkA K M (X 0) (X (n + 1)) Ex Wp
  | 0 => b 0
  | n + 1 => (chain X b n).seq (b (n + 1))

end BkA
end Cb

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section

structure TreeP (E : Type) [Field E] [Fintype E] where
  St0 : Type
  J : Type
  [finJ : Fintype J]
  g : ℕ
  U : St0 → (J → E) → (l : ℕ) → (Fin (g + l) → Bool) → E
  /-- The incoming form of level 0, read off the state and the point. -/
  inc0 : St0 → (Fin (g + 0) → E) → J → E
  wAt : (l : ℕ) → PIdx (List.replicate (g + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cAt : ℕ → Bool → J
  /-- the order of the rounds: the j-th variable of level l's sumcheck (j from 0, in the order of
  their rounds) is coordinate sg l j; by default the j-th variable is coordinate j -/
  sg : (l : ℕ) → Equiv.Perm (Fin (g + l)) := fun _ => Equiv.refl _

attribute [instance] TreeP.finJ

variable {E : Type} [Field E] [Fintype E]

namespace TreeP
variable (D : TreeP E)

def Step : Prop :=
  ∀ st m l (x : Fin (D.g + l) → Bool), D.U st m l x =
    D.U st m (l + 1) (Fin.snoc x false : Fin (D.g + l + 1) → Bool) *
      D.U st m (l + 1) (Fin.snoc x true : Fin (D.g + l + 1) → Bool)

/-- The extension of a half of level l + 1. -/
def half (st : D.St0) (m : D.J → E) (l : ℕ) (b : Bool) : (Fin (D.g + l) → E) → E :=
  Alg.mle fun x : Fin (D.g + l) → Bool => D.U st m (l + 1) (Fin.snoc x b : Fin (D.g + l + 1) → Bool)

structure Lv (k : ℕ) where
  T : PscOur E
  toJ : T.J → D.J
  gam : T.par.Out → Fin k → E
  base : T.St → D.St0
  pnt : T.St → Fin k → E
  two : Bool → T.A

/-- the point of a state of level 0, in the order of the rounds: entry j is coordinate sg 0 j -/
def z0 (s : D.St0 × (Fin (D.g + 0) → E)) : Fin (D.g + 0) → E := fun j => s.2 (D.sg 0 j)

def T0 : PscOur E where
  St := D.St0 × (Fin (D.g + 0) → E)
  J := D.J
  fmt := List.replicate (D.g + 0) (pfCube E 2)
  dat := fun s => pdEqs E 2 (D.g + 0) (D.z0 s)
  A := Bool
  B := Empty
  F := fun s m b X => D.half s.1 m 0 b fun i =>
    hFnOf (pfCube E 2) (D.g + 0) (pdEqs E 2 (D.g + 0) (D.z0 s)) X ((D.sg 0).symm i)
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false * v true
  S1 := fun _ _ _ b => b.elim
  DY := 2
  slS := fun s => D.inc0 s.1 s.2
  wAt := D.wAt 0
  cAt := D.cAt 0

def lv0 : D.Lv (D.g + 0) where
  T := D.T0
  toJ := id
  gam := fun o i =>
    hFnOf (pfCube E 2) (D.g + 0) (pdEqs E 2 (D.g + 0) (D.z0 o.st))
      (D.T0.ini o.st (D.T0.par.hp o.st o.pt)) ((D.sg 0).symm i)
  base := fun s => s.1
  pnt := fun s => s.2
  two := id

def cubeOf (l : ℕ) (L : D.Lv (D.g + l)) : LineCube E where
  P := L.T
  a := L.two
  k := D.g + l
  gam := L.gam
  J := D.J
  jm := L.toJ
  n := 2
  A := Bool
  B := Empty
  F := fun o m b x => D.half (L.base o.st) m (l + 1) b x
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false * v true
  S1 := fun _ _ _ b => b.elim
  DY := 2
  wAt := D.wAt (l + 1)
  cAt := D.cAt (l + 1)
  sg := D.sg (l + 1)

def lvS (l : ℕ) (L : D.Lv (D.g + l)) : D.Lv (D.g + (l + 1)) where
  T := (D.cubeOf l L).next
  toJ := id
  gam := fun o i =>
    hFnOf (pfCube E 2) (D.g + l + 1) (pdEqs E 2 (D.g + l + 1) ((D.cubeOf l L).ptS o.st))
      ((D.cubeOf l L).next.ini o.st ((D.cubeOf l L).next.par.hp o.st o.pt)) ((D.sg (l + 1)).symm i)
  base := fun s => L.base s.1.st
  pnt := fun s => (D.cubeOf l L).pt s
  two := id

def lv : (l : ℕ) → D.Lv (D.g + l)
  | 0 => D.lv0
  | l + 1 => D.lvS l (lv l)

abbrev cube (l : ℕ) : LineCube E := D.cubeOf l (D.lv l)


/-! ### joints and blocks at the base -/
section Base
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)

/-- The entries in the naming of level l. -/
def msgAt (l : ℕ) : M → (D.lv l).T.J → E := fun ms j => msg ms ((D.lv l).toJ j)

variable {Ex M Wp Kc}

/-- What rides along after the sumcheck of level l: what rode before, and the row on the hiding
polynomial's coefficients. -/
def afterU (l : ℕ) (A : Rels Kc (D.lv l).T.St Ex (M × Wp)) :
    Rels Kc (D.lv l).T.par.Out Ex (M × Wp) :=
  ⟨fun o y w => A.rel o.st y w ∧ (D.lv l).T.par.UHolds o (D.msgAt M msg l w.1),
    fun a w => A.relR (a.1.st, a.2) w ∧ (D.lv l).T.par.UHolds a.1 (D.msgAt M msg l w.1),
    fun a => A.on (a.1.st, a.2),
    A.core⟩

/-- What rides along at level l. -/
def ride (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) : (l : ℕ) → Rels Kc (D.lv l).T.St Ex (M × Wp)
  | 0 => A0
  | l + 1 => (D.cube l).toLine.toIn.ride (D.afterU msg l (ride A0 l))

/-- The joint at level l: the sum claim of the level's sumcheck, and what rides along. -/
def jtAt (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (l : ℕ) :
    Rels Kc (E × (D.lv l).T.St) Ex (M × Wp) :=
  (D.lv l).T.baseIn (D.ride msg A0 l) fun w => D.msgAt M msg l w.1


variable (Ex Wp Kc) in
/-- The sumcheck of level l. -/
def pscA (l : ℕ) : BkA Kc M (E × (D.lv l).T.St) (D.lv l).T.par.Out Ex Wp :=
  ⟨(D.lv l).T.par.psc Ex,
    (D.lv l).T.par.hon Ex fun w => D.msgAt M msg l w.1,
    (D.lv l).T.par.nums Ex Kc⟩

variable (Ex M Wp Kc) in
/-- The line step after level l. -/
def lineA (l : ℕ) : BkA Kc M (D.lv l).T.par.Out (E × (D.lv (l + 1)).T.St) Ex Wp :=
  ⟨IOR.draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex,
    Honest.draw (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (M × Wp),
    Nums.draw Kc (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX
      Ex (D.cube l).toLine.toIn.ev.err⟩

variable (Ex Wp Kc) in
/-- One level. -/
def levA (l : ℕ) : BkA Kc M (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex Wp :=
  (D.pscA Ex Wp Kc msg l).seq (D.lineA Ex M Wp Kc l)

variable (Ex Wp Kc) in
/-- The tree: the levels 0, .., n. -/
def treeA (n : ℕ) : BkA Kc M (E × (D.lv 0).T.St) (E × (D.lv (n + 1)).T.St) Ex Wp :=
  BkA.chain (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg) n

end Base
end TreeP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

def ldLkpP_chain : Prop :=
  ∀ (K M : Type) (Ex : ExtSpec) (Wp : Type) (X : ℕ → Type)
      (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (A : ∀ l, Rels K (X l) Ex (M × Wp)) (n : ℕ),
    (∀ l ≤ n, (b l).Good (A l) (A (l + 1))) → (BkA.chain X b n).Good (A 0) (A (n + 1))

section
variable (E : Type) [Field E] [Fintype E]

/-- What the joint at level l says. -/
def ldLkpP_sum : Prop :=
  ∀ (D : TreeP E), D.Step →
    ∀ (l : ℕ) (x : E × (D.lv l).T.St) (m : D.J → E),
      (D.lv l).T.SumHolds x (fun j => m ((D.lv l).toJ j)) ↔
      Alg.mle (D.U ((D.lv l).base x.2) m l) ((D.lv l).pnt x.2) +
          ∑ j, (D.lv l).T.slS x.2 j * m ((D.lv l).toJ j) = x.1

def ldLkpP_ok : Prop :=
  ∀ (D : TreeP E) (l : ℕ), (D.lv l).T.VarsOK ∧ (D.lv l).T.ValInj ∧ (D.lv l).T.DegX ∧ (D.lv l).T.DegY

def ldLkpP_halves : Prop := ∀ (D : TreeP E), D.Step → ∀ l, (D.cube l).Halves

def ldLkpP_level : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (l : ℕ),
    D.Step → (D.levA Ex Wp Kc msg l).Good (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1))

/-- The tree, at the base. -/
def ldLkpP_tree : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (n : ℕ),
    D.Step → (D.treeA Ex Wp Kc msg n).Good (D.jtAt msg A0 0) (D.jtAt msg A0 (n + 1))

/-- The tree over a signature (`GoodB`, Ior/Masked.lean; `Sig`, Cb/Ld/LdSig.lean), under `D.Step`.
-/
def ldLkpP_tree_sig : Prop :=
  ∀ (D : TreeP E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) (msg : S.Msg → D.J → E)
      (A0 : Rels Kc (D.lv 0).T.St E₀ (S.Msg × Wp)) (n : ℕ),
    D.Step →
    GoodB ((D.treeA E₀ Wp Kc msg n).R.keep S.Smp S.ext) (S.liftH (D.treeA E₀ Wp Kc msg n).H)
      (S.over (D.jtAt msg A0 0)) (S.over (D.jtAt msg A0 (n + 1))) (fun _ _ w => w)
      ((D.treeA E₀ Wp Kc msg n).P.keep S.Smp S.ext)

def ldLkpP_rounds : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ),
    (D.treeA Ex Wp Kc msg n).R.shape.length = ∑ l ∈ Finset.range (n + 1), (D.g + l + 3 + 1)

end
end Cb.Spec
