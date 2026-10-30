-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/TowerKnow.lean: the whole test (cut, fold, code switch, .., base case): round-by-round
knowledge soundness alone, from the premises of the library's own lemmas on knowledge soundness.

Definitions and statements; the proofs are in Cb/Ent/TowerKnowProofs.lean.
The library proves its towers as tails of a chain (`LdEnd.OK`, Cb/Ld/LdTower.lean: `TailTr`), a
bundle that holds completeness, zero knowledge and budgets of positions beside knowledge soundness,
and so asks for the honest side's conditions too. The clause on soundness is `know`; this file
states it alone, for THE SAME TERMS (no new tower, no new block, the same extractors, the same
errors), under records without `pack`, `zk`, `reads`, `priv`, `transp` (but see Limits on `Sh.OK`).
Left out with the honest side's conditions: `reads`, from which the library has the locality of the
switch's verifier.

Main names:
  `B.KnowT`, `Z.KnowT` (B : `LdBlock a b`, Z : `LdEnd a`): the clause `know` of `B.OK`, `Z.OK`, to
    the letter: `Reduction.Know` on all statements, from the relaxation of the joint a at its
    radius to that of b (to the trivial relation), with the block's own extractor and errors.
  `Y.HypK d e Lst mC mS mW`, `D.HypK e' L`, `a.BaseHypK d bad L2`: what is left of `SumPar.Hyp`,
    `LdSw.Hyp`, `LdJoint.BaseHyp`. Left out: the fold's packing and the fresh mask's encoding
    (`pack`, `zk`); the switch's `reads`, `priv`, `zk`; the base case's `transp`.
  `T.KnowOK` (T : `LdTower a`), `T.HypK` (T : `LdTowC a`, `LdTowG G Sb sl Z`): by recursion, as
    `LdTower.OK`, `LdTowC.Hyp`, `LdTowG.Hyp`.
  `Y.JohnK d e bC bZ bW`, `D.JohnK d' e'`, `T.JohnK` (T : `LdTowJ a`, `LdTowGJ G Sb sl Z`): the same
    for the records below the Johnson radius of Cb/Obj/LdObjectTowerJohn.lean: laws, distances,
    radii below the Johnson radius, agreement with counts; challenges, the degree of the round
    polynomials, the degrees of the public weights (`QwDeg`); sample and evader.
  `Spec.ldEnt_seq_know`, `Spec.ldEnt_cons_know`: two blocks in a row.
  `Spec.ldEnt_split_know`, `Spec.ldEnt_shape_know`: the two steps without rounds.
  `Spec.ldEnt_sum_know`, `Spec.ldEnt_sumAfter_know`, `Spec.ldEnt_group_know`,
  `Spec.ldEnt_switch_know`, `Spec.ldEnt_base_know`: the blocks.
  `Spec.ldEnt_tower_know`, `Spec.ldEnt_towC_know`, `Spec.ldEnt_towG_know`: towers, any radii.
  `Spec.ldEnt_towJ_know`, `Spec.ldEnt_towKnow`: towers below the Johnson radius; the second on a
    group's complex, its first stage on the group's shape. `Spec.ldEnt_towJ_hypK`,
    `Spec.ldEnt_towGJ_hypK`: there the blocks' conditions hold, the lists at the Johnson bounds.
  `Spec.ldEnt_hypK_of_hyp`, `Spec.ldEnt_johnK_of_john`: each new record follows from the library's.
  `Spec.ldEnt_know_of_ok`: the clause is the bundle's.

Limits: nothing on an honest prover: no completeness, no zero knowledge, no budget of
positions; nothing on locality or on what the verifier reads. Not that any tower meets `HypK` or
`JohnK`, or that the errors are small: lists and agreement (`ListAt`, `MCAat`, `MCArows`, `ErrOK`)
are conditions here, with any numbers; below the Johnson radius the lists are bounded by the
Johnson bound, a theorem of the library, and agreement stays a condition. `Know` with errors as
large as the numbers of verifier messages says nothing. Radii between the Johnson radius and
capacity: only in the general form (`HypK`), with the lists as conditions.
`Sh.OK` is kept whole (case `shaped`): of its clause `view` knowledge soundness uses two laws of
six, and its clause `one` is not used.
Nothing on the bridge in front of a test on a group (`LdRunD`, `PreJ`).
The theorem on codes, taken as given elsewhere (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean), does not
occur in this file: who has `MCArows` beyond a third of the distance is an instance's matter.

Terms: lean/GLOSSARY.md.

-/
import Cb.Obj.LdObjectTowerJohn

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-! ## The clause -/

section
variable {E : Type} [Field E] [Fintype E] {a b : LdJoint E}

/-- Round-by-round knowledge soundness of a block: the clause `know` of `B.OK t t'`. -/
def LdBlock.KnowT (B : LdBlock a b) : Prop :=
  B.R.red.Know a.rels.on a.rels.relR b.rels.relR B.ext B.N.err

/-- Round-by-round knowledge soundness of an end block: the clause `know` of `Z.OK t`. -/
def LdEnd.KnowT (Z : LdEnd a) : Prop :=
  Z.R.red.Know a.rels.on a.rels.relR trivRels.relR Z.ext Z.N.err

end

/-! ## The blocks' conditions -/

/-- The fold: `SumPar.Hyp` without `pack` and `zk`. -/
structure SumPar.HypK {E P : Type} [Field E] [Fintype E] [Fintype P] (Y : SumPar E P)
    (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) : Prop where
  codes : Spec.CodesOK E P Y.C Y.Z Y.Zw d e
  errs  : Y.ErrOK e Lst mC mS mW
  inj   : Function.Injective Y.val
  deg   : 2 ≤ Y.n
  qw    : Y.QwDeg

/-- The code switch: `LdSw.Hyp` without `reads`, `priv` and `zk`. -/
structure LdSw.HypK {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
    [Nonempty P'] (D : LdSw E P P' St) (e' L : ℕ) : Prop where
  laws : D.Cin.Laws
  list : D.Cout.ListAt e' L
  okO  : D.Zo.OK
  okB  : D.Zb.OK

/-- The base case: `LdJoint.BaseHyp` without `transp`. -/
structure LdJoint.BaseHypK {E : Type} [Field E] [Fintype E] (a : LdJoint E) (d bad L2 : ℕ) :
    Prop where
  laws : a.C.Laws
  lt   : a.e < d
  mca  : a.C.MCAat a.e bad
  list : (a.C.il Bool).ListAt a.e L2

/-! ## Towers, any radii -/

/-- The conditions on a tower with abstract folds: as `LdTower.OK`. -/
def LdTower.KnowOK {E : Type} [Field E] [Fintype E] : {a : LdJoint E} → LdTower a → Prop
  | _, .base _ Z _ => Z.KnowT
  | _, @LdTower.step _ _ _ _ _ _ _ _ D F e' L rest => F.KnowT ∧ D.HypK e' L ∧ rest.KnowOK

/-- The conditions on a concrete tower: as `LdTowC.Hyp`. -/
def LdTowC.HypK {E : Type} [Field E] [Fintype E] : {a : LdJoint E} → LdTowC a → Prop
  | _, .base a _ _ d bad L2 => a.BaseHypK d bad L2
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl e S d Lst mC mS mW e' L rest =>
    (Y.reform sl).HypK d e Lst mC mS mW ∧ (S.D e).HypK e' L ∧ rest.HypK

/-- The conditions on a concrete tower on a group's complex: as `LdTowG.Hyp`. -/
def LdTowG.HypK {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S}
    [Nonempty G.P] {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} :
    LdTowG G Sb sl Z → Prop
  | .plain T => T.HypK
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d Lst mC mS mW e' L rest =>
    Sh.OK ∧ Sh.par.HypK d G.e Lst mC mS mW ∧ (Sw.D G.e).HypK e' L ∧ rest.HypK

/-! ## Towers below the Johnson radius -/

/-- A fold below the Johnson radius: `SumPar.John` without `pack` and `zk`. -/
structure SumPar.JohnK {E P : Type} [Field E] [Fintype E] [Fintype P]
    (Y : SumPar E P) (d e bC bZ bW : ℕ) : Prop where
  lawsC : Y.C.Laws
  lawsZ : Y.Z.Laws
  lawsW : Y.Zw.Laws
  distC : Y.C.Dist d
  distZ : Y.Z.Dist d
  distW : Y.Zw.Dist d
  john  : InJohnson (Fintype.card P) d e
  mcaC  : Y.C.MCArows e bC
  mcaZ  : Y.Z.MCArows e bZ
  mcaW  : Y.Zw.MCArows e bW
  inj   : Function.Injective Y.val
  deg   : 2 ≤ Y.n
  qw    : Y.QwDeg

/-- A code switch into a code whose new radius lies below its Johnson radius: `LdSw.John` without
`reads`, `priv` and `zk`. -/
structure LdSw.JohnK {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
    [Nonempty P'] (D : LdSw E P P' St) (d' e' : ℕ) : Prop where
  lawsO : D.Cout.Laws
  distO : D.Cout.Dist d'
  john  : InJohnson (Fintype.card P') d' e'
  lawsI : D.Cin.Laws
  okO   : D.Zo.OK
  okB   : D.Zb.OK

/-- All radii below the Johnson radii: `LdTowJ.John` without the conditions that knowledge soundness
does not use. -/
def LdTowJ.JohnK {E : Type} [Field E] [Fintype E] : {a : LdJoint E} → LdTowJ a → Prop
  | _, .base a _ _ d b =>
    a.C.Laws ∧ a.C.Dist d ∧ InJohnson (Fintype.card a.P) d a.e ∧ a.C.MCAat a.e b
  | _, @LdTowJ.step _ _ _ _ _ _ _ _ _ _ Y sl e S d bC bZ bW e' d' rest =>
    (Y.reform sl).JohnK d e bC bZ bW ∧ (S.D e).JohnK d' e' ∧ rest.JohnK

/-- The same on a group's complex: `LdTowGJ.John` without the conditions that knowledge soundness
does not use (`Sh.OK` is kept whole). -/
def LdTowGJ.JohnK {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S}
    [Nonempty G.P] {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} :
    LdTowGJ G Sb sl Z → Prop
  | .plain T => T.JohnK
  | @LdTowGJ.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d bC bZ bW e' d' rest =>
    Sh.OK ∧ Sh.par.JohnK d G.e bC bZ bW ∧ (Sw.D G.e).JohnK d' e' ∧ rest.JohnK

/-! ## The statements -/

namespace Spec

/-- Two blocks in a row: errors in a row, extractors composed (both by the definition
`LdBlock.seq`). -/
def ldEnt_seq_know : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b c : LdJoint E) (B₁ : LdBlock a b) (B₂ : LdBlock b c),
    B₁.KnowT → B₂.KnowT → (B₁.seq B₂).KnowT

/-- A block, then an end block. -/
def ldEnt_cons_know : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E) (B : LdBlock a b) (Z : LdEnd b),
    B.KnowT → Z.KnowT → (B.cons Z).KnowT

/-- Cutting the form, a step without rounds (P not empty). -/
def ldEnt_split_know : Prop :=
  ∀ (E P St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C₁ C₂ : LdCode E P)
      (sl : Slf E St (C₁.J ⊕ C₂.J)) (e : ℕ),
    (ldSplit C₁ C₂ sl e).KnowT

/-- A reshape with its laws, a step without rounds (P not empty). -/
def ldEnt_shape_know : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C C' : LdCode E P)
      (ρ : Reshape C C') (St : Type) (s : Slf E St C.J) (e : ℕ),
    ρ.Laws → (ldShapeBlock ρ s e).KnowT

/-- The fold, at its own extractor; t enters the block's budget alone. -/
def ldEnt_sum_know : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P) (d e t : ℕ)
      (Lst mC mS mW : ℕ → ℕ),
    Y.HypK d e Lst mC mS mW → (ldSumBlock Y e (Y.ext d) t Lst mC mS mW).KnowT

/-- Cut, then fold. -/
def ldEnt_sumAfter_know : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P) (d e t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (St : Type) (sl : Slf E St Y.Cin.J),
    (Y.reform sl).HypK d e Lst mC mS mW →
    (ldSumAfter Y e t Lst mC mS mW sl ((Y.reform sl).ext d)).KnowT

/-- The first stage's fold on a group's complex: arrangement, cut, fold. -/
def ldEnt_group_know : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
      (d t : ℕ) (Lst mC mS mW : ℕ → ℕ),
    Sh.OK → Sh.par.HypK d G.e Lst mC mS mW → (Sh.block Sb sl Z d t Lst mC mS mW).KnowT

/-- The code switch; t' enters the block's budget alone. -/
def ldEnt_switch_know : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (e e' L t' : ℕ),
    D.HypK e' L → (ldSwBlock D e e' L t').KnowT

/-- The base case. -/
def ldEnt_base_know : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ),
    a.BaseHypK d bad L2 → (ldBaseEnd a t cov d bad L2).KnowT

/-- A tower with abstract folds. -/
def ldEnt_tower_know : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTower a), T.KnowOK → T.toEnd.KnowT

/-- A concrete tower, any radii: the whole test `T.toEnd`, its extractor, its errors. -/
def ldEnt_towC_know : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowC a), T.HypK → T.toEnd.KnowT

/-- A concrete tower on a group's complex, any radii. -/
def ldEnt_towG_know : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowG G Sb sl Z),
    T.HypK → T.toEnd.KnowT

/-- Below the Johnson radius the blocks' conditions hold, the lists at the Johnson bounds. -/
def ldEnt_towJ_hypK : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.JohnK → T.toC.HypK

/-- A tower below the Johnson radius: no condition on lists. -/
def ldEnt_towJ_know : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.JohnK → T.toC.toEnd.KnowT

/-- The same on a group's complex: the blocks' conditions. -/
def ldEnt_towGJ_hypK : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    T.JohnK → T.toG.HypK

/-- The whole test on a group's complex (`G.P` not empty), below the Johnson radius: round-by-round
knowledge soundness of `T.toG.toEnd`, the term of `Spec.ldTowGJ_tail`, with its extractor and its
errors. This is said under the hypotheses that stand in the statement itself, which this comment
does not list; it is no claim that they hold. -/
def ldEnt_towKnow : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    T.JohnK → T.toG.toEnd.KnowT

/-- The library's records give the new ones: concrete towers. -/
def ldEnt_hypK_of_hyp : Prop :=
  (∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowC a), T.Hyp → T.HypK) ∧
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowG G Sb sl Z),
    T.Hyp → T.HypK

/-- The library's records give the new ones: towers below the Johnson radius. -/
def ldEnt_johnK_of_john : Prop :=
  (∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.John → T.JohnK) ∧
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    T.John → T.JohnK

/-- The clause is the bundle's: a block that is a piece, an end block that is a tail, has it. -/
def ldEnt_know_of_ok : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a b : LdJoint E),
    (∀ (B : LdBlock a b) (t t' : ℕ), B.OK t t' → B.KnowT) ∧
    ∀ (Z : LdEnd a) (t : ℕ), Z.OK t → Z.KnowT

end Spec
end Cb
