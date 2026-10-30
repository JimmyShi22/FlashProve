-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Obj/LdObjectTower.lean: a concrete tower, any number of stages: a whole
test whose blocks are given by definitions, with its "OK" from the blocks' own hypotheses.

In standard terms: a whole test (`LdEnd`) is the data of a reduction from a claim on a word (it
encodes a message of which a linear claim holds) to the trivial statement, in the form of an
interactive oracle proof of proximity; what it is asked to have is `LdEnd.OK`. Here it is made of
concrete parts: folds, each followed by a switch to a new code, then a base case; `LdEnd.OK` follows
from the parts' own hypotheses (`T.Hyp`).

Definitions, statements and proofs.
The towers of Cb/Ld/LdTower.lean are generic in their blocks: the fold of a stage is any block with
a property, the end is any end block with a property. So "the whole test is a tower" says little by
itself. Here the blocks are put in:
  the end: the base case of Cb/Ld/LdBase.lean (`ldBaseEnd`), hypotheses `a.BaseHyp d bad L2`;
  a stage: "cut the one batched form in two, then the fold of Cb/Ld/LdSum*.lean" (`ldSumAfter`, with
    the fold's own backward extractor), hypotheses `SumPar.Hyp` (Cb/Ld/LdTowerSumMain.lean); then
    the code switch of Cb/Ld/LdSwitch.lean that starts where the fold ends (`ldSwAfter`), hypotheses
    `LdSw.Hyp`.

Main names:
  `LdTowC a`: a concrete tower at the joint a. `step`: at a joint whose code is the fold's input
    code (main table beside mask table) with one form sl on all its message coordinates; the rest of
    the tower is at the switch's output joint. The joints are part of the types, so only towers
    whose stages fit can be written down.
  `T.toEnd`, `T.q`: the whole test as one block to the trivial statement; the long positions of the
    input word that it needs.
  `T.Hyp`: by recursion: the base case's hypotheses; for each stage the fold's seven and the
    switch's seven, the latter at what the rest of the tower needs.
  `Spec.ldTowC_tail`: `T.Hyp` → `T.toEnd.OK T.q`: the whole test is a tail of a chain. What is left
    are conditions on codes (laws, distances, lists, agreement, hiding, reading, transparency), the
    challenges' map, the packing, samples, evaders and numbers.
  `Spec.ldTowC_run`: as `Spec.ldTowG_run` below, for a concrete tower: the same hypotheses (`T.Hyp`:
    the concrete tower's).
On a group's complex, `G.P` non-empty (the joint `G.joint Sb sl Z`, Cb/Ld/LdGroup.lean, at which a
bridge ends: Cb/Ld/LdBatSig.lean), the first stage needs the arrangement of Cb/Ld/LdGroupFold.lean
in front of its fold:
  `LdTowG G Sb sl Z`: `plain`: a concrete tower at that joint as it stands (the tower without a
    stage, the base case alone, is of this kind); `shaped`: a shape Sh of the group, the block
    "arrangement, cut, fold" (`Sh.block`), a switch after that fold, and a concrete tower after the
    switch.
  `T.Hyp`, shaped: `Sh.OK`, the fold's seven at the group's joint radius, the switch's seven, those
    of the rest of the tower.
  `Spec.ldTowG_tail`: `T.Hyp` → `T.toEnd.OK T.q`. `Spec.ldTowG_run`: one test on a group (`LdRunD`,
    Cb/Ld/LdLinCloseRuns.lean) whose whole test is such a tower, and whose number of positions is
    `T.q`, is OK from: the bridge's evader, the list of the complex, Fits, `T.Hyp`.

Notation: `bad`, `L2`: natural numbers (`a.BaseHyp d bad L2`, Cb/Ld/LdTower.lean, says that `bad`
bounds the count of agreement at the joint's radius, and `L2` the lists of `a.C.il Bool` there); `d`
(a stage), `Lst`, `mC`, `mS`, `mW`: a natural number and maps ℕ → ℕ (`SumPar.Hyp`,
Cb/Ld/LdTowerSumMain.lean, says, by `Spec.CodesOK`, Cb/Ld/LdSumStepStage.lean, `LdCode.Dist d` of
the fold's three codes and, by `SumPar.ErrOK`, Cb/Ld/LdSum.lean, for the j named there and at the
radius `e`, that after j rounds `Lst j` bounds the lists of the complex, and `mC j`, `mS j`, `mW j`
the three tables' counts of agreement); `e'`, `L` (a stage): natural numbers (Cb/Ld/LdTower.lean:
`e'` is the radius of the switch's output joint `LdSw.jOut e'`, and `LdSw.Hyp e' L t'` says that `L`
bounds the new code's lists there).

Limits: that `T.Hyp` can be met is not shown in this file. Guards, within a third, with a stage,
over p = 2^64 - 2^32 + 1: Cb/GlVal/GlGuardTower.lean; below the Johnson radius, under the statement
on codes (`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean): Cb/GlVal/GlGuardJohn.lean.
This file gives no bound on a list or on agreement: it asks for them (`T.Hyp`;
`D.G.C.ListAt D.G.e D.L` in `Spec.ldTowC_run`, `Spec.ldTowG_run`), their numbers are data of the
tower (`D.L`: of the test).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerSumMain
import Cb.Ld.LdTowerMain
import Cb.Ld.LdLinCloseRuns
import Cb.Ld.LdGroupFoldProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- A code switch after the fold Y: the data (`Qo`: the pad; `ts`: the number of positions). -/
structure LdSwD {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    (Y : SumPar E P) (P' : Type) where
  [finAa : Fintype Y.Cout.Aa]
  Cnew : LdCode E P'
  Qo : Type
  [finQo : Fintype Qo]
  [decQo : DecidableEq Qo]
  place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ Qo ≃ Cnew.J
  Zo : Ood.Sample E ((Y.Cout.J ⊕ Y.Cout.Q) ⊕ Qo)
  ts : ℕ
  Zb : Evader E (LdRow Zo.S ts Y.Cout.Aa)

attribute [instance] LdSwD.finQo LdSwD.decQo

/-- the switch -/
def LdSwD.D {E P P' : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    {Y : SumPar E P} (S : LdSwD Y P') (e : ℕ) : LdSw E P P' (Y.jOut e).St :=
  letI := S.finAa
  ldSwAfter Y e S.Cnew S.Qo S.place S.Zo S.ts S.Zb

/-- A concrete tower: the data. -/
inductive LdTowC {E : Type} [Field E] [Fintype E] : LdJoint E → Type 1
  | base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ) : LdTowC a
  | step {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P'] (Y : SumPar E P)
      (sl : Slf E St Y.Cin.J) (e : ℕ) (S : LdSwD (Y.reform sl) P') (d : ℕ) (Lst mC mS mW : ℕ → ℕ)
      (e' L : ℕ) (rest : LdTowC ((S.D e).jOut e')) :
      LdTowC (ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)

namespace LdTowC
variable {E : Type} [Field E] [Fintype E]

/-- The tower. -/
def toTower : {a : LdJoint E} → LdTowC a → LdTower a
  | _, .base a t cov d bad L2 => LdTower.base a (ldBaseEnd a t cov d bad L2) t
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl e S d Lst mC mS mW e' L rest =>
      LdTower.step (ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)
        (S.D e) (ldSumAfter Y e S.ts Lst mC mS mW sl ((Y.reform sl).ext d)) e' L rest.toTower

def toEnd {a : LdJoint E} (T : LdTowC a) : LdEnd a := T.toTower.toEnd
def q {a : LdJoint E} (T : LdTowC a) : ℕ := T.toTower.q

/-- The blocks' own hypotheses. -/
def Hyp : {a : LdJoint E} → LdTowC a → Prop
  | _, .base a _ _ d bad L2 => a.BaseHyp d bad L2
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl e S d Lst mC mS mW e' L rest =>
    (Y.reform sl).Hyp d e S.ts Lst mC mS mW ∧ (S.D e).Hyp e' L rest.q ∧ rest.Hyp

end LdTowC

/-- A concrete tower on a group's complex: the data. -/
inductive LdTowG {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S)
    [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) : Type 1
  | plain (T : LdTowC (G.joint Sb sl Z)) : LdTowG G Sb sl Z
  | shaped {P' : Type} [Fintype P'] [Nonempty P'] (Sh : GShape G) (Sw : LdSwD (Sh.fold Sb sl Z) P')
      (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L : ℕ) (rest : LdTowC ((Sw.D G.e).jOut e')) :
      LdTowG G Sb sl Z

namespace LdTowG
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

def toTower : LdTowG G Sb sl Z → LdTower (G.joint Sb sl Z)
  | .plain T => T.toTower
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d Lst mC mS mW e' L rest =>
      LdTower.step (G.joint Sb sl Z)
        (Sw.D G.e) (Sh.block Sb sl Z d Sw.ts Lst mC mS mW) e' L rest.toTower

def toEnd (T : LdTowG G Sb sl Z) : LdEnd (G.joint Sb sl Z) := T.toTower.toEnd
def q (T : LdTowG G Sb sl Z) : ℕ := T.toTower.q

def Hyp : LdTowG G Sb sl Z → Prop
  | .plain T => T.Hyp
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d Lst mC mS mW e' L rest =>
    Sh.OK ∧ Sh.par.Hyp d G.e Sw.ts Lst mC mS mW ∧ (Sw.D G.e).Hyp e' L rest.q ∧ rest.Hyp

end LdTowG

namespace Spec

def ldTowC_ok : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowC a), T.Hyp → T.toTower.OK

/-- States: a concrete tower is a tail of a chain, from the blocks' own hypotheses (`T.Hyp`). -/
def ldTowC_tail : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowC a), T.Hyp → T.toEnd.OK T.q

/-- One test on a group whose whole test is a concrete tower. -/
def ldTowC_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E)
      (D : LdRunD S) (T : LdTowC (D.G.joint D.Sb D.sl D.Z)),
    D.T = T.toEnd → D.t = T.q → D.Z.OK → D.G.C.ListAt D.G.e D.L → D.G.Fits → T.Hyp → D.OK

/-- States, for `G.P` non-empty and under `T.Hyp`: a concrete tower on a group's complex is a tail
of a chain. -/
def ldTowG_tail : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowG G Sb sl Z),
    T.Hyp → T.toEnd.OK T.q

def ldTowG_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (T : LdTowG D.G D.Sb D.sl D.Z),
    D.T = T.toEnd → D.t = T.q → D.Z.OK → D.G.C.ListAt D.G.e D.L → D.G.Fits → T.Hyp → D.OK

end Spec

theorem ldTowC_ok : Spec.ldTowC_ok := by
  intro E _ _ a T
  induction T with
  | base a t cov d bad L2 => exact fun h => ldTower_base E a t cov d bad L2 h
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨(ldTower_sum_after E _ Y e S.ts Lst mC mS mW _ sl ((Y.reform sl).ext d)
        (sumGood_of_hyp (Y.reform sl) d e S.ts Lst mC mS mW h1)).1,
      h2, ih h3⟩

theorem ldTowC_tail : Spec.ldTowC_tail := fun E _ _ a T h =>
  ldTower_tail E a T.toTower (ldTowC_ok E a T h)

theorem ldTowC_run : Spec.ldTowC_run := fun E _ _ _ D T hT ht hZ hL hF h =>
  ⟨hZ, hL, hF, by rw [hT, ht]; exact ldTowC_tail E _ T h⟩

theorem ldTowG_tail : Spec.ldTowG_tail := by
  intro E B _ _ _ S G _ Sb sl Z T h
  refine ldTower_tail E _ T.toTower ?_
  cases T with
  | plain T => exact ldTowC_ok E _ T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨(ldGroup_block E B S G Sh Sb sl Z d Sw.ts Lst mC mS mW h0 h1).1,
      h2,
      ldTowC_ok E _ rest h3⟩

theorem ldTowG_run : Spec.ldTowG_run := fun E _ _ S D T hT ht hZ hL hF h =>
  ⟨hZ, hL, hF, by rw [hT, ht]; exact ldTowG_tail E _ S D.G D.Sb D.sl D.Z T h⟩

end Cb
