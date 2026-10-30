-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbTower.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for a test of a group of oracle messages that is built of folds and code switches.

Definitions, theorems. Bookkeeping for the passage to one random oracle (`CtbSh`,
CompileK/ImplCountable.lean), as Cb/Obj/LdObjectCtb.lean, which has the base case alone.
A tower (`LdTower`, Cb/Ld/LdTower.lean) is a whole test built by recursion: a fold, then a code
switch, then a tower; at the end an end block. For `LdCode.FinNS` and native symbols see the head of
Cb/Obj/LdObjectCtb.lean.

Main names:
  `ctb_switch`: the code switch: a word under the new code, then the answers. Asked: a native symbol
    of the new code has finitely many coordinates, and the old code's long positions have a member
    (`Nonempty P`).
  `T.Ctb`, `ctb_tower`: a tower, any folds: by recursion: each fold's shape, each new code, the end
    block's shape.
  `T.FinT` (`LdTowC`), `ctb_towC`: a concrete tower (Cb/Obj/LdObjectTower.lean): cut, fold, switch,
    .., base case. Asked, by recursion, of codes alone: at each stage the code of the fresh mask and
    the new code, at the end the last code: a native symbol has finitely many coordinates
    (`LdCode.FinNS`).
  `T.FinT` (`LdTowG`), `ctb_towG`: the same on a group's complex (arrangement in front), whose long
    positions have a member (`Nonempty G.P`).
  `ctb_tow3`, `ctb_towG3`: the same for towers within a third of the distances
    (Cb/Obj/LdObjectTowerThird.lean).

`finNS_reading` (Cb/Obj/LdObjectCtbFin.lean) proves `FinNS` of a family of codes (`Code.Enc`) with
rows, under a reading.

Limits: on a protocol this file has two kinds of conditional conclusion: countability (as in
`ctb_switch`, `ctb_tower`, `ctb_towC`, `ctb_towG`) and, of the codes of a tower, `LdCode.FinNS`
(`finT_tow3`; a clause of `T.toTower.Ctb` in `ctb_towC'`: each from `T.FinT`); beyond these no
statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtb
import Cb.Obj.LdObjectPartReqCtb
import Cb.Obj.LdObjectTowerThird

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- The code switch. -/
theorem ctb_switch {P P' St : Type} [Fintype P] [Nonempty P]
    (D : LdSw E P P' St) (h : D.Cout.FinNS) : CtbSh (ldSwitch D).shape :=
  ⟨⟨inferInstanceAs (Countable D.Cout.NP), fun p => by
      haveI := h p
      exact inferInstanceAs (Countable (D.Cout.NS p → E)), inferInstanceAs (Countable Unit)⟩, ctb_plain (D.Zo.S → E) ((Fin D.t → P) × D.Zb.D) _ trivial⟩

/-- every fold's shape, every new code, the end block's shape -/
def LdTower.Ctb : {a : LdJoint E} → LdTower a → Prop
  | _, .base _ Z _ => CtbSh Z.R.shape
  | _, @LdTower.step _ _ _ _ _ _ _ _ D F _ _ rest => CtbSh F.R.shape ∧ D.Cout.FinNS ∧ rest.Ctb

theorem ctb_tower {a : LdJoint E} (T : LdTower a) : T.Ctb → CtbSh T.toEnd.R.shape := by
  induction T with
  | base a Z t => exact fun h => h
  | step a D F e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    show CtbSh ((F.R.shape ++ (ldSwitch D).shape) ++ rest.toEnd.R.shape)
    exact ctbSh_append (ctbSh_append h1 (ctb_switch D h2)) (ih h3)

/-- A concrete tower: what is asked of its codes. -/
def LdTowC.FinT : {a : LdJoint E} → LdTowC a → Prop
  | _, .base a _ _ _ _ _ => a.C.FinNS
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y _ _ S _ _ _ _ _ _ _ rest =>
    Y.Cw.FinNS ∧ S.Cnew.FinNS ∧ rest.FinT

theorem ctb_towC' {a : LdJoint E} (T : LdTowC a) : T.FinT → T.toTower.Ctb := by
  induction T with
  | base a t cov d bad L2 => exact fun h => ctb_base a t cov d bad L2 h
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ih h3⟩
    show CtbSh ([] ++ (Y.reform sl).ior.shape)
    exact ctb_sum (Y.reform sl) h1

/-- A concrete tower. -/
theorem ctb_towC {a : LdJoint E} (T : LdTowC a) (h : T.FinT) : CtbSh T.toEnd.R.shape :=
  ctb_tower T.toTower (ctb_towC' T h)

section
variable {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
  {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

/-- A concrete tower on a group's complex: what is asked of its codes. -/
def LdTowG.FinT : LdTowG G Sb sl Z → Prop
  | .plain T => T.FinT
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw _ _ _ _ _ _ _ rest =>
    Sh.par.Cw.FinNS ∧ Sw.Cnew.FinNS ∧ rest.FinT

/-- A concrete tower on a group's complex. -/
theorem ctb_towG (T : LdTowG G Sb sl Z) (h : T.FinT) : CtbSh T.toEnd.R.shape := by
  refine ctb_tower T.toTower ?_
  cases T with
  | plain T => exact ctb_towC' T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, h2, ctb_towC' rest h3⟩
    show CtbSh ([] ++ ([] ++ (Sh.par.reform (Sh.form Sb sl Z)).ior.shape))
    exact ctb_sum (Sh.par.reform (Sh.form Sb sl Z)) h1

end

/-- Within a third of the distances: the same conditions on codes. -/
def LdTow3.FinT : {a : LdJoint E} → LdTow3 a → Prop
  | _, .base a _ _ _ => a.C.FinNS
  | _, @LdTow3.step _ _ _ _ _ _ _ _ _ _ Y _ _ S _ _ _ rest => Y.Cw.FinNS ∧ S.Cnew.FinNS ∧ rest.FinT

theorem finT_tow3 {a : LdJoint E} (T : LdTow3 a) : T.FinT → T.toC.FinT := by
  induction T with
  | base a t cov d => exact fun h => h
  | step Y sl e S d e' d' rest ih => exact fun h => ⟨h.1, h.2.1, ih h.2.2⟩

theorem ctb_tow3 {a : LdJoint E} (T : LdTow3 a) (h : T.FinT) : CtbSh T.toC.toEnd.R.shape :=
  ctb_towC T.toC (finT_tow3 T h)

section
variable {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
  {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

def LdTowG3.FinT : LdTowG3 G Sb sl Z → Prop
  | .plain T => T.FinT
  | @LdTowG3.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw _ _ _ rest =>
    Sh.par.Cw.FinNS ∧ Sw.Cnew.FinNS ∧ rest.FinT

theorem ctb_towG3 (T : LdTowG3 G Sb sl Z) (h : T.FinT) : CtbSh T.toG.toEnd.R.shape := by
  refine ctb_towG T.toG ?_
  cases T with
  | plain T => exact finT_tow3 T h
  | shaped Sh Sw d e' d' rest => exact ⟨h.1, h.2.1, finT_tow3 rest h.2.2⟩

end
end
end Cb
