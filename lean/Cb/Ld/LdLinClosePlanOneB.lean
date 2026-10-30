-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanOneB.lean: book-keeping for the last part of an interactive oracle proof that
proves several instances at once (a batch of at most N): the one proximity test of
Cb/Ld/LdLinClosePlanOne.lean (the rest of the plan without a splitting, with one group) is run once
for each instance.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanOneBProofs.lean.
It uses Cb/Ld/LdLinClosePlanOne.lean (the same for one instance: `X.one`),
Cb/Ld/LdBatchBlocksPlan.lean (a plan for a batch: `LdTcA`; knowledge soundness for vectors of
statements: `LdTcA.KB`), Cb/Ld/LdLinCloseVPlan.lean (the honest side of a batch on a plan: `LdTcV`),
Cb/Ld/LdLinCloseVLin.lean (the demand `p.qB₂` at the joint of what is left) and
Cb/Ld/LdLinCloseDemandV.lean (demands on families of positions). By composition only.
The honest side adds at each joint (`IOR.JV`, Cb/Ld/LdLinChainV.lean) a shared witness, a tie of
each slot's statement and witness to it, and a demand on families of positions.

Why: what the preamble left belongs to one slot (one instance of the batch). So the one test X on
all of it (`X : LdRowsD ..`, Cb/Ld/LdLinClosePlanRows.lean) is run in every slot, in that slot's
local rounds.

Main names:
  `X.oneA w₀`: the plan for a batch. Its plan is that of `X.one`, by definition
    (`Spec.ldRowsOneB_same`).
  `X.bOne N`: what it needs of each member of its group: `X.t` of a slot's own, N · X.t of a shared
    one (`needV`, Cb/Ld/LdLinCloseDemandV.lean).
  `X.oneV N q₀ w₀`: its honest side for a batch; the tie at the joint of what is left asks nothing.
  `Spec.ldRowsOneB_kb`: the annotated links are knowledge sound for every vector of statements (the
    trivial key; keys and `KB`, Cb/Ld/LdLinChainB.lean, are told in the head of
    Cb/Ld/LdLinClosePlanPB.lean).
  `Spec.ldRowsOneB_v`: the honest side is in order (`LdTcV.OK`, Cb/Ld/LdLinCloseVPlan.lean: every
    link is a piece; the annotations are coherent; the last demand holds of the empty family).
  Both from: X keeps nothing; the test's own hypotheses (`X.run.OK`); for `Spec.ldRowsOneB_v` also:
  q₀ holds of the empty set, and ι is not empty. Nothing else but whatever the arguments hold as
  proofs.

Limits: this file does not say what the closing says (one instance: Cb/Ld/LdLinClosePlanOne.lean's
three clauses hold of the same plan, under the premises of `Spec.ldRowsOne_three`). It says nothing
on several groups. It does not say that the hypotheses can be met together (`ldRowsOneB_kb` and
`ldRowsOneB_v` are used in the proof of `stdPO_partB`, Cb/Obj/LdObjectPartBatO.lean;
`ldRowsOneB_kb` also in that of
`ldObjRp_hyp`, Cb/Obj/LdObjectPpRows.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanOneProofs
import Cb.Ld.LdLinCloseVLinProofs
import Cb.Ld.LdBatchPlanLin
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdRowsD

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp Cl B : Type} [Fintype B]
  {rows : B → Slf E Cl S.Ent} (X : LdRowsD S E₀ Wp rows)

/-- The test X in every slot, then nothing. -/
def oneA (w₀ : (S.sub X.kp).Wit × Wp) : LdTcA S E₀ Wp :=
  LdTcA.consLo X.run (LdTcA.nil (S.sub X.kp) E₀ Wp w₀) X.d X.d'

end

variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] {C : LdLinC E ι κ J Y} {p : LdLinPl C} {Cl B : Type} [Fintype B]
  {rows : B → Slf E Cl p.S₂.Ent} (X : LdRowsD p.S₂ C.E₀ C.Wpa rows)

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- what it needs of each oracle message that is left -/
def bOne (N : ℕ) : p.S₂.O → ℕ := X.run.needV N (fun a => C.isSh a.1.1) fun _ => 0

/-- the demand on families of positions when nothing is left -/
def qEnd (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) :
    QFam (C.E₀.prod (p.S₂.sub X.kp).ext) N :=
  (p.S₂.sub X.kp).qV (fun a => C.isSh a.1.1.1) (QFam.each q₀) fun _ => 0

/-- Its honest side for a batch. -/
def oneV (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (w₀ : (p.S₂.sub X.kp).Wit × C.Wpa) :
    LdTcV N (X.oneA w₀) ⟨C.P.Sh6, fun _ _ _ _ => True, p.qB₂ N q₀ (X.bOne N)⟩ :=
  LdTcV.consLo X.run (LdTcA.nil (p.S₂.sub X.kp) C.E₀ C.Wpa w₀) X.d X.d'
    ⟨C.P.Sh6, fun _ _ _ _ => True, p.qB₂ N q₀ (X.bOne N)⟩ (fun _ _ _ _ => True) (X.qEnd N q₀)
    (LdTcV.nil (p.S₂.sub X.kp) C.E₀ C.Wpa w₀ _)

end LdRowsD

namespace Spec

/-- The plan for a batch has the plan of one instance. -/
def ldRowsOneB_same : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type)
      [Fintype B] (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E)
      (X : LdRowsD S E₀ Wp rows) (w₀ : (S.sub X.kp).Wit × Wp),
    (X.oneA w₀).Q = (X.one tg w₀).Q

/-- States: the annotated links are knowledge sound for every vector of statements, under the
premises below. -/
def ldRowsOneB_kb : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [Fintype B]
      (rows : B → Slf E Cl S.Ent) (X : LdRowsD S E₀ Wp rows) (w₀ : (S.sub X.kp).Wit × Wp) (N : ℕ),
    (∀ o, ¬ X.kp o) → X.run.OK → (X.oneA w₀).cA.KB N (ldKeyU _) ldKeyT

/-- States: the honest side is in order, under the premises below. -/
def ldRowsOneB_v : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
      [Fintype Y] (C : LdLinC E ι κ J Y) (p : LdLinPl C) (Cl B : Type) [Fintype B]
      (rows : B → Slf E Cl p.S₂.Ent) (X : LdRowsD p.S₂ C.E₀ C.Wpa rows)
      (w₀ : (p.S₂.sub X.kp).Wit × C.Wpa) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop),
    (∀ o, ¬ X.kp o) → X.run.OK → q₀ ∅ → (X.oneV N q₀ w₀).OK

end Spec
end Cb
