-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanOneP.lean: book-keeping for the last part of an interactive oracle proof. All
linear constraints (rows) that an earlier sub-protocol (the preamble) has left open are the input of
one more proximity test, after the three of the plan: for the plan of this protocol's technical
report (lean/CREDITS.md), "the rest" as one more test on one group.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanOnePProofs.lean.
They are the analogues, for the plan `LdLinPp` (Cb/Ld/LdLinClosePlanP.lean: three bridges come
before what closes the rest), of what Cb/Ld/LdLinClosePlanRows.lean, Cb/Ld/LdLinClosePlanOne.lean
and Cb/Ld/LdLinClosePlanOneB.lean have for the plan without a splitting (two bridges).
Generic in the signature, and so used as they are: closings of rows (`LdRowsQ`), `X.one`, `X.oneA`,
`ldRowsOneB_same`, `ldRowsOneB_kb`.
A closing of rows (`LdRowsQ`, Cb/Ld/LdLinClosePlanRows.lean) is a chain of reductions down to the
trivial statement, with a map from claims to its explicit part; `R.Says`: its first joint says, in
the exact and in the relaxed relation, exactly "all rows hold", and it has no condition of its own.
Ab is the base joint that a preamble leaves (`C.Ab`, Cb/Ld/LdLinClosePre.lean); "B' says Ab":
`LdLinPp.SaysA`, Cb/Ld/LdLinClosePlanP.lean.

Main names:
  `Spec.ldRowsQP_saysA`: a closing R of the rows `p.rowsL rowsA` that says exactly "all rows hold"
    says Ab (`p.SaysA R.Q.base R.fx`), if what the preamble left says exactly "the rows hold" (exact
    and relaxed) and what a row reads is kept at all three bridges, at every state.
  `Spec.ldRowsOneP_three`: for one test X on all that is left, with all rows: `p.SaysA`; the closing
    is in order (`Q.OK`); it needs at most `X.t` positions of each oracle message left. Asked
    besides: X keeps nothing; the conditions of `Spec.ldRowsQP_saysA` but for `R.Says`; `X.run.OK`;
    q₀ ∅.
  For a batch (the test runs in every slot): `X.bOneP N` (positions of a member of its group: N · t
    for a shared oracle message, t for a slot's own), `X.qEndP`, `X.oneVP N q₀ w₀` (its honest side;
    the tie behind the plan's third test: none; `IOR.JV.tie`, Cb/Ld/LdLinChainV.lean).
    `Spec.ldRowsOneP_v`: it is in order (`LdTcV.OK`), if X keeps nothing, `X.run.OK`, and q₀ ∅.

Limits: this file says nothing on several groups for what the preamble left, but for
`Spec.ldRowsQP_saysA`, which is stated, under the premises that its row above tells (`R.Says` among
them), for every closing `R : LdRowsQ ..` of the rows (Cb/Ld/LdLinClosePlanRows.lean, with its
warning on `X.Supp` under Limits). If a row also reads a message of the instance's group (the
message of index masks), this file does not say that this message is kept at the third bridge: the
condition on places (the third premise of `Spec.ldRowsQP_saysA`) asks it.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanP
import Cb.Ld.LdLinClosePlanOneBProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The rows that the preamble left, as rows on what is left after the three tests (`p.S₃`): read
through the three bridges. -/
def LdLinPp.rowsL {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPp C)
    {B : Type} (rowsA : B → Slf E C.Sta C.Sa.Ent) : B → Slf E C.Sta p.S₃.Ent :=
  fun b => (((C.upA (rowsA b)).onSub p.kp₁).onSub p.kp₂).onSub p.kp₃

namespace LdRowsD
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] {C : LdLinC E ι κ J Y} {p : LdLinPp C} {Cl B : Type} [Fintype B]
  {rows : B → Slf E Cl p.S₃.Ent} (X : LdRowsD p.S₃ C.E₀ C.Wpa rows)

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- the positions that the test in every slot needs -/
def bOneP (N : ℕ) : p.S₃.O → ℕ := X.run.needV N (fun a => C.isSh a.1.1.1) fun _ => 0

/-- the demand on families of positions when nothing is left -/
def qEndP (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) :
    QFam (C.E₀.prod (p.S₃.sub X.kp).ext) N :=
  (p.S₃.sub X.kp).qV (fun a => C.isSh a.1.1.1.1) (QFam.each q₀) fun _ => 0

/-- Its honest side for a batch. -/
def oneVP (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (w₀ : (p.S₃.sub X.kp).Wit × C.Wpa) :
    LdTcV N (X.oneA w₀)
      ⟨C.P.Sh6, fun _ _ _ _ => True,
        p.S₃.qV (fun a => C.isSh a.1.1.1) (QFam.each q₀) (X.bOneP N)⟩ :=
  LdTcV.consLo X.run (LdTcA.nil (p.S₃.sub X.kp) C.E₀ C.Wpa w₀) X.d X.d'
    ⟨C.P.Sh6, fun _ _ _ _ => True, p.S₃.qV (fun a => C.isSh a.1.1.1) (QFam.each q₀) (X.bOneP N)⟩
    (fun _ _ _ _ => True) (X.qEndP N q₀) (LdTcV.nil (p.S₃.sub X.kp) C.E₀ C.Wpa w₀ _)

end LdRowsD

namespace Spec

/-- States: a closing of the rows says Ab, under the premises below. -/
def ldRowsQP_saysA : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y) (p : LdLinPp C) (B : Type)
      (rowsA : B → Slf E C.Sta C.Sa.Ent) (tgA : C.Sta → B → E)
      (R : LdRowsQ p.S₃ C.E₀ C.Wpa (p.rowsL rowsA) tgA),
    (∀ sa y m wp, C.Ab.rel sa y (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ sa y m wp, C.Ab.relR (sa, y) (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ b st (a : C.Sa.O) j, rowsA b st ⟨a, j⟩ ≠ 0 →
      ∃ (h₁ : p.kp₁ (.inl (.inl (.inl a)))) (h₂ : p.kp₂ ⟨_, h₁⟩), p.kp₃ ⟨⟨_, h₁⟩, h₂⟩) →
    R.Says → p.SaysA R.Q.base R.fx

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The three clauses that the plan asks of "the rest", for one test on all that is left.
(not all hypotheses are named here: see the statement below) -/
def ldRowsOneP_three : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (B : Type) [Fintype B] (rowsA : B → Slf E C.Sta C.Sa.Ent)
      (tgA : C.Sta → B → E) (X : LdRowsD p.S₃ C.E₀ C.Wpa (p.rowsL rowsA))
      (w₀ : (p.S₃.sub X.kp).Wit × C.Wpa) (q₀ : Finset C.E₀.Pos → Prop),
    (∀ b, X.now b) → (∀ o, ¬ X.kp o) →
    (∀ sa y m wp, C.Ab.rel sa y (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ sa y m wp, C.Ab.relR (sa, y) (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ b st (a : C.Sa.O) j, rowsA b st ⟨a, j⟩ ≠ 0 →
      ∃ (h₁ : p.kp₁ (.inl (.inl (.inl a)))) (h₂ : p.kp₂ ⟨_, h₁⟩), p.kp₃ ⟨⟨_, h₁⟩, h₂⟩) →
    X.run.OK → q₀ ∅ →
    p.SaysA (X.one tgA w₀).Q.base (X.one tgA w₀).fx ∧
    (X.one tgA w₀).Q.OK ∧
    ∀ V, (X.one tgA w₀).Q.q V → p.S₃.qFam q₀ (fun _ => X.t) V

/-- States: the honest side for a batch is in order, under the premises below. -/
def ldRowsOneP_v : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (Cl B : Type) [Fintype B]
      (rows : B → Slf E Cl p.S₃.Ent) (X : LdRowsD p.S₃ C.E₀ C.Wpa rows)
      (w₀ : (p.S₃.sub X.kp).Wit × C.Wpa) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop),
    (∀ o, ¬ X.kp o) → X.run.OK → q₀ ∅ → (X.oneVP N q₀ w₀).OK

end
end Spec
end Cb
