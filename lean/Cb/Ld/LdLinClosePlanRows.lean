-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanRows.lean: book-keeping for the last part of an interactive oracle proof. A
finite set of linear constraints (rows) on the messages that the prover's oracles encode is sorted
into sets, one for each group of oracles that one proximity test (a whole test) tests together.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanRowsProofs.lean.
It uses Cb/Ld/LdLinCloseChain.lean (whole tests in a row: `LdTc`), Cb/Ld/LdBatPeel.lean (forms on
all entries, read on a group and on the kept messages), Cb/Ld/LdLinCloseDemand.lean (positions add
up) and Cb/Ld/LdLinClosePlan.lean (the plan of the test for linear constraints).

Why: what a preamble leaves on its own oracle messages is a fixed finite family of rows: linear
forms on the entries of all messages, with forms and targets read off the claim. A test closes one
group and takes rows on that group's message.

Cl are the claims (the state of every row), B the names of the rows.

Main names:
  `R.Says` (R : `LdRowsQ`): the first joint of `R.Q`, at `R.fx cl`, says exactly "all rows hold": in
    the exact and in the relaxed form; it has no condition of its own.
  `X.Supp` (X : `LdRowsD`), the named condition: each row reads entries of one group: a row of this
    group vanishes outside the group; every other row vanishes outside what is kept.
  `Spec.ldRowsQ_nil`, `Spec.ldRowsQ_cons`: `Says`: for `LdRowsQ.nil`, where there is no row (B is
    empty); for `LdRowsQ.cons X rest` from `X.Supp` and `rest.Says`.
  `Spec.ldRowsQ_ok`: `(cons X rest).Q.OK` from `X.run.OK` and `rest.Q.OK`.
  `Spec.ldRowsQ_demand`: positions: if `rest.Q` needs at most b' and q₀, the closing needs at most
    `X.run.need b'` and q₀ (the rule of Cb/Ld/LdLinCloseDemand.lean at `X.run`): an oracle message
    that lies in several tests bears the sum.
  For the test for linear constraints (the plan without a splitting):
  `Spec.ldRowsQ_saysA`: if `C.Ab` says "all rows rowsA hold" (two clauses: exact, relaxed), every
    oracle message that a row reads is kept at both bridges, and R closes `p.rowsL rowsA` with
    `R.Says`, then `p.SaysA R.Q.base R.fx`: a hypothesis of `Spec.ldLinPlan_says`
    (Cb/Ld/LdLinClosePlan.lean) and `Spec.ldLinPlan_tail` (Cb/Ld/LdLinCloseDemand.lean).

Limits:
A warning on the named condition. `X.Supp` is asked at all claims, as `R.Says` is. Where the
coefficients of a row are free data of the claim (a preamble that stores its rows in the state),
`X.Supp` holds only if the type of the stored row says where the row may be non-zero (its places):
Cb/Ld/LdLinClosePlanRowsAt.lean proves both directions (`ldRowsAt_supp`, `ldRowsAt_only`), each
under its premises. So for rows that all have one type of places (the same places for every row),
the theorems of this file have content for one group only (a group in whose members every place
lies); with several groups their hypothesis (`X.Supp`, in `Spec.ldRowsQ_cons`) cannot be met, unless
every place lies in a member of each group that has a row (`now`). That a preamble's verifier puts
out rows with the right support does not help: it says nothing on other claims.
This file does not say that `X.Supp`, the tests' own hypotheses and `R.Says` can be met together at
a concrete code (no guard in this file). It says nothing on a row that reads entries of two groups:
a splitting comes first. It says nothing on how many groups there are: one application of cons for
each. It says nothing on the tests themselves.
The sorting of rows into tests restates a write-up of ours in our own
words (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinCloseDemandProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- All rows hold. -/
def rowsHold {E Cl B J : Type} [Field E] [Fintype J] (rows : B → Slf E Cl J)
    (tg : Cl → B → E) (cl : Cl) (u : J → E) : Prop :=
  ∀ b, (rows b).Holds (tg cl b, cl) u

/-- A closing for a family of rows: the data: Q (whole tests in a row: `LdTc`) and fx (how the
explicit part in front of Q is made from the claim). -/
structure LdRowsQ {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) {Cl B : Type}
    (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E) where
  Q  : LdTc S E₀ Wp
  fx : Cl → Q.St

/-- Its first joint says exactly: all rows hold. -/
structure LdRowsQ.Says {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp Cl B : Type}
    {rows : B → Slf E Cl S.Ent} {tg : Cl → B → E} (R : LdRowsQ S E₀ Wp rows tg) : Prop where
  rel  : ∀ cl y m wp, R.Q.base.rel (R.fx cl) y (m, wp) ↔ rowsHold rows tg cl (S.ents m)
  relR : ∀ cl y m wp, R.Q.base.relR (R.fx cl, y) (m, wp) ↔ rowsHold rows tg cl (S.ents m)
  on   : ∀ cl y, R.Q.base.on (R.fx cl, y)

/-- the case meant: no oracle message, no row (no condition of this definition; `Spec.ldRowsQ_nil`
takes `[IsEmpty B]`) -/
def LdRowsQ.nil {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) {Cl B : Type}
    (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E) (w₀ : S.Wit × Wp) : LdRowsQ S E₀ Wp rows tg :=
  ⟨LdTc.nil S E₀ Wp w₀, fun _ => ()⟩

/-- One more test: the data: the group G (it has a position: `neP`), what is kept (kp; every oracle
message is a member of G or kept: `hc`), which rows are this group's (now), the zero-evader, the
whole test, the bound on the list, the number of positions, and the values `d`, `d'`. -/
structure LdRowsD {E : Type} [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    {Cl B : Type} [Fintype B] (rows : B → Slf E Cl S.Ent) where
  G   : Grp S
  [neP : Nonempty G.P]
  kp  : S.O → Prop
  [decKp : DecidablePred kp]
  hc  : ∀ o, G.mem o ∨ kp o
  /-- the rows of this group -/
  now : B → Prop
  [decNow : DecidablePred now]
  Z   : Evader E (G.Row {b // now b})
  T   : LdEnd (G.joint (fun _ => Cl) (fun b : {b // now b} => (rows b.1).onG G) Z)
  L   : ℕ
  t   : ℕ
  d   : S.Wit × Wp
  d'  : LdBrW G kp Wp

attribute [instance] LdRowsD.decKp LdRowsD.decNow

namespace LdRowsD
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp Cl B : Type} [Fintype B]
  {rows : B → Slf E Cl S.Ent} (X : LdRowsD S E₀ Wp rows)

/-- the data of the test: its rows are the rows with "now", read on the group -/
@[reducible] def run : LdRunD S :=
  { G := X.G, neP := X.neP, kp := X.kp, hc := X.hc, B := {b // X.now b}, Sb := fun _ => Cl,
    sl := fun b => (rows b.1).onG X.G, Z := X.Z, T := X.T, L := X.L, t := X.t }

/-- the other rows, read on the kept messages -/
abbrev rest : {b // ¬ X.now b} → Slf E Cl (S.sub X.kp).Ent := fun b => (rows b.1).onSub X.kp

/-- Each row reads entries of one group. -/
structure Supp : Prop where
  mine  : ∀ b, X.now b → ∀ st (n : S.Ent), ¬ X.G.mem n.1 → rows b st n = 0
  other : ∀ b, ¬ X.now b → ∀ st (n : S.Ent), ¬ X.kp n.1 → rows b st n = 0

end LdRowsD

/-- The test X, then the closing of the other rows. -/
def LdRowsQ.cons {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
    {Wp Cl B : Type} [Fintype B] {rows : B → Slf E Cl S.Ent} {tg : Cl → B → E}
    (X : LdRowsD S E₀ Wp rows) (rest : LdRowsQ (S.sub X.kp) E₀ Wp X.rest fun cl b => tg cl b.1) :
    LdRowsQ S E₀ Wp rows tg :=
  ⟨LdTc.cons X.run rest.Q X.d X.d', fun cl => ((fun b => tg cl b.1, fun _ => cl), rest.fx cl)⟩

/-- a form on the entries of what the preamble left, as a form on all entries at the end of the test
for linear constraints -/
def LdLinC.upA {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y)
    {St : Type} (sl : Slf E St C.Sa.Ent) :
    Slf E St C.S.Ent := fun st n => match n with
  | ⟨.inl (.inl (.inl a)), j⟩ => sl st ⟨a, j⟩
  | ⟨.inl (.inl (.inr _)), _⟩ => 0
  | ⟨.inl (.inr _), _⟩ => 0
  | ⟨.inr _, _⟩ => 0

/-- the preamble's rows, read on the messages that are left after the plan's two tests -/
def LdLinPl.rowsL {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPl C)
    {B : Type} (rowsA : B → Slf E C.Sta C.Sa.Ent) : B → Slf E C.Sta p.S₂.Ent :=
  fun b => ((C.upA (rowsA b)).onSub p.kp₁).onSub p.kp₂

namespace Spec

def ldRowsQ_nil : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [IsEmpty B]
      (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E) (w₀ : S.Wit × Wp),
    (LdRowsQ.nil S E₀ Wp rows tg w₀).Says

/-- One more test: `Says` of `LdRowsQ.cons X rest`, from `X.Supp` and `rest.Says`. -/
def ldRowsQ_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [Fintype B]
      (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E) (X : LdRowsD S E₀ Wp rows)
      (rest : LdRowsQ (S.sub X.kp) E₀ Wp X.rest fun cl b => tg cl b.1),
    X.Supp → rest.Says → (LdRowsQ.cons X rest).Says

def ldRowsQ_ok : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [Fintype B]
      (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E) (X : LdRowsD S E₀ Wp rows)
      (rest : LdRowsQ (S.sub X.kp) E₀ Wp X.rest fun cl b => tg cl b.1),
    X.run.OK → rest.Q.OK → (LdRowsQ.cons X rest).Q.OK

def ldRowsQ_demand : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp Cl B : Type) [Fintype B]
      (rows : B → Slf E Cl S.Ent) (tg : Cl → B → E) (X : LdRowsD S E₀ Wp rows)
      (rest : LdRowsQ (S.sub X.kp) E₀ Wp X.rest fun cl b => tg cl b.1)
      (q₀ : Finset E₀.Pos → Prop) (b' : (S.sub X.kp).O → ℕ),
    (∀ V, rest.Q.q V → (S.sub X.kp).qFam q₀ b' V) →
    ∀ V, (LdRowsQ.cons X rest).Q.q V → S.qFam q₀ (X.run.need b') V

/-- "What is left says Ab", for the plan of the test for linear constraints, under the premises
below. -/
def ldRowsQ_saysA : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y) (p : LdLinPl C) (B : Type)
      (rowsA : B → Slf E C.Sta C.Sa.Ent) (tgA : C.Sta → B → E)
      (R : LdRowsQ p.S₂ C.E₀ C.Wpa (p.rowsL rowsA) tgA),
    (∀ sa y m wp, C.Ab.rel sa y (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ sa y m wp, C.Ab.relR (sa, y) (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ b st (a : C.Sa.O) j,
      rowsA b st ⟨a, j⟩ ≠ 0 → ∃ h : p.kp₁ (.inl (.inl (.inl a))), p.kp₂ ⟨_, h⟩) →
    R.Says → p.SaysA R.Q.base R.fx

end Spec
end Cb
