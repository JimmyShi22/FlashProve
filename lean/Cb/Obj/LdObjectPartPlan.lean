-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartPlan.lean: for the toy object, a standard plan with its tests for the closing of
the test for linear constraints, over any test O: what is asked of plan and tests follows from
conditions on codes, two facts on O, and numbers (`D.Hyp`, `Nonempty P`,
`Nonempty (Fin O.Cf.C₀.n)`).

Definitions; the proofs are in Cb/Obj/LdObjectPartPlanProofs.lean. A tool for guards against empty
theorems; no parameter of a protocol.
`O : LdOL F E` (Cb/Obj/LdObjectLin.lean) has the oracle messages that were left before the test, a
function "rest" (`O.restM`) and a predicate "more" (`O.more`) of a claim and their messages. A plan
(`LdLinPl`, Cb/Ld/LdLinClosePlan.lean) names groups of the oracle messages at the end of the test.

Why any O: in the object the test's data are read off what comes before it, offline off the preamble
of weights-formedness (`LdOWf.O`, Cb/Obj/LdObjectWf.lean), online off the end of a request.
Cb/Obj/LdObjectLinStd2.lean builds a test of its own.

The data, `StdPO O P`:
  `slR`: "rest" as a linear form, with the claim as its state, on all entries of the messages that
    were left.
  `BM`, `rowsA`, `tgA`: "more" as finitely many rows on all these entries, with the claim as their
    state; their targets.
  `posAll`: how each oracle message at the end of the test is read at the common positions P. One
    set of positions, one joint radius `er`, one distance `d` for all: the case of equal base codes.
  `tb₁`, `tb₂`, `tb₃`: the numbers of positions that the three base cases draw.

The plan `D.pl` (without a splitting) and the tests `D.T`: three whole tests, each the base case on
the group's code complex (`Grp.C`), bridges with independent coefficients.
  First group: all oracle messages sent with G_u (`O.NU`) and with Ω (`O.NO`) (so all its members
    are shared in a batch). Kept: all but those sent with G_u.
  Second group: all that is kept (Ω's family, W's family `O.NW`, all that was left: `O.S`). Kept:
    all that was left.
  Third group (`D.G₃`; its test: `D.X`): all that was left, with all rows of "more"
    (Cb/Ld/LdLinClosePlanOne.lean). Nothing is kept.

Main names:
  `D.Hyp`: the two facts on O: `O.restM` is the value of `slR`; `O.more` says that the rows hold.
    Every oracle message, as read at the common positions: laws, distance `d`, transparent, `er`
    implies its own radius. `er` < `d`. Lists (`Lc`, `L2`) and exceptional coefficients (`bad`) of
    codes at these positions.

Limits: the senders are not built (a parameter of whoever uses the plan). The second group is wider
than this protocol's technical report (lean/CREDITS.md) has it (Ω, W and the message of index
masks): "rest" may read entries of several messages.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinFullProofs
import Cb.Obj.LdObjectWfRestProofs
import Cb.Ld.LdLinClosePlanOneProofs
import Cb.Obj.LdObjectLinStd2Proofs
import Cb.Ld.LdLinCloseDemandV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data of the standard plan over any test `O`. -/
structure StdPO {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E)
    (P : Type) [Fintype P] where
  slR    : Slf E O.Cl O.S.Ent
  BM     : Type
  [finBM : Fintype BM]
  rowsA  : BM → Slf E O.Cl O.S.Ent
  tgA    : O.Cl → BM → E
  posAll : ∀ o : O.toC.S.O, P → (O.toC.S.om o).P
  er  : ℕ
  tb₁ : ℕ
  tb₂ : ℕ
  tb₃ : ℕ
  d   : ℕ
  bad : ℕ
  L2  : ℕ
  Lc  : ℕ

attribute [instance] StdPO.finBM

/-- The names of what was sent with G_u; `isL`, below: of what was left. -/
def LdLinC.isU {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) : C.S.O → Prop
  | .inl (.inr _) => True
  | _ => False

instance {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) :
    DecidablePred C.isU := fun o => match o with
  | .inl (.inl _) => isFalse fun h => h
  | .inl (.inr _) => isTrue trivial
  | .inr _ => isFalse fun h => h

def LdLinC.isL {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) : C.S.O → Prop
  | .inl (.inl (.inl _)) => True
  | _ => False

instance {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) :
    DecidablePred C.isL := fun o => match o with
  | .inl (.inl (.inl _)) => isTrue trivial
  | .inl (.inl (.inr _)) => isFalse fun h => h
  | .inl (.inr _) => isFalse fun h => h
  | .inr _ => isFalse fun h => h

namespace StdPO
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {O : LdOL F E} {P : Type}
  [Fintype P] (D : StdPO O P)

/-- What is kept at the first bridge. -/
abbrev kp₁ : O.toC.S.O → Prop := fun o => ¬ O.toC.isU o

@[reducible] def G₁ : Grp O.toC.S :=
  { P := P, mem := O.toC.isSh, pos := fun a => D.posAll a.1, e := D.er }
@[reducible] def G₂ : Grp (O.toC.S.sub (kp₁ (O := O))) :=
  { P := P, mem := fun _ => True, pos := fun a => D.posAll a.1.1, e := D.er }

/-- The plan. -/
@[reducible] def pl : LdLinPl O.toC where
  G₁ := D.G₁
  hU := trivial
  hO := trivial
  kp₁ := kp₁
  kW := fun h => h
  kO := fun h => h
  G₂ := D.G₂
  hW₂ := trivial
  hO₂ := trivial
  kp₂ := fun a => O.toC.isL a.1
  restG := ((O.toC.upA D.slR).onSub kp₁).onG D.G₂

@[reducible] def G₃ : Grp D.pl.S₂ :=
  { P := P, mem := fun _ => True, pos := fun a => D.posAll a.1.1.1, e := D.er }

variable [Nonempty P]

/-- The third test: all rows of "more", on all that was left. -/
@[reducible] def X : LdRowsD D.pl.S₂ O.toC.E₀ O.toC.Wpa (D.pl.rowsL D.rowsA) where
  G := D.G₃
  neP := inferInstanceAs (Nonempty P)
  kp := fun _ => False
  decKp := fun _ => instDecidableFalse
  hc := fun _ => Or.inl trivial
  now := fun _ => True
  decNow := fun _ => instDecidableTrue
  Z := @Evader.indep E (D.G₃.Row {_b : D.BM // True}) _ _ _ (Classical.decEq _)
  T := ldBaseEnd _ D.tb₃ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L := D.Lc
  t := D.tb₃
  d := (fun _ => (fun _ => 0, fun _ => 0), ())
  d' := ((fun _ => 0, fun _ => 0), (fun a => a.2.elim, ()))

/-- The closing of what is left: the third test, then nothing. -/
def R : LdRowsQ D.pl.S₂ O.toC.E₀ O.toC.Wpa (D.pl.rowsL D.rowsA) D.tgA :=
  D.X.one D.tgA (fun a => a.2.elim, ())

/-- The tests. -/
@[reducible] def T : LdLinPlT D.pl where
  ne₁ := inferInstanceAs (Nonempty P)
  hc₁ := fun o => by
    rcases o with ((a | w) | u) | o
    · exact Or.inr fun h => h
    · exact Or.inr fun h => h
    · exact Or.inl trivial
    · exact Or.inl trivial
  Z₁ := @Evader.indep E (D.pl.G₁.Row O.toC.B₁) _ _ _ (Classical.decEq _)
  T₁ := ldBaseEnd _ D.tb₁ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L₁ := D.Lc
  t₁ := D.tb₁
  ne₂ := inferInstanceAs (Nonempty P)
  hc₂ := fun _ => Or.inl trivial
  Z₂ := @Evader.indep E (D.pl.G₂.Row LinB₂) _ _ _ (Classical.decEq _)
  T₂ := ldBaseEnd _ D.tb₂ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L₂ := D.Lc
  t₂ := D.tb₂
  Q' := D.R.Q
  fa := D.R.fx
  d₁ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₁' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))
  d₂ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₂' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))

omit [Nonempty P] in
/-- What is asked. -/
structure Hyp : Prop where
  rest : ∀ cl m, O.restM cl m = D.slR.val cl (O.S.ents m)
  more : ∀ cl m, O.more cl m ↔ rowsHold D.rowsA D.tgA cl (O.S.ents m)
  laws : ∀ o, ((O.toC.S.om o).C.atPos (D.posAll o)).Laws
  dist : ∀ o, ((O.toC.S.om o).C.atPos (D.posAll o)).Dist D.d
  tr   : ∀ o, ((O.toC.S.om o).C.atPos (D.posAll o)).Transparent
  fits : ∀ o (f g : (O.toC.S.om o).C.Word),
    ((O.toC.S.om o).C.atPos (D.posAll o)).Near D.er f g → (O.toC.S.om o).C.Near (O.toC.S.om o).e f g
  lt   : D.er < D.d
  lc   : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.er D.Lc
  l2   : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.er D.L2
  mca  : ∀ C : LdCode E P, C.Laws → C.MCAat D.er D.bad

end StdPO
end Cb
