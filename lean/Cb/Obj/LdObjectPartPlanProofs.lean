-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartPlanProofs.lean: what the standard plan over any test O
(Cb/Obj/LdObjectPartPlan.lean) has, from `D.Hyp` and the two conditions of non-emptiness named
below.

The closing of a test for linear constraints is a chain of whole tests on groups of oracle messages,
down to the trivial statement; a plan says which groups it tests, in which order, and what is kept
after each test. This file proves what is asked of such a closing, for the standard plan with three
tests.
Statements are the theorems' own texts (tools for toys). All but the first two also take the set P
of common positions to be non-empty (`Nonempty P`): the tests are defined under it.

Main names:
  `stdPO_shared` (no hypothesis beside whatever the arguments hold as proofs): all members of the
    first group are shared oracle messages.
  `stdPO_rest` (from `D.Hyp`): `restG`, the plan's form on the second group's message, is "rest",
    the test's function `O.toC.rest` of the state and of the messages left (`Spec.ldRest_is`,
    Cb/Obj/LdObjectWfRest.lean; in this plan every oracle message that was left is kept at the first
    bridge and is a member of the second group).
  `stdPO_d1`, `stdPO_d2`, `stdPO_d3` (from `D.Hyp`): the three tests meet their conditions
    (`D.T.D₁.OK`, `D.T.D₂.OK`, `D.X.run.OK`).
  `stdPO_three` (from `D.Hyp` and `Nonempty (Fin O.Cf.C₀.n)`): what is left says `O.toC.Ab`, the
    base joint that the preamble leaves (`D.pl.SaysA`: `LdLinPl.SaysA`, Cb/Ld/LdLinClosePlan.lean);
    its closing meets its conditions (`D.R.Q.OK`); it needs at most tb₃ long positions of each
    oracle message left, nothing of further oracles (Cb/Ld/LdLinClosePlanOne.lean).
  `stdPO_says`, `stdPO_q` (from the same two): so the plan says the rows and `Ab` (`O.toC.Says`:
    `LdLinC.Says`, Cb/Ld/LdLinClosePre.lean); the plan meets its conditions (`D.T.Q.OK`).
  `stdPO_needA`, `stdPO_needW`, `stdPO_needU`, `stdPO_needO` (no hypothesis beside `Nonempty P` and
    whatever the arguments hold as proofs): what the three tests need of an oracle message: left
    (`O.toC.Sa`): tb₂ + tb₃; sent with W (`O.toC.NW`): tb₂; with G_u (`O.toC.NU`): tb₁; with Ω
    (`O.toC.NO`): tb₁ + tb₂.

Notation: W, G_u, Ω (the head of Cb/Ld/LdLin.lean): the members `iW`, `iU`, `iO` of the three
families that the test sends (`NW`, `NU`, `NO`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartPlan
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {O : LdOL F E} {P : Type}
  [Fintype P] {D : StdPO O P}

instance stdPO_decG₃ : DecidableEq D.G₃.A := D.G₃.decMemEq

omit [Fintype E] in
theorem stdPO_shared : D.pl.Shared := by
  intro o ho
  rcases o with ((a | w) | u) | o
  · exact ho.elim
  · exact ho.elim
  · exact Or.inl ⟨u, rfl⟩
  · exact Or.inr ⟨o, rfl⟩

theorem stdPO_rest (h : D.Hyp) (sa : O.toC.Sta) (m : O.toC.S.Msg) :
    D.pl.restG.val sa (D.pl.G₂.msg (O.toC.S.res (T := OMsg.Msg) D.pl.kp₁ m)) =
      O.toC.rest sa (O.toC.aM m) :=
  ldRest_is E _ _ _ _ O.toC D.pl D.slR rfl h.rest (fun _ _ _ _ => ⟨fun hh => hh, trivial⟩) sa m

variable [Nonempty P]

theorem stdPO_d1 (h : D.Hyp) : D.T.D₁.OK := by
  have hL : D.pl.G₁.C.Laws := ld_laws_fam E P _ _ fun a => h.laws a.1
  have hD : D.pl.G₁.C.Dist D.d := ld_dist_fam _ D.d fun a => h.dist a.1
  exact
    { ev := by
        letI : DecidableEq (D.pl.G₁.Row O.toC.B₁) := Classical.decEq _
        exact ok_indep E (D.pl.G₁.Row O.toC.B₁)
      list := h.lc _ hL hD
      fits := fun a f g hn => h.fits a.1 f g hn
      tail := ldTower_base E _ D.tb₁ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => h.tr a.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

theorem stdPO_d2 (h : D.Hyp) : D.T.D₂.OK := by
  have hL : D.pl.G₂.C.Laws := ld_laws_fam E P _ _ fun a => h.laws a.1.1
  have hD : D.pl.G₂.C.Dist D.d := ld_dist_fam _ D.d fun a => h.dist a.1.1
  exact
    { ev := by
        letI : DecidableEq (D.pl.G₂.Row LinB₂) := Classical.decEq _
        exact ok_indep E (D.pl.G₂.Row LinB₂)
      list := h.lc _ hL hD
      fits := fun a f g hn => h.fits a.1.1 f g hn
      tail := ldTower_base E _ D.tb₂ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => h.tr a.1.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

theorem stdPO_d3 (h : D.Hyp) : D.X.run.OK := by
  have hL : D.G₃.C.Laws := ld_laws_fam E P _ _ fun a => h.laws a.1.1.1
  have hD : D.G₃.C.Dist D.d := ld_dist_fam _ D.d fun a => h.dist a.1.1.1
  exact
    { ev := by
        letI : DecidableEq (D.G₃.Row {_b : D.BM // True}) := Classical.decEq _
        exact ok_indep E (D.G₃.Row {_b : D.BM // True})
      list := h.lc _ hL hD
      fits := fun a f g hn => h.fits a.1.1.1 f g hn
      tail := ldTower_base E _ D.tb₃ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => h.tr a.1.1.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

/-- The three clauses on what is left. -/
theorem stdPO_three [Nonempty (Fin O.Cf.C₀.n)] (h : D.Hyp) :
    D.pl.SaysA D.R.Q.base D.R.fx ∧
    D.R.Q.OK ∧
    ∀ V, D.R.Q.q V → D.pl.S₂.qFam (fun U : Finset O.toC.E₀.Pos => U = ∅) (fun _ => D.tb₃) V :=
  ldRowsOne_three E _ _ _ _ O.toC D.pl D.BM D.rowsA D.tgA D.X (fun a => a.2.elim, ())
    (fun U => U = ∅) (fun _ => trivial) (fun _ hh => hh) (fun sa _ m _ => h.more sa m)
    (fun sa _ m _ => h.more sa m) (fun _ _ _ _ _ => ⟨fun hh => hh, trivial⟩) (stdPO_d3 h) rfl

theorem stdPO_says [Nonempty (Fin O.Cf.C₀.n)] (h : D.Hyp) : O.toC.Says D.T.Q.base D.T.fq :=
  ldLinPlan_says E _ _ _ _ O.toC D.pl _ D.T.Q'.base D.T.fa (stdPO_rest h) (stdPO_three h).1

theorem stdPO_q [Nonempty (Fin O.Cf.C₀.n)] (h : D.Hyp) : D.T.Q.OK :=
  ldChain_cons E _ _ _ D.T.D₁ _ D.T.d₁ D.T.d₁' (stdPO_d1 h)
    (ldChain_cons E _ _ _ D.T.D₂ D.T.Q' D.T.d₂ D.T.d₂' (stdPO_d2 h) (stdPO_three h).2.1)

/-- What the three tests need of each oracle message. -/
theorem stdPO_needA (a : O.toC.Sa.O) :
    D.T.D₁.need (D.T.D₂.need fun _ => D.tb₃) (.inl (.inl (.inl a))) = D.tb₂ + D.tb₃ := by
  simp [LdRunD.need, LdLinC.isSh, LdLinC.isU, LdLinC.isL]

theorem stdPO_needW (a : O.toC.NW.O) :
    D.T.D₁.need (D.T.D₂.need fun _ => D.tb₃) (.inl (.inl (.inr a))) = D.tb₂ := by
  simp [LdRunD.need, LdLinC.isSh, LdLinC.isU, LdLinC.isL]

theorem stdPO_needU (a : O.toC.NU.O) :
    D.T.D₁.need (D.T.D₂.need fun _ => D.tb₃) (.inl (.inr a)) = D.tb₁ := by
  simp [LdRunD.need, LdLinC.isSh, LdLinC.isU]

theorem stdPO_needO (a : O.toC.NO.O) :
    D.T.D₁.need (D.T.D₂.need fun _ => D.tb₃) (.inr a) = D.tb₁ + D.tb₂ := by
  simp [LdRunD.need, LdLinC.isSh, LdLinC.isU, LdLinC.isL]

end
end Cb
