-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaRun.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean): one whole test on a group as a link; closings as chains of such tests; the test for
linear constraints and the link with their closings. These errors are numbers that a link, or the
test `D.T` on the complex, lists (the data fields `Link.P.err`, `LdEnd.N.err`) or that a clause
writes out (`bridge`: `D.L * D.Z.err`): that a link or test is sound at the numbers that it lists is
no statement of this file; for the link of one whole test that tie is `Spec.ldChain_link`
(Cb/Ld/LdLinCloseChain.lean), under its hypotheses (that condition itself asks soundness of some of
the parts one level down: for these the tie carries soundness, it does not found it).

One record and theorems: glue along the rules of composition; nothing is evaluated.
A whole test (`LdRunD`, Cb/Ld/LdLinCloseRuns.lean) is one test on a group of oracle messages, as one
link. A closing (`LdTc`, Cb/Ld/LdLinCloseChain.lean) is a chain of links from a statement over a
signature down to the trivial statement.

Main names:
  `LdRunD.Kap`: `D.Kap κ`, for one whole test D, has two clauses: for the bridge's round, (bound on
    the list of the group's complex) · (the zero-evader's exceptional seeds) ≤ κ · (number of
    seeds); and every round's error of the whole test `D.T` on the complex, as a probability, is at
    most κ (a clause on a term here; for a tower it comes down to numbers: Cb/Ld/LdKappaTow.lean).
  `ldKappa_run`: `D.Kap κ` → every error of the link of D, as a probability, is at most κ.
  `ldKappa_nil`, `ldKappa_cons`: closings: "nothing is left": nothing is asked; a test with
    `D.Kap κ`, then a closing whose errors, as probabilities, are at most κ: so are the whole's.
  `ldKappa_linZ`, `ldKappa_linkZ`: the closing of the test for linear constraints with a plan Q
    (the step without rounds, then Q's chain) whose errors, as probabilities, are at most κ; the
    closing of the link, from `K.run.Kap κ`: so are the closing's.
  `ldKappa_linC`, `ldKappa_linkC`: the test for linear constraints (the link) with its closing, as
    one link: every error, as a probability, is at most κ, from the core's numbers (`KapC`,
    Cb/Ld/LdKappaKit.lean) and a closing of which the same holds; the type ι of positions is taken
    nonempty.

Limits: this file says nothing on the size of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaKit
import Cb.Ld.LdLinCloseLin
import Cb.Ld.LdLinkClose

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E}

/-- One whole test on a group: its numbers, and its test's list of errors (`test`). -/
structure LdRunD.Kap (D : LdRunD S) (κ : ℝ≥0∞) : Prop where
  bridge : ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)
  test   : Err.Below D.T.N.err κ

theorem ldKappa_run (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
    (κ : ℝ≥0∞) (h : D.Kap κ) :
    Err.Below (D.link A₀ d d').P.err κ :=
  Err.Below.app (⟨h.bridge, trivial⟩ :
      Err.Below (ldBridgeN D.G D.kp D.Sb D.Z St₀ E₀ Unit (D.L * D.Z.err)).err κ)
    (Err.Below.app h.test trivial)

omit [Fintype E] in
theorem ldKappa_nil (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) (κ : ℝ≥0∞) :
    (LdTc.nil S E₀ Wp w₀).c.ErrBelow κ :=
  (errBelow_one _ κ).2 trivial

theorem ldKappa_cons {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S) (Q : LdTc (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞) (h : D.Kap κ) (hQ : Q.c.ErrBelow κ) :
    (LdTc.cons D Q d d').c.ErrBelow κ :=
  (errBelow_append Unit _ _ _ _ _ κ).2 ⟨(errBelow_one _ κ).2 (ldKappa_run D Q.base d d' κ h), hQ⟩

end

section
variable {E ι κ' J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Y]

omit [Fintype E] [Nonempty ι] in
theorem ldKappa_linZ (C : LdLinC E ι κ' J Y) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St)
    (κ : ℝ≥0∞) (h : Q.c.ErrBelow κ) : (C.cZ Q fq).ErrBelow κ :=
  (errBelow_append Unit _ _ _ _ _ κ).2 ⟨(errBelow_one _ κ).2 trivial, h⟩

theorem ldKappa_linC (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf : ℕ) (cZ : Chain Unit P.J6 LdLinP.JT) (d : P.W0) (κ : ℝ≥0∞)
    (h : P.KapC S εf κ) (hZ : cZ.ErrBelow κ) :
    Err.Below (P.linC on0 S εf cZ d).P.err κ := by
  unfold LdLinP.linC
  exact chain_errBelow Unit _ _ _ _ κ
    ((errBelow_append Unit _ _ _ _ _ κ).2 ⟨ldKappa_lin P on0 S εf κ h, hZ⟩)

end

section
variable {E ι κ' J Λ : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Λ]

omit [Fintype ι] [Nonempty ι] in
theorem ldKappa_linkZ (P : LdLkP E ι κ' J Λ) (K : P.Cl) (d : P.W2) (κ : ℝ≥0∞) (h : K.run.Kap κ) :
    (K.cZ d).ErrBelow κ :=
  (errBelow_append Unit _ _ _ _ _ κ).2
    ⟨(errBelow_one _ κ).2 trivial, ldKappa_cons K.run _ _ _ κ h (ldKappa_nil _ _ _ κ)⟩

theorem ldKappa_linkC (P : LdLkP E ι κ' J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (ε₀ ε₁ : ℕ) (cZ : Chain Unit P.J4 ldJT) (d : P.W0) (κ : ℝ≥0∞)
    (h : P.KapC S ε₀ ε₁ κ) (hZ : cZ.ErrBelow κ) :
    Err.Below (P.linkC on0 on1 S ε₀ ε₁ cZ d).P.err κ := by
  unfold LdLkP.linkC
  exact chain_errBelow Unit _ _ _ _ κ
    ((errBelow_append Unit _ _ _ _ _ κ).2 ⟨ldKappa_link P on0 on1 S ε₀ ε₁ κ h, hZ⟩)

end
end Cb
