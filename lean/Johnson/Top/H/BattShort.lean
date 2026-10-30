-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BattShort.lean: the kind of block BATT in its short form (several pending tensor rows
become one: a round of coefficients, then a sumcheck in whose rounds the linear coefficient is not
sent) as a value of `BaseKind` (Johnson/Top/Kind.lean), at any written list of callers, with the
kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/BattShort.lean. The callers, the joints, the
extractor and the condition are those of `kBatt` (Johnson/Top/H/Batt.lean), which has the library's
long form; the reduction and the errors are `Cb.Pv.BattShort.R` and `Cb.Pv.BattShort.eps`.
Main names:
  `kBattShort L`: the kind.
  `kBattShort_know`, `_point`, `_local`, `_onOut`, `_good`: under `BattOK L`; `_good` is of the kind
    lifted over the caller's signature.
  `kBattShort_total`: under `BattOK L` the verifier never rejects.
  `HBattShort`: closed, over the field `Cb.Gl.E`: for every list of callers that meet the condition
    the kind is knowledge sound. `hBattShort`: it holds.
  The rounds, the errors and the numbers of values as lists: `rounds`, `errs`, `vals` of
  Cb/Pv/BattShort.lean.
Limits: those of Johnson/Top/H/Batt.lean on the tuple of committed messages. That the short form is
the programs' is meant, not compared here. No list of callers is written here, so the condition is
proved of no value. Nothing says that a block of the kind is the step that the programs run, or that
its errors are small. Nothing on an honest prover.

-/
import Johnson.Top.H.Batt
import Cb.Pv.BattShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- BATT in its short form, at a written list of callers. -/
@[reducible] noncomputable def kBattShort (L : List (BattCaller E)) : BaseKind.{1} E where
  Size := BattCaller E
  sizes := L
  Sg := fun c => c.Sg
  Kc := fun c => c.Kc
  St := fun c => (c.B.Q → E) × c.B.St
  St' := fun c => c.B.par.Mid
  Wp := fun c => c.Wp
  Wp' := fun c => c.Wp
  E₀ := fun c => c.Ex
  E₀' := fun c => c.Ex
  R := fun c => Cb.Pv.BattShort.R c.B c.Ex
  A := fun c => c.B.baseIn c.Ex c.A0 fun w => c.msg w.1
  B := fun c => c.B.baseOut c.Ex c.A0 fun w => c.msg w.1
  ext := fun _ _ _ _ wp => wp
  ε := fun c => Cb.Pv.BattShort.eps c.B c.Ex

variable (L : List (BattCaller E)) (h : BattOK L)
include h

theorem kBattShort_know : (kBattShort L).Know := fun c hc m =>
  Cb.Pv.BattShort.hAt c.B (h c hc).1 (h c hc).2 c.Ex c.Sg.Msg c.Wp c.Kc c.A0 c.msg m

theorem kBattShort_point : (kBattShort L).Point := fun c hc =>
  (Cb.Pv.BattShort.knowAt c.B (h c hc).1 (h c hc).2 c.Ex c.Sg.Msg c.Wp c.Kc c.A0 c.msg).point

theorem kBattShort_local : (kBattShort L).Local := fun c hc =>
  (Cb.Pv.BattShort.knowAt c.B (h c hc).1 (h c hc).2 c.Ex c.Sg.Msg c.Wp c.Kc c.A0 c.msg).isLocal

theorem kBattShort_onOut : (kBattShort L).OnOut := fun c hc =>
  (Cb.Pv.BattShort.knowAt c.B (h c hc).1 (h c hc).2 c.Ex c.Sg.Msg c.Wp c.Kc c.A0 c.msg).onOut

theorem kBattShort_good : ∀ c ∈ L, ((kBattShort L).toKind.block c).Good :=
  BaseKind.good (kBattShort_know L h) (kBattShort_point L h) (kBattShort_local L h)
    (kBattShort_onOut L h)

/-- The verifier never rejects. -/
theorem kBattShort_total : ∀ c ∈ L, ∀ x y τ, (((kBattShort L).R c).out x y τ).isSome :=
  fun c hc x y τ =>
    Cb.Pv.BattShort.never_rejects c.B (le_trans (by norm_num) (h c hc).1) c.Ex x y τ

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the condition. -/
def HBattShort : Prop := ∀ L : List (BattCaller Cb.Gl.E), BattOK L → (kBattShort L).Know

theorem hBattShort : HBattShort := kBattShort_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hBattShort
#print axioms VerifiableInference.OnPublicFiles.kBattShort_good
#print axioms VerifiableInference.OnPublicFiles.kBattShort_total
