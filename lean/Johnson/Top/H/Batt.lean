-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Batt.lean: the kind of block BATT (several pending tensor rows become one: a round of
coefficients, then a sumcheck) as a value of `BaseKind` (Johnson/Top/Kind.lean), at any written list
of callers, with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Batt.lean. The block is the library's
`BattPar.batt` (Cb/Ld/LdBatt.lean), stated at the base: for each fixed tuple of committed messages.
A size is a caller: the library's record B, the further oracles, a signature whose messages are the
committed ones, the joint that rides along, and the reading of the entries off the messages: data
alone.
Main names:
  `BattCaller`: who calls the batching. `kBatt L`: the kind.
  `BattOK L`: the condition at every caller of the list: 2 ≤ B.n, and the coefficients evade zero.
  `kBatt_know`, `_point`, `_local`, `_onOut`, `_good`: under `BattOK L`; `_good` is of the kind
    lifted over the caller's signature.
  `HBatt`: closed, over the field `Cb.Gl.E`: for every list of callers that meet the condition the
    kind is knowledge sound. `hBatt`: it holds.
Limits: the tuple of committed messages is that of a signature. Where the entries are also read off
the message of an encoded index, as in the library's preamble (`LdWfP.lBatt`, Cb/Ld/LdWf.lean), the
block is lifted in another way (Cb/Ld/LdWfIdx.lean) and is not a value of this kind. No list of
callers is written here, so the condition is proved of no value. Nothing says that a block of the
kind is the step that the programs run, or that its errors are small. Nothing on an honest prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Batt
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

/-- Who calls the batching. Data alone. -/
structure BattCaller (E : Type) [Field E] [Fintype E] : Type 1 where
  B : BattPar E
  Ex : ExtSpec
  Kc : Type
  Wp : Type
  /-- the signature: the committed messages are its -/
  Sg : Sig E
  /-- the joint that rides along -/
  A0 : Rels Kc B.St Ex (Sg.Msg × Wp)
  /-- the entries, read off the messages -/
  msg : Sg.Msg → B.J → E

section
variable {E : Type} [Field E] [Fintype E]

/-- BATT, at a written list of callers. -/
@[reducible] noncomputable def kBatt (L : List (BattCaller E)) : BaseKind.{1} E where
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
  R := fun c => c.B.batt c.Ex
  A := fun c => c.B.baseIn c.Ex c.A0 fun w => c.msg w.1
  B := fun c => c.B.baseOut c.Ex c.A0 fun w => c.msg w.1
  ext := fun _ _ _ _ wp => wp
  ε := fun c => (c.B.nums c.Ex c.Kc).err

/-- The condition. -/
def BattOK (L : List (BattCaller E)) : Prop := ∀ c ∈ L, 2 ≤ c.B.n ∧ c.B.Z.OK

variable (L : List (BattCaller E)) (h : BattOK L)
include h

theorem kBatt_know : (kBatt L).Know := fun c hc m =>
  Cb.Pv.Batt.hAt c.B (h c hc).1 (h c hc).2 c.Ex c.Sg.Msg c.Wp c.Kc c.A0 c.msg m

theorem kBatt_point : (kBatt L).Point := fun c hc =>
  Cb.Pv.Batt.point c.B (h c hc).1 (h c hc).2 c.Ex

theorem kBatt_local : (kBatt L).Local := fun c hc =>
  Cb.Pv.Batt.isLocal c.B (h c hc).1 (h c hc).2 c.Ex

theorem kBatt_onOut : (kBatt L).OnOut := fun c hc =>
  Cb.Pv.Batt.onOut c.B (h c hc).1 (h c hc).2 c.Ex c.Sg.Msg c.Wp c.Kc c.A0 c.msg

theorem kBatt_good : ∀ c ∈ L, ((kBatt L).toKind.block c).Good :=
  BaseKind.good (kBatt_know L h) (kBatt_point L h) (kBatt_local L h) (kBatt_onOut L h)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the condition. -/
def HBatt : Prop := ∀ L : List (BattCaller Cb.Gl.E), BattOK L → (kBatt L).Know

theorem hBatt : HBatt := kBatt_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hBatt
#print axioms VerifiableInference.OnPublicFiles.kBatt_good
