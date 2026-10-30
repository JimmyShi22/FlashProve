-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Bat.lean: the kind of block BAT (one round before a proximity test's first fold: all
open rows on a group of oracle messages and the sample rows of its members become one row) as a
value of `Kind` (Johnson/Top/Kind.lean), at any written list of callers, with the kind's hypothesis
and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Bat.lean. A size is a caller: that file's
record `Size` (the family, the group, which members are kept, the open rows, the coefficients, a
bound on the lists) and the joint on the kept messages that is carried beside the test: data alone.
Main names:
  `BatCaller`: who calls the round. `kBat L`: the kind.
  `BatOK L`: the condition at every caller of the list: the coefficients evade zero, the lists of
    the group's code at the joint radius are bounded, the joint radius implies each member's own.
  `kBat_know`, `_onOut`, `_good`: under `BatOK L`. `kBat_point`, `_local`: without a premise.
  `HBat`: closed, over the field `Cb.Gl.E`: for every list of callers that meet the condition the
    kind is knowledge sound. `hBat`: it holds.
Limits: no list of callers is written here: the groups at which a description of the programs'
protocol has such a round are built nowhere, so the condition is not stated at them, clause by
clause, and is proved of no value. The batching of rows that are still claimed of decoded messages
is another kind. Nothing says that a block of the kind is the step that the programs run, or that
its error is small. Nothing on an honest prover.
-/
import Johnson.Top.Kind
import Cb.Pv.Bat
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

/-- Who calls the round: the group and its rows, and the joint that is carried. Data alone. -/
structure BatCaller (E : Type) [Field E] [Fintype E] : Type 1 where
  s : Cb.Pv.Bat.Size E
  Kc : Type
  St₀ : Type
  Wp : Type
  E₀ : ExtSpec
  /-- the joint on the kept messages -/
  A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)

section
variable {E : Type} [Field E] [Fintype E]

/-- BAT, at a written list of callers. -/
@[reducible] noncomputable def kBat (L : List (BatCaller E)) : Kind.{1} where
  Size := BatCaller E
  sizes := L
  src := fun c => jOf (Cb.Pv.Bat.inJ c.s c.A₀)
  dst := fun c => jOf (Cb.Pv.Bat.outJ c.s c.A₀)
  block := fun c =>
    ⟨Cb.Pv.Bat.R c.s c.St₀ c.E₀, fun _ _ w => ldBrBack c.s.G c.s.kp c.Wp c.s.hc w,
      Cb.Pv.Bat.eps c.s⟩

/-- The condition at one size. -/
structure BatOKAt (s : Cb.Pv.Bat.Size E) : Prop where
  z : s.Z.OK
  list : s.G.C.ListAt s.G.e s.L
  fits : s.G.Fits

/-- The condition. -/
def BatOK (L : List (BatCaller E)) : Prop := ∀ c ∈ L, BatOKAt c.s

variable (L : List (BatCaller E))

theorem kBat_know (h : BatOK L) : (kBat L).Know := fun c hc =>
  Cb.Pv.Bat.hAt c.s (h c hc).z (h c hc).list (h c hc).fits c.Kc c.St₀ c.Wp c.E₀ c.A₀

theorem kBat_point : (kBat L).Point := fun c _ => Cb.Pv.Bat.point c.s c.St₀ c.E₀

theorem kBat_local : (kBat L).Local := fun c _ => Cb.Pv.Bat.isLocal c.s c.St₀ c.E₀

theorem kBat_onOut (h : BatOK L) : (kBat L).OnOut := fun c hc a τ b hb ha =>
  Cb.Pv.Bat.onOut c.s (h c hc).z (h c hc).list (h c hc).fits c.A₀ a τ b ha hb

theorem kBat_good (h : BatOK L) : ∀ c ∈ L, ((kBat L).block c).Good :=
  Kind.good (kBat_know L h) (kBat_point L) (kBat_local L) (kBat_onOut L h)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the condition. -/
def HBat : Prop := ∀ L : List (BatCaller Cb.Gl.E), BatOK L → (kBat L).Know

theorem hBat : HBat := kBat_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hBat
#print axioms VerifiableInference.OnPublicFiles.kBat_good
