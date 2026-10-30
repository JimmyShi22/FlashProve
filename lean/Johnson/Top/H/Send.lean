-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Send.lean: the kind of block SEND (two rounds: the words of a family of oracle
messages, a joint seed; the answers) as a value of `Kind` (Johnson/Top/Kind.lean), at any written
list of callers, with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Send.lean. A size is a caller: that file's
record `Size` (the family, how its seeds are drawn, a bound on the lists of each member) and the
joint before the sending, with the map that makes a part of its witness from the sent messages: data
alone.
Main names:
  `SendCaller`: who calls a sending. `kSend L`: the kind.
  `SendOK L`: the condition: `Cb.Pv.Send.Size.OK` at every caller of the list: the codes' laws, fair
    seeds, bounded lists, evading samples: on public data alone.
  `kSend_know`, `_local`, `_good`: under `SendOK L`. `kSend_point`, `_onOut`: without a premise.
  `HSend`: closed, over the field `Cb.Gl.E`: for every list of callers that meet the condition the
    kind is knowledge sound. `hSend`: it holds.
Limits: no list of callers is written here: the families at which a description of the programs'
protocol has a sending are built nowhere, so the condition is not stated at them, clause by
clause, and is proved of no value. A sending whose first message also holds an oracle of a later
block is not of this kind. The first round of a code switch is not of this kind
(Johnson/Top/H/Cs.lean). Nothing says that a block of the kind is the step that the programs run, or
that its errors are small. Nothing on an honest prover.
-/
import Johnson.Top.Kind
import Cb.Pv.Send
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

/-- Who calls a sending: the family, and the joint before the sending. Data alone. -/
structure SendCaller (E : Type) [Field E] : Type 1 where
  s : Cb.Pv.Send.Size E
  Kc : Type
  X : Type
  W : Type
  W' : Type
  E₀ : ExtSpec
  /-- the joint before the sending -/
  A : Rels Kc X E₀ W
  /-- a witness of that joint, from the sent messages and the further witness -/
  back : s.N.Msg → W' → W

section
variable {E : Type} [Field E]

/-- SEND, at a written list of callers. -/
@[reducible] noncomputable def kSend (L : List (SendCaller E)) : Kind.{1} where
  Size := SendCaller E
  sizes := L
  src := fun c => jOf c.A
  dst := fun c => jOf (Cb.Pv.Send.outJ c.s c.A c.back)
  block := fun c =>
    ⟨Cb.Pv.Send.R c.s c.X c.E₀, fun _ _ w => c.back (c.s.N.msgs w.1) w.2, Cb.Pv.Send.eps c.s⟩

/-- The condition, on public data alone. -/
def SendOK (L : List (SendCaller E)) : Prop := ∀ c ∈ L, c.s.OK

variable (L : List (SendCaller E))

theorem kSend_know (h : SendOK L) : (kSend L).Know := fun c hc =>
  Cb.Pv.Send.hAt_of_ok c.s (h c hc) c.Kc c.X c.W c.W' c.E₀ c.A c.back

theorem kSend_point : (kSend L).Point := fun c _ => Cb.Pv.Send.point c.s c.X c.E₀

theorem kSend_local (h : SendOK L) : (kSend L).Local := fun c hc =>
  Cb.Pv.Send.isLocal c.s c.X c.E₀ (h c hc).laws

theorem kSend_onOut : (kSend L).OnOut := fun c _ a τ b hb ha =>
  Cb.Pv.Send.onOut c.s c.A c.back a τ b ha hb

theorem kSend_good (h : SendOK L) : ∀ c ∈ L, ((kSend L).block c).Good :=
  Kind.good (kSend_know L h) (kSend_point L) (kSend_local L h) (kSend_onOut L)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the condition. -/
def HSend : Prop := ∀ L : List (SendCaller Cb.Gl.E), SendOK L → (kSend L).Know

theorem hSend : HSend := kSend_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hSend
#print axioms VerifiableInference.OnPublicFiles.kSend_good
