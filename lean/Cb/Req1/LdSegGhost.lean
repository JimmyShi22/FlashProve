-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegGhost.lean: the core of a chain as a ghost in the further witness: one step without
rounds.

Definitions, statements (Cb.Spec.ldSegGhost_*) and proofs. Framework only; no place of a text is
rendered.
In standard terms: a reduction without rounds that leaves explicit part and oracles as they are and
adds to the witness a copy of the part that the joint's map `core` reads off it (`ghostJ`,
`LdStage.ghostMv`; `IOR.Rels.core`, Ior/Chain.lean).

Why: every link of a chain is asked to hand the core of the witness on, at all witnesses
(`IOR.GoodB.keeps`): the part that a hidden withheld set may read (a range check: the integer
cells). After a sending the base joint reads its witness, so also its core, through the new messages
(Cb/Ld/LdSigSum.lean: `S.grow`). A bridge drops oracle messages: a core that is read off dropped
messages cannot be handed on.
So this file has, for use before the first closing, a step without rounds in which the honest prover
copies the core into a further part of the witness, which no relaxed relation reads and which every
later move hands on with the further witness, in this sense: `ghostJ`'s field `relR`, the relaxed
relation of `a.ghost`, does not read it; of later stages and moves nothing is stated here (see
Limits).

Main names:
  `a.ghost`: the stage a with further witness (Wp, k), k : Kc. Exact: a's relation, and k is a's
    core (an exact-only clause); relaxed: a's, k is not read; condition: a's; core: k.
  `a.ghostMv`: the step from a to a.ghost: the honest prover computes k from its witness; the
    extractor forgets k.
  `Spec.ldSegGhost_hyp`: the step's hypothesis holds without any condition beside whatever the
    arguments hold as proofs (the core is handed on at all witnesses, since k is computed from the
    witness).
  `Spec.ldSegGhost_free`: its kind is "step"; no round; zero knowledge asks nothing of it, beside
    its hypotheses (`a.ghostMv.Hyp`).
  `Spec.ldSegGhost_carry`: a fact f on a's witnesses is carried, without condition beside the
    premise that is written out and whatever the arguments hold as proofs, as the fact that reads
    a.ghost's witness without k. (A reading that takes k in is carried only if overwriting the masks
    does not change a's core: not stated here.)

Limits: this file does not say that later moves hand k on: their data do (bk of a sending, Wp of a
fold, bk₀ of a closing).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCarry
import Cb.Req1.LdSegCloseProofs
import Cb.Req1.LdSegProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- the base joint with the core as a ghost -/
def ghostJ {St M Wp : Type} {E₀ : ExtSpec} (A : Rels Kc St E₀ (M × Wp)) :
    Rels Kc St E₀ (M × (Wp × Kc)) where
  rel  := fun st y w => A.rel st y (w.1, w.2.1) ∧ w.2.2 = A.core (w.1, w.2.1)
  relR := fun a w => A.relR a (w.1, w.2.1)
  on   := A.on
  core := fun w => w.2.2

/-- The stage with the core as a ghost. -/
@[reducible] def LdStage.ghost (a : LdStage E Kc) : LdStage E Kc :=
  ⟨a.S, a.St, a.E₀, a.Wp × Kc, ghostJ a.A⟩

/-- The step. -/
def LdStage.ghostMv (a : LdStage E Kc) : LdMv a a.ghost :=
  .step a a.ghost (sideF a.S id) (sideG a.S (ExtMap.id a.E₀))
    (sideM a.S id fun _ w => (w.2, a.A.core w)) (sideB a.S fun _ w => w.2.1)

end

namespace Spec

def ldSegGhost_hyp : Prop := ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc), a.ghostMv.Hyp

def ldSegGhost_free : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc), a.ghostMv.tag = .step ∧
    a.ghostMv.chain.nAll = 0 ∧ a.ghostMv.chain.pBad = 0 ∧
    a.ghostMv.chain.pHid = 0 ∧ ∀ base, a.ghostMv.Zk base

def ldSegGhost_carry : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc)
      (base : MaskFact a.J.W → Prop) (f : MaskFact a.J.W),
    base f → a.ghostMv.After base ⟨f.Kc, fun w => f.kc (w.1, w.2.1), f.Mk, f.put⟩

end Spec

theorem ldSegGhost_hyp : Spec.ldSegGhost_hyp := fun E Kc _ _ a =>
  ldPeel_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldPeel_base E Kc a.St a.St a.Wp (a.Wp × Kc) a.S a.E₀ a.E₀ a.A (ghostJ a.A) id (ExtMap.id a.E₀)
      (fun _ w => (w.2, a.A.core w)) (fun _ w => w.2.1) (extMap_isLocal.1 a.E₀)
      (fun _ _ _ h => ⟨h, rfl⟩) (fun _ _ h => h) (fun _ _ => rfl) (fun _ _ _ _ h => h))

theorem ldSegGhost_free : Spec.ldSegGhost_free := fun E Kc _ _ a =>
  have h := (ldSeg_rounds E Kc).2.2.2.2.2 a a.ghost (sideF a.S id) (sideG a.S (ExtMap.id a.E₀))
    (sideM a.S id fun _ w => (w.2, a.A.core w)) (sideB a.S fun _ w => w.2.1)
  ⟨rfl, h.1, h.2.2.1, h.2.2.2, fun _ => trivial⟩

theorem ldSegGhost_carry : Spec.ldSegGhost_carry := fun _ _ _ _ a base f hb =>
  segCarry_step a a.ghost _ _ _ _ base f f.Kc (fun w => f.kc (w.1, w.2.1))
    f.put hb (fun _ _ _ _ h => ⟨rfl, h⟩)

end Cb
