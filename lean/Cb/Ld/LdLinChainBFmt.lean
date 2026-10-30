-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChainBFmt.lean: the order of local and shared rounds in a batch protocol ("the format"),
followed along a chain of reductions and through the core of the test for linear constraints for a
batch.

A batch protocol runs at most N instances (slots) side by side. In a local round the verifier draws
a message for each slot, in a shared round one for all; a prover message has a slot's component and
a shared component. An annotation (`RoundSplits`, Iop/Batch.lean) says this round by round. The format
(`RoundSplits.Fmt`, Iop/BatchFmt.lean) asks: local rounds, then shared rounds, then local rounds; the
first round is no shared round; in a local round the shared component is empty; in a shared round
after the first shared one the slot's component is empty.

Definitions, statements and proofs.
The compiled scheme carries a session with the format. Ior/BatchFmtApp.lean follows that through
pieces in a row (`RoundSplits.Runs`); this file, through chains of annotated links (`ChainA`,
Cb/Ld/LdLinChainB.lean).
An annotation runs from the phase ph to ph' (`RoundSplits.Runs`; the phases: `FPhase`, Iop/BatchFmt.lean)
if, begun in ph, each of its rounds meets the format's conditions and the phase after its last round
is ph'. An annotated link (`LinkA`, Cb/Ld/LdLinChainB.lean) is a step of a chain of reductions with
an annotation of its rounds and its errors for a batch.

Main names:
  `Iop.Spec.chainA_runs`, `Iop.Spec.chainA_runs_append`: a chain as one link; two chains in a row.
  `Cb.Spec.ldLinCB_runs`: for a nonempty ι (the set of positions of the encoded index), the core of
    the test for at most N instances (`P.chainA`) runs from a phase before the shared rounds
    ("before the first round" or "in the local rounds": `ph.afterLo = .loc`) to "in the shared
    rounds": the slot's sending of its own family is local; the shared point is the joining round;
    all that follows is sent by the shared part alone.
  `Iop.Spec.online_fmt`: the format of a session.

Notation: `on0`: a predicate on `P.D.X.Row → ι → E` and `P.D.X.Rec`; `S`: the honest senders, and
the numbers of the three sendings (`P.Snd`, Cb/Ld/LdLin.lean); `εf`: a natural number; `ph`: a phase
(`FPhase`: `first`, `loc`, `shr`, `aft`); `ph.afterLo`: the phase after a local round.

Limits: this file says nothing on the closing of the test. The closing is a chain of its own: it
has to run from "in the shared rounds".

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChainB
import Ior.BatchFmtApp

set_option autoImplicit false

namespace Iop
namespace IOR
variable {K : Type}

def LinkA.Runs {A B : Joint K} (a : LinkA K A B) (ph ph' : FPhase) : Prop := a.ann.Runs ph ph'

def ChainA.Runs : {A B : Joint K} → ChainA K A B → FPhase → FPhase → Prop
  | _, _, .one a, ph, ph' => a.Runs ph ph'
  | _, _, .snoc c a, ph, ph' => ∃ mid, c.Runs ph mid ∧ a.Runs mid ph'

theorem ChainA.runs_one {A B : Joint K} (a : LinkA K A B) (ph ph' : FPhase) :
    (ChainA.one a).Runs ph ph' ↔ a.Runs ph ph' := by rw [ChainA.Runs]
theorem ChainA.runs_snoc {A B C : Joint K} (c : ChainA K A B) (a : LinkA K B C) (ph ph' : FPhase) :
    (c.snoc a).Runs ph ph' ↔ ∃ mid, c.Runs ph mid ∧ a.Runs mid ph' := by rw [ChainA.Runs]

end IOR

namespace Spec
open IOR

def chainA_runs : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : ChainA K A B) (d : A.W) (ph ph' : FPhase),
    c.Runs ph ph' → (c.linkA d).Runs ph ph'

def chainA_runs_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : ChainA K A B) (c' : ChainA K B C) (ph ph' ph'' : FPhase),
    c.Runs ph ph' → c'.Runs ph' ph'' → (c.append c').Runs ph ph''

/-- States: a session (`online F Q`, Ior/Batch.lean: a preamble in local rounds, then a batch
protocol) has the format if Q's annotation runs from the phase after the preamble. -/
def online_fmt : Prop :=
  ∀ (X Xl : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej))
      (Q : BIOP Xl (E0.prod Ej)) (ph' : FPhase),
    Q.ann.Runs (if F.shape = [] then .first else .loc) ph' → (online F Q).ann.Fmt

end Spec

open IOR IOR.ChainA

theorem chainA_runs : Spec.chainA_runs := by
  intro K A B c d ph ph' h
  induction c generalizing ph' with
  | one a =>
    rw [linkA_one]
    exact (ChainA.runs_one a ph ph').1 h
  | snoc c a ih =>
    obtain ⟨mid, h1, h2⟩ := (ChainA.runs_snoc c a ph ph').1 h
    rw [linkA_snoc]
    exact fmtRuns_app _ _ _ _ ph mid ph' (ih mid h1) h2

theorem chainA_runs_append : Spec.chainA_runs_append := by
  intro K A B C c c' ph ph' ph'' h h'
  induction c' generalizing ph'' with
  | one a =>
    rw [append_one]
    exact (ChainA.runs_snoc c a ph ph'').2 ⟨ph', h, (ChainA.runs_one a ph' ph'').1 h'⟩
  | snoc c' a ih =>
    obtain ⟨mid, h1, h2⟩ := (ChainA.runs_snoc c' a ph' ph'').1 h'
    rw [append_snoc]
    exact (ChainA.runs_snoc _ a ph ph'').2 ⟨mid, ih mid h1, h2⟩

theorem online_fmt : Spec.online_fmt := fun _ _ _ _ F Q ph' h =>
  fmtRuns_fmt _ _ ph'
    (fmtRuns_app _ _ (RoundSplits.allLocal F.shape) Q.ann .first _ ph' (fmtRuns_local F.shape .first) h)

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

def Spec.ldLinCB_runs (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ]
    [Fintype J] [Fintype Y] : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (S : P.Snd)
      (εf N : ℕ) (ph : FPhase),
    ph.afterLo = .loc → (P.chainA on0 S εf N).Runs ph .shr

theorem ldLinCB_runs (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ]
    [Fintype J] [Fintype Y] :
    Spec.ldLinCB_runs E ι κ J Y := by
  intro P on0 S εf N ph hph
  unfold LdLinP.chainA
  rw [ChainA.runs_snoc]
  refine ⟨.shr, ?_, (fmtRuns_shared _).1⟩
  rw [ChainA.runs_snoc]
  refine ⟨.shr, ?_, (fmtRuns_shared _).1⟩
  rw [ChainA.runs_snoc]
  refine ⟨.shr, ?_, (fmtRuns_shared _).1⟩
  rw [ChainA.runs_snoc]
  refine ⟨.shr, ?_, (fmtRuns_shared _).1⟩
  rw [ChainA.runs_snoc]
  refine ⟨.loc, ?_, (fmtRuns_shared _).2 (List.cons_ne_nil _ _)⟩
  rw [ChainA.runs_snoc]
  refine ⟨ph, ?_, ?_⟩
  · rw [ChainA.runs_one]
    exact fmtRuns_nil _ ph
  · have h := fmtRuns_local (P.lkW on0 S).R.shape ph
    have hne : (P.lkW on0 S).R.shape ≠ [] := List.cons_ne_nil _ _
    rw [if_neg hne, hph] at h
    exact h

end Cb
