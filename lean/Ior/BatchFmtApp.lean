-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchFmtApp.lean: the format of the rounds of a batch IOP, piece by piece.
Book-keeping for batch IOPs: the condition on the order of local and shared rounds and on who sends
in them (`RoundSplits.Fmt`, Iop/BatchFmt.lean) follows for a concatenation of annotated shapes from
conditions on its parts.

Definitions, statements (`Iop.Spec`) and proofs. No protocol occurs here.
An annotation of a shape (`RoundSplits`, Iop/Batch.lean) says for each round whether it is local or shared,
and how a prover message splits into the shared part and a slot's part. In a local round the
verifier message is drawn for each slot apart, in a shared round once for all slots. A slot is one
of the N places of a batch, each with one instance or empty, with its own local transcript.
Iop/BatchFmt.lean says which annotations the compiled scheme can carry: the kinds run "local rounds,
then shared rounds, then local rounds" (the first round, if there is one, is local), and a component
that is not sent is empty (`RoundSplits.Fmt`). It is a property of a whole annotation. A session is put
together from many pieces (a preamble; sendings by a slot; shared rounds; tests by the shared part;
tests in every slot).

Main names:
  `A.Runs ph ph'` (ph, ph' : `FPhase`, Iop/BatchFmt.lean): see its docstring.
  `Spec.fmtRuns_app`: pieces in a row.
  `Spec.fmtRuns_nil`: no round: the phase stays.
  `Spec.fmtRuns_local`: local rounds in which only the slot speaks: from any phase; afterwards: the
    phase after a local round (the same phase, if there is no round).
  `Spec.fmtRuns_shared`: shared rounds in which only the shared part speaks: from "in the shared
    rounds" to the same; from "in the local rounds before" too, if there is a round (the first one
    is the joining round).
  `Spec.fmtRuns_fmt`: from `Runs` at the first phase to `RoundSplits.Fmt`.

Limits: a joining round in which both components speak is covered by the definition, not by a rule
here.
Terms: lean/GLOSSARY.md.
-/
import Iop.SplitKit

set_option autoImplicit false

namespace Iop

/-- From ph on every round has a format and a component that is not sent is empty (`RoundSplits.FmtFrom`);
afterwards the phase is ph'. -/
def RoundSplits.Runs {s : Shape} (A : RoundSplits s) (ph ph' : FPhase) : Prop :=
  RoundSplits.FmtFrom s A ph ∧ RoundSplits.endPhase A ph = ph'

/-- what `FmtFrom` says of the rounds after the first -/
theorem RoundSplits.fmtFrom_tail {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {ph : FPhase} (h : RoundSplits.FmtFrom (r :: s) (a, A) ph) :
    RoundSplits.FmtFrom s A (FPhase.after a.kind ph) := by
  unfold RoundSplits.FmtFrom at h
  cases hk : a.kind <;> cases ph <;> simp only [hk] at h <;> first | exact h.2 | exact h

/-- the first round's own condition does not read the rounds after it -/
theorem RoundSplits.fmtFrom_cons {r : Round} {s t : Shape} {a : RAnn r} {A : RoundSplits s} {B : RoundSplits t}
    {ph : FPhase} (h : RoundSplits.FmtFrom (r :: s) (a, A) ph)
    (hB : RoundSplits.FmtFrom t B (FPhase.after a.kind ph)) :
    RoundSplits.FmtFrom (r :: t) (a, B) ph := by
  unfold RoundSplits.FmtFrom at h ⊢
  cases hk : a.kind <;> cases ph <;> simp only [hk] at h hB ⊢ <;> first | exact ⟨h.1, hB⟩ | exact hB

theorem RoundSplits.fmtFrom_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ph : FPhase), RoundSplits.FmtFrom s A ph →
      RoundSplits.FmtFrom t B (RoundSplits.endPhase A ph) → RoundSplits.FmtFrom (s ++ t) (RoundSplits.app A B) ph
  | [], _, _, _, _, _, hB => hB
  | _ :: _, _, (a, A), B, ph, hA, hB =>
    RoundSplits.fmtFrom_cons hA (RoundSplits.fmtFrom_app A B (FPhase.after a.kind ph) (RoundSplits.fmtFrom_tail hA) hB)

theorem RoundSplits.endPhase_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ph : FPhase),
      RoundSplits.endPhase (RoundSplits.app A B) ph = RoundSplits.endPhase B (RoundSplits.endPhase A ph)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, ph => RoundSplits.endPhase_app A B (FPhase.after a.kind ph)

namespace Spec

def fmtRuns_app : Prop :=
  ∀ (s t : Shape) (A : RoundSplits s) (B : RoundSplits t) (ph ph' ph'' : FPhase),
    A.Runs ph ph' → B.Runs ph' ph'' → (RoundSplits.app A B).Runs ph ph''

def fmtRuns_nil : Prop := ∀ (A : RoundSplits []) (ph : FPhase), A.Runs ph ph

def fmtRuns_local : Prop :=
  ∀ (s : Shape) (ph : FPhase), (RoundSplits.allLocal s).Runs ph (if s = [] then ph else ph.afterLo)

def fmtRuns_shared : Prop :=
  ∀ (s : Shape),
    (RoundSplits.const (RAnn.ofShared .sh) s).Runs .shr .shr ∧
    (s ≠ [] → (RoundSplits.const (RAnn.ofShared .sh) s).Runs .loc .shr)

def fmtRuns_fmt : Prop := ∀ (s : Shape) (A : RoundSplits s) (ph' : FPhase), A.Runs .first ph' → A.Fmt

end Spec

theorem fmtRuns_app : Spec.fmtRuns_app := fun _ _ A B ph _ _ hA hB =>
  ⟨RoundSplits.fmtFrom_app A B ph hA.1 (hA.2 ▸ hB.1), (RoundSplits.endPhase_app A B ph).trans (hA.2 ▸ hB.2)⟩

theorem fmtRuns_nil : Spec.fmtRuns_nil := fun _ _ => ⟨trivial, rfl⟩

theorem FPhase.afterLo_twice (ph : FPhase) : ph.afterLo.afterLo = ph.afterLo := by cases ph <;> rfl

theorem RoundSplits.endPhase_allLocal :
    ∀ (s : Shape) (ph : FPhase),
      RoundSplits.endPhase (RoundSplits.allLocal s) ph = if s = [] then ph else ph.afterLo
  | [], _ => rfl
  | _ :: s, ph => by
    show RoundSplits.endPhase (RoundSplits.allLocal s) ph.afterLo = _
    rw [RoundSplits.endPhase_allLocal s ph.afterLo, if_neg (List.cons_ne_nil _ _)]
    split
    · rfl
    · exact FPhase.afterLo_twice ph

theorem fmtRuns_local : Spec.fmtRuns_local := fun s ph =>
  ⟨RoundSplits.fmtFrom_allLocal s ph, RoundSplits.endPhase_allLocal s ph⟩

theorem RoundSplits.runs_sharedShr : ∀ s : Shape, (RoundSplits.const (RAnn.ofShared .sh) s).Runs .shr .shr
  | [] => ⟨trivial, rfl⟩
  | _ :: s =>
    ⟨⟨⟨fun _ => rfl, inferInstanceAs (Subsingleton Unit)⟩, (RoundSplits.runs_sharedShr s).1⟩,
      (RoundSplits.runs_sharedShr s).2⟩

theorem fmtRuns_shared : Spec.fmtRuns_shared := fun s => ⟨RoundSplits.runs_sharedShr s, fun h => by
  cases s with
  | nil => exact absurd rfl h
  | cons r s => exact ⟨(RoundSplits.runs_sharedShr s).1, (RoundSplits.runs_sharedShr s).2⟩⟩

theorem fmtRuns_fmt : Spec.fmtRuns_fmt := fun _ _ _ h => h.1

end Iop
