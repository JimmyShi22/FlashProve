-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeftOut.lean: what the law of the kind K5 asks of the lookup
(`K3LeftOutIs`, Johnson/Desc/First/Att/K05LeftSeats.lean) follows from `K3LeftAtIs`
(Johnson/Desc/First/Att/K05EntryAt.lean) alone, at the lookup's written out-statement.

Why. `K3LeftAtIs` says "there are rounds": a condition on a carried record cannot name the lookup's
transcript. So whoever lays the kind K5 behind the lookup in a table of joints may take, as the
typed statement in front of K5, the written out-statement at any rounds for which `K3LeftAtIs`
holds. The relation behind the lookup's block has then to be read at these rounds.

Statement and proof. Main name:
  `leftOut_of_leftAtIs`: under `K3LeftAtIs` at s there are rounds rs and a heard record g with
    `K3LeftOutIs` at `lookOutE` h lm first ι st (endsOf h lm first rs), g and s. The four ties hold
    by definition (`outTies_lookOutE`, Johnson/Desc/First/Att/K05OutTies.lean).
Limits: nothing here says that the relation behind the lookup's block holds at these rounds. Nothing
is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeftSeats
import Johnson.Desc.First.Att.K05OutTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb OnBytes OnBytes.Model

/-- **The sharp promise gives the promise that the kind's law asks**, at the written out-statement. -/
theorem leftOut_of_leftAtIs {S St₀ J₀ : Type} [DecidableEq J₀] {fork : S → Option Fork}
    {heard : S → Option Forest.Heard} {h : Forest.Shape} {lm first : ℕ} (ι : Fo.Pl → Option J₀) {Q : Fork → Prop}
    (st : St₀) {s : S} (A : K3LeftAtIs fork heard h lm first Q s) :
    ∃ (rs : TwV.Rounds Cb.Gl.E) (g : Forest.Heard),
      K3LeftOutIs fork heard h lm first ι Q (Fo.lookOutE h lm first ι st (Fo.endsOf h lm first rs)) g s := by
  obtain ⟨F, F', g, rs, q, hn, L, hh, hf⟩ := A
  refine ⟨rs, g, F, F', rs, q, hn, L, hh, hf, ?_⟩
  rw [hn]
  exact outTies_lookOutE h lm first ι st _

end VerifiableInference.Desc.First.Att.P
