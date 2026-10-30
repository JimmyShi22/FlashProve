-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/LeftOnKept.lean: K4's YES MAKES THE LOOKUP's LASTING PROMISE OUT OF ITS SHARP ONE,
AT THE RECORD's OWN TWO READERS `S.fork?` AND `S.lookHeard?` (the readers at which the lookup's own
law concludes `K3LeftAt`: Johnson/Top/H/K3LeftStatement.lean). One statement with its proof:
calls.

  **`leftOn_of_kept`**: `KeptAtS q s s'` (KeptAtS.lean: what a yes of K4's block leaves) and
    `K3LeftAt S.fork? S.lookHeard? h lm first Q s`: then
    `K3LeftOn S.fork? S.lookHeard? h lm first Q s'`, at the same h, lm, first and Q: what was heard
    at that reader stays (`Rest.lookHeard`); the ledger behind is later than the one behind the
    lookup's hearing (`laterFo_of_psc`) and sized (`Later.sized`, from `K3Left.padLeft.fit`).

Limits. ONE DIRECTION. `K3LeftAt` in front is a premise. What the table of joints' item leftOn m
says is a letter of that table's meaning: that `K3LeftOn` gives it is a line on the meaning, asked
where K4's row is laid at the table (files that are not in this tree yet). LeftOnOfYes.lean has the
like at the seat seatS's readers, from a `Yes`. Nothing on soundness.
-/
import Johnson.Road.K4.KeptAtS
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (K3LeftAt K3LeftOn laterFo_of_psc)

/-- **The lasting promise behind K4's yes, out of the sharp one in front.** -/
theorem leftOn_of_kept {q : Par} {s s' : S} (K : KeptAtS q s s') {h : Forest.Shape}
    {lm first : ℕ} {Q : Fork → Prop}
    (hl : K3LeftAt S.fork? S.lookHeard? h lm first Q s) :
    K3LeftOn S.fork? S.lookHeard? h lm first Q s' := by
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _, _, _, _, hR, _⟩ := K
  obtain ⟨F, F', g, rs, qq, n, L, hg, hf⟩ := hl
  have e : s.fork? = some a.F := by simp [S.fork?, ha]
  obtain rfl : a.F = F' := Option.some.inj (e.symm.trans hf)
  exact ⟨F, a.F, G, g, rs, qq, n, L, hR.lookHeard.trans hg, h3, laterFo_of_psc hL,
    hL.sized L.padLeft.fit⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.leftOn_of_kept
