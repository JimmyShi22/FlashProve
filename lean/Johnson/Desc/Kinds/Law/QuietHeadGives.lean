-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/QuietHeadGives.lean: WHAT AN ACCEPT OF THE QUIET STEP BEHIND THE LOOKUP ON
THE DIGITS, AT THE OUTPUT HEAD'S SEGMENT (Johnson/Desc/First/Look/K3Whole.lean: K3.quietHead), GIVES
OF THE STATE BEHIND IT: for whoever must show, of a state in front of the merge, two clauses of the
structure WaK6 (Johnson/Desc/Kinds/Law/WtJointAt.lean): "the covered positions are read" and "the
claim that lies in the state is the one that the program's weightsClaim makes".

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  quietHead_form: the accept, written out: what it read (the covered positions, what the head heard,
      the head's tables), the claim that it made, and the state behind: the state in front with the
      field claim of the head's own part laid, and nothing else turned.
  keptW_claim: laying that field is KeptW (Johnson/Desc/Kinds/Law/WeightAtSame.lean).
  covered_claim: it leaves the reader of the covered positions.
  quietHead_gives: the three together, in the letters of WaK6's clauses.

Every letter under "there is": quietHead_form: a by the state's field here; cov, x, t by the three
reads' equations; claim by weightsClaim's equation. quietHead_gives: cov, t: the same two.
What it does not say. That the step accepts. Nothing on what the claim says of the weights. Nothing
on soundness.
-/
import Johnson.Desc.First.Look.K3Whole
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Kinds.Law.WeightTwinAt
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S HeadOwn)

/-- **The accept, written out.** -/
theorem quietHead_form (X : OnBytes.Model.Verify.Public) {m sF : S}
    (h : K3.quietHead X m = .ok sF) :
    ∃ (a : HeadOwn) (cov : OnBytes.Model.Head.Covered) (x : OnBytes.Model.Head.Heard)
      (t : OnBytes.Model.Head.Tables) (claim : OnBytes.Model.WsClaim),
      m.here = .head a ∧ a.opened = true ∧ m.covered X.T X.P.h.V = .ok cov ∧ a.x = some x ∧
      a.t = some t ∧ First.Look.weightsClaim (runAt X cov x t) X.layers.wsLay = .ok claim ∧
      sF = { m with here := .head { a with claim := some claim } } := by
  unfold K3.quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨_, h1, h⟩ := OnBytes.TieK.ok_of_bind h
    obtain ⟨cov, hc, h⟩ := OnBytes.TieK.ok_of_bind h
    obtain ⟨x, hx, h⟩ := OnBytes.TieK.ok_of_bind h
    obtain ⟨t, ht, h⟩ := OnBytes.TieK.ok_of_bind h
    obtain ⟨claim, hcl, h⟩ := OnBytes.TieK.ok_of_bind h
    obtain ⟨_, _, h⟩ := OnBytes.TieK.ok_of_bind h
    refine ⟨a, cov, x, t, claim, ha, ?_, hc, ?_, ?_, hcl, (Except.ok.inj h).symm⟩
    · unfold need at h1
      split at h1
      · assumption
      · cases h1
    · unfold named at hx
      split at hx
      · rename_i y hy
        rw [hy, Except.ok.inj hx]
      · cases hx
    · unfold named at ht
      split at ht
      · rename_i y hy
        rw [hy, Except.ok.inj ht]
      · cases ht
  · cases h

/-- Laying the head's claim. -/
theorem keptW_claim {m : S} {a : HeadOwn} (ha : m.here = .head a)
    (c : Option OnBytes.Model.WsClaim) : KeptW m { m with here := .head { a with claim := c } } :=
  ⟨a, _, ha, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _⟩

/-- It leaves the reader of the covered positions. -/
theorem covered_claim (m : S) (hr : VerifiableInference.Desc.First.Here) (T V : Nat) :
    ({ m with here := hr } : S).covered T V = m.covered T V := rfl

/-- **What the accept gives, in the letters of WaK6's clauses.** -/
theorem quietHead_gives (X : OnBytes.Model.Verify.Public) {m sF : S}
    (h : K3.quietHead X m = .ok sF) :
    KeptW m sF ∧ ∃ (cov : OnBytes.Model.Head.Covered) (t : OnBytes.Model.Head.Tables),
      sF.covered X.T X.P.h.V = .ok cov ∧
      ∀ o' x claim, sF.here = .head o' → o'.x = some x → o'.claim = some claim →
        First.Look.weightsClaim (runAt X cov x t) X.layers.wsLay = .ok claim := by
  obtain ⟨a, cov, x, t, claim, ha, _, hc, hx, _, hcl, rfl⟩ := quietHead_form X h
  refine ⟨keptW_claim ha _, cov, t, hc, ?_⟩
  intro o' x' claim' ho' hx' hc'
  obtain rfl := VerifiableInference.Desc.First.Here.head.inj ho'
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  obtain rfl : claim = claim' := Option.some.inj hc'
  exact hcl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.quietHead_form
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keptW_claim
#print axioms VerifiableInference.Desc.Kinds.Head.Law.covered_claim
#print axioms VerifiableInference.Desc.Kinds.Head.Law.quietHead_gives
