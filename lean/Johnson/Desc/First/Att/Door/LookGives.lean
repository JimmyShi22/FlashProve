-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/LookGives.lean: BESIDE THE TABLE: WHAT A YES OF sameHeardB (Johnson/Desc/First/Att/Door/PubK5.lean: "both readers of what the lookup on the calls returned give one thing") GIVES: EQUATIONS, FIELD BY FIELD, at the fields that K5's texts read of the two homes: the points zx | zy | zb0 | zb1 | zk · theta | alpha | a · e | tT · the three numbers of owed claims · sBit · leavesA · the last claim's form's slots and constant. No Mathlib.
sameHeard_shape: the lookups' own test on the two shapes says yes (what THAT gives is left to the lookups' files) · lookAtt_opens: a yes of lookAttB gives both homes and sameHeardB's yes. NOT OPENED: rows · the leaves' sumcheck · cEnd's entries (lookAttB asks beside that gL's are none).
-/
import Johnson.Desc.First.Att.Door.PubK5

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model

theorem sameHeard_gives {g h : Forest.Heard} (e : sameHeardB g h = true) :
    g.theta = h.theta ∧ g.alpha = h.alpha ∧ g.a = h.a ∧ g.leavesA = h.leavesA ∧ g.sBit = h.sBit ∧ g.zx = h.zx ∧
      g.zy = h.zy ∧ g.e = h.e ∧ g.zb0 = h.zb0 ∧ g.zb1 = h.zb1 ∧ g.tT = h.tT ∧ g.zk = h.zk ∧
      g.owedObjects = h.owedObjects ∧ g.owedPlanes = h.owedPlanes ∧ g.owedJoin = h.owedJoin ∧
      g.cEnd.slots = h.cEnd.slots ∧ g.cEnd.const = h.cEnd.const := by
  unfold sameHeardB sameAff at e
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩,
    ⟨⟨_, c1⟩, c2⟩⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := e
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, c1, c2⟩

/-- And the lookups' own test on the two shapes says yes. -/
theorem sameHeard_shape {g h : Forest.Heard} (e : sameHeardB g h = true) :
    VerifiableInference.Desc.K3.sameShapeAll g.shape h.shape = true := by
  unfold sameHeardB at e
  simp only [Bool.and_eq_true] at e
  exact e.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1

/-- **What a yes of look m's Bool gives, opened**: both homes are laid, and what they hold is one in the seventeen fields and by the lookups' test on the shapes. -/
theorem lookAtt_opens {s : VerifiableInference.Desc.First.S} (e : lookAttB s = true) :
    ∃ a g gL, s.here = .att a ∧ a.g = some g ∧ a.lookHeard = some gL ∧ sameHeardB g gL = true := by
  unfold lookAttB lookAttUpTo at e
  split at e
  · rename_i a ha
    split at e
    · rename_i g gL e1 e2
      simp only [Bool.and_eq_true] at e
      exact ⟨a, g, gL, ha, e1, e2, e.1.1⟩
    · cases e
  · cases e

#print axioms sameHeard_gives
#print axioms sameHeard_shape
#print axioms lookAtt_opens

end H2K5.Door
