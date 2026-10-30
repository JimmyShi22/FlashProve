-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/Fills.lean: WHAT ONE CALL OF THE PLAIN ENGINE FILLS: a run of hidden values; a
sending of claimed values; a product layer; a token sumcheck. Statements and proofs: each is read
off a law of the call (`hideRun_ok`, `hideRun_keeps`, OnBytes/Tie/Pv/Psc/; `claimsIn_spec`,
`levelIn_heard`, `tscIn_heard`, `filledA_of_publicPart`, OnBytes/Desc/First/P1/).

Each law: from a ledger F with arrays of the right sizes (`Sized`) to the ledger G that the call
hands on: G is `Sized`; what is filled in F is filled in G; and
  `run_fills`: the run's slots are filled in G.
  `claimsIn_fills`: the n slots from the returned one on.
  `level_fills`: the layer's two end values' slots; and EVERY SLOT THAT THE LAYER's OWN CLAIM
    (`Level.row`) NAMES: the layer lays its own window itself, and it begins only where the public
    part of its start form C is there, which is so only where every slot of C is filled.
  `tsc_fills`: the slot of the claimed sum; the n end values' slots; the start form's slots. NOT ITS
    WINDOW: a token sumcheck's own claim is made later.

Limits. One direction, from a return. Nothing on what lies under a slot. Nothing on soundness.

-/
import Johnson.Road.K4.Slots.SlotsIn
import OnBytes.Desc.First.P1.Heard
import OnBytes.Desc.First.P1.BatchPoint
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.PscRun (Sized Filled hideRun_ok hideRun_keeps)
open OnBytes.Desc.First.P1 (levelIn_heard tscIn_heard claimsIn_spec filledA_of_publicPart)

/-- A run of hidden values. -/
theorem run_fills {F G : Fork} {first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (h : F.hideRun first v k = some G) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧ ∀ i, i < v.size → Filled G (first + i) := by
  obtain ⟨_, s, f, _⟩ := hideRun_ok F G first v k hF h
  exact ⟨s, fun j hj => ((hideRun_keeps h).keep j hj).1, fun i hi => (f i hi).2.2.1⟩

/-- A sending of n claimed values. -/
theorem claimsIn_fills {n j : ℕ} {F G : Fork} {t u : Tape} (hF : Sized F)
    (h : Fl.claimsIn n F t = some (j, G, u)) :
    Sized G ∧ (∀ x, Filled F x → Filled G x) ∧ ∀ i, i < n → Filled G (j + i) := by
  obtain ⟨rfl, v, hv, _, _, r⟩ := claimsIn_spec h
  obtain ⟨s, k, f⟩ := run_fills (show Sized ({ F with next := F.next + n } : Fork) from hF) r
  exact ⟨s, k, fun i hi => f i (by omega)⟩

/-- **A product layer.** -/
theorem level_fills {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape}
    {L : Level} (hF : Sized F) (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧ Filled G L.sL ∧ Filled G L.sR ∧
      SlotsIn (Filled G) L.row := by
  obtain ⟨_, _, hpub, _, _, _, _, _, _, _, _, hst, _, _, _, hsR, _, _, v, G1, hv, r1, hrow, r2⟩ :=
    levelIn_heard h
  obtain ⟨s1, k1, f1⟩ :=
    run_fills (show Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) from hF) r1
  obtain ⟨s2, k2, f2⟩ := run_fills s1 r2
  refine ⟨s2, fun j hj => k2 j (k1 j hj), k2 _ (by simpa using f1 0 (by omega)), ?_, ?_⟩
  · rw [hsR]
    exact k2 _ (f1 1 (by omega))
  · rw [hrow]
    refine slotsIn_rowForm _ _ (fun i hi => f2 i (by simpa using hi)) ?_ slotsIn_empty
    rw [hst]
    exact fun x hx => k2 _ (k1 _ (filledA_of_publicPart hpub x hx).2)

/-- **A token sumcheck.** -/
theorem tsc_fills {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc} (hF : Sized F)
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧ Filled G o.sCl ∧
      (∀ i, i < n → Filled G (o.sEnd + i)) ∧ SlotsIn (Filled G) o.p.start := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hst, hcl, _, _, v, G0, r0, _, _, _, hvn, r1⟩ := tscIn_heard h
  obtain ⟨s0, k0, f0⟩ := run_fills (show Sized ({ F with next := F.next + 1 } : Fork) from hF) r0
  obtain ⟨s1, k1, f1⟩ := run_fills (show Sized ({ G0 with
    next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) from s0) r1
  have hc : Filled G F.next := k1 _ (by simpa using f0 0 (by simp))
  refine ⟨s1, fun j hj => k1 j (k0 j hj), by rw [hcl]; exact hc, fun i hi => f1 i (by omega), ?_⟩
  rw [hst]
  exact slotsIn_slot hc

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.level_fills
#print axioms OnBytes.Desc.First.K4.Slots.tsc_fills
#print axioms OnBytes.Desc.First.K4.Slots.claimsIn_fills
