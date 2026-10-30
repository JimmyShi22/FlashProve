-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4KeepKeeper.lean: THE TABLE's OWN LAYER's THREE PUBLIC ITEMS (ledger · freeAbove ·
unheard: Johnson/Desc/First/FillKeeper.lean: `ledgerB`, `freeAboveB n`, `unheardB`) RIDE PAST A YES
OF K4's BLOCK. Said of `KeptAtS` (KeptAtS.lean: what a yes of K4's block leaves), then of the layer
`fillKeeper` at a `Yes`. Statements and proofs: calls of FreeAboveKept.lean; the tests' texts are
unfolded.

  `ledgerB_kept`: `ledgerB s` gives `ledgerB s'` (`sized_kept`).
  `freeAboveB_kept`: `ledgerB s` and `freeAboveB n s` give `freeAboveB n s'` (`freeAboveN_kept`):
    K4's yes takes slots from the ledger's next free number on and moves that number past them; the
    number of slots stays.
  `unheardB_kept`: `unheardB s'` is `unheardB s` (`Rest.out`).
  **`keeper_rides`**: at `fillKeeper nsOf Mg`, every Mg, at a `Yes`: where ledger m is true in
    front: each of ledger m' · freeAbove m' · unheard that is true in front is true behind: THREE
    MEMBERS OF THE SENTENCE keepQ OF K4PubBehind.lean.

Limits. AT `fillKeeper … Mg` ITSELF: a layer that is laid over it must hand the three on. The tests
read the OPEN segment's ledger whatever the item's number m' is (the layer's own make). ONE
DIRECTION, FROM A YES. Nothing on soundness.
-/
import Johnson.Road.K4.FreeAboveKept
import Johnson.Road.K4.KeptOfYes
import Johnson.Desc.First.FillKeeper

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (S Pub Meaning ledgerB freeAboveB unheardB fillKeeper)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K3 (sizedB)

variable {q : Par} {s s' : S}

/-- `fillKeeper`'s test on the ledger is "a ledger is open, and it is sized". -/
theorem ledgerB_iff (s : S) : ledgerB s = true ↔ ∃ F, s.fork? = some F ∧ sizedB F = true := by
  unfold ledgerB sizedB
  cases s.fork? with
  | none => simp
  | some F => simp

/-- `fillKeeper`'s test on the room is "a ledger is open, free above, with n slots". -/
theorem freeAboveB_iff (n : ℕ) (s : S) :
    freeAboveB n s = true ↔ ∃ F, s.fork? = some F ∧ freeAboveN n F = true := by
  unfold freeAboveB freeAboveN freeAboveF
  cases s.fork? with
  | none => simp
  | some F => simp

/-- Behind a yes of K4's block a ledger is open. -/
theorem fork_kept (K : KeptAtS q s s') : ∃ G, s'.fork? = some G := by
  obtain ⟨_, _, _, G, _, _, h3, _⟩ := K
  exact ⟨G, h3⟩

theorem ledgerB_kept (K : KeptAtS q s s') (h : ledgerB s = true) : ledgerB s' = true := by
  obtain ⟨F, e, hz⟩ := (ledgerB_iff s).mp h
  obtain ⟨G, hG⟩ := fork_kept K
  exact (ledgerB_iff s').mpr ⟨G, hG,
    sized_kept K (fun F' e' => by rw [Option.some.inj (e.symm.trans e')] at hz; exact hz) G hG⟩

theorem freeAboveB_kept (K : KeptAtS q s s') {n : ℕ} (hl : ledgerB s = true)
    (h : freeAboveB n s = true) : freeAboveB n s' = true := by
  obtain ⟨F, e, hz⟩ := (ledgerB_iff s).mp hl
  obtain ⟨F1, e1, hf⟩ := (freeAboveB_iff n s).mp h
  obtain ⟨G, hG⟩ := fork_kept K
  exact (freeAboveB_iff n s').mpr ⟨G, hG, freeAboveN_kept K
    (fun F' e' => by rw [Option.some.inj (e.symm.trans e')] at hz; exact hz)
    (fun F' e' => by rw [Option.some.inj (e1.symm.trans e')] at hf; exact hf) G hG⟩

theorem unheardB_kept (K : KeptAtS q s s') : unheardB s' = unheardB s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := K
  unfold unheardB
  rw [hR.out]

variable {P W Cl : Type} {Fr : Frame} (nsOf : ℕ → Option ℕ) (Mg : Meaning P W) (Z : P)
  {pc : Piece (ckP .two) Fr S Cl W} {par : Par}

/-- **The table's own three items ride past a `Yes`**, at the table's own layer, over every meaning.
-/
theorem keeper_rides {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard}
    {o : Own} {G : Fork} (y : Yes seatS par pc a τ fo o G) (m : ℕ)
    (hl : (fillKeeper nsOf Mg).pub (.ledger m) (Z, a.1) = true) (m' : ℕ) :
    (fillKeeper nsOf Mg).pub (.ledger m') (Z, (behindOf seatS pc a τ o G).1) = true ∧
    ((fillKeeper nsOf Mg).pub (.freeAbove m') (Z, a.1) = true →
      (fillKeeper nsOf Mg).pub (.freeAbove m') (Z, (behindOf seatS pc a τ o G).1) = true) ∧
    ((fillKeeper nsOf Mg).pub .unheard (Z, a.1) = true →
      (fillKeeper nsOf Mg).pub .unheard (Z, (behindOf seatS pc a τ o G).1) = true) := by
  have K := kept_of_yes y
  have hl' : ledgerB a.1 = true := hl
  refine ⟨ledgerB_kept K hl', fun h => ?_, fun h => ?_⟩
  · show ((nsOf m').any fun n => freeAboveB n (behindOf seatS pc a τ o G).1) = true
    have h' : ((nsOf m').any fun n => freeAboveB n a.1) = true := h
    cases hn : nsOf m' with
    | none => simp [hn] at h'
    | some n =>
      have h2 : freeAboveB n a.1 = true := by simpa [hn] using h'
      simpa using freeAboveB_kept K hl' h2
  · show unheardB (behindOf seatS pc a τ o G).1 = true
    rw [unheardB_kept K]
    exact h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ledgerB_kept
#print axioms OnBytes.Road.K4.freeAboveB_kept
#print axioms OnBytes.Road.K4.keeper_rides
