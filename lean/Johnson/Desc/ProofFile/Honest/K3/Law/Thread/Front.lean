-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/Front.lean: the honest side of the kind "lookup" (K3):
what the lookup's promise in front (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean) gives the
honest side. One structure; theorems.

Terms. Honest/K3/GLOSSARY.md: see there promise (the lookup's, in front), seat, ledger, slot, shape
and public parameters. In this file: p is a lookup's public parameters, s the verifier's state, F a
ledger.

What is shown.
  `FrontOk`: the verifier's state in front, as the theorems on the lookup ask it: the place has a
    shape; the ledger is open; nothing was heard yet; no row waits; the ledger's arrays have their
    size; its count is the place's first slot; there is room for the lookup's slots; they are free.
  `front_calls`, `front_digits`: the lookup's promise in front gives `FrontOk`, at either seat.
Helpers: `ledger_of` (what the two Boolean tests on a ledger say), `onIn_parts` (`k3OnIn`, taken
apart).

Hypotheses that remain.
  `h`: `k3OnIn p s = true`.
  `hd`: the parameters are of the lookup on the calls, or of the one on the digits.
  `hs`, `hf`: (in `ledger_of`) the two Boolean tests accept.

Imported. The library, and of the honest side one file on numbers (Honest/K3/Law/SlotsElems.lean).

Users. Honest/K3/Law/Thread/FrontAt.lean and Honest/K3/Law/Thread/FrontSite.lean call `front_calls`
and `front_digits`.

Limits. Where `k3OnIn` comes from is another file's (FrontAt.lean). Lemmas on the verifier's side
alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Psc.PscFork
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Look.K3Seat
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits faceOf k3OnIn sizedB freeB heardAt)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 The state in front -/

/-- **The verifier's state in front of a lookup's sub-protocol**, at a seat. -/
structure FrontOk {Cl : Type} (seat : Seat FS Cl) (p : P) (h : Shape) (s : FS)
    (F : Fork) : Prop where
  shape : p.shape = some h
  fork : seat.fork s = some F
  heard : (seat.heard s).isNone = true
  owed : (seat.owed s).noneWaits = true
  sized : Sized F
  next : F.next = p.first
  room : p.first + (faceOf h).slots ≤ F.ns
  free : ∀ j, F.next ≤ j → j < p.first + (faceOf h).slots → ¬ Filled F j

/-- What the two Boolean tests on a ledger say. -/
theorem ledger_of {G : Fork} {first n : Nat} (hs : sizedB G = true) (hf : freeB G first n = true) :
    Sized G ∧ first + n ≤ G.ns ∧ ∀ j, first ≤ j → j < first + n → ¬ Filled G j := by
  simp only [sizedB, Bool.and_eq_true, beq_iff_eq] at hs
  simp only [freeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hf
  refine ⟨⟨hs.1.1, hs.1.2, hs.2⟩, hf.1, fun j h1 h2 hfil => ?_⟩
  have e := hf.2 (j - first) (by omega)
  rw [show first + (j - first) = j by omega] at e
  have hlt : j < G.gotF.size := by rw [hs.2]; omega
  have hfil' : G.gotF.getD j false = true := hfil
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    at e hfil'
  rw [e] at hfil'
  exact Bool.noConfusion hfil'

/-- The test `k3OnIn`, taken apart. -/
theorem onIn_parts {p : P} {s : FS} (h : k3OnIn p s = true) :
    ∃ hh G, p.shape = some hh ∧ (heardAt p.digits s).isNone = true ∧
      VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits s.rowsOwed = true ∧ s.fork? = some G ∧
      G.next = p.first ∧ sizedB G = true ∧ freeB G p.first (OnBytes.Model.Forest.elems hh) = true :=
        by
  unfold k3OnIn at h
  cases hs : p.shape with
  | none => rw [hs] at h; exact Bool.noConfusion h
  | some hh =>
    rw [hs] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨a1, a2⟩, a3⟩ := h
    cases hf : s.fork? with
    | none => rw [hf] at a3; exact Bool.noConfusion a3
    | some G =>
      rw [hf] at a3
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at a3
      exact ⟨hh, G, rfl, a1, a2, rfl, a3.1.1, a3.1.2, a3.2⟩

/-- **At the lookup on a link's calls: the lookup's promise in front gives `FrontOk`.** -/
theorem front_calls {Cl : Type} (claim : OnBytes.Model.Aff → Cl) {p : P} {s : FS}
    (hd : p.digits = false) (h : k3OnIn p s = true) :
    ∃ hh F, FrontOk (seatCalls claim) p hh s F := by
  obtain ⟨hh, G, a1, a2, a3, a4, a5, a6, a7⟩ := onIn_parts h
  obtain ⟨b1, b2, b3⟩ := ledger_of a6 a7
  rw [hd] at a2
  refine ⟨hh, G, a1, a4, a2, a3, b1, a5, ?_, ?_⟩
  · rw [Spec.slots_elems]; exact b2
  · intro j h1 h2
    rw [Spec.slots_elems] at h2
    exact b3 j (by rw [← a5]; exact h1) h2

/-- **At the lookup on the digits: the same.** -/
theorem front_digits {Cl : Type} (claim : OnBytes.Model.Aff → Cl) {p : P} {s : FS}
    (hd : p.digits = true) (h : k3OnIn p s = true) :
    ∃ hh F, FrontOk (seatDigits claim) p hh s F := by
  obtain ⟨hh, G, a1, a2, a3, a4, a5, a6, a7⟩ := onIn_parts h
  obtain ⟨b1, b2, b3⟩ := ledger_of a6 a7
  rw [hd] at a2
  refine ⟨hh, G, a1, a4, a2, a3, b1, a5, ?_, ?_⟩
  · rw [Spec.slots_elems]; exact b2
  · intro j h1 h2
    rw [Spec.slots_elems] at h2
    exact b3 j (by rw [← a5]; exact h1) h2

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ledger_of
#print axioms ProofFile.Honest.K3.Law.AtThr.onIn_parts
#print axioms ProofFile.Honest.K3.Law.AtThr.front_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.front_digits
