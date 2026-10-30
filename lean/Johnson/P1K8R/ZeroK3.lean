-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroK3.lean: THE TWO LOOKUPS' DECISIONS (K3) STEP IN `KeepsZero`. MADE BY PROGRAM FROM
THE LIBRARY's Johnson/Desc/First/Link/Law/LooksK3.lean, WITH THE ROWS' FIRST COLUMNS (`l0s`,
Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE OF
KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under a
new name; the others are called where they lie. None of the library's goals. No prover stands in it;
nothing on completeness, soundness or hiding.

  `k3_kz_seat`, **`k3_kz_calls`**, **`k3_kz_digits`**, `via_kz_calls`, `via_kz_digits`   there: the
      same names with "steps"; the ground is the library's lkPad_arrays: the lookup's hearing leaves
      the arrays
Limits. THE DECISIONS ALONE: nothing on the runs of claims (Johnson/P1K8R/ZeroVia.lean has these).
The last two under "the sub-protocol's test on the plan says yes". Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroShims
import Johnson.Desc.First.Link.Law.LooksK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps decide_lkPad
        lkPad_arrays)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- At any seat that reads the open ledger, keeps the ledger laid, and leaves the context. -/
theorem k3_kz_seat {Cl : Type} (seat : Seat S Cl)
    (hf : ∀ s, seat.fork s = s.fork?) (hk : SeatKeeps seat)
    (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    (K3.block seat piece laid before p guests).Steps KeepsZero := by
  intro s rs gs s' h
  obtain ⟨F, F', g, t, hF, hn, hp, rfl⟩ := decide_lkPad seat piece laid before p guests s s' rs gs h
  have e1 : (seat.put s g F').fork? = some F' := by
    rw [← hf]
    exact hk s g F' (by rw [hF]; rfl) hn
  refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF
  · rw [← hl s g F']
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact congrArg (·.map l0s) (lkPad_arrays p.calls p.pub p.lid F F' t [] g hp)

/-- **K3: the lookup on a link's calls.** -/
theorem k3_kz_calls {Cl : Type} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    (K3.block (seatCalls claim) piece laid before p guests).Steps KeepsZero :=
  k3_kz_seat _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) piece laid
    before p guests

/-- **K3: the lookup on the approximate range proof's digits.** -/
theorem k3_kz_digits {Cl : Type} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    (K3.block (seatDigits claim) piece laid before p guests).Steps KeepsZero :=
  k3_kz_seat _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim) piece laid
    before p guests

/-- So of `blockVia`, where its test on the plan says yes: on the calls. -/
theorem via_kz_calls {Cl : Type} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl))
    (hplan : (K3.Law.blockVia (seatCalls claim) piece laid before p guests).planOk = true) :
    (K3.Law.blockVia (seatCalls claim) piece laid before p guests).Steps KeepsZero :=
  fun s rs gs s' h => k3_kz_calls claim piece laid before p guests s rs gs s'
    (K3.Law.blockVia_decide hplan h)

/-- On the digits. -/
theorem via_kz_digits {Cl : Type} (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl))
    (hplan : (K3.Law.blockVia (seatDigits claim) piece laid before p guests).planOk = true) :
    (K3.Law.blockVia (seatDigits claim) piece laid before p guests).Steps KeepsZero :=
  fun s rs gs s' h => k3_kz_digits claim piece laid before p guests s rs gs s'
    (K3.Law.blockVia_decide hplan h)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k3_kz_seat
#print axioms VerifiableInference.Desc.LinkJoin.k3_kz_calls
#print axioms VerifiableInference.Desc.LinkJoin.k3_kz_digits
#print axioms VerifiableInference.Desc.LinkJoin.via_kz_calls
#print axioms VerifiableInference.Desc.LinkJoin.via_kz_digits
