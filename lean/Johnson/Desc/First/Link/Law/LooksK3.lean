-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksK3.lean: THE TWO LOOKUPS OF A LINK (kind K3: on the calls; on the
approximate range proof's digits) HAND ON «THE LEDGER's ARRAYS HAVE THE PLAN's SHAPES»: K3's share
of the walk of Johnson/Desc/First/Link/Law/LooksWalk.lean. Theorems: THE CALL ALONE. No other file
turns.

THE FACT IS `lkPad_arrays` (Johnson/Top/H/K3Arrays.lean: wherever the flat
function of the lookup's messages returns, the field of the arrays is as it was: no premise), with
`decide_lkPad` (K3KeySizes.lean) and `seatCalls_keeps`, `seatDigits_keeps` (K3SeatFits.lean). New
here:
the seats' laying leaves the link's context.
  `link_putFork`, `link_mark`, `link_hearLook`; `calls_put_link`, `digits_put_link`.
  `k3_steps_seat`: at any seat at the first chain's state that reads the open ledger, keeps the
    ledger laid, and whose laying leaves the context.
  `k3_steps_calls`, `k3_steps_digits`: **(K3.block (seatCalls | seatDigits claim) …).Steps
    (KeepsLooks shOf)**. `via_steps_calls`, `via_steps_digits`: so of `K3.Law.blockVia`, where its
    test
    on the plan says yes.
Limits. THE DECISION ALONE: nothing on the runs of claims, NOR ON THE STEP WITHOUT A ROUND THAT IS
JOINED BEHIND THE ROUNDS (`K3.quietAt`). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Top.H.K3Arrays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps decide_lkPad
        lkPad_arrays)

theorem link_putFork (s : S) (G : Fork) : (s.putFork G).link? = s.link? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, S.link?, ho]
  | _ => rfl

theorem link_mark (s : S) (n : String) : (s.mark n).link? = s.link? := by
  unfold S.mark
  split <;> rfl

theorem link_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).link? = s.link? := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact link_mark s _
    · simp [S.link?, ha]
  · rename_i a ha
    split
    · exact link_mark s _
    · simp [S.link?, ha]
  · rename_i a ha
    split
    · exact link_mark s _
    · split
      · exact link_mark s _
      · simp [S.link?, ha]
  · exact link_mark s _

theorem calls_put_link {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatCalls claim).put s g G).link? = s.link? :=
  (link_hearLook _ g).trans (link_putFork s G)

theorem digits_put_link {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatDigits claim).put s g G).link? = s.link? := by
  unfold seatDigits
  dsimp only
  split
  · exact (link_putFork _ G).trans (First.K8.putTl_link _ _)
  · exact link_mark s _

/-- At any seat that reads the open ledger, keeps the ledger laid, and leaves the context. -/
theorem k3_steps_seat {Cl : Type} (shOf : ℕ → List Look) (seat : Seat S Cl)
    (hf : ∀ s, seat.fork s = s.fork?) (hk : SeatKeeps seat)
    (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    (K3.block seat piece laid before p guests).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  obtain ⟨F, F', g, t, hF, hn, hp, rfl⟩ := decide_lkPad seat piece laid before p guests s s' rs gs h
  have e1 : (seat.put s g F').fork? = some F' := by
    rw [← hf]
    exact hk s g F' (by rw [hF]; rfl) hn
  refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF
  · rw [← hl s g F']
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact congrArg (·.map look) (lkPad_arrays p.calls p.pub p.lid F F' t [] g hp)

/-- **K3: the lookup on a link's calls.** -/
theorem k3_steps_calls {Cl : Type} (shOf : ℕ → List Look) (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    (K3.block (seatCalls claim) piece laid before p guests).Steps (KeepsLooks shOf) :=
  k3_steps_seat shOf _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) piece laid
    before p guests

/-- **K3: the lookup on the approximate range proof's digits.** -/
theorem k3_steps_digits {Cl : Type} (shOf : ℕ → List Look) (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    (K3.block (seatDigits claim) piece laid before p guests).Steps (KeepsLooks shOf) :=
  k3_steps_seat shOf _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim) piece laid
    before p guests

/-- So of `blockVia`, where its test on the plan says yes: on the calls. -/
theorem via_steps_calls {Cl : Type} (shOf : ℕ → List Look) (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl))
    (hplan : (K3.Law.blockVia (seatCalls claim) piece laid before p guests).planOk = true) :
    (K3.Law.blockVia (seatCalls claim) piece laid before p guests).Steps (KeepsLooks shOf) :=
  fun s rs gs s' h => k3_steps_calls shOf claim piece laid before p guests s rs gs s'
    (K3.Law.blockVia_decide hplan h)

/-- On the digits. -/
theorem via_steps_digits {Cl : Type} (shOf : ℕ → List Look) (claim : Aff → Cl) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl))
    (hplan : (K3.Law.blockVia (seatDigits claim) piece laid before p guests).planOk = true) :
    (K3.Law.blockVia (seatDigits claim) piece laid before p guests).Steps (KeepsLooks shOf) :=
  fun s rs gs s' h => k3_steps_digits shOf claim piece laid before p guests s rs gs s'
    (K3.Law.blockVia_decide hplan h)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k3_steps_seat
#print axioms VerifiableInference.Desc.LinkJoin.k3_steps_calls
#print axioms VerifiableInference.Desc.LinkJoin.k3_steps_digits
#print axioms VerifiableInference.Desc.LinkJoin.via_steps_calls
#print axioms VerifiableInference.Desc.LinkJoin.via_steps_digits
