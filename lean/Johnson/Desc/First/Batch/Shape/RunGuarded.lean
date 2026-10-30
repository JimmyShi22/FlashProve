-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/RunGuarded.lean: FROM A BARE RUN OF CLAIMS TO THE RUN AS IT STANDS IN
A SEATED CHAIN. General laws; nothing is evaluated.

Why. In the proof file's chain a hearing sub-protocol stands behind a guard (Block.guarded,
Johnson/Desc/SeatGuard.lean): each of its runs of claims is laid as "the run; then a refusal if the
seat is not as it was in front". The kinds' laws (RunLaw, ClaimShape.lean) speak of the bare runs;
the gathering at the seat calls the guarded ones.

  `guardRun same run`: the run behind the guard, as Block.guarded lays it.
  `guardRun_iff`: it returns y just where the run returns y and the seat stayed.
  `lookup_map` (the library's Johnson/Desc/K6/Shape/Core.lean has it too); `lookup_guarded`: a run
    that is looked up by name in a guarded sub-protocol is guardRun of the run of that name in the
    bare one.
  **`RunLaw.guarded`**: a bare run's RunLaw gives the guarded run's, with the same runG and the same
    pre, IF THE BARE RUN KEEPS THE SEAT WHERE IT RETURNS (one small law for each run).
  `guarded_same`: a guarded run returns only where the seat stayed.

Limits. As ClaimShape.lean's. RunLaw.guarded asks "keeps" at every return of the bare run and spends
it behind R.returns alone: a run that keeps the seat only under its pre is not served. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.ClaimShape
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh)

/-- The run behind the guard. -/
def guardRun (same : S → S → Bool) (run : Run) : Run :=
  fun n t => (run n t).bind fun y => (seatSame same t y.2).map fun _ => y

theorem guardRun_iff (same : S → S → Bool) (run : Run) (n : Nat) (s : S) (y : List Claim × S) :
    guardRun same run n s = .ok y ↔ run n s = .ok y ∧ same s y.2 = true := by
  unfold guardRun
  cases hr : run n s with
  | error e => exact ⟨(fun h => nomatch h), (fun h => nomatch h.1)⟩
  | ok z =>
    show ((seatSame same s z.2).map fun _ => z) = .ok y ↔ _
    unfold seatSame
    by_cases hs : same s z.2 = true
    · rw [if_pos hs]
      constructor
      · intro h
        obtain rfl : z = y := Except.ok.inj h
        exact ⟨rfl, hs⟩
      · rintro ⟨h, -⟩
        obtain rfl : z = y := Except.ok.inj h
        rfl
    · rw [if_neg hs]
      constructor
      · intro h
        exact nomatch h
      · rintro ⟨h, h2⟩
        obtain rfl : z = y := Except.ok.inj h
        exact absurd h2 hs

theorem lookup_map {α β : Type} (f : α → β) (nm : String) : ∀ l : List (String × α),
    (l.map fun c => (c.1, f c.2)).lookup nm = (l.lookup nm).map f
  | [] => rfl
  | c :: l => by
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    cases nm == c.1 with
    | true => rfl
    | false => exact lookup_map f nm l

theorem lookup_guarded (same : S → S → Bool) (but : Place → Bool) (b : Block S Claim)
    (nm : String) :
    (b.guarded same but).claims.lookup nm = (b.claims.lookup nm).map (guardRun same) :=
  lookup_map (guardRun same) nm b.claims

/-- **From a bare run's law to the guarded run's.** -/
def RunLaw.guarded {run : Run} (R : RunLaw run) (same : S → S → Bool)
    (keeps : ∀ (n : Nat) (s s' : S) (cs : List Claim), run n s = .ok (cs, s') →
      same s s' = true) : RunLaw (guardRun same run) where
  runG := R.runG
  pre := R.pre
  carries := fun n s s' cs y hp h hg =>
    R.carries n s s' cs y hp ((guardRun_iff same run n s (cs, s')).1 h).1 hg
  returns := fun n s y hg hp => by
    obtain ⟨⟨cs, s'⟩, hz⟩ := R.returns n s y hg hp
    exact ⟨(cs, s'), (guardRun_iff same run n s (cs, s')).2 ⟨hz, keeps n s s' cs hz⟩⟩

theorem guarded_same (same : S → S → Bool) (run : Run) (n : Nat) (s s' : S) (cs : List Claim)
    (h : guardRun same run n s = .ok (cs, s')) : same s s' = true :=
  ((guardRun_iff same run n s (cs, s')).1 h).2

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.guardRun_iff
#print axioms VerifiableInference.Desc.K9.Shape.lookup_guarded
#print axioms VerifiableInference.Desc.K9.Shape.RunLaw.guarded
#print axioms VerifiableInference.Desc.K9.Shape.guardRun
#print axioms VerifiableInference.Desc.K9.Shape.lookup_map
#print axioms VerifiableInference.Desc.K9.Shape.guarded_same
