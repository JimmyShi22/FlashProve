-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/SendersW.lean: at the last chain's proximity test, two of
the group's members held to their senders, as far as that is small: the review's term (h1), «no
laying before each is the sender's own, by rfl or a lemma». W's own member is held by K1's authors'
laying (`wLotAt_halves`, not here). Definitions none; five theorems.

  `firstRide_eq`   the first opening's two texts of its ride are one, at every first record
  `rowsR_no_main`   a message without main rows reads no data
  `first_last_no_main`   the index-mask message has no main row, at the written plan
  `first_member_is_sender`   THE INDEX-MASK MEMBER: `jobW`'s job `K1.firstJob` and the filling's
                 sender `placeJob … (firstFold …) D` have one plan and one ride, and where the
                 message has no main row they lay one row at every data, input and front
  `omega_data_shift`   THE OMEGA MEMBER: the data of Omega's sending at the number of "LIN point"
                 moved by the length of what stands in front of what it heard is its data at what
                 it heard

Limits.
- `first_member_is_sender` has no main row as a premise: `first_last_no_main` pays it at the written
  plan; under the head `eG_atAll` is the caller's.
- `omega_data_shift` is on the job's `data`, at one `ask` on both sides. That the last chain's
  `heard` is the first chain's then the shared chain's is `Ready.start₃`'s text; that its first
  part's length is n₁ is a duty of whoever lays the job (JobW.lean). It holds Omega to its data at
  all that the shared chain heard, not yet to the sender's, which had heard a prefix of that: the
  data reads one challenge, number a, and that does not move while a stands within the prefix
  (the shared rounds' authors' `drop_take_snoc`, K14/ExactOfRows.lean): no law here. The test's
  `ask` and the sender's are one where the readers are one; `memOmega_rand` (HalfO.lean) takes
  `rand` out of it; for `weights`: OmegaMemberSent.lean.
- `first_member_is_sender`'s last clause is typed at `rideOf (firstFold …)` on both sides; `memK1`'s
  purse is at `firstRide`: the step across `firstRide_eq` is a cast that a caller must make.
- The same coins: that the stretch which the test carries holds the coins with which the sender
  made its message is not here.
- What may be said of this pair on hiding stands in the head of HalfW.lean in this folder.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes.Slice (GE GF)
open Johnson.Prover.Send (shapeAt)

/-- **The first opening's two texts of its ride are one.** -/
theorem firstRide_eq (q : OnBytes.Params.First) :
    ProofFile.Honest.K1.firstRide q = ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold q) := by
  funext k
  rfl

/-- **A message without main rows reads no data.** -/
theorem rowsR_no_main (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (d d' : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (K1.dueR P ride)) (k : Nat)
    (h : (shapeAt P k).mainRows = 0) : K1.rowsR P ride d c k = K1.rowsR P ride d' c k := by
  simp [K1.rowsR, h]

set_option maxRecDepth 1000000 in
/-- The index-mask message has no main row, at the written plan. An evaluation in Lean's kernel. -/
theorem first_last_no_main : (shapeAt VerifiableInference.Desc.K1.parGF
    (VerifiableInference.Desc.K1.parGF.sent.size - 1)).mainRows = 0 := by decide +kernel

/-- **The index-mask member's job and the filling's sender have one plan and one ride, and at a
message without main rows they lay one row**, at every data, input and front. -/
theorem first_member_is_sender {X Xi : Type} (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (first : Nat) (D : RowDataOf Xi) (part : Nat) :
    (K1.firstJob S Z G : K1.SendJob Readers X).P =
        (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar G.first
          (VerifiableInference.Desc.K1.gpOf Z)) first (K1.firstFold G.first) D part).P ∧
      (K1.firstJob S Z G : K1.SendJob Readers X).ride =
        (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar G.first
          (VerifiableInference.Desc.K1.gpOf Z)) first (K1.firstFold G.first) D part).ride ∧
      ∀ (w : Readers) (fr : Front X) (v : K1.PlaceIn Xi) (gr : Front X)
        (c : Cs (K1.dueR (VerifiableInference.Desc.K1.firstPar G.first
          (VerifiableInference.Desc.K1.gpOf Z)) (K1.rideOf (K1.firstFold G.first)))) (k : Nat),
        (shapeAt (VerifiableInference.Desc.K1.firstPar G.first
          (VerifiableInference.Desc.K1.gpOf Z)) k).mainRows = 0 →
        K1.rowsR _ (K1.rideOf (K1.firstFold G.first))
            ((K1.firstJob S Z G : K1.SendJob Readers X).data w fr) c k =
          K1.rowsR _ (K1.rideOf (K1.firstFold G.first))
            ((K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar G.first
              (VerifiableInference.Desc.K1.gpOf Z)) first (K1.firstFold G.first) D part).data v gr)
            c k :=
  ⟨rfl, firstRide_eq _, fun _ _ _ _ c k h => rowsR_no_main _ _ _ _ c k h⟩

/-- **Omega's data at the moved number, at what stands in front and what it heard, is its data at
what it heard.** -/
theorem omega_data_shift (P : Desc.K14.P14) (a : Nat) (ask : ProofFile.Honest.K14.Ask)
    (h₁ h₂ : List Fmt.Drawn) (k : Nat) :
    (ProofFile.Honest.K14.jobOmega ⟨P, h₁.length + a⟩).data ⟨ask, h₁ ++ h₂, ()⟩ k =
      (ProofFile.Honest.K14.jobOmega ⟨P, a⟩).data ⟨ask, h₂, ()⟩ k := by
  have e : (h₁ ++ h₂).drop (h₁.length + a) = h₂.drop a := by
    induction h₁ with
    | nil => simp
    | cons z zs ih =>
      have e' : (z :: zs).length + a = (zs.length + a) + 1 := by
        simp only [List.length_cons]
        omega
      rw [e', List.cons_append, List.drop_succ_cons, ih]
  simp only [ProofFile.Honest.K14.jobOmega, heardFrom, e]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.firstRide_eq
#print axioms ProofFile.Honest.K12.AtProof.rowsR_no_main
#print axioms ProofFile.Honest.K12.AtProof.first_last_no_main
#print axioms ProofFile.Honest.K12.AtProof.first_member_is_sender
#print axioms ProofFile.Honest.K12.AtProof.omega_data_shift
