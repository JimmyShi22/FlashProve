-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineMembersFits.lean: the frame's test on a side (`Side.fits`) at a lookup's row at owners
(`proverSideOfLookupInChain`, Honest/K3/RowOwned.lean), each part beside `lookSims`: the row that the key file's
prover lays. It stands beside E2E/OfflineMembers.lean, which has `exact` and `fresh` at that row.

  `fits_owned`       `Side.fits` at such a side, from the block's entries: it reads no book

A test of form: it says nothing on whether the job is the protocol's. Nothing on any property.
-/
import E2E.OfflineMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Oracle)
open VerifiableInference.Desc.K3 (entriesV entriesFit)

variable {S Cl V W X Pb Wk : Type}

/-- **The side passes the frame's test** (`Side.fits`): each simulator names its part's address, the
row has one move for each declared round, and each round has its list of oracle messages. Conditional
on hrow, on the sub-protocol's place, and on the four premises of `rowStated_owned`. It reads no book:
a test of form. -/
theorem fits_owned {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads) (J : LookJobs Wk)
    (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (hp : σ.block.place = a.place) (es : List Fmt.Entry) (hr : σ.block.rounds = es.map declOf)
    (ho : σ.block.oracles = es.map fun _ => []) (hfit : entriesFit a.face es = true)
    (hok : a.face.ok = true) : σ.fits = true := by
  have h2 : 2 ≤ a.face.planes := by
    unfold VerifiableInference.Desc.K3.Face.ok at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1.1.1.1.2
  have hl : es.length = (entriesV a.face).length := by
    unfold entriesFit at hfit
    have e : (es.map fun e => { e with work := 0 }) = entriesV a.face :=
      of_decide_eq_true (by simpa using hfit)
    rw [← e, List.length_map]
  have hlen : (proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.length =
      (lookSims (Pb := Pb) a).length := by
    have e := congrArg List.length (owned_seat_moves (V := V) (X := X) o R J wit a)
    rw [List.length_map, List.length_map] at e
    rw [e, lookSims_length]
  have h1 : σ.row.zipIdx.all (fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) = true := by
    rw [hrow, hp]
    exact addrs_fit a (stages a.face) _ 0
  have h3 : σ.half.rounds = σ.block.rounds.length := by
    unfold Side.half Placed.rounds
    show List.foldl _ 0 (σ.row.map (·.1)) = _
    rw [hrow, map_fst_zip_eq _ _ hlen, foldl_add_eq_sum (fun p : Part V W X => p.moves.length),
      owned_seat_moves, rounds_stages a.face h2, hr, List.length_map, hl, Nat.zero_add]
  have h4 : σ.block.oracles.length = σ.block.rounds.length := by
    rw [ho, hr, List.length_map, List.length_map]
  unfold Side.fits
  simp only [h1, h3, h4, beq_self_eq_true, Bool.and_self]

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.fits_owned
