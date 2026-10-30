-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotCount.lean: the two lists of the honest sender's jobs of the kind K1 on the
first chain have 52 entries together, in the scope of the release's goal statements, where the maker
returns at OnBytes.secondHashFunction.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  lotJobs_length     For all public parts Z and grounds G, the list lotJobs
                     (Johnson/SendSim/Seat/Lot.lean) is as long as the list of sub-protocols of K1's
                     own lot (ProofFile.k1Pure Z).
  jobs_52_in_scope   Let the public files P be in the goals' scope and readable (VerifierAndGoals.InScope: the
                     stored full-size example's files, but for the scale file and eight numbers,
                     with 2^8 ≤ theta). If the maker of the proof file's description returns at P's
                     files policy.txt and KL.bin and any layout file, at the hash function
                     OnBytes.secondHashFunction (IM.Open), then lotJobs ++ wJobs has 52 entries. In the proof
                     they are the 51 of K1's own lot and the one at the request's own table.

How it fits. "For every job of the two lists" in Spec.fieldsAtLots and Spec.handAtLots
(AtDescLots.lean) therefore ranges over 52 entries at in-scope files and that hash function, for
every no and D, not over an empty list. It rests on k1_length_in_scope
(Johnson/AtFull/Rounds/K1.lean), lotSide_places (Johnson/Desc/ProofFile/Honest/K1/PlaceJob.lean) and
wJobs_some (AtDescStands.lean). Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits. A count alone: it says nothing on what a job holds. That the 52 entries are at different
places is jobPlaces_nodup (LotPlaces.lean). The first chain has other sendings of new tables, of the
kinds K2 and K12; they are not counted here (see AtDescLots.lean). That the maker returns at given
public files is not shown here (see AtDescLots.lean).
-/
import Johnson.SendSim.Seat.AtDescStands
import Johnson.AtFull.Rounds.K1

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {X Xi : Type}

/-- The list of jobs of the kind's own lot is as long as the list of that lot's sub-protocols. -/
theorem lotJobs_length (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    (lotJobs (X := X) no D Z G).length = ((ProofFile.k1Pure Z).blocks G).length := by
  have h : ((lotSide (V := Unit) (X := X) (id : PlaceIn Xi → PlaceIn Xi) no D).halves Z G).map
      (·.place) = ((ProofFile.k1Pure Z).own G).map (·.place) := by
    unfold ProofFile.k1Pure
    dsimp only
    exact lotSide_places _ no D _ Z G
  have h' := congrArg List.length h
  rw [List.length_map, List.length_map] at h'
  have e : (lotSide (V := Unit) (X := X) (id : PlaceIn Xi → PlaceIn Xi) no D).halves Z G =
      (lotJobs no D Z G).map (placeHalf id) := lotHalves_eq id no D Z G
  rw [e, List.length_map] at h'
  rw [h']
  show _ = (((ProofFile.k1Pure Z).own G).map _ ++ []).length
  rw [List.append_nil, List.length_map]

/-- **In the goals' scope, where the description's maker returns, the two lots have 52 jobs.** -/
theorem jobs_52_in_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block First.S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol ly P.KL F Z Bs base c A B) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    (lotJobs (X := X) no D Z Bs.G₀ ++ wJobs (X := X) no D Z Bs.G₀).length = 52 := by
  obtain ⟨msg, -, e⟩ := wJobs_some (X := X) O no D Bs.G₀
  rw [List.length_append, e, lotJobs_length,
    Johnson.AtFull.Rounds.K1.k1_length_in_scope hS hR O.pub O.blank]
  rfl

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.lotJobs_length
#print axioms OnBytes.SendSim.Seat.jobs_52_in_scope
