-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/FitsAtKey.lean: if a key file's description passes its own tests on the plan,
the public numbers and the tables sent along at its three sub-protocols of the kind K1 in the first
chain fit (sendFits).
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". There the description is the proof
file's; here it is the key file's Key.descriptionFromSource. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has.
  fits_at_key     Its one premise is (Key.descriptionFromSource Xs N Q).planOk = true. It holds for any source Xs,
                  any numbers N of the ranges' test and any numbers Q of the later places. For every
                  entry x of keyPars Xs (Johnson/SendSim/Seat/AtKeyPars.lean):
                  sendFits x.1 x.2 = true. So every job with these public numbers and these tables
                  sent along fits its place, whatever its data and the number of its first new
                  message are: sendFits reads neither. These are the jobs that Spec.fieldsAtKey
                  (Johnson/SendSim/Seat/AtKey.lean) names.

How it fits. At a description that passes its tests on the plan, every job that Spec.fieldsAtKey
names fits its place. The statement does not ask this. Where a job does not fit, its part discloses
only the error value, on both sides of both equations: exact then says nothing, and fresh speaks of
the sender's coins alone. fits_at_lots_plan (Johnson/SendSim/Seat/RideFitsW.lean) is the like
statement for the proof file. Meant as steps toward index privacy (Johnson/WholeKey/Statement.lean);
nothing in this folder derives index privacy from them. Not one of the release's goal statements.

How it is proved. sendFits_of_plan (Johnson/SendSim/Seat/FitsAtLots.lean) asks three things.
Every code's message length is a power of two. That is the clause "lengths" of Key.sourceClauses
(Johnson/Desc/Key/Source.lean), which the description's test on the file asks (key_plan_facts,
Johnson/SendSim/Seat/RideTies.lean).
The kind's own test on the plan accepts. (Key.descriptionFromSource Xs N Q).planOk asks every member of the first
chain's list to pass its own test (FileDescription.PlanOk.blocks₁, Johnson/Desc/RunLaws.lean), and each of
the three members has K1.planOkOwn among its conjuncts (key_planOwn).
Each table that is sent along fits its message's shape. It is announced as its fold's fresh mask
(msg_rideOwn, wKey_rideOwn, Johnson/SendSim/Seat/AtKeyStands.lean). The fold has the numbers of its
test's first stage (msgFold_spec, wFold_spec, RideTies.lean). That test's stages fit together
(key_plan_facts), and the first stage's three bounds follow (first_stage_of_ioppOk, RideFitsW.lean;
rideFits_of_own, Johnson/SendSim/Seat/RideFits.lean).

The other names.
  key_planOwn     Under the same premise: for every entry x of keyPars Xs the kind's own test on the
                  plan accepts (K1.planOkOwn x.1, Johnson/Desc/K1/Own.lean).
  ride_of_ioppOk  For all public numbers P. Suppose that the stages of a proximity test fit together
                  under P's codes (ioppOk, OnBytes/Iop/Prox.lean). Suppose also that a fold has the
                  k, h and codes' numbers of the test's first stage, and that a message of P is
                  announced as that fold's fresh mask (rideOwn). Then the table that is sent along
                  fits that message's shape (rideFits).
  sendW_plan      Where the shape has a message for W, sendW returns a sub-protocol, and its test on
                  the plan has K1.planOkOwn at the sender's numbers among its conjuncts.

Limits.
The premise is not shown here. The library proves it at the Xs, N and Q that the maker makes of
given files: wherever Key.keyDataAndDecisionAtDigest returns (key_sits_row_laidAt, Johnson/Loose/H2K12/SitsRowKey.lean),
and, for files in the scope of the release's goals, at the fixed digest where the maker's routines
return (key_planOk_in_scope, Johnson/HB/LLHARD/KB4/RowInScope.lean).
Of the three public tests at these places (the fit, the book, the queried positions), only the first
is proved here.
Under this premise keyPars has three entries (key_w_there, RideTies.lean). Without it, where the
shape has no message for W, keyPars has two.
A key file's first chain has six sendings of new tables, and these are three. That msgFold's fold is
the one that Wf.messageOf sends along is by inspection, not proved (for both see AtKeyPars.lean,
Limits).
Among the files that this folder imports there is no honest prover of a key file in the framework of
Johnson/Desc/ProofFile/Honest/ (parts at the description's places).
Pointwise statements: no distribution is named.
-/
import Johnson.SendSim.Seat.RideTies
import Johnson.SendSim.Seat.AtKeyStands

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc.Key (groupsTold rootsAt rootsBefore lastSendRound batchRound pieces
  sendW layRows rangesTest enterRanges leaveRanges batchTableRows firstChain FirstState)

/-- Where the shape has a message for W, sendW returns a sub-protocol, and its test on the plan has
the kind's own test at the sender's numbers among its conjuncts. -/
theorem sendW_plan (one : OneTime) (sent : Nat) (g : List (List Nat))
    {msg : Array OracleNotice} (hm : linMessageW one.lin = some msg) :
    ∃ b : Block FirstState Key.Claim, sendW one pieces sent g = some b ∧
      (b.planOk = true → K1.planOkOwn (K1.parWKey one msg g) = true) := by
  unfold sendW
  rw [hm]
  refine ⟨_, rfl, fun h => ?_⟩
  have h' : ((((true && K1.planOkOwn (K1.parWKey one msg g)) && true) && true) : Bool) = true := h
  simpa using h'

/-- At each of the three places the kind's own test on the plan accepts, if the description passes
its tests on the plan. -/
theorem key_planOwn (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N Q).planOk = true) : ∀ x ∈ keyPars Xs, K1.planOkOwn x.1 = true := by
  have hb := ((FileDescription.planOk_ok _).1 hp).blocks₁
  intro x hx
  unfold keyPars at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl) | hx
  · have h := (hb _ (mem_flat_first (Key.descriptionFromSource Xs N Q).first)).1
    have h' : (((K1.planOkOwn (K1.parIdx Xs.Y.k.oneTime
        (groupsTold Xs.Y.told.1 0 (rootsAt Xs.Y.D.1 0))) && true) && _) : Bool) = true := h
    simp only [Bool.and_eq_true] at h'
    exact h'.1.1
  · have h := (hb _ (mem_flat_front (Key.descriptionFromSource Xs N Q).first (List.mem_singleton.2 rfl))).1
    have h' : (((K1.planOkOwn (K1.parMsg Xs.Y.k.oneTime
        (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 2) (rootsAt Xs.Y.D.1 2))) && true) && _) :
          Bool) = true := h
    simp only [Bool.and_eq_true] at h'
    exact h'.1.1
  · cases hm : linMessageW Xs.Y.k.oneTime.lin with
    | none =>
      rw [hm] at hx
      cases hx
    | some msg =>
      rw [hm] at hx
      obtain rfl := List.mem_singleton.1 hx
      obtain ⟨b, hbW, hpl⟩ := sendW_plan Xs.Y.k.oneTime
        (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))
        (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
          (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1))) hm
      have hmem : b ∈ (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).back := by
        show b ∈ [layRows Xs.Y.k.oneTime, rangesTest (enterRanges Xs.Y.k.oneTime) leaveRanges N,
          batchTableRows (·.keys) Xs.Y.k.oneTime pieces _] ++
            (sendW Xs.Y.k.oneTime pieces _ _).toList
        rw [hbW]
        exact List.mem_append_right _ (List.mem_singleton.2 rfl)
      have h := (hb _ (mem_flat_back (firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N)
        hmem)).1
      have h' : ((b.planOk && b.hasNoClaimsAndNothingAfter) : Bool) = true := h
      rw [Bool.and_eq_true] at h'
      exact hpl h'.1

/-- If the stages of a proximity test fit together, and a message of P is announced as the fresh
mask of a fold with the numbers of the test's first stage, then the table sent along at that message
fits its shape. The premise hs has the four equations that msgFold_spec and wFold_spec conclude; the
one on the main code's number is not used. -/
theorem ride_of_ioppOk {P : K1.Par} {st : List IoppStage} {answers n : Nat} {Fd : FoldShape}
    (hi : ioppOk P.codes st answers = true) (ho : rideOwn P (some (n, Fd)) = true)
    (hs : ∃ s, st.head? = some s ∧ Fd.layout.k = s.k ∧ Fd.layout.h = s.h ∧ Fd.code = s.code ∧
      Fd.maskCode = s.maskCode) :
    ∀ k R, rideOf (some (n, Fd)) k = some R → rideFits P.codes (shapeAt P k) R = true := by
  obtain ⟨s, hs, e1, e2, -, e4⟩ := hs
  have h := first_stage_of_ioppOk hi
  rw [hs] at h
  simp only [Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at h
  exact rideFits_of_own ho (by rw [e1]; exact h.1.1) (by rw [e1, e2]; exact h.1.2)
    (by rw [e1, e2, e4]; exact h.2)

/-- **If a key file's description passes its tests on the plan, then at every entry (P, ride) of
keyPars, sendFits P ride holds: every job with these public numbers and these tables sent along fits
its place.** -/
theorem fits_at_key (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource Xs N Q).planOk = true) : ∀ x ∈ keyPars Xs, sendFits x.1 x.2 = true := by
  obtain ⟨hl, h1, h2, -, -⟩ := key_plan_facts Xs N Q hp
  intro x hx
  have hown := key_planOwn Xs N Q hp x hx
  unfold keyPars at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl) | hx
  · exact sendFits_of_plan hl hown fun k R _ hk => by cases hk
  · refine sendFits_of_plan hl hown fun k R _ hk => ?_
    cases hf : msgFold Xs.Y.k.oneTime.ranges with
    | none =>
      rw [hf] at hk
      cases hk
    | some y =>
      obtain ⟨n, Fd⟩ := y
      rw [hf] at hk
      have ho := msg_rideOwn Xs.Y.k.oneTime
        (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 2) (rootsAt Xs.Y.D.1 2))
      rw [hf] at ho
      exact ride_of_ioppOk (P := K1.parMsg Xs.Y.k.oneTime _) h1 ho (msgFold_spec hf) k R hk
  · cases hm : linMessageW Xs.Y.k.oneTime.lin with
    | none =>
      rw [hm] at hx
      cases hx
    | some msg =>
      rw [hm] at hx
      obtain rfl := List.mem_singleton.1 hx
      refine sendFits_of_plan hl hown fun k R _ hk => ?_
      cases hf : wFold Xs.Y.k.oneTime.lin with
      | none =>
        rw [hf] at hk
        cases hk
      | some y =>
        obtain ⟨n, Fd⟩ := y
        rw [hf] at hk
        have ho := wKey_rideOwn Xs.Y.k.oneTime msg
          (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
            (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1))) hm
        rw [hf] at ho
        exact ride_of_ioppOk (P := K1.parWKey Xs.Y.k.oneTime msg _) h2 ho (wFold_spec hf) k R hk

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.sendW_plan
#print axioms OnBytes.SendSim.Seat.key_planOwn
#print axioms OnBytes.SendSim.Seat.ride_of_ioppOk
#print axioms OnBytes.SendSim.Seat.fits_at_key
