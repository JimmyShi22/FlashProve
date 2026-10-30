-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/BlindRunsK5.lean: THE ATTENTION CALLER's RUNS OF CLAIMS ("first",
"keys", "join", "second") COMMUTE WITH THE SMALLNESS TEST's DRAW (`RunBlind`,
Johnson/Desc/First/K8/BlindReaders.lean), AND ITS READERS OF THE PLANES' MATRIX AND ITS KEYS, WHICH
THE LOOKUPS' RUNS "planes" AND "join" CALL, ARE BLIND TO IT (`TlBlind`,
Johnson/Desc/First/K8/BlindPub.lean). Theorems.
  `seatCO_blind`: the claims' seat (Johnson/Desc/First/Att/SeatO.lean) reads the attention segment's
    own heard values and ledger: neither of the two fields that the draw writes. `inOf_blind`,
    `keysOfK_blind`, `readersOfK_blind`: so what the runs read.
  `runsK_blind`, `runsO_blind`, `k5AtN_blind`: **the runs, up to the kind's sub-protocol at a
    segment** (`k5AtN`, SeatN.lean). `readersOfO_blind`, `keysOfO_blind`: the premises hr and hk of
    BlindRunsK3.lean at an attention segment.
Limits. The walk from `k5AtN` to what the seated link states (the seat's guard:
`claimsBlind_guarded`) is not made here. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.BlindRunsK3
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Att.Guest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P

/-- The claims' seat reads neither of the two fields that the draw writes. -/
theorem seatCO_blind (c : ParC) :
    TlBlind (seatCO c).pts ∧ TlBlind (seatCO c).cols ∧ TlBlind (seatCO c).look ∧
      TlBlind (seatCO c).pad ∧ TlBlind (seatCO c).zk := by
  refine ⟨fun s t h => ?_, fun s t h => ?_, fun s t h => ?_, fun s t h => ?_, fun s t h => ?_⟩
  · refine drawn_ind (motive := fun s t => (seatCO c).pts t = (seatCO c).pts s) ?_ ?_ ?_ h <;>
      intros <;> simp_all [seatCO, S.heard5?]
  · refine drawn_ind (motive := fun s t => (seatCO c).cols t = (seatCO c).cols s) ?_ ?_ ?_ h <;>
      intros <;> simp_all [seatCO]
  · refine drawn_ind (motive := fun s t => (seatCO c).look t = (seatCO c).look s) ?_ ?_ ?_ h <;>
      intros <;> simp_all [seatCO]
  · refine drawn_ind (motive := fun s t => (seatCO c).pad t = (seatCO c).pad s) ?_ ?_ ?_ h <;>
      intros <;> simp_all [seatCO]
  · refine drawn_ind (motive := fun s t => (seatCO c).zk t = (seatCO c).zk s) ?_ ?_ ?_ h <;>
      intros <;> simp_all [seatCO]

/-- A run that returns forms which are blind, and the state as it was. -/
theorem runBlind_same (msg : String) (o : S → Option (List Aff)) (ho : TlBlind o) :
    RunBlindC fun s => named msg ((o s).map fun l => (l, s)) := fun s t hd => by
  show (named msg ((o t).map fun l => (l, t))).toOption.map _ =
    (named msg ((o s).map fun l => (l, s))).toOption.map _
  rw [ho s t hd]
  cases o s with
  | none => rfl
  | some l =>
    show some (l, t.fork?) = some (l, s.fork?)
    rw [blind_fork s t hd]

theorem firstK_eq (seat : SeatC S) (c : ParC) (s : S) : firstK seat c s =
    (((inOf seat c s).bind fun x => (Runs.firstRun x.1 x.2).map (·.1)).map fun l => (l, s)) := by
  unfold firstK
  cases inOf seat c s with
  | none => rfl
  | some x =>
    obtain ⟨i, K⟩ := x
    show ((Runs.firstRun i K).bind fun y => some (y.1, s)) =
      ((Runs.firstRun i K).map (·.1)).map fun l => (l, s)
    cases Runs.firstRun i K <;> rfl

theorem secondK_eq (seat : SeatC S) (c : ParC) (s : S) : secondK seat c s =
    (((inOf seat c s).bind fun x => Runs.secondRun x.1 x.2).map fun l => (l, s)) := by
  unfold secondK
  cases inOf seat c s with
  | none => rfl
  | some x =>
    obtain ⟨i, K⟩ := x
    show ((Runs.secondRun i K).bind fun y => some (y, s)) =
      (Runs.secondRun i K).map fun l => (l, s)
    cases Runs.secondRun i K <;> rfl

theorem keysK_eq (seat : SeatC S) (c : ParC) (s : S) : keysK seat c s =
    (((keysOfK seat c s).map fun _ => ([] : List Aff)).map fun l => (l, s)) := by
  unfold keysK
  cases keysOfK seat c s <;> rfl

section
variable (seat : SeatC S) (c : ParC)
  (H : TlBlind seat.pts ∧ TlBlind seat.cols ∧ TlBlind seat.look ∧ TlBlind seat.pad ∧
    TlBlind seat.zk)
include H

/-- What the runs read. -/
theorem inOf_blind : TlBlind (inOf seat c) := fun s t h => by
  unfold inOf
  rw [H.1 s t h, H.2.1 s t h, H.2.2.1 s t h, H.2.2.2.2 s t h]

/-- The calls' key forms. -/
theorem keysOfK_blind : TlBlind (keysOfK seat c) := fun s t h => by
  unfold keysOfK
  rw [inOf_blind seat c H s t h, H.2.2.2.1 s t h]

/-- The readers of the planes' matrix. -/
theorem readersOfK_blind : TlBlind (readersOfK seat c) := fun s t h => by
  unfold readersOfK
  rw [inOf_blind seat c H s t h]

/-- **K5's three named runs.** -/
theorem runsK_blind : ∀ r ∈ runsK seat c, ∀ n, RunBlindC (r.2 n) := by
  intro r hr n
  unfold runsK at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show RunBlindC fun s => named "K5.first" (firstK seat c s)
    rw [show (fun s => named "K5.first" (firstK seat c s)) = _ from
      funext fun s => congrArg (named "K5.first") (firstK_eq seat c s)]
    exact runBlind_same "K5.first"
      (fun s => (inOf seat c s).bind fun x => (Runs.firstRun x.1 x.2).map (·.1)) fun s t h =>
        congrArg (·.bind fun x => (Runs.firstRun x.1 x.2).map (·.1)) (inOf_blind seat c H s t h)
  · show RunBlindC fun s => named "K5.keys" (keysK seat c s)
    rw [show (fun s => named "K5.keys" (keysK seat c s)) = _ from
      funext fun s => congrArg (named "K5.keys") (keysK_eq seat c s)]
    exact runBlind_same "K5.keys" (fun s => (keysOfK seat c s).map fun _ => ([] : List Aff))
      fun s t h => congrArg (·.map fun _ => ([] : List Aff)) (keysOfK_blind seat c H s t h)
  · show RunBlindC fun s => named "K5.second" (secondK seat c s)
    rw [show (fun s => named "K5.second" (secondK seat c s)) = _ from
      funext fun s => congrArg (named "K5.second") (secondK_eq seat c s)]
    exact runBlind_same "K5.second" (fun s => (inOf seat c s).bind fun x => Runs.secondRun x.1 x.2)
      fun s t h => congrArg (·.bind fun x => Runs.secondRun x.1 x.2) (inOf_blind seat c H s t h)

end

/-- The attention caller's readers of the planes' matrix, as K3's lot seats them. -/
theorem readersOfO_blind (A : Attention.Plan) : TlBlind (readersOfO A) :=
  readersOfK_blind _ _ (seatCO_blind _)

theorem keysOfO_blind (A : Attention.Plan) : TlBlind (keysOfO A) :=
  keysOfK_blind _ _ (seatCO_blind _)

/-- K5's four named runs of forms. -/
theorem runsO_blind (A : Attention.Plan) : ∀ r ∈ runsO A, ∀ n, RunBlindC (r.2 n) := by
  intro r hr n
  unfold runsO at hr
  obtain ⟨r₀, h₀, hr⟩ := List.mem_flatMap.1 hr
  have k := runsK_blind _ _ (seatCO_blind (parCOf A)) r₀ h₀
  split at hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact k n
    · exact joinRun_blind _ (calls_blind id).1 (calls_blind id).2.1 (calls_blind id).2.2 _
        (keysOfO_blind A) n
  · obtain rfl := List.mem_singleton.1 hr
    exact k n

/-- **K5's SUB-PROTOCOL AT A SEGMENT: EVERY RUN ("first", "keys", "join", "second") COMMUTES WITH
THE DRAW.** -/
theorem k5AtN_blind {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b : Block S Claim}
    (h : k5AtN W l g before = some b) : ClaimsBlind b := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro c hc n
  have hc' : c ∈ runsN p := hc
  unfold runsN at hc'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
  exact runBlind_map claimOf (r.2 n) (runsO_blind p r hr n)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.readersOfO_blind
#print axioms VerifiableInference.Desc.First.K8.runsO_blind
#print axioms VerifiableInference.Desc.First.K8.k5AtN_blind
