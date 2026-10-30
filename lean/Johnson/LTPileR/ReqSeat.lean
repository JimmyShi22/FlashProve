-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/ReqSeat.lean
(over Johnson/IMR/SeatKeeps.lean, Johnson/IMR/RecRun.lean and
Johnson/Top/H0/Walk/Reach.lean): THE FOLD'S FACT "reqIs": at every reached state without a mark the
state's request's words are the public part's.

Main names (namespace `Meaning.K2`).
  **`seatKeeps_req`** : `SeatKeeps ReqStays`; **`seatBack_req`** : `SeatBack ReqStays`: every field
    of both. `flat_req`: so every sub-protocol of `c.blocksInOrder` that passes its own test on the list of
    rounds keeps `fun s t => t.req = s.req` (the letters of the files in Johnson/IMR/).
  `req_start`: the chain's own start `ProofFile.startS Z p`, where it bears no mark, bears `Verify.words32
    p.request`.
  **`reach_req`**: at the IOP as written in Lean for the proof file (F = `fileDescBy … c`), under
    `Block.planOk` at every sub-protocol of `c.blocksInOrder`: `Reach ft c.blocksInOrder (ProofFile.startS Z) k a →
    a.2.failed = none → a.2.req = Verify.words32 a.1.request`.
  **`reqIs_field`**: the same in the letters of the structure of fold facts
    (Johnson/Desc/First/FoldFacts.lean: not imported), general in Rch and at_, at reqW := fun p =>
    `Verify.words32 p.request`; hR: whatever Rch holds is reached along the chain at at_'s two
    halves.

Every "there is", walked. Z, A, B, c: tied by `pureRoad.pub … = .ok Z` and F's equation. hR's ft:
any.
IT COVERS EVERY BORDER OF THE CHAIN. The premise on `planOk`: as in PileSeat.lean's head.
Limits. The seat is the harness's. Nothing on soundness or on hiding.

-/
import Johnson.IMR.SeatKeeps
import Johnson.IMR.RecRun
import Johnson.Desc.First.Pile.ReqSeated
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)
open Johnson.Desc.First.Walk.Tied (Reach)

theorem readsBlockAt_req {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole ReqStays b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact layers_req _
  · split at h
    · cases h
      exact headReads_req _
    · cases h

theorem readsQuietAt_req {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) : Whole ReqStays b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtO_req h
    | exact readsBlockAt_req h
    | cases h

/-- **EVERY MAKER OF THE SEAT IN FRONT OF THE SUB-PROTOCOLS BEHIND THE LAST LINK.** -/
theorem seatKeeps_req : SeatKeeps ReqStays where
  refl := req_refl
  trans := req_trans
  frames := fun _ h => framesOf_req h
  k1First := fun q gp _ => firstAtS_req q gp
  k1Later := fun q gp l p m a _ => laterAt_req q gp l p m a
  reads := fun h => readsQuietAt_req h
  k3 := fun c r X cs' sh' a _ h => theStated_req c r X cs' sh' a h
  k4 := fun p => blockAtC_req p
  k5 := fun W l g bf _ h => k5AtN_req W l g bf h
  k6 := fun h => seatedClaims_req h
  k7 := fun W l => k7Of_req W l
  k8 := fun p => k8Whole_req p
  k11 := fun Q => headMerge11_req Q
  closeOf := closeOf_req
  batch := fun p _ hf => batch_req p hf
  k2 := fun p _ => k2_req p
  front := headFrontQ_req
  openQ := fun Q _ => headOpenQ_req Q
  finFront := finishFrontQ_req
  finBehind := finishBehindQ_req

/-- **THE MAKERS BEHIND THE LAST LINK.** -/
theorem seatBack_req : SeatBack ReqStays where
  k12 := fun _ _ => atFinish_req _
  k13M3 := fun p => atM3_req p
  k13M4 := fun p Q _ => atM4_req p Q

/-- The chain's own start: without a mark it bears the request's words. -/
theorem req_start (Z : Pub) (p : ProofFile.InstPub) (h : (ProofFile.startS Z p).failed = none) :
    (ProofFile.startS Z p).req = Verify.words32 p.request := by
  unfold ProofFile.startS at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  · rename_i hq
    rw [if_neg hq] at h
    cases h

/-- **THE FOLD's FACT FOR "reqIs", AT "REACHED".** -/
theorem reach_req {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ (ft k : Nat) (a : ProofFile.InstPub × S),
        Reach ft c.blocksInOrder (ProofFile.startS Z) k a → a.2.failed = none →
        a.2.req = Verify.words32 a.1.request) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ :=
    descPure_flat seatKeeps_req seatBack_req (fun _ _ => trivial) h
  refine ⟨Z, A, B, c, h1, h2, fun hp ft n a hr hm => ?_⟩
  obtain ⟨-, rs, cols, hf⟩ := hr.fold
  have q := Keeps.foldBlocks_keeps ReqStays req_refl req_trans ft (c.blocksInOrder.take n)
    (fun b hb => k b (List.mem_of_mem_take hb) (hp b (List.mem_of_mem_take hb))) _ rs cols _ hf
  rw [q.1]
  exact req_start Z a.1 (q.2 hm)

/-- **THE FIELD IN THE LETTERS OF THE TABLES' OWNER's STRUCTURE OF FOLD FACTS**, general in Rch and
at_: hR: whatever Rch holds is reached along the chain from its own start, at at_'s two halves. -/
theorem reqIs_field {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ {X : Type} (Rch : Nat → X → Prop)
        (at_ : X → ProofFile.InstPub × S),
        (∀ k a, Rch k a → ∃ ft, Reach ft c.blocksInOrder (ProofFile.startS Z) k (at_ a)) →
        ∀ k a, Rch k a → (at_ a).2.failed = none →
          (at_ a).2.req = (fun p : ProofFile.InstPub => Verify.words32 p.request) (at_ a).1) := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ := reach_req h
  refine ⟨Z, A, B, c, h1, h2, fun hp X Rch at_ hR n a ha hm => ?_⟩
  obtain ⟨ft, hr⟩ := hR n a ha
  exact k hp ft n _ hr hm

/-- The relation in the letters of the files in Johnson/IMR/. -/
theorem flat_req {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides (fun s t : S => t.req = s.req) b := by
  obtain ⟨Z, A, B, c, h1, h2, k⟩ :=
    descPure_flat seatKeeps_req seatBack_req (fun _ _ => trivial) h
  exact ⟨Z, A, B, c, h1, h2, fun b hb hp s rs gs s' hd => (k b hb hp s rs gs s' hd).1⟩

#print axioms readsBlockAt_req
#print axioms readsQuietAt_req
#print axioms seatKeeps_req
#print axioms seatBack_req
#print axioms req_start
#print axioms reach_req
#print axioms reqIs_field
#print axioms flat_req

end Meaning.K2
