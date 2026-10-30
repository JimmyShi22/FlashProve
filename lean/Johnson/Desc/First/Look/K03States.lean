-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K03States.lean: THE KIND "LOOKUP" (K3): WHICH RUNS OF CLAIMS THE
DESCRIPTION's OWN LINK STATES AT A LOOKUP's PLACE. At the link of the first chain of the description
that `ProofFile.onlineDescription` returns, what block number i of the hearing blocks states (`K9.statesOfLink`,
Johnson/Desc/First/Batch/ReadersOfLink.lean) is what the kind's stated block states
(`K3.theStated`'s value), name by name, EACH RUN BEHIND THE DRIVER's GUARD ON THE REPLY's SEAT
(`IM.guardRun ProofFile.sameReply`): the run, then the test that the reply's seat is as it was. THE RUNS
DO NOT PASS UNTURNED. Theorems with their proofs.

WHOSE. A joining: `k3_alone`, `k3_of`, `claims_alone`, `guardRun_yes`
(Johnson/IMR/K3Seat.lean, SeatForm.lean). The walk through the three makers' texts is the lookup's
files' (Johnson/Top/H/Keep/RunsStated.lean: `theOwn_two`, `theWhole_two`, `theStated_two`), here
with the seat told by the piece.

  `TwoAt seat l`: the list l begins with "objects": `objectsRun seat`, and "guests": `guestsRun []`.
  `seatOf claim d`: the seat of the digits (d) or of the calls.
  `theOwn_twoAt`, `theWhole_twoAt`, **`theStated_twoAt`**: at an address of link i whose piece is
    `pieceAt X i d` the value's list begins so AT THE SEAT `seatOf claim d`.
  **`k03_states_every`**: no scope: every o in the second hash's place, every link, both lookups.
  **`k03_states_of`**: in the goals' scope, at the fifty places.
  `find_guarded`: `find?` by a name goes through the guard.
  **`k03_objects_of`**, `k03_guests_of`: in scope: what `find?` finds at the description's own link
    under "objects" and under "guests": the guarded run, at the seat told by d.
  **`k03_planes_of`**: the like under "planes", at the lookup on the calls of a link at which the
    lot has the calling kind's readers: over `theStated_planes` and `theWhole_names` (K3OwnIs.lean).
  `k03_atS2_calls`, `k03_atS2_digits`: the lot's maker of claims `K3Lot.ofForm` is plain: `AtS2` at
    both seats (Johnson/Top/H/Keep/RunsAtS.lean). THE GUARD, BOTH WAYS: `guardRun_under`: a yes of
    the guarded run is a yes of the run. `sameReply_putFork`, **`guardRun_of_putFork`**: a yes of a
    run that turns the state by `putFork` alone is a yes of the guarded run.

Limits. Nothing on soundness. On texts alone: no view. Of "join" (the calling kind's block's run)
nothing here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.IMR.K3Seat
import Johnson.P5K3R.SitsRounds
import Johnson.P5K3R.SitsEvery
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Top.H.Keep.RunsStated
import Johnson.Top.H.Keep.RunsAtS
import Johnson.Desc.First.Look.K3PlanOfOk
import Johnson.Desc.First.StateOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits pieceAt)

section Makers
variable {Cl : Type}

/-- The list begins with "objects" and "guests", at this seat. -/
def TwoAt (seat : Seat S Cl) (l : List (RunN Cl)) : Prop :=
  ∃ tail, l = ("objects", objectsRun seat) ::
    ("guests", guestsRun ([] : List (Desc.First.Look.Guest S Cl))) :: tail

theorem TwoAt.more {seat : Seat S Cl} {l : List (RunN Cl)} (h : TwoAt seat l)
    (t : List (RunN Cl)) : TwoAt seat (l ++ t) := by
  obtain ⟨tail, rfl⟩ := h
  exact ⟨tail ++ t, rfl⟩

/-- The seat of the lookup on the digits (d), or on the calls. -/
def seatOf (claim : Aff → Cl) (d : Bool) : Seat S Cl :=
  if d then seatDigits claim else seatCalls claim

theorem theOwn_twoAt (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theOwn claim true X codes shape a = some x) (i : ℕ) (d : Bool)
    (hl : a.link = some i) (hpc : a.piece = pieceAt X i d) : TwoAt (seatOf claim d) x.claims := by
  unfold Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i', hi', h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl : i = i' := Option.some.inj (hl.symm.trans hi')
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hne
      have e : a.piece = pieceAt X i digits := by simpa using hne
      obtain rfl : d = digits := Desc.K3.pieceAt_inj X i (hpc.symm.trans e)
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      cases d
      · exact ⟨[], rfl⟩
      · exact ⟨[], rfl⟩

theorem theWhole_twoAt (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theWhole claim true X codes shape a = some x) (i : ℕ) (d : Bool)
    (hl : a.link = some i) (hpc : a.piece = pieceAt X i d) : TwoAt (seatOf claim d) x.claims := by
  unfold Desc.K3.theWhole at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_twoAt claim X codes shape a b hb i d hl hpc
  split
  · exact h0.more []
  · exact h0

/-- **The stated block's first two runs, at the seat that the piece tells.** -/
theorem theStated_twoAt (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S Cl) (h : Desc.K3.theStated claim readers X codes shape a = some B) (i : ℕ)
    (d : Bool) (hl : a.link = some i) (hpc : a.piece = pieceAt X i d) :
    TwoAt (seatOf claim d) B.claims := by
  unfold Desc.K3.theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  have h0 := theWhole_twoAt claim X codes shape a b hb i d hl hpc
  split at h
  · obtain rfl := Option.some.inj h
    exact h0
  · split at h
    · obtain rfl := Option.some.inj h
      exact h0
    · split at h
      · obtain rfl := Option.some.inj h
        exact h0
      · obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact h0.more _

end Makers

/-- `find?` by a name goes through the guard. -/
theorem find_guarded (same : S → S → Bool) (l : List (RunN ProofFile.Cl)) (n : String) :
    (l.map fun r => (r.1, IM.guardRun same r.2)).find? (fun r => r.1 == n) =
      (l.find? fun r => r.1 == n).map fun r => (r.1, IM.guardRun same r.2) := by
  rw [List.find?_map]
  rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **What the description's own link states at a lookup's place: no scope.** -/
theorem k03_states_every (O : IM.Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K3) :
    ∃ (Lk : Link S ProofFile.Cl) (b' : Block S ProofFile.Cl), c.links[l]? = some Lk ∧
      Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
        { chain := 1, link := some l, piece := i + 1, kind := .K3 } = some b' ∧
      Desc.K9.statesOfLink Lk i =
        b'.claims.map fun r => (r.1, IM.guardRun ProofFile.sameReply r.2) := by
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_alone O l sub hl i hk (K3Lot.k3Index sub _ i hk)
  refine ⟨Lk, b', h1, h3, ?_⟩
  unfold Desc.K9.statesOfLink
  rw [h2]
  exact IM.claims_alone h4

end

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The same in the goals' scope, at the fifty places.** -/
theorem k03_states_of (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∃ (Lk : Link S ProofFile.Cl) (b' : Block S ProofFile.Cl), c.links[l]? = some Lk ∧
      Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
        (IM.k3Place l d) = some b' ∧
      Desc.K9.statesOfLink Lk (IM.k3Ix l d) =
        b'.claims.map fun r => (r.1, IM.guardRun ProofFile.sameReply r.2) := by
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl d
  refine ⟨Lk, b', h1, h3, ?_⟩
  unfold Desc.K9.statesOfLink
  rw [h2]
  exact IM.claims_alone h4

/-- **What `find?` finds under "objects" at the description's own link.** -/
theorem k03_objects_of (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∃ Lk : Link S ProofFile.Cl, c.links[l]? = some Lk ∧
      (Desc.K9.statesOfLink Lk (IM.k3Ix l d)).find? (fun r => r.1 == "objects") =
        some ("objects", IM.guardRun ProofFile.sameReply (objectsRun (seatOf K3Lot.ofForm d))) := by
  obtain ⟨Lk, b', h1, h3, h4⟩ := k03_states_of hS hR O l hl d
  obtain ⟨tail, e⟩ := theStated_twoAt _ _ _ _ _ _ b' h3 l d rfl
    (K3Lot.k03_place _ _ _ _ _ l d b' h3).1
  refine ⟨Lk, h1, ?_⟩
  rw [h4, find_guarded, e]
  rfl

/-- The like under "guests". -/
theorem k03_guests_of (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∃ Lk : Link S ProofFile.Cl, c.links[l]? = some Lk ∧
      (Desc.K9.statesOfLink Lk (IM.k3Ix l d)).find? (fun r => r.1 == "guests") =
        some ("guests", IM.guardRun ProofFile.sameReply
          (guestsRun ([] : List (Desc.First.Look.Guest S ProofFile.Cl)))) := by
  obtain ⟨Lk, b', h1, h3, h4⟩ := k03_states_of hS hR O l hl d
  obtain ⟨tail, e⟩ := theStated_twoAt _ _ _ _ _ _ b' h3 l d rfl
    (K3Lot.k03_place _ _ _ _ _ l d b' h3).1
  refine ⟨Lk, h1, ?_⟩
  rw [h4, find_guarded, e]
  rfl

/-- **What `find?` finds under "planes"** at the lookup on the calls of a link at which the lot has
the calling kind's readers. -/
theorem k03_planes_of (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (r : Desc.K3.Readers S) (hr : K3Lot.readersAt Bs.G₀.W l = some r) :
    ∃ (Lk : Link S ProofFile.Cl) (p : Desc.First.Look.P), c.links[l]? = some Lk ∧
      Desc.First.Look.placeAt Bs.G₀.W l false = some p ∧
      (Desc.K9.statesOfLink Lk (IM.k3Ix l false)).find? (fun x => x.1 == "planes") =
        some ("planes", IM.guardRun ProofFile.sameReply
          (Desc.K3.planesRun (seatCalls K3Lot.ofForm) p.lm r)) := by
  obtain ⟨Lk, b', h1, h3, h4⟩ := k03_states_of hS hR O l hl false
  obtain ⟨p, b, hp, hb, e⟩ := Desc.K3.theStated_planes _ _ _ _ _ _ b' h3 l r rfl
    (K3Lot.k03_place _ _ _ _ _ l false b' h3).1 hr
  have hn := (Desc.K3.theWhole_names _ _ _ _ _ b hb).1
  have h0 : b.claims.find? (fun x => x.1 == "planes") = none := by
    refine List.find?_eq_none.2 fun x hx => ?_
    have hm : x.1 ∈ b.claims.map (·.1) := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [hn] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e' | e' <;> rw [e'] <;> decide
  refine ⟨Lk, p, h1, hp, ?_⟩
  rw [h4, find_guarded, e, List.find?_append, h0]
  rfl

end

/-- The lot's maker of claims is plain, at the calls' seat. -/
theorem k03_atS2_calls : AtS2 (seatCalls K3Lot.ofForm) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The like at the digits' seat. -/
theorem k03_atS2_digits : AtS2 (seatDigits K3Lot.ofForm) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## The guard, both ways -/

/-- A yes of the guarded run is a yes of the run, with the same answer. -/
theorem guardRun_under (same : S → S → Bool)
    (r : ℕ → S → Except String (List ProofFile.Cl × S)) :
    ∀ n t y, IM.guardRun same r n t = .ok y → r n t = .ok y :=
  fun n t y h => ((IM.guardRun_yes r n t y).1 h).1

/-- Laying a ledger leaves the reply's seat. -/
theorem sameReply_putFork (t : S) (G : Fork) : ProofFile.sameReply t (t.putFork G) = true := by
  unfold ProofFile.sameReply
  rw [Desc.First.S.out_putFork]
  exact beq_self_eq_true _

/-- **A yes of a run that turns the state by `putFork` alone is a yes of the guarded run.** -/
theorem guardRun_of_putFork (r : ℕ → S → Except String (List ProofFile.Cl × S)) (n : ℕ) (t : S)
    (cl : List ProofFile.Cl) (G : Fork) (h : r n t = .ok (cl, t.putFork G)) :
    IM.guardRun ProofFile.sameReply r n t = .ok (cl, t.putFork G) :=
  (IM.guardRun_yes r n t _).2 ⟨h, sameReply_putFork t G⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.TwoAt.more
#print axioms VerifiableInference.OnPublicFiles.theOwn_twoAt
#print axioms VerifiableInference.OnPublicFiles.theWhole_twoAt
#print axioms VerifiableInference.OnPublicFiles.theStated_twoAt
#print axioms VerifiableInference.OnPublicFiles.find_guarded
#print axioms VerifiableInference.OnPublicFiles.k03_states_every
#print axioms VerifiableInference.OnPublicFiles.k03_states_of
#print axioms VerifiableInference.OnPublicFiles.k03_objects_of
#print axioms VerifiableInference.OnPublicFiles.k03_guests_of
#print axioms VerifiableInference.OnPublicFiles.k03_planes_of
#print axioms VerifiableInference.OnPublicFiles.k03_atS2_calls
#print axioms VerifiableInference.OnPublicFiles.k03_atS2_digits
#print axioms VerifiableInference.OnPublicFiles.guardRun_under
#print axioms VerifiableInference.OnPublicFiles.sameReply_putFork
#print axioms VerifiableInference.OnPublicFiles.guardRun_of_putFork
