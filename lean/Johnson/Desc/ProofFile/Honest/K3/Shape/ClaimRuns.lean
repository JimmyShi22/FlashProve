-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimRuns.lean: the lookup's runs of claims "objects" and
"guests" on the shape of the first chain's state: each as a `RunLaw`
(Johnson/Desc/First/Batch/Shape/ClaimShape.lean). Definitions with code; theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a state is `chainSh`
(Johnson/Desc/First/Shape/Chain.lean). A run on shapes is a function that does on shapes what a run
of claims does on states. A law is a value of `RunLaw`: a run on shapes (runG), a hypothesis (pre),
and two fields, carries and returns, that tie the run on shapes to the run. The guard on the reply
is `IM.guardRun sameReply` (Johnson/IMR/SeatForm.lean).

What is shown.
  `heardShAt d c`: where the chain's shape keeps what the lookup heard: on the digits (d) in the
    smallness test's structure, on the calls in the component of its own.
  `objectsG d`: "objects" on shapes: the heard rows' shapes as claims; the ledger's shape with the
    debt marked.
  `objectsG_returns`: where it returns: just where a ledger's shape and a heard structure's shape
    are there.
  `objects_strong`: if the run returns (cs, s'), then `objectsG` returns their shapes.
  `objectsG_back`: if `objectsG` returns at a state's shape, then the run returns there.
  `objectsLaw d`: the law of "objects", at the hypothesis "true".
  `guestsG`, `guests_strong`, `guestsLaw`: "guests" at the empty list of guests: no claim, the state
    as it is; it never refuses.
  `guardLaw`: general in the run: a law of a run that leaves what the guard compares is a law of the
    run behind the guard, with the same run on shapes and the same hypothesis.
  `objectsLawG d`, `guestsLawG`: the two laws behind the guard on the reply, as a description's
    member states the runs.
  `stated_two`: the sub-protocol at a lookup's address states these two runs first, at its seat.
Helpers: `heardShAt_is`, `led_is`, `mark_is`, `claimSh_ofForm`, `guard_same`, `guard_back`,
`putFork_reply`, `objectsRun_reply`.

Hypotheses that remain.
  `h`: the return of the run, or of the run on shapes (in `objects_strong`, `objectsG_back`,
    `guests_strong`); in `guardLaw`, that the run leaves what the guard compares; in `stated_two`,
    the return of the maker `K3.theOwn` at the address.
  `hl`, `hpc`: (in `stated_two`) the address's link and piece.
  `hs`: (in `guard_same`, beside `h`) the run leaves what the guard compares.

Imported: Johnson/Desc/First/Batch/Shape/ClaimShape.lean, and beneath it
Johnson/Desc/First/Shape/Chain.lean.

Users. `planesLaw` and the other laws of Honest/K3/Shape/ClaimPlanes.lean stand beside these; that
file imports this one. `member_states_two` (Honest/K3/Shape/ClaimAtMember.lean
[not in this library]) shows that a description's member states the two runs behind the guard.

Limits. The two ways in which a `RunLaw` can be idle, looked at as terms. The run on shapes:
`objectsG_returns` says where it returns, and `guestsG` is ".ok" by its text. The hypothesis: it is
fun _ _ => True at both.
Which rows stand in the heard structure is not said here (Honest/K3/Shape/HeardWalk.lean). The run
"planes" is not here. That a description's member states the runs behind this guard is another
file's. No instance of these hypotheses is exhibited in this file. Nothing is evaluated here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Batch.Shape.ClaimShape
import Johnson.Desc.First.Look.K03States
import Johnson.Top.H.Keep.RunsGuests
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.IMR.SeatForm
import Johnson.Desc.ProofFile.Honest.K3.Law.StatedReply

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Claim named seatSame)
open VerifiableInference.Desc.K3 (seatCalls seatDigits)
open VerifiableInference.Desc.K9.Shape (RunLaw)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh LedSh ledSh AffSh affSh
  HeardAll heardAll tailSh paidB ledSh_paid chainSh_putFork)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun seatOf guestsRun_nil)
open ProofFile (sameReply)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "RunT" => VerifiableInference.Desc.K9.Shape.Run

/-! ## 1 What the shape keeps of what was heard -/

/-- Where the chain's shape keeps what the lookup heard. Here d is true on the digits. -/
def heardShAt (d : Bool) (c : ChainSh) : Option HeardAll :=
  if d then c.tl.bind (·.heard) else c.lookHeard

/-- It is the shape of what the seat reads as heard. No hypothesis. -/
theorem heardShAt_is (d : Bool) (s : FS) :
    heardShAt d (chainSh s) = ((seatOf K3Lot.ofForm d).heard s).map heardAll := by
  cases d with
  | false => rfl
  | true =>
    show (s.tl?.map tailSh).bind (·.heard) = (s.tl?.bind (·.heard)).map heardAll
    cases s.tl? <;> rfl

/-- The ledger's shape is the shape of what the seat reads as the ledger. No hypothesis. -/
theorem led_is (d : Bool) (s : FS) :
    (chainSh s).led = ((seatOf K3Lot.ofForm d).fork s).map ledSh := by
  cases d <;> rfl

/-- Both seats mark by setting the ledger. No hypothesis. -/
theorem mark_is (d : Bool) (s : FS) (G : Fork) :
    (seatOf K3Lot.ofForm d).mark s G = s.putFork G := by
  cases d <;> rfl

/-- A form as a claim has the form's shape, no run, and its own number's weight. No hypothesis. -/
theorem claimSh_ofForm (d : Bool) (a : Aff) :
    claimSh ((seatOf K3Lot.ofForm d).claim a) = ClaimSh.mk none (affSh a) [] := by
  cases d <;> rfl

/-! ## 2 "objects" -/

/-- **"objects" on shapes.** -/
def objectsG (d : Bool) (_ : Nat) (c : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  match c.led, heardShAt d c with
  | some L, some h =>
    .ok (h.rows.map fun a => ClaimSh.mk none a [],
      c.setLed (L.setOwed (paidB L.owed h.owedObjects)))
  | _, _ => .error "K3 objects, on shapes: no ledger, or nothing heard"

/-- **Where it returns.** No hypothesis. -/
theorem objectsG_returns (d : Bool) (n : Nat) (c : ChainSh) :
    (∃ y, objectsG d n c = .ok y) ↔ c.led.isSome = true ∧ (heardShAt d c).isSome = true := by
  unfold objectsG
  cases c.led with
  | none =>
    cases heardShAt d c with
    | none => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h.1)⟩
    | some _ => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h.1)⟩
  | some L =>
    cases heardShAt d c with
    | none => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h.2)⟩
    | some h => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨_, rfl⟩⟩

/-- **If the run returns, the run on shapes returns the claims' shapes and the shape behind.**
Conditional on the run's return. -/
theorem objects_strong (d : Bool) (n : Nat) (s s' : FS) (cs : List Claim)
    (h : objectsRun (seatOf K3Lot.ofForm d) n s = .ok (cs, s')) :
    objectsG d n (chainSh s) = .ok (cs.map claimSh, chainSh s') := by
  unfold objectsRun at h
  cases hF : (seatOf K3Lot.ofForm d).fork s with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    cases hg : (seatOf K3Lot.ofForm d).heard s with
    | none => simp [hF, hg, named, bind, Except.bind] at h
    | some g =>
      simp only [hF, hg, named, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold objectsG
      rw [led_is d s, heardShAt_is d s, hF, hg, mark_is, chainSh_putFork, ledSh_paid]
      show Except.ok ((g.rows.toList.map affSh).map (fun a => ClaimSh.mk none a []), _) = _
      rw [List.map_map, List.map_map]
      congr 2
      exact List.map_congr_left fun a _ => (claimSh_ofForm d a).symm

/-- **If the run on shapes returns at a state's shape, the run returns.** Conditional on that
return. -/
theorem objectsG_back (d : Bool) (n : Nat) (s : FS) (y : List ClaimSh × ChainSh)
    (h : objectsG d n (chainSh s) = .ok y) :
    ∃ z, objectsRun (seatOf K3Lot.ofForm d) n s = .ok z := by
  obtain ⟨h1, h2⟩ := (objectsG_returns d n (chainSh s)).1 ⟨y, h⟩
  rw [led_is d s, Option.isSome_map] at h1
  rw [heardShAt_is d s, Option.isSome_map] at h2
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h2
  refine ⟨(g.rows.toList.map (seatOf K3Lot.ofForm d).claim,
    (seatOf K3Lot.ofForm d).mark s (F.paid g.owedObjects)), ?_⟩
  unfold objectsRun
  simp only [hF, hg, named, bind, Except.bind, pure, Except.pure]

/-- **The law of "objects".** Its hypothesis is "true". -/
def objectsLaw (d : Bool) : RunLaw (objectsRun (seatOf K3Lot.ofForm d)) :=
  RunLaw.ofStrong (objectsG d) (fun _ _ => True) (objects_strong d)
    fun n s y h _ => objectsG_back d n s y h

/-! ## 3 "guests", at the empty list -/

/-- **"guests" on shapes**: no claim; the shape as it is. -/
def guestsG (_ : Nat) (c : ChainSh) : Except String (List ClaimSh × ChainSh) := .ok ([], c)

theorem guests_strong (n : Nat) (s s' : FS) (cs : List Claim)
    (h : guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim)) n s =
      .ok (cs, s')) : guestsG n (chainSh s) = .ok (cs.map claimSh, chainSh s') := by
  rw [guestsRun_nil] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  rfl

/-- **The law of "guests".** Its hypothesis is "true"; its run on shapes never refuses. -/
def guestsLaw :
    RunLaw (guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim))) :=
  RunLaw.ofStrong guestsG (fun _ _ => True) guests_strong fun n s _ _ _ => ⟨_, guestsRun_nil n s⟩

/-! ## 4 Behind the guard -/

/-- Where the run returns and leaves what the guard compares, the run behind the guard returns the
same. -/
theorem guard_same {same : FS → FS → Bool} {run : RunT} {n : Nat} {s : FS} {z : List Claim × FS}
    (h : run n s = .ok z) (hs : same s z.2 = true) : IM.guardRun same run n s = .ok z := by
  unfold IM.guardRun seatSame
  rw [h]
  show (if same s z.2 then Except.ok z.2 else _).map (fun _ => z) = _
  rw [if_pos hs]
  rfl

/-- Where the run behind the guard returns, the run returns the same. -/
theorem guard_back {same : FS → FS → Bool} {run : RunT} {n : Nat} {s : FS} {z : List Claim × FS}
    (h : IM.guardRun same run n s = .ok z) : run n s = .ok z := by
  unfold IM.guardRun seatSame at h
  cases hr : run n s with
  | error e =>
    rw [hr] at h
    exact nomatch h
  | ok y =>
    rw [hr] at h
    have h' : (if same s y.2 then Except.ok y.2 else
      Except.error "a block wrote a part of the record that it may not write").map
        (fun _ => y) = .ok z := h
    split at h'
    · exact h'
    · exact nomatch h'

/-- **A law of a run is a law of the run behind the guard**, with the same run on shapes and the
same hypothesis. General in the run. Conditional on the run leaving what the guard compares. -/
def guardLaw {same : FS → FS → Bool} {run : RunT} (R : RunLaw run)
    (h : ∀ n s z, run n s = .ok z → same s z.2 = true) : RunLaw (IM.guardRun same run) where
  runG := R.runG
  pre := R.pre
  carries := fun n s s' cs y hp hr hg => R.carries n s s' cs y hp (guard_back hr) hg
  returns := fun n s y hg hp => by
    obtain ⟨z, hz⟩ := R.returns n s y hg hp
    exact ⟨z, guard_same hz (h n s z hz)⟩

/-- Setting a ledger leaves the reply. -/
theorem putFork_reply (s : FS) (F : Fork) : sameReply s (s.putFork F) = true := by
  unfold sameReply
  rw [ProofFile.Honest.K3.Law.putFork_out]
  simp

theorem objectsRun_reply (d : Bool) (n : Nat) (s : FS) (z : List Claim × FS)
    (h : objectsRun (seatOf K3Lot.ofForm d) n s = .ok z) : sameReply s z.2 = true := by
  unfold objectsRun at h
  cases hF : (seatOf K3Lot.ofForm d).fork s with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    cases hg : (seatOf K3Lot.ofForm d).heard s with
    | none => simp [hF, hg, named, bind, Except.bind] at h
    | some g =>
      simp only [hF, hg, named, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      show sameReply s ((seatOf K3Lot.ofForm d).mark s _) = true
      rw [mark_is]
      exact putFork_reply s _

/-- "objects" behind the guard on the reply. -/
def objectsLawG (d : Bool) : RunLaw (IM.guardRun sameReply (objectsRun (seatOf K3Lot.ofForm d))) :=
  guardLaw (objectsLaw d) (objectsRun_reply d)

/-- "guests" behind the guard on the reply. -/
def guestsLawG : RunLaw (IM.guardRun sameReply
    (guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim)))) :=
  guardLaw guestsLaw fun n s z h => by
    rw [guestsRun_nil] at h
    obtain rfl := Except.ok.inj h
    unfold sameReply
    simp

/-! ## 5 They are the runs that the sub-protocol at a lookup's address states -/

/-- **The sub-protocol at a lookup's address states these two runs first, at its seat.** The
library's own law, called. Conditional on the maker's return at the address. -/
theorem stated_two (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes)
    (shape : OnBytes.Params.ReqShape) (a : VerifiableInference.Desc.Place)
    (x : VerifiableInference.Desc.Block FS Claim)
    (h : VerifiableInference.Desc.K3.theOwn K3Lot.ofForm true X codes shape a = some x) (i : Nat)
    (d : Bool) (hl : a.link = some i) (hpc : a.piece = VerifiableInference.Desc.K3.pieceAt X i d) :
    ∃ tail, x.claims = ("objects", objectsRun (seatOf K3Lot.ofForm d)) ::
      ("guests", guestsRun []) :: tail :=
  VerifiableInference.OnPublicFiles.theOwn_twoAt K3Lot.ofForm X codes shape a x h i d hl hpc

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.heardShAt_is
#print axioms ProofFile.Honest.K3.Shape.led_is
#print axioms ProofFile.Honest.K3.Shape.mark_is
#print axioms ProofFile.Honest.K3.Shape.claimSh_ofForm
#print axioms ProofFile.Honest.K3.Shape.objectsG_returns
#print axioms ProofFile.Honest.K3.Shape.objects_strong
#print axioms ProofFile.Honest.K3.Shape.objectsG_back
#print axioms ProofFile.Honest.K3.Shape.guests_strong
#print axioms ProofFile.Honest.K3.Shape.guard_same
#print axioms ProofFile.Honest.K3.Shape.guard_back
#print axioms ProofFile.Honest.K3.Shape.putFork_reply
#print axioms ProofFile.Honest.K3.Shape.objectsRun_reply
#print axioms ProofFile.Honest.K3.Shape.stated_two
#print axioms ProofFile.Honest.K3.Shape.objectsLaw
#print axioms ProofFile.Honest.K3.Shape.guestsLaw
#print axioms ProofFile.Honest.K3.Shape.guardLaw
#print axioms ProofFile.Honest.K3.Shape.objectsLawG
#print axioms ProofFile.Honest.K3.Shape.guestsLawG
