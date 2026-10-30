-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3StatedRuns.lean: the kind "lookup" (K3): EVERY RUN OF CLAIMS THAT THE BLOCK OF
K3.theStated STATES AT AN ADDRESS (Johnson/Desc/First/Look/K3Stated.lean) STEPS AS Block.RunsStep
ASKS, at both readings of "heard". Statements and proofs: a peeling of four makers' texts, then
calls of Johnson/Top/H/K3StepsAt.lean.

Main names:
  `theOwn_runs_of`, `theWhole_runs_of`, `withCaller_runs_of`, `callsWith_runs_of`: whatever holds of
  every run of K3.block at the two seats (and of "planes") holds of every run of the block that
  these makers hand out.
  `theOwn_runs_calls`, `theOwn_runs_digits`, `theWhole_runs_calls`, `theWhole_runs_digits`: so these
  blocks' runs step along CarriesFo S.fork? hd, at hd := S.lookHeard? and at hd := tlHeard.
  `withCaller_runs_calls`, `withCaller_runs_digits`: "planes" behind ANY block whose runs step.
  `theStated_runs_of`: one proof for every relation R.
  `theStated_runs_calls`, `theStated_runs_digits`: **theStated ... a = some b gives b.RunsStep
  (CarriesFo S.fork? hd)**, general in claim and readers.
  `block_states_a_run`, `runsStep_bites`: two controls: K3's block states a run; along the relation
  that nothing has, RunsStep fails at it.

OBJECT: K3.theStated (Johnson/Desc/First/Look/K3Stated.lean): the block at a lookup's address with
every listed run of claims stated.
Used by KindsAtPure.lean (Johnson/Desc/First/K9x/) and ReadersSeated.lean (Johnson/Desc/K1/Law/).
LETTERS: general in claim, readers, X, codes, shape, a.


Compiled with the whole library.
The peeling names neither how many public data theOwn
asks nor the block's maker: it asks Lean to see by rfl that the runs of what theOwn lays are
K3.block's.

Limits. A frame's law on the runs: no error term. Nothing on decide; nothing on what the runs'
claims are worth; nothing where theStated gives no block. Which names the block states is not said
here. runs := false is not treated.
Not claimed: anything on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H.K3StepsAt
import Johnson.Desc.First.Look.K3Stated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits planesRun Readers)

/-- A named run of claims, as a block states it. -/
abbrev RunK (T Cl : Type) : Type := String × (Nat → T → Except String (List Cl × T))

section Own
variable {Cl : Type}

/-- **The runs of the block at an address are K3.block's, at one of the two seats.** -/
theorem theOwn_runs_of (Pr : RunK S Cl → Prop) (claim : Aff → Cl)
    (hC : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (seatCalls claim) piece laid sent p []).claims, Pr c)
    (hD : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (seatDigits claim) piece laid sent p []).claims, Pr c)
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (x : Block S Cl) (h : Desc.K3.theOwn claim true X codes shape a = some x) :
    ∀ c ∈ x.claims, Pr c := by
  unfold Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      intro c hc
      cases digits
      · exact hC a.piece #[] [] p c hc
      · exact hD a.piece #[] [] p c hc

end Own

section With
variable {T Cl : Type}

/-- **With "planes" stated behind its own runs.** -/
theorem withCaller_runs_of (Pr : RunK T Cl → Prop) (seat : Seat T Cl) (p : Desc.First.Look.P)
    (readers : Readers T) (b : Block T Cl) (hb : ∀ c ∈ b.claims, Pr c)
    (hp : Pr ("planes", planesRun seat p.lm readers)) :
    ∀ c ∈ (Desc.K3.withCaller seat p readers b).claims, Pr c := by
  intro c hc
  have hc' : c ∈ b.claims ++ [("planes", planesRun seat p.lm readers)] := hc
  rcases List.mem_append.1 hc' with h | h
  · exact hb c h
  · obtain rfl := List.mem_singleton.1 h
    exact hp

end With

section CallsWith
variable {Cl : Type}

/-- **The block at a link's calls, with a caller's readers.** -/
theorem callsWith_runs_of (Pr : RunK S Cl → Prop) (claim : Aff → Cl)
    (hC : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (seatCalls claim) piece laid sent p []).claims, Pr c)
    (hD : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (seatDigits claim) piece laid sent p []).claims, Pr c)
    (readers : Readers S) (hP : ∀ lm, Pr ("planes", planesRun (seatCalls claim) lm readers))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat) (x : Block S Cl)
    (h : ((Desc.First.Look.placeAt X i false).bind fun p =>
      (Desc.K3.theOwn claim true X codes shape ⟨1, some i, Desc.K3.pieceAt X i false, .K3⟩).map
        fun b => Desc.K3.withCaller (seatCalls claim) p readers b) = some x) :
    ∀ c ∈ x.claims, Pr c := by
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact withCaller_runs_of Pr (seatCalls claim) p readers b
    (theOwn_runs_of Pr claim hC hD X codes shape _ b hb) (hP p.lm)

/-- A CHECK AT A SILLY MEMBER: theOwn_runs_of's two premises bear load: a property that no run has
is had by no run of K3.block at the calls' seat: that block states a run. -/
theorem block_states_a_run (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (sent : List (Nat × Nat))
    (p : Desc.First.Look.P) :
    ¬ ∀ c ∈ (Desc.K3.block (seatCalls claim) piece laid sent p []).claims, False := by
  intro H
  exact H _ (List.mem_cons_self)

end CallsWith

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place CarriesFo)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits planesRun Readers)

variable {Cl : Type}

/-- What Block.RunsStep asks of one run. -/
abbrev StepsAlong (R : S → S → Prop) (c : RunK S Cl) : Prop :=
  ∀ n s cl s', c.2 n s = .ok (cl, s') → R s s'

/-- **The block at an address steps along its runs**: "heard" read at the calls. -/
theorem theOwn_runs_calls (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theOwn claim true X codes shape a = some x) :
    x.RunsStep (CarriesFo S.fork? S.lookHeard?) :=
  theOwn_runs_of (StepsAlong (CarriesFo S.fork? S.lookHeard?)) claim
    (fun piece laid sent p => calls_runs_calls claim piece laid sent p [])
    (fun piece laid sent p => digits_runs_calls claim piece laid sent p []) X codes shape a x h

/-- The same: "heard" read at the digits. -/
theorem theOwn_runs_digits (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theOwn claim true X codes shape a = some x) :
    x.RunsStep (CarriesFo S.fork? tlHeard) :=
  theOwn_runs_of (StepsAlong (CarriesFo S.fork? tlHeard)) claim
    (fun piece laid sent p => calls_runs_digits claim piece laid sent p [])
    (fun piece laid sent p => digits_runs_digits claim piece laid sent p []) X codes shape a x h

/-- **The block at a link's calls, with a caller's readers**: "heard" read at the calls. -/
theorem callsWith_runs_calls (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (i : Nat) (readers : Readers S) (x : Block S Cl)
    (h : ((Desc.First.Look.placeAt X i false).bind fun p =>
      (Desc.K3.theOwn claim true X codes shape ⟨1, some i, Desc.K3.pieceAt X i false, .K3⟩).map
        fun b => Desc.K3.withCaller (seatCalls claim) p readers b) = some x) :
    x.RunsStep (CarriesFo S.fork? S.lookHeard?) :=
  callsWith_runs_of (StepsAlong (CarriesFo S.fork? S.lookHeard?)) claim
    (fun piece laid sent p => calls_runs_calls claim piece laid sent p [])
    (fun piece laid sent p => digits_runs_calls claim piece laid sent p []) readers
    (fun lm n s cl s' hr => planes_step (seatCalls claim) (fun s F G h => fork_putFork s F G h)
      S.lookHeard? (mark_calls claim) lm readers n s s' cl hr) X codes shape i x h

/-- The same: "heard" read at the digits. -/
theorem callsWith_runs_digits (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (i : Nat) (readers : Readers S) (x : Block S Cl)
    (h : ((Desc.First.Look.placeAt X i false).bind fun p =>
      (Desc.K3.theOwn claim true X codes shape ⟨1, some i, Desc.K3.pieceAt X i false, .K3⟩).map
        fun b => Desc.K3.withCaller (seatCalls claim) p readers b) = some x) :
    x.RunsStep (CarriesFo S.fork? tlHeard) :=
  callsWith_runs_of (StepsAlong (CarriesFo S.fork? tlHeard)) claim
    (fun piece laid sent p => calls_runs_digits claim piece laid sent p [])
    (fun piece laid sent p => digits_runs_digits claim piece laid sent p []) readers
    (fun lm n s cl s' hr => planes_step (seatCalls claim) (fun s F G h => fork_putFork s F G h)
      tlHeard (mark_digits claim) lm readers n s s' cl hr) X codes shape i x h

/-- **K3.block at the calls' seat with a caller's readers**, at any piece, counts, list, place and
guests: the term at which a kind that lays the block itself (not through theOwn) meets it: "heard"
read at the calls. -/
theorem withCaller_block_calls (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p q : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (readers : Readers S) :
    (Desc.K3.withCaller (seatCalls claim) q readers
      (Desc.K3.block (seatCalls claim) piece laid before p guests)).RunsStep
      (CarriesFo S.fork? S.lookHeard?) :=
  withCaller_runs_of (StepsAlong (CarriesFo S.fork? S.lookHeard?)) (seatCalls claim) q readers _
    (calls_runs_calls claim piece laid before p guests)
    (fun n s cl s' hr => planes_step (seatCalls claim) (fun s F G h => fork_putFork s F G h)
      S.lookHeard? (mark_calls claim) q.lm readers n s s' cl hr)

/-- The same: "heard" read at the digits. -/
theorem withCaller_block_digits (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p q : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (readers : Readers S) :
    (Desc.K3.withCaller (seatCalls claim) q readers
      (Desc.K3.block (seatCalls claim) piece laid before p guests)).RunsStep
      (CarriesFo S.fork? tlHeard) :=
  withCaller_runs_of (StepsAlong (CarriesFo S.fork? tlHeard)) (seatCalls claim) q readers _
    (calls_runs_digits claim piece laid before p guests)
    (fun n s cl s' hr => planes_step (seatCalls claim) (fun s F G h => fork_putFork s F G h)
      tlHeard (mark_digits claim) q.lm readers n s s' cl hr)

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place CarriesFo roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits planesRun Readers)

variable {Cl : Type}

/-- A step without a round behind a block states no run. -/
theorem andThen_quiet_runs_of {T : Type} (Pr : RunK T Cl → Prop) (b : Block T Cl) (name n : String)
    (chain : Nat) (link : Option Nat) (piece : Nat) (f : T → Except String T)
    (hb : ∀ c ∈ b.claims, Pr c) :
    ∀ c ∈ (b.andThen name (roundlessBlock n chain link piece f)).claims, Pr c := by
  intro c hc
  have hc' : c ∈ b.claims ++ [] := hc
  rw [List.append_nil] at hc'
  exact hb c hc'

/-- **The runs of the block at an address, whole, are K3.block's.** -/
theorem theWhole_runs_of (Pr : RunK S Cl → Prop) (claim : Aff → Cl)
    (hC : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (seatCalls claim) piece laid sent p []).claims, Pr c)
    (hD : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (seatDigits claim) piece laid sent p []).claims, Pr c)
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (x : Block S Cl) (h : Desc.K3.theWhole claim true X codes shape a = some x) :
    ∀ c ∈ x.claims, Pr c := by
  unfold Desc.K3.theWhole at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_runs_of Pr claim hC hD X codes shape a b hb
  split
  · exact andThen_quiet_runs_of Pr b _ _ _ _ _ _ h0
  · exact h0

theorem theWhole_runs_calls (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theWhole claim true X codes shape a = some x) :
    x.RunsStep (CarriesFo S.fork? S.lookHeard?) :=
  theWhole_runs_of (StepsAlong (CarriesFo S.fork? S.lookHeard?)) claim
    (fun piece laid sent p => calls_runs_calls claim piece laid sent p [])
    (fun piece laid sent p => digits_runs_calls claim piece laid sent p []) X codes shape a x h

theorem theWhole_runs_digits (claim : Aff → Cl) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (x : Block S Cl)
    (h : Desc.K3.theWhole claim true X codes shape a = some x) :
    x.RunsStep (CarriesFo S.fork? tlHeard) :=
  theWhole_runs_of (StepsAlong (CarriesFo S.fork? tlHeard)) claim
    (fun piece laid sent p => calls_runs_digits claim piece laid sent p [])
    (fun piece laid sent p => digits_runs_digits claim piece laid sent p []) X codes shape a x h

/-- **With a caller's "planes" behind ANY block whose runs step.** -/
theorem withCaller_runs_calls (claim : Aff → Cl) (p : Desc.First.Look.P) (readers : Readers S)
    (b : Block S Cl) (hb : b.RunsStep (CarriesFo S.fork? S.lookHeard?)) :
    (Desc.K3.withCaller (seatCalls claim) p readers b).RunsStep (CarriesFo S.fork? S.lookHeard?) :=
  withCaller_runs_of (StepsAlong (CarriesFo S.fork? S.lookHeard?)) (seatCalls claim) p readers b hb
    (fun n s cl s' hr => planes_step (seatCalls claim) (fun s F G h => fork_putFork s F G h)
      S.lookHeard? (mark_calls claim) p.lm readers n s s' cl hr)

theorem withCaller_runs_digits (claim : Aff → Cl) (p : Desc.First.Look.P) (readers : Readers S)
    (b : Block S Cl) (hb : b.RunsStep (CarriesFo S.fork? tlHeard)) :
    (Desc.K3.withCaller (seatCalls claim) p readers b).RunsStep (CarriesFo S.fork? tlHeard) :=
  withCaller_runs_of (StepsAlong (CarriesFo S.fork? tlHeard)) (seatCalls claim) p readers b hb
    (fun n s cl s' hr => planes_step (seatCalls claim) (fun s F G h => fork_putFork s F G h)
      tlHeard (mark_digits claim) p.lm readers n s s' cl hr)

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place CarriesFo roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits planesRun Readers theOwn theWhole
  theStated withCaller pieceAt)

variable {Cl : Type}

/-! ## (2) The runs step -/

/-- One proof for both readings: from the two facts that part them. -/
theorem theStated_runs_of (R : S → S → Prop) (claim : Aff → Cl)
    (hW : ∀ X codes shape a (x : Block S Cl), theWhole claim true X codes shape a = some x →
      x.RunsStep R)
    (hC : ∀ p readers (x : Block S Cl), x.RunsStep R →
      (withCaller (seatCalls claim) p readers x).RunsStep R)
    (readers : Nat → Option (Readers S)) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (b : Block S Cl)
    (h : theStated claim readers X codes shape a = some b) : b.RunsStep R := by
  unfold theStated at h
  obtain ⟨b₀, h₀, h⟩ := Option.bind_eq_some_iff.1 h
  have e0 := hW X codes shape a b₀ h₀
  cases hl : a.link with
  | none =>
    simp only [hl] at h
    obtain rfl : b₀ = b := Option.some.inj h
    exact e0
  | some i =>
    simp only [hl] at h
    by_cases hp : (a.piece != pieceAt X i false) = true
    · rw [if_pos hp] at h
      obtain rfl : b₀ = b := Option.some.inj h
      exact e0
    · rw [if_neg hp] at h
      cases hr : readers i with
      | none =>
        simp only [hr] at h
        obtain rfl : b₀ = b := Option.some.inj h
        exact e0
      | some r =>
        simp only [hr] at h
        obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hC p r b₀ e0

/-- **Every run that theStated's block states steps**: "heard" read at the calls. -/
theorem theStated_runs_calls (claim : Aff → Cl) (readers : Nat → Option (Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (b : Block S Cl) (h : theStated claim readers X codes shape a = some b) :
    b.RunsStep (CarriesFo S.fork? S.lookHeard?) :=
  theStated_runs_of _ claim (theWhole_runs_calls claim) (withCaller_runs_calls claim) readers X
    codes shape a b h

/-- The same: "heard" read at the digits. -/
theorem theStated_runs_digits (claim : Aff → Cl) (readers : Nat → Option (Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (b : Block S Cl) (h : theStated claim readers X codes shape a = some b) :
    b.RunsStep (CarriesFo S.fork? tlHeard) :=
  theStated_runs_of _ claim (theWhole_runs_digits claim) (withCaller_runs_digits claim) readers X
    codes shape a b h

/-- A CONTROL: RunsStep bites at K3's own block: along the relation that nothing has it fails: the
run "guests" returns. -/
theorem runsStep_bites (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (sent : List (Nat × Nat)) (p : Desc.First.Look.P) :
    ¬ (Desc.K3.block (seatCalls claim) piece laid sent p []).RunsStep (fun _ _ => False) := by
  intro H
  exact H _ (List.mem_cons_of_mem _ List.mem_cons_self) 0 S.blank [] S.blank rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.theOwn_runs_of
#print axioms VerifiableInference.OnPublicFiles.withCaller_runs_of
#print axioms VerifiableInference.OnPublicFiles.callsWith_runs_of
#print axioms VerifiableInference.OnPublicFiles.block_states_a_run
#print axioms VerifiableInference.OnPublicFiles.withCaller_block_calls
#print axioms VerifiableInference.OnPublicFiles.withCaller_block_digits
#print axioms VerifiableInference.OnPublicFiles.theOwn_runs_calls
#print axioms VerifiableInference.OnPublicFiles.theOwn_runs_digits
#print axioms VerifiableInference.OnPublicFiles.callsWith_runs_calls
#print axioms VerifiableInference.OnPublicFiles.callsWith_runs_digits
#print axioms VerifiableInference.OnPublicFiles.theWhole_runs_calls
#print axioms VerifiableInference.OnPublicFiles.theWhole_runs_digits
#print axioms VerifiableInference.OnPublicFiles.withCaller_runs_calls
#print axioms VerifiableInference.OnPublicFiles.withCaller_runs_digits
#print axioms VerifiableInference.OnPublicFiles.theStated_runs_calls
#print axioms VerifiableInference.OnPublicFiles.theStated_runs_digits
#print axioms VerifiableInference.OnPublicFiles.runsStep_bites
