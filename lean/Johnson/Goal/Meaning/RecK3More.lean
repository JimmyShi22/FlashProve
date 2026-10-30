-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK3More.lean: kind K3's other texts: its run "planes", the block with that
run laid behind its own, and the kind's three further forms: each keeps every reflexive relation
that its seat's two layings keep. At the two seats at the first chain's record they are Quiet
(Johnson/Goal/Meaning/RecQuiet.lean).

GENERAL RULES, at any record and seat:
  planesRun_keep: the run "planes" (Johnson/Desc/First/Look/K3Runs.lean) lays through the seat's
    mark alone.
  withCaller_whole: the block with "planes" behind its own runs (withCaller) keeps what the block
    and the seat's mark keep.
  blockG_whole: the kind general in its numbers (lookupKind, Johnson/Desc/First/Look/K3LookupGeneral.lean):
    its decide and its three runs "objects", "planes", "guests".
  blockV_whole: the same hearing on a view's rounds (blockV,
  Johnson/Desc/First/Look/Via/Rounds.lean). blockVia_whole: the first form with the hearing
    exchanged (blockVia, Johnson/Desc/First/Look/Via/Via.lean).
AT THE RECORD:
  withCallerCalls_quiet, withCallerDigits_quiet: withCaller at the seats seatCalls and seatDigits
    (K3Seat.lean), over a Quiet block.
  blockViaCalls_quiet, blockViaDigits_quiet: blockVia at these two seats.
  lookClaims_quiet: every block that lookClaims gives (Johnson/Stored/HeadAddsAtS.lean: the lookup
    on the head's calls, with "planes").
  THE BLOCK AT AN ADDRESS: theOwn_quiet: every block that theOwn gives at an address is Quiet:
    theOwn (Johnson/Desc/First/Look/K3Own.lean) is made of blockVia.
    theWhole_quiet: Whole Quiet b for every b with theWhole claim runs X codes shape a = some b
    (Johnson/Desc/First/Look/K3Whole.lean); theWhole_rec, theWhole_grows.
With whole_rec and whole_grows each gives Whole (RecRel cs sh) and Whole (GrowsBy fun s => s.st).
Not claimed: a seat of lookupKind or blockV at the record: the tree has none.
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecK3
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.First.Look.Via.Via
import Johnson.Stored.HeadAddsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole FnCl)

variable {T Cl : Type}

/-- The run "planes" lays through the seat's mark alone. -/
theorem planesRun_keep (R : T → T → Prop) (seat : K3.Seat T Cl)
    (hmark : ∀ s G, R s (seat.mark s G)) (lm : Nat) (readers : K3.Readers T) (n : Nat) :
    FnCl R (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, _, h⟩ := bindE h
  obtain ⟨g, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨r, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  cases h
  exact hmark _ _

/-- The block with "planes" behind its own runs. -/
theorem withCaller_whole (R : T → T → Prop) (seat : K3.Seat T Cl)
    (hmark : ∀ s G, R s (seat.mark s G)) (p : First.Look.P) (readers : K3.Readers T)
    {b : Block T Cl} (W : Whole R b) : Whole R (K3.withCaller seat p readers b) := by
  refine ⟨W.1, fun c hc n => ?_, W.2.2⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact W.2.1 c hc n
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact planesRun_keep R seat hmark _ readers n
    · cases hc

/-- The run "guests" hands the record back as it is. -/
theorem guests_keep (R : T → T → Prop) (hr : ∀ s, R s s) (name : String)
    (guests : List (First.Look.Guest T Cl)) :
    FnCl R fun s => named name
      ((guests.mapM fun (g : First.Look.Guest T Cl) => g.form s).map fun l => (l, s)) := by
  intro s y h
  obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (Keeps.named_ok h)
  rw [← e]
  exact hr s

/-- **The kind general in its numbers.** -/
theorem blockG_whole (R : T → T → Prop) (hr : ∀ s, R s s) (seat : K3.SeatG T Cl)
    (hput : ∀ s g G, R s (seat.put s g G)) (hmark : ∀ s G, R s (seat.mark s G))
    (before : List (Nat × Nat)) (bits : Nat) (guests : List (First.Look.Guest T Cl)) (p : K3.PG) :
    Whole R (K3.lookupKind seat before bits guests p) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · obtain ⟨F, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, _, h⟩ := bindE h
    cases h
    exact hput _ _ _
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨F, _, h⟩ := bindE h
      obtain ⟨g, _, h⟩ := bindE h
      cases h
      exact hmark _ _
    · rcases List.mem_cons.1 hc with rfl | hc
      · obtain ⟨F, _, h⟩ := bindE h
        obtain ⟨g, _, h⟩ := bindE h
        obtain ⟨_, _, h⟩ := bindE h
        obtain ⟨x, _, h⟩ := bindE h
        obtain ⟨l, _, h⟩ := bindE h
        cases h
        exact hmark _ _
      · rcases List.mem_cons.1 hc with rfl | hc
        · exact guests_keep R hr _ guests s y h
        · cases hc

/-- **The same, hearing on a view's rounds.** -/
theorem blockV_whole (R : T → T → Prop) (hr : ∀ s, R s s) (seat : K3.SeatV T Cl)
    (hput : ∀ s g G, R s (seat.put s g G)) (hmark : ∀ s G, R s (seat.mark s G))
    (before : List (Nat × Nat)) (bits : Nat) (guests : List (First.Look.Guest T Cl)) (p : K3.PG) :
    Whole R (K3.blockV seat before bits guests p) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · obtain ⟨F, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, _, h⟩ := bindE h
    cases h
    exact hput _ _ _
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨F, _, h⟩ := bindE h
      obtain ⟨g, _, h⟩ := bindE h
      cases h
      exact hmark _ _
    · rcases List.mem_cons.1 hc with rfl | hc
      · obtain ⟨F, _, h⟩ := bindE h
        obtain ⟨g, _, h⟩ := bindE h
        obtain ⟨_, _, h⟩ := bindE h
        obtain ⟨x, _, h⟩ := bindE h
        obtain ⟨l, _, h⟩ := bindE h
        cases h
        exact hmark _ _
      · rcases List.mem_cons.1 hc with rfl | hc
        · exact guests_keep R hr _ guests s y h
        · cases hc

/-- **The first form with the hearing exchanged.** -/
theorem blockVia_whole (R : T → T → Prop) (hr : ∀ s, R s s) (seat : K3.Seat T Cl)
    (hput : ∀ s g G, R s (seat.put s g G)) (hmark : ∀ s G, R s (seat.mark s G)) (piece : Nat)
    (laid : Array Nat) (before : List (Nat × Nat)) (p : First.Look.P)
    (guests : List (First.Look.Guest T Cl)) :
    Whole R (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · have h' : K3.Law.decideVia seat p s rs = .ok s' := h
    unfold K3.Law.decideVia at h'
    obtain ⟨F, _, h'⟩ := bindE h'
    obtain ⟨_, _, h'⟩ := bindE h'
    obtain ⟨_, _, h'⟩ := bindE h'
    obtain ⟨_, _, h'⟩ := bindE h'
    obtain ⟨x, _, h'⟩ := bindE h'
    cases h'
    exact hput _ _ _
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨F, _, h⟩ := bindE h
      obtain ⟨g, _, h⟩ := bindE h
      cases h
      exact hmark _ _
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact guests_keep R hr _ guests s y h
      · cases hc

/-! ## At the record -/

theorem withCallerCalls_quiet (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole Quiet b) :
    Whole Quiet (K3.withCaller (K3.seatCalls claim) p readers b) :=
  withCaller_whole Quiet _ (seatCalls_mark claim) p readers W

theorem withCallerDigits_quiet (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole Quiet b) :
    Whole Quiet (K3.withCaller (K3.seatDigits claim) p readers b) :=
  withCaller_whole Quiet _ (seatDigits_mark claim) p readers W

theorem blockViaCalls_quiet (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole Quiet (K3.Law.blockVia (K3.seatCalls claim) piece laid before p guests) :=
  blockVia_whole Quiet quiet_refl _ (seatCalls_put claim) (seatCalls_mark claim) _ _ _ _ _

theorem blockViaDigits_quiet (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole Quiet (K3.Law.blockVia (K3.seatDigits claim) piece laid before p guests) :=
  blockVia_whole Quiet quiet_refl _ (seatDigits_put claim) (seatDigits_mark claim) _ _ _ _ _

/-- Every block that lookClaims gives is Quiet. -/
theorem lookClaims_quiet (W : Verify.Public) (l : Nat) {b : Block S Claim}
    (h : Kinds.Head.lookClaims W l = some b) : Whole Quiet b := by
  unfold Kinds.Head.lookClaims at h
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact withCallerCalls_quiet _ p _ (blockViaCalls_quiet _ _ _ _ _ _)

/-! ## The block at an address (`theOwn`: Look/K3Own.lean; `theWhole`: Look/K3Whole.lean) -/

/-- **Every block that theOwn gives is Quiet.** -/
theorem theOwn_quiet (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole Quiet b := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      have W : Whole Quiet (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockViaCalls_quiet claim _ _ _ _ _
        · exact blockViaDigits_quiet claim _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

/-- **The block at an address, whole, is Quiet.** -/
theorem theWhole_quiet (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole Quiet b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_quiet claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole Quiet quiet_trans _ _ _ W
      ⟨Keeps.quiet_decides Quiet _ _ _ _ f (quietAt_quiet X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

theorem theWhole_rec {cs : Codes} {sh : ReqShape} (claim : Aff → Cl) (runs : Bool)
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole (RecRel cs sh) b :=
  whole_rec (theWhole_quiet claim runs X codes shape a h)

theorem theWhole_grows (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) :
    Whole (ChainEnd.GrowsBy fun s : S => s.st) b :=
  whole_grows (theWhole_quiet claim runs X codes shape a h)

#print axioms planesRun_keep
#print axioms withCaller_whole
#print axioms blockG_whole
#print axioms blockV_whole
#print axioms blockVia_whole
#print axioms blockViaCalls_quiet
#print axioms blockViaDigits_quiet
#print axioms lookClaims_quiet
#print axioms theOwn_quiet
#print axioms theWhole_quiet
#print axioms theWhole_rec
#print axioms theWhole_grows

end Meaning.K2
