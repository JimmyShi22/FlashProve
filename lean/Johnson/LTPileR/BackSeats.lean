-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/BackSeats.lean (over two files:
Johnson/IMR/SeatKeeps.lean and RecSeat.lean): THE SUB-PROTOCOLS BEHIND THE LAST LINK OF THE
REQUEST'S OWN CHAIN, AT THE TWO RELATIONS OwnRel AND RecRel: so that the two walks at them, which
stop at the border behind the last link, go on to the chain's end.

Main names (namespace `Meaning.K2`).
  `atFinish_two`, `atM3_two`, `atM4_two`: what kind K12 at the chain's last proximity test, kind
    K13's batching, and W's commitment with kind K13's sub-protocol behind it leave of the
    verifier's state's "check" and "here": "check" is as it was at all three; "here" is as it was ·
    goes from the finish to the chain's end · stands at the chain's end in front and behind.
  **`seatBack_own A lay`** : `SeatBack (OwnRel A lay)` (Johnson/Goal/Meaning/OwnInv.lean: the rows'
    layout of both copies, and the open link's name): by `atFinish_ctx`, `atM3_ctx`, `atM4_ctx` :
    `Whole SameCtx`.
  **`seatBack_rec cs sh`** : `SeatBack (RecRel cs sh)` (Johnson/Goal/Meaning/RecRel.lean: the codes;
    every copy of the frame has the shape and groups of the list of rounds): by `same_frames`: no
    new copy of the frame comes in, and the codes stay.
  `codes_k12`, `codes_m3`, `codes_m4`:
    the three leave the statement's codes.
    THEIR PROOFS ARE THOSE OF `seatBack_codes` (Johnson/IMR/CodesSeat.lean),
    REPEATED HERE.

WHAT FOLLOWS, NOT TYPED HERE: with `seatKeeps_rec` (under the premise `K2Share`) |
`seatKeeps_own` and `descPure_flat`: `RecAll` | `OwnInv` at every border of the chain.
NOT HERE: kind K2's place at the finish ("F:1"): it is paid by `SeatKeeps`' five fields on kind K2,
not by `SeatBack`.
Limits. Frame laws. Nothing on soundness or on hiding.

-/
import Johnson.IMR.RecSeat
import Johnson.Goal.Meaning.OwnInv
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K12.Law.RunCodes
import Johnson.Desc.K12.SeatLeaves
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K1.Law.HereAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape ReqLayout)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (groundKeeps_grows)

variable {Cl : Type}

/-! ## What the three sub-protocols behind the last link leave of "check" and "here" -/

/-- Kind K12 at the chain's last proximity test: "check" and "here" are as they were. -/
theorem atFinish_two (p : K12.P12) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K12.atFinish p).decide s rs gs = .ok s') :
    s'.check = s.check ∧ s'.here = s.here :=
  ⟨K12.Seat.atFinish_leaves_check p s rs gs s' h, K12.Seat.atFinish_leaves_here p s rs gs s' h⟩

/-- Kind K13's batching: "check" is as it was; the chain goes from the finish to its end. -/
theorem atM3_two (p : K13.Where) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K13.atM3 (Cl := Cl) p).decide s rs gs = .ok s') :
    s'.check = s.check ∧ (∃ f, s.here = .fin f) ∧ ∃ o, s'.here = .mem o := by
  obtain ⟨f, st', o, hf, rfl⟩ := K13.Law.atM3_rec h
  exact ⟨rfl, ⟨f, hf⟩, o, rfl⟩

/-- W's commitment with kind K13's sub-protocol behind it: "check" is as it was; the chain stands at
its end in front and behind. -/
theorem atM4_two (p : K13.Where) (Q : K1.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) p (K1.sendAtS Q)).decide s rs gs = .ok s') :
    s'.check = s.check ∧ (∃ a, s.here = .mem a) ∧ ∃ o, s'.here = .mem o := by
  have h' : ((K1.sendAtS Q : Block S Cl).decide s _ _).bind (fun m =>
      (K13.rowsB (Cl := Cl) K13.atS p).decide m _ _) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := Keeps.ebind_ok h'
  obtain ⟨a, ids, ha, -, -, hc, -⟩ := K1.sendAtS_here Q s s₁ _ _ h1
  obtain ⟨m₀, l, o, owed, -, -, -, rfl⟩ := K13.Law.rowsB_at h2
  exact ⟨hc, ⟨a, ha⟩, _, rfl⟩

/-! ## At the invariant on the rows' layout and the open link's name -/

theorem atFinish_ctx (p : K12.P12) : Whole SameCtx (K12.atFinish p) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨h1, h2⟩ := atFinish_two p h
      unfold SameCtx ctxOf
      rw [h1, h2],
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem atM3_ctx (p : K13.Where) : Whole SameCtx (K13.atM3 (Cl := Cl) p) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨h1, ⟨f, h2⟩, o, h3⟩ := atM3_two p h
      unfold SameCtx ctxOf
      rw [h1, h2, h3],
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem atM4_ctx (p : K13.Where) (Q : K1.Par) :
    Whole SameCtx (K13.atM4 (Cl := Cl) p (K1.sendAtS Q)) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨h1, ⟨a, h2⟩, o, h3⟩ := atM4_two p Q h
      unfold SameCtx ctxOf
      rw [h1, h2, h3],
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **THE MAKERS BEHIND THE LAST LINK, AT `OwnRel` (Johnson/Goal/Meaning/OwnInv.lean).** -/
theorem seatBack_own (A : Nat → Array (Nat × String)) (lay : ReqLayout) :
    SeatBack (OwnRel A lay) where
  k12 := fun _ _ => whole_ownC (atFinish_ctx _)
  k13M3 := fun p => whole_ownC (atM3_ctx p)
  k13M4 := fun p Q _ => whole_ownC (atM4_ctx p Q)

/-! ## At "the state's public part is the list of rounds', in every copy" -/

/-- The three leave the statement's codes.
THE PROOFS ARE THOSE OF `seatBack_codes` (Johnson/IMR/CodesSeat.lean),
repeated here. -/
theorem codes_k12 (m : Johnson.G.OfPlan.Made)
    (hp : (K12.atFinish (H2U.p12OfMade m)).planOk = true) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s') :
    s'.st.codes = s.st.codes := by
  obtain ⟨o, t', -, -, -, hk, rfl⟩ := K12.Seat.atFinish_ok _ s s' rs gs h
  exact (H2K.Out.k12_run_codes _ (atFinish_planOk hp) _ t' rs gs hk).2

theorem codes_m3 (p : K13.Where) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM3 (Cl := Unit) p).decide s rs gs = .ok s') : s'.st.codes = s.st.codes :=
  (K13.atM3_grows p s rs gs s' h).1

theorem codes_m4 (p : K13.Where) (Q : K1.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Unit) p (K1.sendAtS Q)).decide s rs gs = .ok s') :
    s'.st.codes = s.st.codes :=
  (K13.atM4_keeps groundKeeps_grows.quiet p _ (K1.Rel.sendAtS_keeps groundKeeps_grows Q)
    s rs gs s' h).1

/-- **THE MAKERS BEHIND THE LAST LINK, AT `RecRel` (Johnson/Goal/Meaning/RecRel.lean).** -/
theorem seatBack_rec (cs : Codes) (sh : ReqShape) : SeatBack (RecRel cs sh) where
  k12 := fun m hp => ⟨fun s rs gs s' h R => by
      obtain ⟨h1, h2⟩ := atFinish_two _ h
      refine same_frames R (codes_k12 m hp h) fun f hf => ?_
      unfold framesIn at hf ⊢
      rw [h1, h2] at hf
      exact hf,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => ⟨fun s rs gs s' h R => by
      obtain ⟨h1, -, o, h3⟩ := atM3_two p h
      refine same_frames R (codes_m3 p h) fun f hf => ?_
      unfold framesIn at hf ⊢
      rw [h1, h3] at hf
      obtain rfl := List.mem_singleton.1 hf
      exact List.mem_cons_self,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p Q _ => ⟨fun s rs gs s' h R => by
      obtain ⟨h1, -, o, h3⟩ := atM4_two p Q h
      refine same_frames R (codes_m4 p Q h) fun f hf => ?_
      unfold framesIn at hf ⊢
      rw [h1, h3] at hf
      obtain rfl := List.mem_singleton.1 hf
      exact List.mem_cons_self,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

#print axioms atFinish_two
#print axioms atM3_two
#print axioms atM4_two
#print axioms atFinish_ctx
#print axioms atM3_ctx
#print axioms atM4_ctx
#print axioms seatBack_own
#print axioms codes_k12
#print axioms codes_m3
#print axioms codes_m4
#print axioms seatBack_rec

end Meaning.K2
