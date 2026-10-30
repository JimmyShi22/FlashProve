-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/SeatTie.lean: THE SEAT's TIE FOR K4's TWO RUNS (`StatesAt`, InT/Statement.lean)
AT A LINK WHOSE SUB-PROTOCOL NUMBER b IS K4's SUB-PROTOCOL BEHIND THE DRIVER's GUARD
(`Block.guarded`, Johnson/Desc/SeatGuard.lean: each run of claims is followed by a test that the run
has not written the guarded part of the verifier's state). Statements and proofs.

  `out_wrote`: a run of K4's writes the segment's ledger and the debt of rows alone: the state's out
    stays.
  `k4_run_out`: wherever a run "front" or "back" of `blockAtC p` returns, out stays.
  **`statesAt_guarded`**: where the segment's sub-protocol number b has, as its runs, `blockAtC p`'s
    runs each behind the guard at a test same, and same accepts at two states with one out:
    `StatesAt` at "front" and at "back", AT EVERY STATE: the guarded run and the bare run give one
    answer: where the bare run rejects, both reject alike; where it returns, the guard's test
    accepts.

Limits. hcl ("the sub-protocol's runs are these, behind the guard") and hb ("the segment's
sub-protocol number b is that sub-protocol") are premises: the seat's own laws have them. hsame is a
premise on the test: the driver's test compares the replies, which stand in out. K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.InT.Statement
import Johnson.Road.K4.InT.ReaderAtK4
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.InT

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par blockAtC blockAtS atClaims runAtC frontAtS backAtS Wrote)
open OnBytes.Desc.First.K4.InT (find_of_lookup)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc (Claim Link Block seatSame K9.statesOfLink)

/-- A lookup through a map that leaves the names. -/
theorem lookup_mapSnd {α β : Type} (f : α → β) : ∀ (l : List (String × α)) (name : String) (x : α),
    l.lookup name = some x → (l.map fun c => (c.1, f c.2)).lookup name = some (f x)
  | [], _, _, h => by simp at h
  | (k, v) :: l, name, x, h => by
    cases hb : (name == k) with
    | true =>
      simp only [List.lookup_cons, hb, Option.some.injEq] at h
      subst h
      simp only [List.map_cons, List.lookup_cons, hb]
    | false =>
      simp only [List.lookup_cons, hb] at h
      simp only [List.map_cons, List.lookup_cons, hb]
      exact lookup_mapSnd f l name x h

/-- A run of K4's leaves the state's out. -/
theorem out_wrote {s s' : S} {a : LayOwn} {G : Fork} (h : Wrote s a G s') : s'.out = s.out := by
  rw [h.2]

/-- Wherever a run "front" or "back" of K4's sub-protocol at the one type of a claim returns, out
stays. -/
theorem k4_run_out {p : Par} {name : String} (hn : name = "front" ∨ name = "back")
    {runC : ℕ → S → Except String (List Claim × S)}
    (hC : (blockAtC p).claims.lookup name = some runC) {n : ℕ} {s : S} {y : List Claim × S}
    (h : runC n s = .ok y) : y.2.out = s.out := by
  obtain ⟨cl, s'⟩ := y
  obtain ⟨r0, fl, h0, h1, _⟩ := runAtC (b := blockAtS p) hC h
  rcases hn with rfl | rfl
  · obtain ⟨a, _, _, G, _, _, _, hw⟩ := frontAtS h0 h1
    exact out_wrote hw
  · obtain ⟨a, _, _, G, _, _, _, hw⟩ := backAtS h0 h1
    exact out_wrote hw

/-- **The seat's tie at a guarded seat**, at every state. -/
theorem statesAt_guarded {l : Link S Claim} {b : ℕ} {B : Block S Claim} {p : Par}
    {same : S → S → Bool} (hb : l.hear[b]? = some B)
    (hcl : B.claims = (blockAtC p).claims.map fun c =>
      (c.1, fun n t => (c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y))
    (hsame : ∀ t s : S, s.out = t.out → same t s = true) {name : String}
    (hn : name = "front" ∨ name = "back")
    {runC : ℕ → S → Except String (List Claim × S)}
    (hC : (blockAtC p).claims.lookup name = some runC) (s : S) :
    StatesAt (K9.statesOfLink l) b p name s := by
  have hl : B.claims.lookup name =
      some fun n t => (runC n t).bind fun y => (seatSame same t y.2).map fun _ => y := by
    rw [hcl]
    exact lookup_mapSnd (fun (r : ℕ → S → Except String (List Claim × S)) n t =>
      (r n t).bind fun y => (seatSame same t y.2).map fun _ => y) _ _ _ hC
  refine ⟨(name, fun n t => (runC n t).bind fun y => (seatSame same t y.2).map fun _ => y), runC,
  ?_,
    hC, ?_⟩
  · show (((l.hear[b]?).map fun x => x.claims).getD []).find? _ = _
    rw [hb]
    exact find_of_lookup _ _ _ hl
  · show ((runC 0 s).bind fun y => (seatSame same s y.2).map fun _ => y) = runC 0 s
    cases h : runC 0 s with
    | error e => rfl
    | ok y =>
      have e := hsame s y.2 (k4_run_out hn hC h)
      show ((seatSame same s y.2).map fun _ => y) = .ok y
      unfold seatSame
      rw [if_pos e]
      rfl

end OnBytes.Road.K4.InT

#print axioms OnBytes.Road.K4.InT.k4_run_out
#print axioms OnBytes.Road.K4.InT.statesAt_guarded
