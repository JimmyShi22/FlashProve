-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4WholeSt.lean: THE SUB-PROTOCOL K4 KEEPS THE RELATION Rest
(Johnson/Desc/First/K4/ReadsAtS.lean), AND SO THE STATEMENT st OF THE VERIFIER's STATE, IN THE FORM
OF Johnson/Desc/FoldKeeps.lean (Whole R b: where b's decision accepts, where a run of claims of b's
returns, and where a run of b's behind the batching returns, the state behind is in R to the state
in front): at K4's own term blockAtS p, at the one type of a claim (blockAtC p), and behind the
driver's two guards under another name and place. Statements and proofs.

  `whole_mono`: Whole passes to every weaker relation.
  **`k4_whole_rest`**: Whole Rest (blockAtS p). **`k4_whole_st`**: Whole (the statement stays)
    (blockAtS p).
  `whole_atClaims`: Whole R b gives Whole R (atClaims b). **`k4C_whole_rest`**, **`k4C_whole_st`**:
    at blockAtC p.
  `seatSame_ok`, `whole_guarded`: the guard on a part of the state tests and hands on: Whole R b
    gives Whole R (b.guarded same but), at every test and every exception. `whole_guardMark`: so the
    guard on the mark. **`whole_seated`**: so the driver's seated form.
No new argument: heard_reads, runOfAtS, freeSlotAtS, wrote_reads.
**Limits.** ONE DIRECTION, FROM AN ACCEPT OR A RETURN. Rest says what stays (st, book, roots,
failed, check, out, req, and four readers of the open link); it says nothing of the link's ledger,
of what K4 has heard, or of the rows owed. That a chain's sub-protocol at K4's place is the seated
form of blockAtC p with another test on the plan is another file's law. Nothing on soundness.
K04_law, the law of the sub-protocol K4 itself, IS NOT PROVED.


-/
import Johnson.Desc.FoldKeeps
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.SeatGuard
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par Rest blockAtS blockAtC atClaims block seatOwn part? setPart runOf
  runOfAtS freeSlotAtS freeSlot wrote_reads heard_reads liftPart_after formsFront formsFrontNoRows
  formsBack claimOf)
open VerifiableInference.Desc (Block Claim Place named seatSame)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.First (S)

/-- Whole passes to every weaker relation. -/
theorem whole_mono {T Cl : Type} {R R' : T → T → Prop} {b : Block T Cl}
    (hm : ∀ s s', R s s' → R' s s') (W : Whole R b) : Whole R' b :=
  ⟨fun s rs gs s' h => hm _ _ (W.1 s rs gs s' h), fun c hc n s y h => hm _ _ (W.2.1 c hc n s y h),
    fun c hc s s' h => hm _ _ (W.2.2 c hc s s' h)⟩

/-- **K4's own term keeps Rest.** -/
theorem k4_whole_rest (p : Par) : Whole Rest (blockAtS p) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hR⟩ := heard_reads h
    exact hR
  · obtain ⟨cl, s'⟩ := y
    change c ∈ [_, _] at hc
    rcases List.mem_cons.1 hc with rfl | hc
    · have h' : ((named "the part is not there" (part? s)).bind fun q =>
          (runOf seatOwn "K4.claims-front"
            ((if p.k3Runs then formsFrontNoRows else formsFront) p.P p.g) q).map
            fun y => (y.1, setPart s y.2)) = .ok (cl, s') := h
      obtain ⟨_, _, _, _, _, _, _, hw⟩ := runOfAtS h'
      exact (wrote_reads hw).2.2.2.2
    · obtain rfl := List.mem_singleton.1 hc
      have h' : ((named "the part is not there" (part? s)).bind fun q =>
          (runOf seatOwn "K4.claims-back" formsBack q).map
            fun y => (y.1, setPart s y.2)) = .ok (cl, s') := h
      obtain ⟨_, _, _, _, _, _, _, hw⟩ := runOfAtS h'
      exact (wrote_reads hw).2.2.2.2
  · change c ∈ [_] at hc
    obtain rfl := List.mem_singleton.1 hc
    have e := liftPart_after part? setPart (block seatOwn p) "free-slot"
    have eb : (block seatOwn p).after.lookup "free-slot" = some (freeSlot seatOwn p.hp) := by
      simp [block]
    rw [eb] at e
    obtain ⟨_, hw⟩ := freeSlotAtS e h
    exact (wrote_reads hw).2.2.2.2

/-- **K4's own term keeps the statement.** -/
theorem k4_whole_st (p : Par) : Whole (fun s s' : S => s'.st = s.st) (blockAtS p) :=
  whole_mono (fun _ _ h => h.st) (k4_whole_rest p)

/-- At the one type of a claim. -/
theorem whole_atClaims {T : Type} {R : T → T → Prop} {b : Block T Aff} (W : Whole R b) :
    Whole R (atClaims b) := by
  refine ⟨W.1, fun c hc n s y h => ?_, W.2.2⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  have h' : ((x.2 n s).map fun y => (y.1.map claimOf, y.2)) = .ok y := h
  cases hz : x.2 n s with
  | error e =>
    rw [hz] at h'
    cases h'
  | ok z =>
    rw [hz] at h'
    obtain rfl : (z.1.map claimOf, z.2) = y := Except.ok.inj h'
    exact W.2.1 x hx n s z hz

theorem k4C_whole_rest (p : Par) : Whole Rest (blockAtC p) := whole_atClaims (k4_whole_rest p)

theorem k4C_whole_st (p : Par) : Whole (fun s s' : S => s'.st = s.st) (blockAtC p) :=
  whole_atClaims (k4_whole_st p)

/-- The guard hands on the state that it tests. -/
theorem seatSame_ok {T : Type} {same : T → T → Bool} {t s s' : T}
    (h : seatSame same t s = .ok s') : s' = s := by
  unfold seatSame at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

/-- **Behind the guard on a part of the state.** -/
theorem whole_guarded {T Cl : Type} {R : T → T → Prop} {b : Block T Cl} (same : T → T → Bool)
    (but : Place → Bool) (W : Whole R b) : Whole R (b.guarded same but) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · have h' : (if but b.place then b.decide s rs gs
        else (b.decide s rs gs).bind (seatSame same s)) = .ok s' := h
    split at h'
    · exact W.1 s rs gs s' h'
    · obtain ⟨z, hz, hs⟩ := VerifiableInference.Desc.Keeps.ebind_ok h'
      rw [seatSame_ok hs]
      exact W.1 s rs gs z hz
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    have h' : ((x.2 n s).bind fun y => (seatSame same s y.2).map fun _ => y) = .ok y := h
    obtain ⟨z, hz, hs⟩ := VerifiableInference.Desc.Keeps.ebind_ok h'
    cases hq : seatSame same s z.2 with
    | error e =>
      rw [hq] at hs
      cases hs
    | ok q =>
      rw [hq] at hs
      obtain rfl : z = y := Except.ok.inj hs
      exact W.2.1 x hx n s z hz
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    have h' : ((x.2 s).bind (seatSame same s)) = .ok s' := h
    obtain ⟨z, hz, hs⟩ := VerifiableInference.Desc.Keeps.ebind_ok h'
    rw [seatSame_ok hs]
    exact W.2.2 x hx s z hz

/-- Behind the guard on the mark. -/
theorem whole_guardMark {R : S → S → Prop} {b : Block S Claim} (W : Whole R b) :
    Whole R (ProofFile.guardMark b) := by
  refine ⟨fun s rs gs s' h => ?_, W.2.1, W.2.2⟩
  have h' : ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)) = .ok s' := h
  obtain ⟨z, hz, hs⟩ := VerifiableInference.Desc.Keeps.ebind_ok h'
  split at hs
  · obtain rfl : z = s' := Except.ok.inj hs
    exact W.1 s rs gs z hz
  · cases hs

/-- **Behind the driver's two guards, under another name and place.** -/
theorem whole_seated {R : S → S → Prop} {b : Block S Claim} (same : S → S → Bool)
    (but : Place → Bool) (nm : String) (a : Place) (W : Whole R b) :
    Whole R (Block.guarded same but { { ProofFile.guardMark b with name := nm } with place := a }) :=
  whole_guarded same but
    (show Whole R { { ProofFile.guardMark b with name := nm } with place := a } from whole_guardMark W)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.whole_mono
#print axioms OnBytes.Road.K4.k4_whole_rest
#print axioms OnBytes.Road.K4.k4_whole_st
#print axioms OnBytes.Road.K4.whole_atClaims
#print axioms OnBytes.Road.K4.k4C_whole_rest
#print axioms OnBytes.Road.K4.k4C_whole_st
#print axioms OnBytes.Road.K4.seatSame_ok
#print axioms OnBytes.Road.K4.whole_guarded
#print axioms OnBytes.Road.K4.whole_guardMark
#print axioms OnBytes.Road.K4.whole_seated
