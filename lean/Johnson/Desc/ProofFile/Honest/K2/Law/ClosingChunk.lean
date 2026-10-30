-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingChunk.lean: the kind "the code switch" (K2): the light
closing test at one place of the closed list, cut into stretches of segments, so that Lean's kernel
can be asked stretch by stretch, side by side, in little memory.

  chunkK, chunkPrev, chunkBase   what the walk at a place reads: the place's carried stretches; the kept shapes
                  in front of a segment, which are those of the switch in front of it; the number
                  of the segment's first message
  chunkOk         the test on one stretch: from chunkPrev a the segments a to a + b leave chunkPrev (a + b)
  ChunkReach, chunkReach_zero, chunkReach_step   the walk from the first segment, stretch by stretch
  closingAt_of_reach   where the walk reaches the place, closingAt says yes

Limits. A cut of the test of Honest/K2/Law/ClosingTest.lean: nothing new is stated of the closing.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- The carried stretches of the place number i. -/
def chunkK (i : Nat) : Nat → Except String Stretch :=
  match placesW[i]? with
  | some p => Stretch.carried p.carries (shapeZerosAll p.carries)
  | none => fun _ => .error "no such place"

/-- The kept shapes in front of the segment number a: the kept members of the switch that stands
behind segment a - 1. -/
def chunkPrev : Nat → Option (List OnBytes.OracleShape)
  | 0 => none
  | a + 1 => placesW[a]?.map (·.sizes.kept)

/-- The number of the first message of the segment number a. -/
def chunkBase (a : Nat) : Nat := ((segsW.take a).map (·.messages)).sum

/-- **The test on one stretch**: the segments a to a + b, at the place number i. -/
def chunkOk (i a b : Nat) : Bool :=
  match lightFrom freshTable (chunkK i) ((segsW.drop a).take b) (chunkBase a) (chunkPrev a) with
  | .ok x => decide (x = chunkPrev (a + b))
  | .error _ => false

/-- A chain of segments, one stretch behind the other. -/
theorem lightFrom_append (k : Nat → Except String Stretch) :
    ∀ (l₁ l₂ : List SegmentPub) (b : Nat) (x y : Option (List OnBytes.OracleShape)),
      lightFrom freshTable k l₁ b x = .ok y →
      lightFrom freshTable k (l₁ ++ l₂) b x =
        lightFrom freshTable k l₂ (b + (l₁.map (·.messages)).sum) y
  | [], l₂, b, x, y, h => by
    have e : x = y := Except.ok.inj h
    subst e
    simp
  | S :: rest, l₂, b, x, y, h => by
    show (segmentLight freshTable S x k b).bind _ = _
    have h' : (segmentLight freshTable S x k b).bind (fun W =>
        lightFrom freshTable k rest (b + S.messages) (some W)) = .ok y := h
    cases hs : segmentLight freshTable S x k b with
    | error e =>
      rw [hs] at h'
      cases h'
    | ok W =>
      rw [hs] at h'
      have t := lightFrom_append k rest l₂ (b + S.messages) (some W) y h'
      show lightFrom freshTable k (rest ++ l₂) (b + S.messages) (some W) = _
      rw [t, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **The walk from the first segment has reached the segment number a.** -/
def ChunkReach (i a : Nat) : Prop :=
  lightFrom freshTable (chunkK i) (segsW.take a) 0 none = .ok (chunkPrev a)

theorem chunkReach_zero (i : Nat) : ChunkReach i 0 := rfl

/-- One stretch more. -/
theorem chunkReach_step {i a : Nat} (h : ChunkReach i a) (b : Nat) (t : chunkOk i a b = true) :
    ChunkReach i (a + b) := by
  unfold ChunkReach at h ⊢
  rw [List.take_add, lightFrom_append _ _ _ _ _ _ h]
  unfold chunkOk at t
  have e : 0 + ((segsW.take a).map (·.messages)).sum = chunkBase a := Nat.zero_add _
  rw [e]
  cases hl : lightFrom freshTable (chunkK i) ((segsW.drop a).take b) (chunkBase a) (chunkPrev a) with
  | error e =>
    rw [hl] at t
    cases t
  | ok x =>
    rw [hl] at t
    exact congrArg Except.ok (of_decide_eq_true t)

/-- **Where the walk reaches the place's link, closingAt says yes.** -/
theorem closingAt_of_reach {i : Nat} {p : SwitchPlace} (hp : placesW[i]? = some p)
    (hl : p.link = i + 1) (h : ChunkReach i (i + 1)) : closingAt i = true := by
  have hi : i < placesW.length := (List.getElem?_eq_some_iff.1 hp).1
  have ep : placesW[i] = p := (List.getElem?_eq_some_iff.1 hp).2
  unfold closingAt
  rw [List.drop_eq_getElem_cons hi, ep]
  simp only [List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil, Bool.and_true]
  unfold ChunkReach at h
  have ek : chunkK i = Stretch.carried p.carries (shapeZerosAll p.carries) := by
    unfold chunkK
    rw [hp]
  have ev : chunkPrev (i + 1) = some p.sizes.kept := by
    show placesW[i]?.map (·.sizes.kept) = _
    rw [hp]
    rfl
  rw [ek, ev] at h
  unfold closingOkLight closingLightFor
  rw [hl, h]
  simp [Except.bind, Except.toOption]

/-- The same, with the place named by its link alone. -/
theorem closingAt_of_links {i : Nat} (hl : (placesW[i]?.map (·.link)) = some (i + 1))
    (h : ChunkReach i (i + 1)) : closingAt i = true := by
  cases hp : placesW[i]? with
  | none =>
    rw [hp] at hl
    cases hl
  | some p =>
    rw [hp] at hl
    exact closingAt_of_reach hp (Option.some.inj hl) h

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingAt_of_links
#print axioms ProofFile.Honest.K2.Law.lightFrom_append
#print axioms ProofFile.Honest.K2.Law.chunkReach_step
#print axioms ProofFile.Honest.K2.Law.closingAt_of_reach
