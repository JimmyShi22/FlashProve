-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngAtKeyD.lean: RngAnyCl.lean's LAWS ON THE RANGES' TEST, AT THE BLOCK THAT STANDS IN THE KEY FILE's DESCRIPTION: `Key.rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim` (Johnson/Desc/Key/Chain1.lean: firstChain). Statements and proofs.
OBJECT. The block named above. That it stands in the description's blocksInOrder list: Johnson/RunOne/Sound/KeyMapAtFK.lean: fk_rng_at.
USER. Meant for whoever pays, at the ranges' test's seat, that the row behind is on and that what rides beside is kept: keyD_out_inv, keyD_passes.
LETTERS. one and N are free. Premises: the block's yes; where named, its test on the plan.

The laws themselves are general in the state, in the seat's two halves and in the type of claims (Johnson/RunOne/Law/RngAnyCl.lean). Here the two halves are the description's own, unfolded.

What is said.
  `laidD_ok`, `backD_ok`: what the two halves say where they return.
  `laidD_rows`, `keyD_rows`: the rest of what the first half asks, for whoever closes the seam behind the lookups: all lookups are laid; the group's open rows are as many as the lookups' rows.
  `hin`, `hout`: the first half lays the state's statement; the second writes the record's.
  `keyD_yes`: WHERE THE BLOCK's decide RETURNS s' AT s: no count of rows waited; the ranges' group was there and no test of it had begun; the asking asksOnRecord (Johnson/Desc/Key/Ranges.lean) returned at the record made of s; the kind K12's block in the variant `proximityTestKind guardedProximityTestParts` (guardedProximityTestParts: Johnson/Desc/K12/JoinGuarded.lean) returned tE there; tE shows that the test has run to its end; and s' is s with tE's statement,
    book and count of roots, and no count waiting.
  `keyD_passes`: SO EVERY OTHER FIELD OF THE STATE IS WHAT IT WAS, THE KEY FILE's OWN SMALL RECORD (base: the claims on the parts' keys among it) WHOLE.
  `keyD_in_inv`, `keyD_out_inv`: the invariants of the two rows of the table of joints at this place hold: in front, at every state at which the block says yes; behind, at the state that the yes leaves (with the test on the plan).
  `keyD_grows`: the block keeps "the statement only grows", WRITTEN OUT (the frame's `Keeps.Decides (By Grows fun s => s.d.st)` unfolds to it; that frame's files are not imported here). UNDER THE BLOCK's TEST ON THE PLAN: the laws of the kind K12's files on what a yes leaves want two numbers of the place (early; answers = 1), which
    that test asks.
Limits. Those of the laws carried. A block that says no to all meets every statement. Nothing on soundness.

-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.RunOne.Law.RngAnyCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngAtKeyD
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)
open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngAnyCl
open VerifiableInference.Desc (Block Grows)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)

variable {one : OneTime} {N : H2U.PlaceNums}

theorem laidD_ok {s : FirstState} {l : RangesLaid} (h : enterRanges one s = .ok l) :
    s.noneWaits = true ∧ (∃ G, s.d.st.groups[s.grp]? = some G ∧ G.inRun = false) ∧
      l = ⟨s.d, s.grp, s.rider⟩ := by
  unfold enterRanges at h
  obtain ⟨_, h1, k1⟩ := RngBat.bind_ok h
  obtain ⟨_, _, k2⟩ := RngBat.bind_ok k1
  obtain ⟨_, h3, k3⟩ := RngBat.bind_ok k2
  refine ⟨needD_ok h1, ?_, (Except.ok.inj k3).symm⟩
  have h3' := needD_ok h3
  cases hG : s.d.st.groups[s.grp]? with
  | none =>
    rw [hG] at h3'
    cases h3'
  | some G =>
    rw [hG] at h3'
    have h4 : (!G.inRun && G.rows.size == s.base.rows.flatten.length) = true := h3'
    rw [Bool.and_eq_true] at h4
    exact ⟨G, rfl, by simpa using h4.1⟩

/-- The rest of what the first half asks: all lookups are laid; the group's open rows are as many as the lookups' rows. -/
theorem laidD_rows {s : FirstState} {l : RangesLaid} (h : enterRanges one s = .ok l) :
    s.base.keys.length = (VerifiableInference.Desc.Key.lookupsOf one).length ∧
      ∃ G, s.d.st.groups[s.grp]? = some G ∧ G.rows.size = s.base.rows.flatten.length := by
  unfold enterRanges at h
  obtain ⟨_, _, k1⟩ := RngBat.bind_ok h
  obtain ⟨_, h2, k2⟩ := RngBat.bind_ok k1
  obtain ⟨_, h3, _⟩ := RngBat.bind_ok k2
  refine ⟨by simpa using needD_ok h2, ?_⟩
  have h3' := needD_ok h3
  cases hG : s.d.st.groups[s.grp]? with
  | none =>
    rw [hG] at h3'
    cases h3'
  | some G =>
    rw [hG] at h3'
    have h4 : (!G.inRun && G.rows.size == s.base.rows.flatten.length) = true := h3'
    rw [Bool.and_eq_true] at h4
    exact ⟨G, rfl, by simpa using h4.2⟩

theorem backD_ok {s s' : FirstState} {t : T12} (h : leaveRanges s t = .ok s') :
    testEnded t = true ∧
      s' = { s with d := { s.d with st := t.st, book := t.book, roots := t.roots }, owed := none } := by
  unfold leaveRanges at h
  split at h
  · rename_i he
    exact ⟨he, (Except.ok.inj h).symm⟩
  · cases h

theorem hin : ∀ (s : FirstState) (l : RangesLaid), enterRanges one s = .ok l → l.d.st = s.d.st := fun s l h => by
  obtain ⟨_, _, rfl⟩ := laidD_ok h
  rfl

theorem hout : ∀ (s : FirstState) (t : T12) (s' : FirstState), leaveRanges s t = .ok s' → s'.d.st = t.st := fun s t s' h => by
  obtain ⟨_, rfl⟩ := backD_ok h
  rfl

/-- The record that the kind is handed at a state. -/
def recD (s : FirstState) : T12 := { st := s.d.st, book := s.d.book, roots := s.d.roots, g := s.grp, pass := .nothing, mask := s.rider }

section
variable {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

/-- **Where the block's decide returns.** -/
theorem keyD_yes (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    ∃ tE, s.noneWaits = true ∧ (∃ G, s.d.st.groups[s.grp]? = some G ∧ G.inRun = false) ∧
      asksOnRecord (rangesParams N) (recD s) = .ok () ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Claim).decide (recD s) rs gs = .ok tE ∧ testEnded tE = true ∧
      s' = { s with d := { s.d with st := tE.st, book := tE.book, roots := tE.roots }, owed := none } := by
  obtain ⟨t0, tE, h1, h2, h3, h4⟩ := decide_ok h
  unfold rangesRecord at h1
  obtain ⟨l, h5, h6⟩ := mapE_ok h1
  obtain ⟨a1, a2, rfl⟩ := laidD_ok h5
  subst h6
  obtain ⟨b1, b2⟩ := backD_ok h4
  exact ⟨tE, a1, a2, h2, h3, b1, b2⟩

/-- For the seam behind the lookups: at every state at which the block says yes all lookups are laid, and the group's open rows are as many as the lookups' rows. -/
theorem keyD_rows (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    s.base.keys.length = (VerifiableInference.Desc.Key.lookupsOf one).length ∧
      ∃ G, s.d.st.groups[s.grp]? = some G ∧ G.rows.size = s.base.rows.flatten.length := by
  obtain ⟨_, _, h1, _, _, _⟩ := decide_ok h
  unfold rangesRecord at h1
  obtain ⟨l, h5, _⟩ := mapE_ok h1
  exact laidD_rows h5

/-- **Every other field of the state is what it was.** -/
theorem keyD_passes (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    s'.base = s.base ∧ s'.pile = s.pile ∧ s'.lin = s.lin ∧ s'.sent = s.sent ∧ s'.idx = s.idx ∧
      s'.grp = s.grp ∧ s'.rider = s.rider ∧ s'.atEnd = s.atEnd ∧ s'.msgW = s.msgW ∧ s'.ids = s.ids ∧
      s'.owed = none ∧ s'.d.opened = s.d.opened := by
  obtain ⟨tE, _, _, _, _, _, rfl⟩ := keyD_yes h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The invariant of the row in front holds at every state at which the block says yes. -/
theorem keyD_in_inv (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    s.noneWaits = true ∧ ∃ G, s.d.st.groups[s.grp]? = some G ∧ G.inRun = false := by
  obtain ⟨_, a1, a2, _⟩ := keyD_yes h
  exact ⟨a1, a2⟩

/-- The invariant of the row behind holds at the state that a yes leaves. -/
theorem keyD_out_inv (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    s'.owed = none ∧ ∃ G, s'.d.st.groups[s'.grp]? = some G ∧ G.inRun = true ∧ G.rows = #[] := by
  obtain ⟨t0, tE, G, h1, h4, k⟩ := out_of_yes_cl hp h
  unfold rangesRecord at h1
  obtain ⟨l, h5, h6⟩ := mapE_ok h1
  obtain ⟨_, _, rfl⟩ := laidD_ok h5
  subst h6
  obtain ⟨_, rfl⟩ := backD_ok h4
  exact ⟨rfl, _, k.begunG, rfl, rfl⟩

end

/-- **The block keeps "the statement only grows"**: written out: a yes leaves a statement that has grown out of the one in front. -/
theorem keyD_grows (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true) :
    ∀ s rs gs s', (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s' →
      Grows s.d.st s'.d.st :=
  fun s rs gs s' h => seat_grows_cl (fun s : FirstState => s.d.st) hin hout hp s rs gs s' h

end Johnson.RunOne.Law.RngAtKeyD

#print axioms Johnson.RunOne.Law.RngAtKeyD.keyD_rows
#print axioms Johnson.RunOne.Law.RngAtKeyD.keyD_yes
#print axioms Johnson.RunOne.Law.RngAtKeyD.keyD_passes
#print axioms Johnson.RunOne.Law.RngAtKeyD.keyD_in_inv
#print axioms Johnson.RunOne.Law.RngAtKeyD.keyD_out_inv
#print axioms Johnson.RunOne.Law.RngAtKeyD.keyD_grows
