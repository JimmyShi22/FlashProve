-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsNoMark.lean: AT EACH OF THE 25 PLACES OF THE CODE SWITCH IN THE PROOF FILE's
    DESCRIPTION THE DOOR's WAY OUT HANDS ON NO MARKED STATE. Two definitions, eleven theorems. A law
    file: no sub-protocol imports it.

Why. See Johnson/Top/H0/K2Ties/NoMarkSeat.lean: "no accept at a marked state" is owed at every
    place; the guard against the mark stands in the ways out (`noMark`,
    Johnson/P1K2R/SitsStep.lean).

What is said.
  `noMark_ok`: the guard accepts only a state without a mark. `guards_unmarked`,
      `leaveOpened_unmarked`: so do the two texts that close a way out.
  `EndsUnmarked leave`: whatever the way out hands on bears no mark. Five theorems: the five doors
      of `KeepsAt` and `KeepsJoined` (Johnson/P1K2R/SitsDoor.lean).
  `SitsLeftU b`: `SitsLeft`'s sentence (Johnson/P1K2R/SitsLeft.lean) with `EndsUnmarked` beside it,
      at one and the same door. `leftU_of_keepsAt`, `leftU_of_keepsJoined`: each arm gives it.
  `k02_leftU_file`: IN SCOPE, AT THE PROOF FILE's DESCRIPTION, WHERE ITS TEST ON THE PLAN ACCEPTS:
      at all 25 places.

Limits. The step to the piece is `unmarked_of_seat`; it is not called here. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.SitsLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 HeadPar codeSwitchKind headOpenQ finishFrontQ finishBehindQ)
open H2K.JointK (Sits)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open ProofFile (Cl)
open IM (Open)

theorem noMark_ok {t u : S} (h : noMark t = .ok u) : t.failed = none := by
  unfold noMark at h
  split at h
  · assumption
  · cases h

theorem guards_unmarked {s t u : S} (h : guards s t = .ok u) : u.failed = none := by
  have e := guards_same h
  unfold guards at h
  obtain ⟨m, h1, _⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  rw [e]
  exact noMark_ok h1

theorem leaveOpened_unmarked {f : LinkFrame} {s t s' : S} (h : leaveOpened f s t = .ok s') :
    s'.failed = none := by
  unfold leaveOpened at h
  obtain ⟨m, _, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u, _, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u₁, h3, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u₂, h4, h5⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  rw [seatSame_same h5, seatSame_same h4, noMark_same h3]
  exact noMark_ok h3

/-- Whatever the way out hands on bears no mark. -/
def EndsUnmarked (leave : S → S → Except String S) : Prop := ∀ s t s', leave s t = .ok s' →
    s'.failed = none

theorem ends_guards : EndsUnmarked fun s t => guards s t := fun _ _ _ h => guards_unmarked h

theorem ends_finish : EndsUnmarked fun s t => (finishBehindQ t).bind (guards s) := fun _ _ _ h => by
  obtain ⟨m, _, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  exact guards_unmarked h2

theorem ends_head (HP : HeadPar) : EndsUnmarked fun s t => (headOpenQ HP t).bind (guards s) := fun _
    _ _ h => by
  obtain ⟨m, _, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  exact guards_unmarked h2

theorem ends_opened (f : LinkFrame) : EndsUnmarked fun s t => leaveOpened f s t := fun _ _ _ h =>
    leaveOpened_unmarked h

theorem ends_head_opened (f : LinkFrame) (HP : HeadPar) : EndsUnmarked fun s t => (headOpenQ HP
    t).bind (leaveOpened f s) := fun _ _ _ h => by
  obtain ⟨m, _, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  exact leaveOpened_unmarked h2

/-- `SitsLeft`'s sentence with "the way out hands on no marked state", at one door. -/
def SitsLeftU (b : Block S Cl) : Prop :=
  ∃ (p : P2) (enter : S → Except String S) (leave : S → S → Except String S), Sits b (codeSwitchKind p : Block S
      Unit) enter leave ∧ LeftDoor enter leave ∧ EndsUnmarked leave

theorem leftU_of_keepsAt {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {b : Block S Cl}
    (h : KeepsAt Z G a nm b) : SitsLeftU b := by
  obtain ⟨P, n, _, _, h⟩ := h
  rcases h with ⟨_, hX, _⟩ | ⟨l, HP, _, _, hX, _⟩ | ⟨l, _, hX, _⟩
  · exact ⟨_, _, _, hX, leftDoor_finish, ends_finish⟩
  · exact ⟨_, _, _, hX, leftDoor_head HP, ends_head HP⟩
  · exact ⟨_, _, _, hX, leftDoor_guards, ends_guards⟩

theorem leftU_of_keepsJoined {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {b : Block S
                Cl} {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (hfs : framesOf Z.p.built.links Z.first
                Z.p.X = .ok fs) (hf : fs[l]? = some f) (hl : l ≠ 0) (h : KeepsJoined Z G a nm b f) : SitsLeftU b
    := by
  obtain ⟨P, n, _, _, h⟩ := h
  rcases h with ⟨l', HP, _, _, hX, _⟩ | ⟨l', _, hX, _⟩
  · exact ⟨_, _, _, hX, leftDoor_head_opened hfs hf hl HP, ends_head_opened f HP⟩
  · exact ⟨_, _, _, hX, leftDoor_opened hfs hf hl, ends_opened f⟩

/-- **At all 25 places of the proof file's description.** -/
theorem k02_leftU_file {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription
                         ProofFile.Inst} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (hF : ProofFile.onlineDescription
                               OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hp : F.planOk = true) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧ (∀ l, 1 ≤ l → l < 24 →
                    ∃ b : Block S Cl, c.blocksInOrder[14 * l + 0 + 2]? = some b ∧ SitsLeftU b) ∧ (∃ b : Block S Cl,
                             c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧ SitsLeftU b) ∧ ∃ b : Block S Cl, c.back[0]? = some b ∧
        SitsLeftU b := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits_file hS hR hF hp
  refine ⟨Z, Bs, base, c, A, B, O, fun l a1 a24 => ?_, ?_, ?_⟩
  · obtain ⟨b, nm, fs, f, hb, hfs, hf, hk⟩ := h1 l a1 a24
    exact ⟨b, hb, leftU_of_keepsJoined hfs hf (by omega) hk⟩
  · obtain ⟨b, nm, hb, hk⟩ := h2
    exact ⟨b, hb, leftU_of_keepsAt hk⟩
  · obtain ⟨b, nm, hb, hk⟩ := h3
    exact ⟨b, hb, leftU_of_keepsAt hk⟩

end P1K2

#print axioms P1K2.guards_unmarked
#print axioms P1K2.leaveOpened_unmarked
#print axioms P1K2.ends_finish
#print axioms P1K2.ends_head
#print axioms P1K2.ends_head_opened
#print axioms P1K2.leftU_of_keepsAt
#print axioms P1K2.leftU_of_keepsJoined
#print axioms P1K2.k02_leftU_file
