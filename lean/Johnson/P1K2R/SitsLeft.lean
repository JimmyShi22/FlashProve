-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsLeft.lean: AT EACH OF THE 25 PLACES OF THE CODE SWITCH IN THE PROOF FILE's
DESCRIPTION THE
DOOR BEHIND WHICH THE SUB-PROTOCOL SITS ON THE KIND's LEAVES WHAT THE OPEN CLAIMS READ. Two
definitions,
nine theorems. A law file: no sub-protocol imports it.

Why. The code switch's fifth tie (Johnson/Top/H0/K2Ties/T5.lean) owes: an accept of the seated
sub-protocol gives `Left` (Johnson/Top/H0/K2Ties/Left.lean). `left_of_seat` (Doors.lean) pays it
from the
clause at the step and `Left` at the way in and at the way out. Which doors stand in the description
is said by Johnson/P1K2R/SitsDoor.lean (`KeepsAt`, `KeepsJoined`, `k02_sits_file`).

What is said.
  `LeftDoor enter leave`: the way in and the way out each give `Left`. `left_id`: the way in that
  hands
    the state on as it is.
  `leftDoor_finish`, `leftDoor_head`, `leftDoor_guards`, `leftDoor_opened`, `leftDoor_head_opened`:
  the
    five doors of these two definitions' arms.
  `SitsLeft b`: there are numbers p of a place and a door with `Sits b (codeSwitchKind p) enter leave` and
    `LeftDoor enter leave`. `left_of_keepsAt`, `left_of_keepsJoined`: each arm gives it.
  `k02_left_file`: IN SCOPE, AT THE PROOF FILE's DESCRIPTION, WHERE ITS TEST ON THE PLAN ACCEPTS: at
  the
    23 segments' first places, at the output head's and behind the last segment.

Limits. The step from `Sits` and `LeftDoor` to the field left of `K2Owes` at the chain's own piece
is
`left_of_seat`; it is not called here. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.SitsDoor
import Johnson.Top.H0.K2Ties.DoorsFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 HeadPar codeSwitchKind headOpenQ finishFrontQ finishBehindQ)
open VerifiableInference.Desc.First.K2Ties (Left left_finishFront left_finishBehind left_headOpen
  left_frameOpened left_bind)
open H2K.JointK (Sits)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open ProofFile (Cl)
open IM (Open)

/-- The way in and the way out each leave what the open claims read. -/
def LeftDoor (enter : S → Except String S) (leave : S → S → Except String S) : Prop :=
  (∀ s t, enter s = .ok t → Left s t) ∧ ∀ s t s', leave s t = .ok s' → Left t s'

theorem left_id {s t : S} (h : (Except.ok s : Except String S) = .ok t) : Left s t := by
  cases h
  exact Left.refl _

theorem leftDoor_finish : LeftDoor finishFrontQ fun s t => (finishBehindQ t).bind (guards s) :=
  ⟨fun _ _ h => left_finishFront h, fun _ _ _ h =>
    left_bind (fun _ _ e => guards_same e) (fun _ e => left_finishBehind e) h⟩

theorem leftDoor_head (HP : HeadPar) :
    LeftDoor (fun s => .ok s) fun s t => (headOpenQ HP t).bind (guards s) :=
  ⟨fun _ _ h => left_id h, fun _ _ _ h =>
    left_bind (fun _ _ e => guards_same e) (fun _ e => left_headOpen e) h⟩

theorem leftDoor_guards : LeftDoor (fun s => .ok s) fun s t => guards s t :=
  ⟨fun _ _ h => left_id h, fun _ _ _ h => by
    rw [guards_same h]
    exact Left.refl _⟩

section
variable {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
  {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}

theorem leftDoor_opened (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f)
    (hl : l ≠ 0) : LeftDoor (fun s => .ok s) fun s t => leaveOpened f s t :=
  ⟨fun _ _ e => left_id e, fun _ _ _ e => left_frameOpened h hf hl (leaveOpened_is e)⟩

theorem leftDoor_head_opened (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f)
    (hl : l ≠ 0) (HP : HeadPar) :
    LeftDoor (fun s => .ok s) fun s t => (headOpenQ HP t).bind (leaveOpened f s) :=
  ⟨fun _ _ e => left_id e, fun _ _ _ e => by
    obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    exact (left_headOpen h1).trans (left_frameOpened h hf hl (leaveOpened_is h2))⟩

end

/-- What each arm gives. -/
def SitsLeft (b : Block S Cl) : Prop :=
  ∃ (p : P2) (enter : S → Except String S) (leave : S → S → Except String S),
    Sits b (codeSwitchKind p : Block S Unit) enter leave ∧ LeftDoor enter leave

theorem left_of_keepsAt {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {b : Block S Cl}
    (h : KeepsAt Z G a nm b) : SitsLeft b := by
  obtain ⟨P, n, _, _, h⟩ := h
  rcases h with ⟨_, hX, _⟩ | ⟨l, HP, _, _, hX, _⟩ | ⟨l, _, hX, _⟩
  · exact ⟨_, _, _, hX, leftDoor_finish⟩
  · exact ⟨_, _, _, hX, leftDoor_head HP⟩
  · exact ⟨_, _, _, hX, leftDoor_guards⟩

theorem left_of_keepsJoined {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String}
    {b : Block S Cl} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (hfs : framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (hf : fs[l]? = some f) (hl : l ≠ 0)
    (h : KeepsJoined Z G a nm b f) : SitsLeft b := by
  obtain ⟨P, n, _, _, h⟩ := h
  rcases h with ⟨l', HP, _, _, hX, _⟩ | ⟨l', _, hX, _⟩
  · exact ⟨_, _, _, hX, leftDoor_head_opened hfs hf hl HP⟩
  · exact ⟨_, _, _, hX, leftDoor_opened hfs hf hl⟩

/-- **At all 25 places of the proof file's description.** -/
theorem k02_left_file {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hp : F.planOk = true) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (∀ l, 1 ≤ l → l < 24 → ∃ b : Block S Cl, c.blocksInOrder[14 * l + 0 + 2]? = some b ∧ SitsLeft b) ∧
      (∃ b : Block S Cl, c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧ SitsLeft b) ∧
      ∃ b : Block S Cl, c.back[0]? = some b ∧ SitsLeft b := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits_file hS hR hF hp
  refine ⟨Z, Bs, base, c, A, B, O, fun l a1 a24 => ?_, ?_, ?_⟩
  · obtain ⟨b, nm, fs, f, hb, hfs, hf, hk⟩ := h1 l a1 a24
    exact ⟨b, hb, left_of_keepsJoined hfs hf (by omega) hk⟩
  · obtain ⟨b, nm, hb, hk⟩ := h2
    exact ⟨b, hb, left_of_keepsAt hk⟩
  · obtain ⟨b, nm, hb, hk⟩ := h3
    exact ⟨b, hb, left_of_keepsAt hk⟩

end P1K2

#print axioms P1K2.leftDoor_finish
#print axioms P1K2.leftDoor_head
#print axioms P1K2.leftDoor_guards
#print axioms P1K2.leftDoor_opened
#print axioms P1K2.leftDoor_head_opened
#print axioms P1K2.left_of_keepsAt
#print axioms P1K2.left_of_keepsJoined
#print axioms P1K2.k02_left_file
