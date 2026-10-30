-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/HeldYes.lean: **WHAT A YES OF THE FILE's OWN PIECE SAYS FOR SURE OF THE BLOCK
THAT IT HOLDS.** Statements and proofs. No probability is spent: each is a fact on one transcript at
which the piece puts out.
  `step_of_held`: a yes of the step of `held B` (a description's block as a piece holds it) is a yes
    of B's own step at the second component, at the same rounds, columns and count; the first
    component is handed on.
  `held_under_yes`: p.b = held B, B is `UnderR` a block b' (Johnson/Desc/Sound/SeatGuardChain.lean:
    B has the rounds of b', and where B says yes b' says the same yes), b' sits on K behind (enter,
    leave): where the piece puts out b at a, `StepYes F.ft K enter leave a.1.2 b.1.2`
    (SitsYes.lean): THE DOORS ARE THOSE OF b': whatever guards B stands behind, and whatever is
    joined behind them, is not spoken of. (Where B itself sits on K: `stepYes_of_held_sits`,
    in a file of the kind's, Johnson/Loose/H2K12/HandsOnAtFirstSeat.lean.)

  `grownAt_piece`: so `k12_grownAt` (K12Grows.lean) at the file's own piece: from the piece's yes,
    at the lot's own doors.
Limits. That a description's seated block is `UnderR` its lot's block is not shown here. Nothing on
soundness.

-/
import Johnson.Desc.K12.Coin.K12Grows
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.Sound.FoldLiftProof
import Johnson.Desc.Sound.FoldBelowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers Item ModelPart shapeAt rowsHeld membersHeld bookAt rowSegs
  standAt)
open H2K.JointK

/-- A held block's step is the block's own. -/
theorem step_of_held {P S Cl : Type} (B : Block S Cl) (ft : ℕ) (a b : P × S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : ℕ) (h : (held (P := P) B).step ft a rs cols = .ok (b, k)) :
    B.step ft a.2 rs cols = .ok (b.2, k) ∧ b.1 = a.1 := by
  have h1 : ((below B).step ft a.2 rs cols).map (fun x => ((a.1, x.1), x.2)) = .ok (b, k) := by
    rw [← step_lift Prod.snd (fun (t : P × S) s => (t.1, s)) ft (below B) a rs cols]
    exact h
  cases hb : (below B).step ft a.2 rs cols with
  | error e => rw [hb] at h1; cases h1
  | ok x =>
    rw [hb] at h1
    have e : ((a.1, x.1), x.2) = (b, k) := Except.ok.inj h1
    have eb : (a.1, x.1) = b := congrArg Prod.fst e
    have ek : x.2 = k := congrArg Prod.snd e
    have hx : x = (b.2, k) := by
      rw [← eb, ← ek]
    have h2 := step_below ft B a.2 rs cols
    rw [hb] at h2
    split at h2
    · cases hB : B.step ft a.2 rs cols with
      | error e' => rw [hB] at h2; cases h2
      | ok y =>
        rw [hB] at h2
        have : x = y := Option.some.inj h2
        exact ⟨by rw [← this, hx], by rw [← eb]⟩
    · cases h2

section
variable {P S T Cl Cl' W : Type} {C : PQ.CK} {F : Frame}

/-- **For sure, at the file's own piece, at the doors of a block that B stands under.** -/
theorem held_under_yes (K : Block T Cl) (enter : S → Except String T)
    (leave : S → T → Except String S) (B b' : Block S Cl') (hU : B.UnderR b')
    (hS : Sits b' K enter leave) (p : Piece C F (P × S) Cl' W) (hb : p.b = held (P := P) B)
    (h0 : p.back = []) (a : (P × S) × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : (P × S) × F.E.Str) (h : p.ior.red.out a τ = some b) :
    StepYes F.ft K enter leave a.1.2 b.1.2 ∧ b.1.1 = a.1.1 := by
  obtain ⟨_, k, hst, _⟩ := yes_step p h0 a τ b h
  rw [hb] at hst
  obtain ⟨h1, h2⟩ := step_of_held B F.ft a.1 b.1 _ _ k hst
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step F.ft _ _ _ _ k (step_under hU h1)
  exact ⟨⟨t, t', _, _, k, e1, e2, e3⟩, h2⟩

end

/-- **`k12_grownAt` at the file's own piece**, from the piece's yes, at the doors of a block that
the held block stands under. -/
theorem grownAt_piece {P Cl W : Type} {C : PQ.CK} {F : Frame} (links : List ModelPart) (N : Numbers)
    (q q' : Place) (O' : List Item) (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true)
    (ho : π.nums.ownMask = false) (he : π.early = true) (ha : π.answers = 1)
    (hq' : standAt links q' = .fin) (hO' : rowSegs O' = []) (B b' : Block First.S Cl)
    (hU : B.UnderR b') (leave : First.S → T12 → Except String First.S)
    (hS : Sits b' (proximityTestKind guardedProximityTestParts π : Blk') enterFinish leave) (hl : LaysOnly leave) (L : Door.Laid)
    (p : Piece C F (P × First.S) Cl W) (hb : p.b = held (P := P) B) (h0 : p.back = [])
    (a : (P × First.S) × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (b : (P × First.S) × F.E.Str)
    (hG : GoOn N q q' π (Door.toTree L) a.1.2) (h : p.ior.red.out a τ = some b) :
    ((a.1.2.failed = none ∧ b.1.2.failed = none) ∧
    shapeAt links (some q') b.1.2 = true ∧ rowsHeld N O' b.1.2 = true ∧
    membersHeld N O' b.1.2 = true ∧
    (bookAt N (some q) a.1.2 = true → bookAt N (some q') b.1.2 = true) ∧
    (Door.atFirstBook π.nums.firstTree a.1.2 = true →
      Door.atFirstBook π.nums.firstTree b.1.2 = true) ∧
    (Door.atFirstSeats L a.1.2 = true → Door.atFirstSeats L b.1.2 = true)) ∧ b.1.1 = a.1.1 := by
  obtain ⟨_, k, hst, _⟩ := yes_step p h0 a τ b h
  rw [hb] at hst
  obtain ⟨h1, h2⟩ := step_of_held B F.ft a.1 b.1 _ _ k hst
  exact ⟨k12_grownAt links N q q' O' π hp ho he ha hq' hO' b' leave hS hl L F.ft _ _ _ _ k hG
    (step_under hU h1), h2⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.step_of_held
#print axioms VerifiableInference.Desc.K12.Coin.held_under_yes
#print axioms VerifiableInference.Desc.K12.Coin.grownAt_piece
