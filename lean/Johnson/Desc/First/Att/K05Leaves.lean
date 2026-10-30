-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Leaves.lean: kind K5: WHAT THE KIND's SUB-PROTOCOL LEAVES OF THE VERIFIER's STATE: one law, general in the relation, of the block k5AtN (Johnson/Desc/First/Att/SeatN.lean) and of every block of the kind's lot
(Johnson/Desc/ProofFile/Lot/K5.lean): its decision, each of its four runs of claims and each run behind the batching (there is none) keep every relation R that is reflexive, that the seat's lay keeps and that a write of the ledger keeps.
By the walk over the kind's text that is general in R (Johnson/Goal/Meaning/RecK5K8.lean: k5_whole · runsK_keep · joinRun_keep), called.

Main names:
  withJoin_whole: the three runs with "join" laid behind "keys" keep R. k5AtN_whole: **the block.** lotN_whole: every block of the lot.
  k5AtN_st | lotN_st: AN INSTANCE: the statement, the book of trees and the roots are as they were (t.st = s.st ∧ t.book = s.book ∧ t.roots = s.roots).
  k5AtN_leaves_tl | lotN_leaves_tl: the decision leaves the smallness test's part (S.tl?): by k5_leaves_tl (Att/K05LeavesTl.lean).
LIMITS. All six speak of the LOT's block (k5AtN's | lotN's). The chain's entry is that block SEATED: its decision and each run stand behind the seat's guard, which only refuses more: that Whole R and Leaves go over to the seated entry is not in this file.
  Leaves speaks of the decision alone; Whole of the decision, the runs of claims and the runs behind the batching.
IS IT EMPTY HERE? Where a decision or a run refuses nothing is said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Goal.Meaning.RecK5K8
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Att.K05LeavesTl
import Johnson.Desc.ProofFile.Lot.K5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Meaning.K2 (k5_whole runsK_keep joinRun_keep whole_same)

section
variable (R : First.S → First.S → Prop) (hr : ∀ s, R s s) (hmark : ∀ (s : First.S) (G : Fork), R s (s.putFork G))
include hr hmark

/-- The three runs with "join" laid behind "keys" keep R. -/
theorem withJoin_whole (A : Attention.Plan) : ∀ x ∈ runsO A, ∀ n, FnCl R (x.2 n) := by
  intro x hx n
  unfold runsO at hx
  obtain ⟨r, hr', hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep R hr _ _ _ hr' n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep R _ (fun s G => hmark s G) _ n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep R hr _ _ _ hr' n
    · cases hx

variable (hlay : ∀ s h G s', seatSO.lay s h G = some s' → R s s')
include hlay

/-- **THE KIND's BLOCK KEEPS R: its decision, each run of claims, each run behind the batching.** -/
theorem k5AtN_whole {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b' : Block First.S Claim}
    (hb : k5AtN W l g before = some b') : Whole R b' := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  refine whole_same (k5_whole R _ hlay (runsN p) (fun c hc n s y e => ?_) _) rfl (fun _ hx => hx) rfl
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := runN_ok e
  exact withJoin_whole R hr hmark p r hr' n s _ e'

/-- Every block of the kind's lot. -/
theorem lotN_whole {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block First.S ProofFile.Cl} (h : b₁ ∈ (H2K5.lotN Z).blocks G) : Whole R b₁ := by
  have h' : b₁ ∈ H2K5.k5OwnN Z G := by simpa [ProofFile.Lot.blocks, H2K5.lotN, ProofFile.asCl] using h
  unfold H2K5.k5OwnN at h'
  obtain ⟨x, _, e⟩ := List.mem_filterMap.1 h'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e
  exact whole_same (k5AtN_whole R hr hmark hlay hb) rfl (fun _ hx => hx) rfl

end

/-- The statement, the book of trees and the roots. -/
def SameSt (s t : First.S) : Prop := t.st = s.st ∧ t.book = s.book ∧ t.roots = s.roots

theorem sameSt_refl (s : First.S) : SameSt s s := ⟨rfl, rfl, rfl⟩

theorem sameSt_putFork (s : First.S) (G : Fork) : SameSt s (s.putFork G) := by
  unfold First.S.putFork
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, SameSt]
  | _ => exact ⟨rfl, rfl, rfl⟩

theorem sameSt_lay (s : First.S) (h : Heard) (G : Fork) (s' : First.S) (hl : seatSO.lay s h G = some s') : SameSt s s' := by
  obtain ⟨a, _, rfl⟩ := seatSO_lay hl
  exact ⟨rfl, rfl, rfl⟩

/-- **The kind's sub-protocol leaves the statement, the book and the roots.** -/
theorem k5AtN_st {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b' : Block First.S Claim}
    (hb : k5AtN W l g before = some b') : Whole SameSt b' :=
  k5AtN_whole SameSt sameSt_refl sameSt_putFork sameSt_lay hb

theorem lotN_st {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block First.S ProofFile.Cl} (h : b₁ ∈ (H2K5.lotN Z).blocks G) : Whole SameSt b₁ :=
  lotN_whole SameSt sameSt_refl sameSt_putFork sameSt_lay h

/-- **The decision leaves the smallness test's part.** -/
theorem k5AtN_leaves_tl {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b' : Block First.S Claim}
    (hb : k5AtN W l g before = some b') : b'.Leaves First.S.tl? := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun s rs gs s' h => k5_leaves_tl (runsN p) _ s rs gs s' h

theorem lotN_leaves_tl {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block First.S ProofFile.Cl} (h : b₁ ∈ (H2K5.lotN Z).blocks G) :
    b₁.Leaves First.S.tl? := by
  have h' : b₁ ∈ H2K5.k5OwnN Z G := by simpa [ProofFile.Lot.blocks, H2K5.lotN, ProofFile.asCl] using h
  unfold H2K5.k5OwnN at h'
  obtain ⟨x, _, e⟩ := List.mem_filterMap.1 h'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e
  exact fun s rs gs s' hd => k5AtN_leaves_tl hb s rs gs s' hd

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_whole
#print axioms VerifiableInference.Desc.First.Att.P.lotN_whole
#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_st
#print axioms VerifiableInference.Desc.First.Att.P.lotN_st
#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_leaves_tl
#print axioms VerifiableInference.Desc.First.Att.P.lotN_leaves_tl
