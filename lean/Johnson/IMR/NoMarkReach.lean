-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/NoMarkReach.lean: EVERY REACHED STATE IS WITHOUT A MARK, BUT AT 27 BORDERS: asked,
for a working list, not named here ("can a state reached at 356 or 357 bear a mark?"). In the goals'
scope, at an opening: whatever is reached at a border k of the flat list of the first chain of the
IOP as written in Lean, from whatever first states and at whatever first tree's number, bears no
mark, if 2 ≤ k and k is none of the 25 borders 14 l + nAt l + 4 (l < 25: behind a link's "behind the
batching").

  noMark_reach     THE TOP: of every reached state, a cheating prover's too: no run is spoken of.
  noMark_reach_below   the same at the narrower family (by reach_raw).
  noMark_late      so at every border from 350 to 358.

HOW. What is reached at k + 1 is behind an accepting step of entry k (Reach's own second clause); of
the ten forms of a flat entry eight end in "no mark at the state behind" (case_noMark,
Johnson/IMR/MemberPath.lean, off flat_cases, Johnson/IMR/FlatCases.lean); the two others are entry 0
and the 25
entries 14 l + nAt l + 3.
WHAT IS NOT SAID. Anything at the 27 borders 0, 1 and 14 l + nAt l + 4: at 0 and 1 a reached state
does bear a mark where ProofFile.startS falls to the blank state; at the 25 it is shown only of a state
from which a step goes on (noMark_path). That anything is reached. No soundness.
-/
import Johnson.IMR.MemberPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type}

/-- **In scope: every state that is reached at a border k of the first chain's flat list bears no
mark, if 2 ≤ k and k is not behind a link's "behind the batching".** -/
theorem noMark_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {start : Q → S} {k : ℕ}
    {a : Q × S} (h : Reach ft c.blocksInOrder start k a) (h2 : 2 ≤ k)
    (hb : ∀ l < 25, k ≠ 14 * l + nAt l + 4) : a.2.failed = none := by
  cases h with
  | zero z => exact absurd h2 (by omega)
  | @succ k' z s s' b R hbk hy =>
    obtain ⟨R', C', -, hy'⟩ := hy
    have d := ((Sound.step_ok_iff ft b _ _ R' C' C'.length).1 hy').2.2.2
    rcases case_noMark (flat_cases hS hR O k' b hbk) d with h | ⟨rfl, -⟩ | ⟨l, hl, rfl⟩
    · exact h
    · exact absurd h2 (by omega)
    · exact absurd rfl (hb l hl)

/-- The same at the narrower family. -/
theorem noMark_reach_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {start : Q → S} {k : ℕ}
    {a : Q × S} (h : Reach ft (c.blocksInOrder.map Sound.below) start k a) (h2 : 2 ≤ k)
    (hb : ∀ l < 25, k ≠ 14 * l + nAt l + 4) : a.2.failed = none :=
  noMark_reach hS hR O (reach_raw h) h2 hb

/-- So at every border from 350 on. -/
theorem noMark_late (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {start : Q → S} {k : ℕ}
    {a : Q × S} (h : Reach ft c.blocksInOrder start k a) (hk : 350 ≤ k) : a.2.failed = none :=
  noMark_reach hS hR O h (by omega) fun l hl => by unfold nAt; split <;> omega

end

#print axioms noMark_reach
#print axioms noMark_reach_below
#print axioms noMark_late

end IM
