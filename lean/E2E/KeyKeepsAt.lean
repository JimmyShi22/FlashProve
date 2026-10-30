-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyKeepsAt.lean: THE JOIN: the payers of E2E/KeyKeeps.lean and E2E/KeyKeepsLayer.lean, which
stand at free letters, AT THE KEY FILE's OWN THREE THREADS, WITH ANY HALVES AND ANY TABLES LAID
(`laid₁`, `laid₃`, E2E/KeyRest.lean), AND ANY THREAD OVER THE SHARED CHAIN: each statement ends in
the thread's own letter
`keeps`, at the thread's own list of sub-protocols, from the sub-protocol's accepting step; and from
a thread's own step (`Thread.Stepped`). On the verifier's step alone. NOTHING IS SHOWN OF ANY
PROVER.

WHY IT IS SHORT: the description's first chain IS the library's `firstChain` at the public values
`one₀` (Johnson/Desc/Key/Desc.lean), and these are the values at which the thread's clause is laid:
both by unfolding.

  `stepYes_of_step`: GENERAL: a yes of a sub-protocol's own step at columns all of which it reads is
      the library's `StepYes`
  **`keeps_filled₁`**: at the twelve sub-protocols of no kind of the first chain
  **`same_ends₂`**: the shared chain's front and end (numbers 0 and 11) leave the state as it was
  **`keeps_filled₂`**: so the letter `keeps` holds there, at any thread over that chain whose letter
      holds of a state and itself
  **`keeps_filled₃`**: at the last chain's test on the taken trees' sources and its end (numbers 1
      and 3)
  `keeps_stepped₁`: the first of these from `Thread.Stepped`: the third clause of `Behind`
      (Johnson/Desc/ProofFile/Honest/Thread/Pays.lean)

Limits.
- THREE PUBLIC PREMISES, none shown here: the plan has just two lookups · the shape has a message
  with W (for the first chain's seal) · the shared chain has twelve sub-protocols (for its end's
  number).
- Equations alone: see E2E/KeyRides.lean for what rides past.
- For all halves and tables: these statements read neither.
- Three names still say "filled": the statements stand at `laid₁`, `laid₃`, and any shared thread.

-/
import E2E.KeyRest
import E2E.KeyKeeps
import E2E.KeyKeepsLayer
import Johnson.Desc.Plain.PieceFits
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Key (FirstState Claim Lookup lookupsOf Xi)
open Johnson.Desc.First.Walk.Tied (StepYes)
open ProofFile.Honest

/-- A yes of the step is the library's `StepYes`. -/
theorem stepYes_of_step {S Cl : Type} {ft : Nat} {b : Block S Cl} {s s' : S} {R : List Fmt.RoundView}
    {c : List OpenedColumn} (h : b.step ft s R c = .ok (s', c.length)) : StepYes ft b s s' :=
  ⟨R, c, VerifiableInference.Desc.Plain.roundsFit_length _ _
    (VerifiableInference.Desc.Block.step_ok.1 h).1, h⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : VerifiableInference.Desc.Key.Source)
  (N : H2U.PlaceNums) (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}

/-- "The shape has a message with W", at the description's own values. -/
def HasW (bw : Block FirstState Claim) : Prop :=
  VerifiableInference.Desc.Key.sendW (one₀ Xs) VerifiableInference.Desc.Key.pieces
    (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1
      (VerifiableInference.Desc.Key.batchRound Xs.Y.D.1))
    (VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1
      (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1
        (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))
      (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1
        (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))) = some bw

/-- **The first chain's twelve.** -/
theorem keeps_filled₁ {x₀ x₁ : Lookup} (hl : lookupsOf (one₀ Xs) = [x₀, x₁])
    {bw : Block FirstState Claim} (hw : HasW Xs bw) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18], ∀ blk,
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk → ∀ s s',
      StepYes (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).ft blk s s' →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).keeps b s s' := by
  intro b hb blk hblk s s' hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact keeps_paid₁ (one₀ Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N x₀ x₁ L.kind₁ hl bw hw _ _
        (by decide) blk hblk s s' hy
    | exact keeps_layers (one₀ Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N x₀ x₁ hl _ L.kind₁ _ (by decide)
        blk hblk s s' hy

/-- **The shared chain's front and end leave the state as it was.** -/
theorem same_ends₂ (hlen : (D Xs N Pl).shared.blocksInOrder.length = 12) (ft : Nat) :
    ∀ b ∈ [0, 11], ∀ blk, (D Xs N Pl).shared.blocksInOrder[b]? = some blk → ∀ s s',
      StepYes ft blk s s' → s' = s := by
  intro b hb blk hblk s s' hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact (keeps_paid₂ Xs N Pl _).1 blk hblk s s' hy
  · refine (keeps_paid₂ Xs N Pl _).2 blk ?_ s s' hy
    have e : (D Xs N Pl).shared.blocksInOrder.length - 1 = 11 := by rw [hlen]
    show (D Xs N Pl).shared.blocksInOrder[(D Xs N Pl).shared.blocksInOrder.length - 1]? = some blk
    rw [e]
    exact hblk

/-- **The shared chain's front and end**, at any thread over that chain whose letter holds of a
state and itself. -/
theorem keeps_filled₂ {V W Xh Pb : Type}
    {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hlen : (D Xs N Pl).shared.blocksInOrder.length = 12) (hbs : T.bs = (D Xs N Pl).shared.blocksInOrder)
    (hK : ∀ b ∈ [0, 11], ∀ s, T.keeps b s s) :
    ∀ b ∈ [0, 11], ∀ blk, T.bs[b]? = some blk → ∀ s s', StepYes T.ft blk s s' →
      T.keeps b s s' := by
  intro b hb blk hblk s s' hy
  rw [hbs] at hblk
  rw [same_ends₂ Xs N Pl hlen _ b hb blk hblk s s' hy]
  exact hK b hb s

/-- **The last chain's test on the taken trees' sources, and its end.** -/
theorem keeps_filled₃ :
    ∀ b ∈ [1, 3], ∀ blk, (laid₃ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk → ∀ s s',
      StepYes (laid₃ Xs N Pl L w₀ rc x hs₁ tb₁).ft blk s s' →
      (laid₃ Xs N Pl L w₀ rc x hs₁ tb₁).keeps b s s' := by
  intro b hb blk hblk s s' hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact (keeps_paid₃ Xs N Pl _).1 blk hblk s s' hy
  · exact (keeps_paid₃ Xs N Pl _).2 blk hblk s s' hy

/-- The first from a thread's own step. -/
theorem keeps_stepped₁ {x₀ x₁ : Lookup} (hl : lookupsOf (one₀ Xs) = [x₀, x₁])
    {bw : Block FirstState Claim} (hw : HasW Xs bw) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18], ∀ blk,
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk → ∀ k s m E ds y cols s',
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s' →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).keeps b s s' :=
  fun b hb blk hblk _ s _ _ _ _ _ s' h =>
    keeps_filled₁ Xs N Pl L w₀ rc x hl hw b hb blk hblk s s' (stepYes_of_step h.2)

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.stepYes_of_step
#print axioms AtPublicFiles.KeyThread.keeps_filled₁
#print axioms AtPublicFiles.KeyThread.keeps_filled₂
#print axioms AtPublicFiles.KeyThread.keeps_filled₃
#print axioms AtPublicFiles.KeyThread.keeps_stepped₁
