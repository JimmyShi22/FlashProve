-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/HeldAtStand.lean: THE SMALLNESS TEST: IN THE FORM IN WHICH THE BATCHING's
HOUSE TAKES IT (its premise held; the text of its StandJ is written out): at any thread T over the first
chain's list that counts its columns from 0 and begins at the description's own first state, wherever T
stands, with Said, in front of a batching (border 14 l + 8 + 1, or 337 + 10 at the head's) and J holds there,
whatever record and list the state shows, the list is held. Said and J are letters; neither is read.

  held_at_stand, held_at_stand_head  one call of thr_reach_of (Honest/Thread/ReachBack.lean) and one of
                                     held_at_batching, held_at_batching_head (Honest/K8/HeldAtBatch.lean)
  held_at_stand_letters, held_at_stand_head_letters  the same at the library's own thread of the first
                                     chain, lettersHead, whose three premises hold by its text (as
                                     seat_at_head, Honest/K9/BatchValuesSeat.lean, has them)

Limits. That T stands anywhere is not shown: where it stands nowhere the statement is idle. Under the head
P5J.AtMgA, at the full size and the format's second hash function alone. Nothing is claimed on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.HeldAtBatch
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.AtFull.Shape.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The premise held of the field "batch", at every batching below the head's.** -/
theorem held_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hstart : ∀ k w hd, ∃ z, ∀ s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp z)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) :
    ∀ l, l < 24 → ∀ s, (∃ k m E, ThrS T Said (14 * l + 8 + 1) k s m E ∧ J (14 * l + 8 + 1) s) →
      ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true := by
  rintro l hl s ⟨k, m, E, hT, -⟩
  obtain ⟨z, h0⟩ := hstart k m.st.input (m.st.heard.take T.front)
  have hb : 14 * l + 8 + 1 ≤ T.bs.length := by
    rw [hbs, Johnson.AtFull.Shape.flat_len h]
    omega
  have hR := thr_reach_of T (ProofFile.startS Zp) z hb h0 hT.1
  rw [hbs, hft] at hR
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact held_at_batching h.scope h.reads O hl hR

/-- **The like at the head's batching.** -/
theorem held_at_stand_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hstart : ∀ k w hd, ∃ z, ∀ s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp z)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) :
    ∀ s, (∃ k m E, ThrS T Said (337 + 10) k s m E ∧ J (337 + 10) s) →
      ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true := by
  rintro s ⟨k, m, E, hT, -⟩
  obtain ⟨z, h0⟩ := hstart k m.st.input (m.st.heard.take T.front)
  have hb : 337 + 10 ≤ T.bs.length := by
    rw [hbs, Johnson.AtFull.Shape.flat_len h]
    omega
  have hR := thr_reach_of T (ProofFile.startS Zp) z hb h0 hT.1
  rw [hbs, hft] at hR
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact held_at_batching_head h.scope h.reads O hR

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (J : Nat → S → Prop)

/-- The same at the library's own thread, with the three premises paid. -/
theorem held_at_stand_letters :
    ∀ l, l < 24 → ∀ s, (∃ k m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread
        Said (14 * l + 8 + 1) k s m E ∧ J (14 * l + 8 + 1) s) →
      ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true :=
  held_at_stand h _ rfl rfl (fun _ w _ => ⟨w.x.pub, fun _ h0 => h0⟩) Said J

/-- The like at the head's batching. -/
theorem held_at_stand_head_letters :
    ∀ s, (∃ k m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread
        Said (337 + 10) k s m E ∧ J (337 + 10) s) →
      ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true :=
  held_at_stand_head h _ rfl rfl (fun _ w _ => ⟨w.x.pub, fun _ h0 => h0⟩) Said J

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.held_at_stand
#print axioms ProofFile.Honest.K8.held_at_stand_head
#print axioms ProofFile.Honest.K8.held_at_stand_letters
#print axioms ProofFile.Honest.K8.held_at_stand_head_letters
