-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StopsHead.lean: `StopsFit` (Honest/Law/SharesStops.lean) at the
proof file's description, under `P5J.AtMg`. `bad_held`, `hid_held` and the bounds on falls
(`falls_head`, Honest/Law/CoverHeadAll.lean) take `StopsFit` as a hypothesis. `stopsFit_of`
(Honest/Law/SharesFit.lean) gives it from five things. Here three of the five are proved at that
description: the cut of the first chain; that its last sub-protocol has exactly one round; and, at
the kit `ckP .two`, that the list of challenges is such as the rounds can draw. The fourth, that
there is no prover's side at the last sub-protocol, is reduced to this: no prover's side of the
first chain is of the kind `frame`.

  1  `cut_seal_kind_yes`, `cut_seal_kind_control`   row number 357 of the written cut is of the kind
     `frame`; row number 356 is not
  2  `seal_kind`   so the chain's last sub-protocol is of that kind
  3  `bare_head`   there is no prover's side there, where none is of that kind
  4  `stopsFit_head`   `StopsFit`, at any kit
  5  `stopsFit_head_two`   at the kit `ckP .two`, with the condition on the list proved
  6  `stopsFit_head_exists`   with the cut itself proved

Limits.
  * Three hypotheses remain: `P5J.AtMg` (with `VerifierAndGoals.InScope` in 5 and 6), one return of `ready` at
    the prover (`hR`), and that no prover's side of the first chain is of the kind `frame` (`hn`).
    None is proved here of any prover.
  * `hn` is the hypothesis `noHalf` of Honest/Law/NoHouse/FrameAll.lean (not in the sealed library).
    It has the form of the conclusion of `wider_no_frame` (Honest/Thread/FirstFill.lean, written for
    another part of this project; not in the sealed library, and its build does not check it), which
    speaks of the prover that the maker returns at one filling, under two hypotheses. That file is
    not imported here, and the lemma is not applied.
  * A verifier's message ρ is an argument: `stopsFit_of` reads counts from one.
  * `StopsFit` holds tests and counts. `ChainHeld`, the other hypothesis of `bad_held` and
    `hid_held`, is not treated here, and no number comes from this file.
  * The statements are at the library's full-size parameter set alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile
import Johnson.Desc.ProofFile.Honest.Law.CoverDrawsAll
import Johnson.Desc.ProofFile.Honest.Law.SharesFit
import Johnson.Desc.ProofFile.Honest.Law.DueData
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Fill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Block Chain FileDescription)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK)
open _root_.Run (ckP)
open P5J (TS)

/-! ## 1 The closed statements -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The row number 357 is of the kind `frame`. -/
theorem cut_seal_kind_yes :
    ((cutFirstFull[357]?).any fun r => r.2.1.kind == KindName.frame) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: the row number 356 is not. -/
theorem cut_seal_kind_control :
    ((cutFirstFull[356]?).any fun r => r.2.1.kind == KindName.frame) = false := by
  decide +kernel

/-! ## 2 The last sub-protocol -/

/-- The chain's last sub-protocol is of the kind `frame`. -/
theorem seal_kind {S Cl : Type} {all pre : List (Block S Cl)} {e₁ : Block S Cl}
    (hcut : cutOf all = cutFirstFull) (cut : all = pre ++ [e₁]) :
    e₁.place.kind = KindName.frame := by
  have hlen : all.length = 358 := by
    rw [← seats_counts.1, ← hps_cut hcut, List.length_map]
  have hpre : pre.length = 357 := by
    rw [cut, List.length_append, List.length_singleton] at hlen
    omega
  have hr := cutOf_at cut
  rw [hcut, hpre] at hr
  have t := cut_seal_kind_yes
  rw [hr] at t
  have t' : (e₁.place.kind == KindName.frame) = true := t
  exact beq_iff_eq.1 t'

/-! ## 3 At the description -/

variable {W₀ Rc Ky Tr X₀ X TF TJ T3 : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
  {pre₁ : List (Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl)}
  {e₁ : Block (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl}

/-- There is no prover's side at the last sub-protocol, where no prover's side is of the kind
`frame`. -/
theorem bare_head (h : P5J.AtMg o Z D r Zp Np cF)
    (cut : (P5J.F0T o Zp Np cF).first.blocksInOrder = pre₁ ++ [e₁])
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) :
    (H.first.find? fun g => g.place == e₁.place) = none :=
  noHalf_of_kind fun g hg => by
    rw [seal_kind (file_head h).2.2 cut]
    exact hn g hg

/-- `StopsFit` at the proof file's description, at any kit. -/
theorem stopsFit_head (C : CK) (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (h : P5J.AtMg o Z D r Zp Np cF) (cut : (P5J.F0T o Zp Np cF).first.blocksInOrder = pre₁ ++ [e₁])
    (hR : ready (P5J.F0T o Zp Np cF) Bk H w₀ rc x k = .ok R)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (hρ : (drawsAt C D tF tJ t3 ρ).due (P5J.F0T o Zp Np cF) = true)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) :
    StopsFit (P5J.F0T o Zp Np cF) H D pre₁ e₁ := by
  obtain ⟨z, hz⟩ := seal_cut (file_head h).2.2 cut
  exact stopsFit_of C D tF tJ t3 hR ρ hρ cut (congrArg List.length hz) (bare_head h cut hn)

/-- At the kit `ckP .two`: every verifier's message shows a list that the rounds can draw. -/
theorem stopsFit_head_two (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (h : P5J.AtMg o Z D r Zp Np cF) (hZ : VerifierAndGoals.InScope Z = true)
    (cut : (P5J.F0T o Zp Np cF).first.blocksInOrder = pre₁ ++ [e₁])
    (hR : ready (P5J.F0T o Zp Np cF) Bk H w₀ rc x k = .ok R)
    (ρ : Iop.Rho (chainsOf (ckP .two) D tF tJ t3).sh)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) :
    StopsFit (P5J.F0T o Zp Np cF) H D pre₁ e₁ :=
  stopsFit_head (ckP .two) tF tJ t3 h cut hR ρ
    (due_at_two tF tJ t3 h.laid.data (draws_decl hZ h.laid) ρ) hn

/-- With the cut itself proved. -/
theorem stopsFit_head_exists (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (h : P5J.AtMg o Z D r Zp Np cF) (hZ : VerifierAndGoals.InScope Z = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk H w₀ rc x k = .ok R)
    (ρ : Iop.Rho (chainsOf (ckP .two) D tF tJ t3).sh)
    (hn : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) :
    ∃ pre e, (P5J.F0T o Zp Np cF).first.blocksInOrder = pre ++ [e] ∧ pre ≠ [] ∧
      StopsFit (P5J.F0T o Zp Np cF) H D pre e := by
  obtain ⟨pre, e, cut, hne⟩ := cut_exists (file_head h).2.2
  exact ⟨pre, e, cut, hne, stopsFit_head_two tF tJ t3 h hZ cut hR ρ hn⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.cut_seal_kind_yes
#print axioms ProofFile.Honest.cut_seal_kind_control
#print axioms ProofFile.Honest.seal_kind
#print axioms ProofFile.Honest.bare_head
#print axioms ProofFile.Honest.stopsFit_head
#print axioms ProofFile.Honest.stopsFit_head_two
#print axioms ProofFile.Honest.stopsFit_head_exists
