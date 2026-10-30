-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/PinsAtLastParts.lean: THE THREE PINS WITH WHICH THE LAST CHAIN's THREAD BEGINS, IN
THE WORDS OF THAT THREAD's OWN MEANING (`lastParts`,
Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean), AT THE LAST CHAIN's WITNESS
(`lastWitness`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean): the index masks' pin and
W's pin, which come over from the first chain's end, and Omega's pin, which comes over from the
shared chain's end. Statements with their proofs; no definition.

Main names.
  `ansJT_at_lastWitness`: a pin of the honest side's form (`ansJT`,
    Johnson/Desc/ProofFile/Honest/Thread/Ans.lean) at a tenant of a tree of the first chain holds of
    the last chain's witness where it holds of the first chain's: the last chain's witness holds
    there what the first chain's holds.
  `pins_first_at_lastParts`: **wherever the first thread's invariant holds at its last border, the
    field pin₁ of the last thread's meaning holds at the index masks' tenant and at W's**, of the
    last chain's witness, at the first chain's last state, at every strings.
  `pinO_at_lastParts`: **wherever, besides, the shared thread's invariant holds at its last border,
    the field pin holds at Omega's tenant**, at the shared chain's last state.

How. The two pins of the first chain are open at its last border, so the invariant holds them of the
first chain's own witness; their tenants are (1, 0) and (82, 0), in trees below the 83 that the
first chain sends. Omega's pin is open at the shared chain's last border; its sample rows read
Omega's words alone, and these are one family at the shared chain's witness and at the last chain's.

Limits. Conditional on the head at the return and on the two invariants, which hold these sentences
among their clauses: the statements move them to the last chain's witness and pay no debt on them;
that the invariants hold at any run is not shown here. At `lastParts` alone. The full size, and the
hash function `OnBytes.secondHashFunction`, alone.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.K14.DotAtLastWitness
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointPins
import Johnson.Desc.ProofFile.Honest.K14.FirstAtLastWitness
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesOfThread
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesAtEnd
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open OnBytes
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (Mem SitsAt msgsOf)
open VerifiableInference.Desc.Shared (Msg2)
open Johnson.Pack (sigOf)
open Desc.K14 (St)
open Desc.K14.Honest (SmpOwn)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders SharedThreadParts
  LastLetters firstThread sharedThread lastWitness lastParts lastWords lastWords_at_lastWitness)

variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}

/-- **A pin at a tenant of a tree of the first chain holds of the last chain's witness where it
holds of the first chain's.** -/
theorem ansJT_at_lastWitness (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) {P : Type} (cs : OnBytes.Codes)
    (smp : P → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (hj : j < hd.description.t₁) (a : P) (y y' : Strs)
    (h0 : ansJT cs (P5J.At.arr A.Z) smp ms j t a y (first.script.wit k w heard)) :
    ansJT cs (P5J.At.arr A.Z) smp ms j t a y' (lastWitness hd first reads k w heard) := by
  obtain ⟨h1, h2⟩ := h0
  refine ⟨h1, fun x hx hs => ?_⟩
  obtain ⟨z, hz, hv⟩ := h2 x hx hs
  refine ⟨z, hz, ?_⟩
  have hs' : x.1.seat x.2 = (j, t) := hs
  have e : msgsOf cs x.1.l x.1.seat (P5J.At.arr A.Z) (lastWitness hd first reads k w heard) x.2 =
      msgsOf cs x.1.l x.1.seat (P5J.At.arr A.Z) (first.script.wit k w heard) x.2 := by
    funext q
    unfold msgsOf
    rw [hs']
    cases q with
    | inl q => exact congrFun (congrFun (congrFun
        (tab_first hd first reads k w heard j t hj cs (x.1.l.get x.2).1) false) q.1.val) q.2.val
    | inr q => exact congrFun (congrFun (congrFun
        (tab_first hd first reads k w heard j t hj cs (x.1.l.get x.2).1) true) q.1.val) q.2.val
  rw [e]
  exact hv

/-- **The index masks' pin and W's pin at the last chain's start, in the last thread's own
meaning.** -/
theorem pins_first_at_lastParts (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (L : LastLetters A) (w : Local W₀ Rc ProofFile.Inst Tr)
    {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    (u₁ : Thr (firstThread hd first w) hd.description.first.blocksInOrder.length k e₁ m₁ E₁)
    (h₂ ds : List Fmt.Drawn) (y : Strs) :
    ((lastParts hd first L).meaning w).pin₁ hd.sharedNumbers.index.1 hd.sharedNumbers.index.2
        (w.x.pub, e₁) y (lastWitness hd first reads k w (m₁.st.heard ++ h₂ ++ ds)) ∧
      ((lastParts hd first L).meaning w).pin₁ hd.sharedNumbers.w.1 hd.sharedNumbers.w.2
        (w.x.pub, e₁) y (lastWitness hd first reads k w (m₁.st.heard ++ h₂ ++ ds)) := by
  have hw : m₁.st.input = w := by
    have t := u₁
    unfold Thr at t
    exact t.2.2.2.2.2.2.1
  obtain ⟨pI, pV⟩ := ProofFile.Honest.K12.AtFile.LotWJoint.pins_at_last_run hd first w u₁ w
    (m₁.st.heard ++ h₂ ++ ds) (h₂ ++ ds) hw (List.append_assoc _ _ _)
  obtain ⟨eW, eI⟩ := hd.head.toAtMg.seats_at
  have e83 : hd.description.t₁ = 83 := first_trees_83 hd.head.toAtMg
  have hI : hd.sharedNumbers.index.1 < hd.description.t₁ := by
    rw [e83]
    show (P5J.At.N A.Z hd.firstChain).index.1 < 83
    rw [eI]
    decide
  have hW : hd.sharedNumbers.w.1 < hd.description.t₁ := by
    rw [e83]
    show (P5J.At.N A.Z hd.firstChain).w.1 < 83
    rw [eW]
    decide
  exact ⟨ansJT_at_lastWitness hd first reads k w _ _ _ _ _ _ hI _ _ y pI,
    ansJT_at_lastWitness hd first reads k w _ _ _ _ _ _ hW _ _ y pV⟩

/-- **Omega's pin at the last chain's start, in the last thread's own meaning.** -/
theorem pinO_at_lastParts {Wt₂ : Type} (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt₂) (L : LastLetters A)
    (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins A.B} {e₁ : TS}
    {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (firstThread hd first w) hd.description.first.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂) (ds : List Fmt.Drawn) (y : Strs) :
    ((lastParts hd first L).meaning w).pin (hd.sharedNumbers.tenant .oOmega).1
      (hd.sharedNumbers.tenant .oOmega).2 e₂ y
      (lastWitness hd first reads k w (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  intro m hm
  have hap := sharedTenantsApart hd
  obtain rfl : m = Msg2.oOmega := hap.1 (by
    show P5J.At.arr A.Z (hd.sharedNumbers.tenant m).1 (hd.sharedNumbers.tenant m).2 =
      P5J.At.arr A.Z (hd.sharedNumbers.tenant .oOmega).1 (hd.sharedNumbers.tenant .oOmega).2
    rw [hm])
  have hin : m₂.st.input = ⟨w.w₀, w.rc, A.H.key w.x⟩ := by
    have t := u₂
    unfold Thr at t
    exact t.2.2.2.2.2.2.1
  have hb := heard_behind hd reads parts first.script _ _ _ _ _ _ _ _ _ w u₁ u₂ ds
  have u12 : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩) 12 k e₂ m₂ E₂ :=
    shared_has_twelve hd.head ▸ u₂
  obtain ⟨x, hx, hs⟩ := smpOwn_of_thread hd reads parts _ u12 pin_open_at_end []
  rw [List.append_nil, hin] at hs
  refine ⟨x, hx, fun r hr => (OnBytes.Means.says_agree_in OnBytes.Slice.rdE
    ((order_of_thread hd reads parts _ u12).samples 2 x hx r hr) fun o ho part i _ => ?_).2
    (hs r hr)⟩
  obtain rfl : o = 2 := by simpa using ho
  rw [show (2 : Nat) = num Msg2.oOmega from rfl,
    lastWords_at_lastWitness hap first reads k w _ .oOmega part i, hb]
  exact (shared_words parts.lens _ _ _ parts.rest k _ _ 2 (ours_at_head hd .oOmega) part i).symm

end AtFullSide.K14

#print axioms AtFullSide.K14.ansJT_at_lastWitness
#print axioms AtFullSide.K14.pins_first_at_lastParts
#print axioms AtFullSide.K14.pinO_at_lastParts
