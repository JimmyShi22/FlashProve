-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/DotAtTheThreads.lean: the linear claim (kinds K13 and K14): the item (Dot) holds at
the start of the proof file's last chain, at that chain's honest witness, wherever the invariants of
the first chain's thread and of the shared chain's thread hold at their chains' ends. One statement
with its proof; no definition. At the full size, at a return of the maker with the library's head
(`HeadAtReturn`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean).

  `dot_at_the_threads`   (Dot), in the library's own filling of the item's meaning (`dotI`,
     Johnson/Desc/Third/Law/Row0DotOm.lean), at `lastWitness`, at the challenges heard on the first
     chain, then those heard on the shared chain, then any others. Omega's words at that witness are
     paid in DotAtLastWitness.lean of this folder; W's come from the record R of W's sender, by
     AtFullSide/K13/HWAtDoor.lean

Limits.
  * R, hx and hwt are hypotheses. R is the record of W's sender at the sub-protocol number 356 of
    the first chain's thread (`K1Seated`, Johnson/Desc/ProofFile/Honest/K1/Seated.lean), at a job
    whose data are W's at the return's own ground. Among its fields: the first chain's witness
    holds, at W's seat, the message and the pad that the job makes. So what the witness holds of W
    is a hypothesis here. hx, hwt: the job's reader of the input hands on the instance, and its
    weights are those of `reads`, from which the shared chain's words in `lastWitness` are made.
  * F and y₀ are idle: arguments of a lemma of the library that is called.
  * That either thread's invariant holds at any state is not shown here.
  * 83 is the number of the first chain's trees at the full size.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K14.DotAtLastWitness
import AtFullSide.K13.HWAtDoor
import Johnson.AtFull.Shape.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13 ProofFile.Honest.K14
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT wordsShared Mem)
open VerifiableInference.Desc.Third.Law (dotI gOfS wvW)
open Desc.K14 (St)
open P5J (TS)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open ProofFile.Honest.K1 (K1Seated PlaceIn)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders SharedThreadParts
  sharedThread lastWitness firstThread firstLetters)

/-- **(Dot) at the start of the last chain, from the two earlier threads' invariants at their
chains' ends.** R, hx, hwt: see the head's Limits. -/
theorem dot_at_the_threads {W₀ Rc Tr X₀ X' Wt₂ : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hd : HeadAtReturn files A) (first₁ : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt₂)
    (w : Local W₀ Rc ProofFile.Inst Tr) {F : VerifiableInference.Desc.Sound.Frame} (y₀ : F.E.Str)
    {first : ℕ} {blk₆ : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {own₀ : X'} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}
    (R : K1Seated (firstLetters hd first₁ w) 356 blk₆ wit
      (K1.wJobAt A.Z.first (K1.wGp A.Z) 4 wMsgFull first (wDataAt pileAnyK3 A.Z A.G)) own₀ .w
      (P5J.At.arr A.Z) seats₀ ms rad)
    (hx : (wit w).x = w.x) (hwt : (wit w).R.weights = reads.weights w.w₀)
    {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (firstThread hd first₁ w) 358 k e₁ m₁ E₁)
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂) (ds : List Fmt.Drawn) (y : Strs) :
    dotI (ToldDesc.p14At A.Z).S (fun q : ProofFile.InstPub × TS => gOfS q.2)
      (fun d v => wordsShared (P5J.At.arr A.Z) 83 d.st d.book v)
      (fun q => wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) q)
      (w.x.pub, e₁) e₂ y (lastWitness hd first₁ reads k w (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  have hl : hd.firstChain.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len hd.head
  obtain ⟨Bs, base, O⟩ := hd.head.laid.opened
  obtain ⟨P, hA⟩ := hd.returned
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground hd.head.laid O.blank hA
  refine dot_at_the_join hd first₁ reads parts first₁.script _ _ _ _ _ 339 _ _ _ w Bs O.made y₀
    (by rw [hl]; decide) (by rw [hl]; exact u₁) u₂ ds ?_ y
  intro c hc
  have key := AtFullSide.K13.k13_hW_at_own hd first₁ reads w R hx hwt u₁ w.x.pub
    (m₂.st.heard ++ ds) c hc
  rw [eG] at key
  rw [List.append_assoc]
  exact key

end AtFullSide.K14

#print axioms AtFullSide.K14.dot_at_the_threads
