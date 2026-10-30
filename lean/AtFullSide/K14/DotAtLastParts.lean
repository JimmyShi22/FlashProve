-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/DotAtLastParts.lean: the linear claim (kinds K13 and K14): the item (Dot), in the
meaning that the last chain's thread bears (`lastParts`,
Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean), holds at that chain's start. One
statement with its proof; no definition. At the full size, at a return of the maker with the
library's head.

  `dot_at_lastParts`   the field `dot` of the meaning of `lastParts`, at the run's input, holds of
     the two earlier chains' last states and of `lastWitness` at the challenges heard on the two
     chains and any others: wherever the two earlier threads' invariants hold at their chains' ends

It is `dot_at_the_threads` (DotAtTheThreads.lean of this folder) with the number of the first
chain's trees read as that meaning reads it: off the written data, where it is 83
(`P5J.trees_at_depth`, Johnson/HB/LLHARD/HeadFacts.lean).

Limits. Those of DotAtTheThreads.lean. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import AtFullSide.K14.DotAtTheThreads
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.HB.LLHARD.HeadFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13 ProofFile.Honest.K14
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT wordsShared Mem)
open VerifiableInference.Desc.Third.Law (dotI gOfS wvW)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open Desc.K14 (St)
open P5J (TS)
open ProofFile.Honest.K1 (K1Seated PlaceIn)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders SharedThreadParts
  sharedThread lastWitness firstThread firstLetters lastParts LastLetters)

/-- **The item (Dot), in the meaning that the last chain's thread bears, at that chain's start.** -/
theorem dot_at_lastParts {W₀ Rc Tr X₀ X' Wt₂ : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hd : HeadAtReturn files A) (first₁ : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt₂) (L : LastLetters A)
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
    ((lastParts hd first₁ L).meaning w).dot (w.x.pub, e₁) e₂ y
      (lastWitness hd first₁ reads k w (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  show dotI (ToldDesc.p14At A.Z).S (fun q : ProofFile.InstPub × TS => gOfS q.2)
    (fun d v => wordsShared (P5J.At.arr A.Z)
      ((VerifierAndGoals.AtTheName.dpZ files).at OnBytes.Slice.frS.P.T.a).t₁ d.st d.book v)
    (fun q => wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) q)
    (w.x.pub, e₁) e₂ y (lastWitness hd first₁ reads k w (m₁.st.heard ++ m₂.st.heard ++ ds))
  rw [(P5J.trees_at_depth hd.head).1]
  exact dot_at_the_threads hd first₁ reads parts w y₀ R hx hwt u₁ u₂ ds y

end AtFullSide.K14

#print axioms AtFullSide.K14.dot_at_lastParts
