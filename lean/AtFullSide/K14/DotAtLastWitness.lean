-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/DotAtLastWitness.lean: the linear claim (kinds K13 and K14): the item (Dot) holds at
the start of the proof file's last chain, at that chain's honest witness `lastWitness`
(Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean). Statements with their proofs, one of
them an evaluation in Lean's kernel; no definition. At the full size, at a return of the maker with
the library's head (`HeadAtReturn`, the same file).

DotAtStart.lean of this folder shows (Dot) at any witness that holds W's text and, at Omega's
number, the shared chain's honest words. Here the second of these two hypotheses is paid at
`lastWitness`: that witness lays the shared chain's three sampled messages at their seats, and the
shared chain's last state seats Omega there.

  `omega_shape_is`   the shape that `lastWitness` gives Omega's table is the plan's
  `omega_words_at_end`   **the words that are read off `lastWitness` at the shared chain's last
     state, at Omega's number, are the shared chain's honest words**, at what the prover holds and
     at the first challenge heard on that chain
  `dot_at_lastWitness`   **(Dot), in the library's own filling of the item's meaning, at
     `lastWitness`**, wherever the two earlier threads' invariants hold at their chains' ends. Of
     the witness one hypothesis is left: hW, that it holds W's text
  `kCol_written`, `heard_behind`, `dot_at_the_join`   the same at the list of challenges at which
     the last chain begins: those heard on the first chain, then those heard on the shared chain,
     then any others

Limits.
  * hW is a hypothesis: W's words at `lastWitness`, read at the first chain's last state, are the
    row weights made of the challenges heard on the first chain, applied to the index's matrix.
  * 83 is the number of the first chain's trees at the full size; the item's meaning is taken at
    that number. At another number Omega's seat is another, and the statements say nothing.
  * That either thread's invariant holds at any state is not shown here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K14.DotAtStart
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesAtLastWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13 ProofFile.Honest.K14
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.K1 (qAt)
open VerifiableInference.Desc.Sound (MsgT wordsShared seatBy noShared)
open VerifiableInference.Desc.Third.Law (dotI gOfS wvW)
open Desc.K14 (St)
open Desc.K14.Honest (words2)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead sentFirstOf HeadAtReturn FirstThreadParts
  IndexReaders SharedThreadParts sharedThread lastWitness sharedShape)
open AtFullSide.K13 (gWords)

/-- The shape that `lastWitness` gives Omega's table is the plan's, where the shape splits the row.
-/
theorem omega_shape_is (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (hS : (qAt Zp Np).S.sharedSplitNeeded = true) :
    sharedShape Zp Np .oOmega = (qAt Zp Np).S.omega := by
  have e := (Desc.K14.Honest.withOmega_two hS).2.1
  show ((Desc.K14.withOmega (qAt Zp Np).S).getD 0 default).shape = _
  rw [Array.getD_eq_getD_getElem?, e]
  rfl

variable {W₀ Rc Tr X₀ X' Wt₂ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}

/-- **The words that are read off `lastWitness` at the shared chain's last state, at Omega's number,
are the shared chain's honest words.** hhd: the challenges behind the first chain's begin as those
heard on the shared chain do. -/
theorem omega_words_at_end (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt₂) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn)
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (hhd : firstRv (heard.drop
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length) =
        firstRv m₂.st.heard) (part : OnBytes.Part) (i : Nat) :
    wordsShared (P5J.At.arr A.Z) 83 e₂.st e₂.book (lastWitness hd first reads k w heard) 2 part i =
      words2 (qAt A.Z hd.places) (sentFirstOf A.Z hd.places)
        (Desc.K14.first (qAt A.Z hd.places).codes (A.H.key w.x)) (firstRv m₂.st.heard)
        (holds2 (qAt A.Z hd.places) reads.weights reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩) 2 part
        i := by
  obtain ⟨-, -, hsh, hseat⟩ := omega_written_at_shared_end A.Z hd.places hd.firstChain A.H _ _ _ _ _
    _ _ _ _ _ _ _ _ _ hd.head u₂
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head hd.head
  have hx : (e₂.st.oracles[2]?).map (·.shape) = some (sharedShape A.Z hd.places .oOmega) := by
    rw [omega_shape_is A.Z hd.places hQ.facts.two]
    exact hsh
  have hs : seatBy (noShared 83) e₂.book 2 = some (hd.sharedNumbers.tenant .oOmega) := by
    rw [hseat 83]
    show _ = some ((Desc.K14.Law.Sh.nums hd.head.toAtMg.shPlan
      (hd.head.toAtMg.shOpen hd.head.𝔇)).tenant .oOmega)
    rw [shNums_tenant hd.head.toAtMg]
  show VerifiableInference.Desc.Sound.wordsBy (P5J.At.arr A.Z) (seatBy (noShared 83) e₂.book) e₂.st
    (lastWitness hd first reads k w heard) 2 part i = _
  rw [omega_words_last hd first reads k w heard _ e₂.st hs hx part i, hhd]

section
variable (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : SharedThreadParts A Wt₂)
  (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **(Dot), in the library's own filling of the item's meaning, at `lastWitness`.** u₁, u₂: the two
earlier threads' invariants at their chains' ends, at one run's coins. hhd: as in
`omega_words_at_end`. hW: the witness holds W's text. -/
theorem dot_at_lastWitness (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    {F : VerifiableInference.Desc.Sound.Frame} (y₀ : F.E.Str)
    (hb₀ : b₀ ≤ hd.firstChain.blocksInOrder.length) (heard : List Fmt.Drawn)
    {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (lettersHead hd.head A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (hhd : firstRv (heard.drop
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length) =
        firstRv m₂.st.heard)
    (hW : ∀ c < 2 ^ A.Z.first.lin.kCol,
      wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) (w.x.pub, e₁)
          (lastWitness hd first reads k w heard) c =
        wVec A.Z.first.lin (reads.weights w.w₀) (gWords A.Z Bs w.x m₁.st.heard) c) (y : Strs) :
    dotI (ToldDesc.p14At A.Z).S (fun q : ProofFile.InstPub × TS => gOfS q.2)
      (fun d v => wordsShared (P5J.At.arr A.Z) 83 d.st d.book v)
      (fun q => wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) q)
      (w.x.pub, e₁) e₂ y (lastWitness hd first reads k w heard) :=
  dotI_at_the_door hd.head A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bs
    hB y₀ hb₀ (P5J.At.arr A.Z) 83 (reads.weights w.w₀) (reads.rand w.rc)
    (holds2 (qAt A.Z hd.places) reads.weights reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩) rfl
    (A.H.key w.x) u₁ u₂ _ hW
    (fun i => omega_words_at_end hd first reads parts k w heard u₂ hhd .main i) y

set_option maxRecDepth 1000000 in
/-- At the written shape a column's number has at least one bit. By the kernel. -/
theorem kCol_written : 0 < VerifiableInference.PlanWritten.proofSizedFull.batch.shape.kCol := by
  decide +kernel

/-- **Behind the first chain's challenges the list at which the last chain begins goes on as the
shared chain's does.** -/
theorem heard_behind {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (lettersHead hd.head A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂) (ds : List Fmt.Drawn) :
    firstRv ((m₁.st.heard ++ m₂.st.heard ++ ds).drop
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length) =
        firstRv m₂.st.heard := by
  have l1 : m₁.st.heard.length =
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length :=
    drawsFit_length _ _ u₁.2.1
  obtain ⟨hpt, hlen⟩ := point_at_shared_end hd.head A.H _ _ _ _ _ _ _ _ _ _ _ _ _ _ u₂
  have hs : A.Z.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope hd.head.scope hd.head.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made hd.head.toAtMg.made_accepts)
  have hk : 0 < (qAt A.Z hd.places).S.kCol := by
    show 0 < A.Z.p.chains.made.sized.proof.batch.shape.kCol
    rw [hs]
    exact kCol_written
  rw [List.append_assoc, ← l1, List.drop_left]
  cases hm : m₂.st.heard with
  | nil =>
    rw [hpt, hm] at hlen
    exact absurd hlen (Nat.ne_of_lt hk)
  | cons a t => rfl

/-- **(Dot) at the list of challenges at which the last chain begins**: those heard on the first
chain, then those heard on the shared chain, then any others. -/
theorem dot_at_the_join (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    {F : VerifiableInference.Desc.Sound.Frame} (y₀ : F.E.Str)
    (hb₀ : b₀ ≤ hd.firstChain.blocksInOrder.length)
    {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (lettersHead hd.head A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : Thr (sharedThread hd reads parts ⟨w.w₀, w.rc, A.H.key w.x⟩)
      hd.description.shared.blocksInOrder.length k e₂ m₂ E₂) (ds : List Fmt.Drawn)
    (hW : ∀ c < 2 ^ A.Z.first.lin.kCol,
      wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) (w.x.pub, e₁)
          (lastWitness hd first reads k w (m₁.st.heard ++ m₂.st.heard ++ ds)) c =
        wVec A.Z.first.lin (reads.weights w.w₀) (gWords A.Z Bs w.x m₁.st.heard) c) (y : Strs) :
    dotI (ToldDesc.p14At A.Z).S (fun q : ProofFile.InstPub × TS => gOfS q.2)
      (fun d v => wordsShared (P5J.At.arr A.Z) 83 d.st d.book v)
      (fun q => wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z) (fun q : ProofFile.InstPub × TS => q.2) q)
      (w.x.pub, e₁) e₂ y (lastWitness hd first reads k w (m₁.st.heard ++ m₂.st.heard ++ ds)) :=
  dot_at_lastWitness hd first reads parts Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs hB y₀ hb₀ _ u₁
    u₂ (heard_behind hd reads parts Q test carryX item n₁ n₂ b₀ Vd Rd Kp w u₁ u₂ ds) hW y

end

end AtFullSide.K14

#print axioms AtFullSide.K14.omega_shape_is
#print axioms AtFullSide.K14.omega_words_at_end
#print axioms AtFullSide.K14.dot_at_lastWitness
#print axioms AtFullSide.K14.kCol_written
#print axioms AtFullSide.K14.heard_behind
#print axioms AtFullSide.K14.dot_at_the_join
