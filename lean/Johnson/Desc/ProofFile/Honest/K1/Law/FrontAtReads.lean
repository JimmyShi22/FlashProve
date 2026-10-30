-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FrontAtReads.lean: WHAT THE FIRST CHAIN's THREAD GIVES AT A SEGMENT's READS, OF THE TWO PARTS:
under the head, at a stand that the pair holds and a step of the member: the open segment's part in front and behind, the second
rides on the first at the seats of the segment's first commitment, and each own and kept message sits at such a seat.

  segAt_of_stand     a state that stands in a link has its part
  front_at_reads     the statement. A default stream σ is laid for RchAt and the promise: they read it not, and the
                     end does not name it

This letter is for the honest run's own forms alone: no statement on any other party may take it. NEVER ON SOUNDNESS's ROAD: it
stands over laws at the meaning "honest".
NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Twin.FirstSeatedAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Law.InAtOfThr
import Johnson.Desc.ProofFile.Honest.K1.Law.YesAtFifty
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.K1.Law.ArmBySort
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.First.Close.Law.HingeMore
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Desc.First.Batch.SmallBehindDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S Stand standOf flatPlacesOf ModelPart)
open VerifiableInference.Desc.Sound (MsgT linksFull mgAll mgBase strsOf Rides)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open P5J (AtMgA CellsM TS F0T)

/-- A state that stands in a link has its part. -/
theorem segAt_of_stand {s : TS} {sub : ModelPart} (h : standOf s = .link sub) : ∃ A, K9.segAt? s = some A := by
  unfold standOf at h
  cases hh : s.here with
  | between => rw [hh] at h; cases h
  | lay a =>
    obtain ⟨A, hA, -⟩ := K9.segAt_of s a.L a.F a.tl (by simp [S.link?, hh]) (by simp [S.fork?, hh])
      (by simp [S.tl?, hh])
    exact ⟨A, hA⟩
  | att a =>
    obtain ⟨A, hA, -⟩ := K9.segAt_of s a.L a.F a.tl (by simp [S.link?, hh]) (by simp [S.fork?, hh])
      (by simp [S.tl?, hh])
    exact ⟨A, hA⟩
  | head a =>
    rw [hh] at h
    have hin : s.inLink = true := by
      by_contra hc
      simp [hc] at h
    have ho : a.opened = true := by
      unfold S.inLink S.fork? at hin
      rw [hh] at hin
      by_contra hc
      simp [hc] at hin
    obtain ⟨A, hA, -⟩ := K9.segAt_of s a.L a.F a.tl (by simp [S.link?, hh, ho])
      (by simp [S.fork?, hh, ho]) (by simp [S.tl?, hh, ho])
    exact ⟨A, hA⟩
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- **The two parts at a segment's reads.** -/
theorem front_at_reads {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {l : ℕ} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[K1.noL l false]? = some blk)
    {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn} {s' : TS}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false)
      k s μ E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y
      cols s') :
    ∃ A B, K9.segAt? s = some A ∧ K9.segAt? s' = some B ∧ Rides (h.𝔇.N.sent l 0) A B ∧
      K1.FirstSeated (h.𝔇.N.sent l 0) A l := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (K1.noL l false) k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hbl : K1.noL l false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1.le
  obtain ⟨X', arrs, hX, hy⟩ := yesOf_reads_head h O hl hblk (yes_of_stepped _ hS) μ.st.input.x.pub
  have hIn := inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT
  have σ : (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str := (fun _ => default, fun _ => default)
  obtain ⟨A, hA⟩ := segAt_of_stand (K1.stand_of_promise l hl _ _ (hIn (strsOf _ σ)))
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, K1.rounds_blkL]
  obtain ⟨B, hB, _, hr, _⟩ := K1.rides_of_rec
    (K1.laterSend_k1Reads Zp Bs.G₀ l X' _ arrs s s' _ gs hlen hd).2.1
    (K1.laterGrows_k1Reads Zp Bs.G₀ l X' _ arrs s s' _ gs hd) (K1.inAt_book (hIn (strsOf _ σ))).1
    (h.𝔇.N.sent l 0) hA
  exact ⟨A, B, hA, hB, hr, K1.firstSeated_at_reads_b h (K1.pin1_atAll h)
    (First.Close.hc_at_laid h.scope h.laid) l hl ((μ.st.input.x.pub, s), σ)
    (thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w σ hbl hT') (hIn (strsOf _ σ)).1
    (hIn (strsOf _ σ)).2 A hA⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.segAt_of_stand
#print axioms ProofFile.Honest.K1.front_at_reads
