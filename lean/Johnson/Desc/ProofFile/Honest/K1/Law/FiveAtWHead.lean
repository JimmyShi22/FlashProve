-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FiveAtWHead.lean: THE SHARED "SENDING" (the kind K1) AT W's
MEMBER (number 356 of the first chain), at lettersHead with the two letters that a thread's keeps
and rides read at their values: Kp := kpBy fHeadJ, Rd := ridersOf (csHead ν st R), b₀ := 339. Every
other letter is free, as the parts of firstThread (Honest/Thread/TheFirstThread.lean) are. A trial.

  fHead_w                fHead at W's place is K1WKeeps
  head_keeps_w           the thread's keeps at 356 gives K1WKeeps
  k1_w_fHeadJ            the thread's clause at W's place, from the thread in front and the step
  k1_w_ridesPastS_head   RidesPastS at 356, at every Said
  k1_w_behindS_head      BehindS at 356, at every Said

Limits. Under the library's head h, a hypothesis. ThrS may hold of no stand. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FiveAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtW
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread

/-- At W's place fHead is K1's arm. -/
theorem fHead_w {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} {G : ProofFile.Ground} {take : Nat → Bool}
    {P11 : Johnson.Desc.First.ForkMerge.HeadMergeP} {p12 : VerifiableInference.Desc.K12.P12}
    {s s' : TS} :
    fHead Zp cF G take P11 p12 (VerifiableInference.Desc.K13.whereOf Zp) KindName.K1
      ⟨1, none, 4, .K1⟩ s s' ↔ K1WKeeps Zp s s' := by
  simp only [fHead, reduceCtorEq, false_and, ↓reduceIte, and_self, K1WKeeps]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (G : ProofFile.Ground) (take : Nat → Bool) (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP)
  (p12 : VerifiableInference.Desc.K12.P12) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "𝐟" => fHeadJ Zp cF G take P11 p12 (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD
local notation "𝐋" => lettersHead h H Q test carryX item n₁ n₂ 339 Vd
  (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12
    (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w

/-- The thread's keeps at 356 gives K1's clause. -/
theorem head_keeps_w {s s' : TS} (hk : 𝐋.keeps 356 s s') : K1WKeeps Zp s s' :=
  fHead_w.1 (hk ⟨1, none, 4, .K1⟩ place356W).1.1.1.1.1

/-- **WHAT GOES PAST W's MEMBER**, at every Said. -/
theorem k1_w_ridesPastS_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    RidesPastS 𝐋.thread Said 356 :=
  ridesPastS_of _ Said (k1_w_ridesPast h H Q test carryX item n₁ n₂ 339 Vd _ _ w
    fun _ _ hk => head_keeps_w h H Q test carryX item n₁ n₂ Vd ν st R G take P11 p12 w hk)

/-- **THE THREAD's CLAUSE AT W's PLACE**, from the thread in front and the member's step. -/
theorem k1_w_fHeadJ {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[356]? = some blk) {k : Coins Bk}
    {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr 𝐋.thread 356 k s m E) (hS : 𝐋.thread.Stepped blk k s m E ds y cols s') :
    𝐟 KindName.K1 ⟨1, none, 4, .K1⟩ s s' := by
  have hF := k1_w_form_behind h H Q test carryX item n₁ n₂ 339 Vd _ _ w hblk hT hS
  have hK := k1w_of_step h (ft := 0) hblk ⟨_, _, _, hS.2⟩
  refine ⟨⟨⟨⟨⟨fHead_w.2 hK, formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd _ _ w
    place356W hF⟩, ?_⟩, trivial⟩, trivial⟩, trivial⟩
  intro l hl
  cases hl

/-- **BEHIND W's MEMBER**, at every Said. -/
theorem k1_w_behindS_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    BehindS 𝐋.thread Said 356 := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  have hT := hA.1
  have hF : 𝐋.thread.Form (356 + 1) k s' y.2 :=
    k1_w_form_behind h H Q test carryX item n₁ n₂ 339 Vd _ _ w hblk hT hS
  have hS' := hS
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hF, ⟨fun _ => ?_, fun c hc h1 h2 => ?_⟩, ?_⟩
  · rw [ei]
    exact k1_w_reply h H Q test carryX item n₁ n₂ 339 Vd _ _ w hblk (by decide) hT hS
  · exfalso
    rcases csHead_span hc with ⟨-, e⟩ | ⟨l, hl, -, e⟩ | ⟨g, hg, -, e⟩ | ⟨g, hg, -, e⟩ <;> omega
  · intro p hp
    obtain rfl : p = ⟨1, none, 4, .K1⟩ := Option.some.inj (hp.symm.trans place356W)
    exact k1_w_fHeadJ h H Q test carryX item n₁ n₂ Vd ν st R G take P11 p12 w hblk hT hS

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.fHead_w
#print axioms ProofFile.Honest.K1.head_keeps_w
#print axioms ProofFile.Honest.K1.k1_w_ridesPastS_head
#print axioms ProofFile.Honest.K1.k1_w_fHeadJ
#print axioms ProofFile.Honest.K1.k1_w_behindS_head
