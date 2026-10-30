-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/KeepsMono.lean: what is proved at the first chain's invariant
at one condition `keeps` holds at every stronger one. `lettersHead` (FirstHead.lean) takes `keeps`
through its argument `Kp`. The invariant itself (`Thr`, Thr.lean) does not read `keeps`. Two
hypotheses of the gathering have `keeps` among their premises: `StaysBy` (Riders.lean) and
`RidesPastAtS` (SharesS.lean). So a proof of either at `Kp` gives it at every `Kp'` that implies
`Kp`. FHeadF.lean lays one clause more beside `fHead`. By these lemmas, what is proved at `fHead`
holds at `fHeadF`. No definition.

  1  `head_keeps_mono`   `keeps` at `Kp'` gives `keeps` at `Kp`
  2  `head_thrS_kp`   the invariant at `Kp'` is the invariant at `Kp`
  3  `head_staysBy_mono`, `head_ridesPastAtS_mono`   the two hypotheses
  4  `kpBy_fHeadF`   `fHeadF` implies `fHead`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadF
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Kp' : Place → TS → TS → Prop)

/-- `keeps` at the stronger condition gives `keeps` at the weaker one. -/
theorem head_keeps_mono (hle : ∀ p s s', Kp' p s s' → Kp p s s') (b : Nat) (s s' : TS)
    (hk : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread.keeps b s s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' :=
  fun p hp => hle p s s' (hk p hp)

/-- The invariant does not read `keeps`. -/
theorem head_thrS_kp (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {b : Nat}
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b k s m E) :
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E := hA

/-- `StaysBy` at the weaker condition gives it at the stronger one. -/
theorem head_staysBy_mono (hle : ∀ p s s', Kp' p s s' → Kp p s s') {b : Nat}
    {c : RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS}
    (hc : StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b c) :
    StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread b c :=
  fun v s s' hk => hc v s s'
    (head_keeps_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Kp' hle b s s' hk)

/-- `RidesPastAtS` at the weaker condition gives it at the stronger one. -/
theorem head_ridesPastAtS_mono (hle : ∀ p s s', Kp' p s s' → Kp p s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {b : Nat} {i : Item}
    (hc : RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp' w).thread Said b i :=
  fun k s m E s' ps v hA hK h0 => hc k s m E s' ps v
    (head_thrS_kp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Kp' Said hA)
    (head_keeps_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Kp' hle b s s' hK) h0

/-- `fHeadF` implies `fHead`. -/
theorem kpBy_fHeadF (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (Dp : VerifiableInference.Desc.First.PubData) :
    ∀ p s s', kpBy (fHeadF Zp cF G take P11 p12 P13 Dp) p s s' →
      kpBy (fHead Zp cF G take P11 p12 P13) p s s' :=
  fun _ _ _ hk => hk.1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_keeps_mono
#print axioms ProofFile.Honest.FirstThread.head_thrS_kp
#print axioms ProofFile.Honest.FirstThread.head_staysBy_mono
#print axioms ProofFile.Honest.FirstThread.head_ridesPastAtS_mono
#print axioms ProofFile.Honest.FirstThread.kpBy_fHeadF
