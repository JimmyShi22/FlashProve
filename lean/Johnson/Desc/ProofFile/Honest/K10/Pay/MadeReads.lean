-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeReads.lean: wherever the first chain's thread of the honest side stands, the run's input is valid; at the first thread at
a return of the maker "valid" holds that the instance passes the description's test on the instance (`FileDescription.okStart`). So
the light test on the reads' data (`ReadsLight`, Honest/K2/Law/LightDebts.lean) holds at the stand's instance, and with it the
code switch's public test at every place of the kind.

  `reads_at_stand`         at the head's letters, from hVd: the letter Vd gives `okStart`
  `publicOk_at_stand`      the code switch's public test there
  **`reads_at_first_stand`**, `publicOk_at_first_stand`   at `firstThread` (Honest/Thread/TheFirstThread.lean): no premise on a letter

By `readsLight_of_okStart`, `publicOk_of_okStart` (Johnson/HonestTrace/Joint/ReadsLightPaid.lean).

Limits. The head and the opening are hypotheses. That the thread stands anywhere is not shown. The full size and the older hash
alone.
-/
import Johnson.HonestTrace.Joint.ReadsLightPaid
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3.Fit (readsLight_of_okStart publicOk_of_okStart)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (switchPlaces segmentsOf publicOk withSwitchData)
open ProofFile.Honest.K2.Law (ReadsLight)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- At a stand the instance passes the description's test on the instance. -/
theorem okStart_at_stand (hVd : ∀ v, Vd v → (F0T OnBytes.secondHashFunction Zp Np cF).okStart v.x = true)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    (F0T OnBytes.secondHashFunction Zp Np cF).okStart m.st.input.x = true :=
  hVd _ ((head_valid h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w _).1 hT.2.2.2.2.2.2).2

/-- **The light test on the reads' data holds at a stand's instance.** -/
theorem reads_at_stand (hVd : ∀ v, Vd v → (F0T OnBytes.secondHashFunction Zp Np cF).okStart v.x = true)
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ReadsLight Zp Bs.G₀ m.st.input.x :=
  readsLight_of_okStart h O
    (okStart_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hVd hT)

/-- The code switch's public test at every place of the kind, at a stand's instance. -/
theorem publicOk_at_stand (hVd : ∀ v, Vd v → (F0T OnBytes.secondHashFunction Zp Np cF).okStart v.x = true)
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      publicOk (withSwitchData Sz.ref (ProofFile.Honest.K1.lotData Sz.ref) Zp Bs.G₀) Bs.G₀.first.layout p
        ((segmentsOf Zp Bs.G₀).take p.link) m.st.input.x = true :=
  publicOk_of_okStart h O
    (okStart_at_stand h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hVd hT)

end

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **AT THE FIRST THREAD: THE LIGHT TEST ON THE READS' DATA HOLDS AT EVERY STAND's INSTANCE.** -/
theorem reads_at_first_stand (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr) {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction files.pol files.lay files.KL
      (F0T OnBytes.secondHashFunction A.Z h.places h.firstChain) A.Z Bs base h.firstChain
      (seatZ A.Z h.places) (secondAt A.Z h.places))
    {b : Nat} {k : Coins A.B} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (firstThread h parts w) b k s m E) : ReadsLight A.Z Bs.G₀ m.st.input.x :=
  reads_at_stand h.head A.H parts.script _ _ _ _ _ _ _ _ _ w (fun _ hv => hv.1) O hT

/-- The code switch's public test there. -/
theorem publicOk_at_first_stand (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr) {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction files.pol files.lay files.KL
      (F0T OnBytes.secondHashFunction A.Z h.places h.firstChain) A.Z Bs base h.firstChain
      (seatZ A.Z h.places) (secondAt A.Z h.places))
    {b : Nat} {k : Coins A.B} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (firstThread h parts w) b k s m E) :
    ∀ p ∈ switchPlaces A.Z Bs.G₀,
      publicOk (withSwitchData Sz.ref (ProofFile.Honest.K1.lotData Sz.ref) A.Z Bs.G₀)
        Bs.G₀.first.layout p ((segmentsOf A.Z Bs.G₀).take p.link) m.st.input.x = true :=
  publicOk_at_stand h.head A.H parts.script _ _ _ _ _ _ _ _ _ w (fun _ hv => hv.1) O hT

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.okStart_at_stand
#print axioms ProofFile.Honest.K10.reads_at_stand
#print axioms ProofFile.Honest.K10.publicOk_at_stand
#print axioms ProofFile.Honest.K10.reads_at_first_stand
#print axioms ProofFile.Honest.K10.publicOk_at_first_stand
