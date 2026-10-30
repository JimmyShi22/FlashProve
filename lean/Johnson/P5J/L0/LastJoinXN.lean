-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastJoinXN.lean: `leads3_at_sh` (Johnson/P5J/L0/LastJoin.lean) WITH TWO OF
ITS SEVEN PREMISES STRUCK: hX by `LLT25.xSamples_of_tests` (Johnson/LLT25R/LastXAt.lean), hN by
`LLT25.hN_of_plan` (Johnson/LLT25R/LastNAt.lean) from the law's own hP. IN THEIR PLACE ONE
PREMISE: hT :
`Sh.Tests (Sh.planAt Zp Np (F0T o Zp Np cF))` ("all the named tests on the parameters say true").
  **`leads3_at_sh_tests`**: the tower's field `leads3_last_chains_table` (as `Leads3`) from hT and
    FIVE of the last table's law's premises: hSig · hRc · hP · hS · row0B [the statement: that
    theorem's own text, the two binders cut out and hT laid in by program].
    [ONE PREMISE MORE, which this list leaves out: q₃ (the law's hflat):
    `(F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃`.]
WHAT IT SHOWS BESIDE: that the two lemmas fit AT THE TOWER's OWN LETTERS: Lean takes them for the two
binders.
Limits. A call: it pays none of the five; hT in scope costs the door's two pins hs · hf, hl and pub
(Johnson/P5J/L0/LastAtHead.lean: under the tower's head). hT AND hP PRESS ON ONE NUMBER, Omega's
radius in `Sh.ms`: seen to fit by an evaluation alone (not in this library). O is pinned at arr
alone; Rc · Ld · M₁ are the caller's: at an Rc that nothing meets all is idle. Z and Zp are tied by no
binder. NO MEMBER is known. Nothing on soundness, nothing on hiding.
-/
import Johnson.P5J.L0.LastJoin
import Johnson.LLT25R.LastXAt
import Johnson.LLT25R.LastNAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J.L0

open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : Chain TS ProofFile.Cl)

set_option maxHeartbeats 4000000 in
/-- **THE SAME WITH hX AND hN STRUCK: THE NAMED TESTS STAND IN THEIR PLACE.** -/
theorem leads3_at_sh_tests
    (O : ShOpen ProofFile.InstPub (ProofFile.InstPub × TS) (CellsM numsFull) At.Tok (Sh.planAt Zp Np (F0T o Zp Np cF)).Q)
    (hT : Sh.Tests (Sh.planAt Zp Np (F0T o Zp Np cF)))
    (harr : O.arr = At.arr Zp) (dB : RDT) (dt : List RDT)
    (decT₁ : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × First.S → Option (CellsM numsFull))
    (M₁ : Meaning ProofFile.InstPub W) (r : Fmt.M1.Stage → ℕ)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (Rc : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ → Prop)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (hML : 𝔏.ML = mlAt o D Zp Np cF) (hPL : 𝔏.PLm = plmAt o Zp Np cF (Sh.X (Sh.planAt Zp Np (F0T o Zp Np cF)) 12))
    (he : 𝔏.e₃ = e3At o Z D Zp Np cF (Sh.oNo (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF)))
      (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0)))
    (hNs : 𝔏.Ns = (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0)))
    (hMg : 𝔏.MgS = Sh.mg (Sh.planAt Zp Np (F0T o Zp Np cF)) O) (hPm : 𝔏.Pm = Sh.pm (Sh.planAt Zp Np (F0T o Zp Np cF)) O)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hSig : meaningSig (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpNamed (p14At Zp).codes
    (At.seats Zp)) (At.ms Zp Z.lay) decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd (getL o Zp Np cF) (At.N Zp
    cF) M₁ fullLinks (First.flatPlaces true fullLinks true) q y → Rc q → ((getL o Zp Np cF)
    q).2.failed = none → ToldDesc.rcLastB 0 (vAt Zp (At.N Zp cF)) Ld (p14At Zp).codes ((getL o Zp Np
    cF) q).2 = true) (hP : PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF)
    (At.arr Zp) dB dt (At.ms Zp Z.lay) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF))) (At.N Zp cF)
    (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layU (Sh.planAt Zp Np (F0T o Zp
    Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0)) fullLinks (First.flatPlaces
    true fullLinks true) r ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld) (hS : ∀ q y, ocEnd
    (getL o Zp Np cF) (At.N Zp cF) M₁ fullLinks (First.flatPlaces true fullLinks true) q y → Rc q →
    ((getL o Zp Np cF) q).2.failed = none → ∀ f, firstOfS ((getL o Zp Np cF) q).2 = some f →
    SeatsNumber (At.seats Zp) f.book) (row0B :
    RowZeroOwed (tiedNumbers (At.N Zp cF) (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np
    cF))) (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF)))
    (0, 0) (0, 0))) (tiedMeaning (getL o Zp Np cF) M₁ (meaningSigS (p14At Zp).codes (F0T o Zp Np cF)
    (At.arr Zp) (smpSt (p14At Zp).codes (Sh.oNo (Sh.planAt Zp Np (F0T o Zp Np cF))) stSh) (Sh.ms
    (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.decT₂ (Sh.planAt Zp Np (F0T o Zp Np cF)) O) (Sh.mg
    (Sh.planAt Zp Np (F0T o Zp Np cF)) O))) (⟨rowsOpen (p14At Zp).codes (At.arr Zp) (D.at
    frS.P.T.a).t₁ (D.at frS.P.T.a).t₂⟩ : MeaningL (F0T o Zp Np cF).S₃ (Wit (CellsM numsFull) At.Tok
    MsgT)) (promSigS (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At Zp).codes (Sh.oNo (Sh.planAt Zp
    Np (F0T o Zp Np cF))) stSh) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF))) (fun s : St => s.st) (fun
    s : St => shiftBook (Sh.nums (Sh.planAt Zp Np (F0T o Zp Np cF)) O).lo s.book) (Sh.pm (Sh.planAt
    Zp Np (F0T o Zp Np cF)) O)) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS ((getL o Zp Np
    cF) q).2) (endedX (Sh.X (Sh.planAt Zp Np (F0T o Zp Np cF)) 12))) (fun q y => ocEnd (getL o Zp Np
    cF) (At.N Zp cF) M₁ fullLinks (First.flatPlaces true fullLinks true) q y ∧ Rc q) (pieceZeroAt
    (F0T o Zp Np cF) (D.at frS.P.T.a) (c0 Zp) (restCap (extsLast (Tok := At.Tok) (F0T o Zp Np cF)
    (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpLast (p14At Zp).codes
    (smpNamed (p14At Zp).codes (At.seats Zp)) (smpSt (p14At Zp).codes (Sh.oNo (Sh.planAt Zp Np (F0T
    o Zp Np cF))) stSh) (getL o Zp Np cF) (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np
    cF))) (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF)))
    (0, 0) (0, 0))) (fun _ _ => none) At.c₀ (mineOf (At.ms Zp Z.lay) (Sh.ms (Sh.planAt Zp Np (F0T o
    Zp Np cF))) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layU
    (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0,
    0))))))) :
    Leads3 o D Zp Np cF M₁ Rc 𝔏 :=
  leads3_at_sh o Z D Zp Np cF O harr dB dt decT₁ M₁ r Ld Rc 𝔏 hML hPL he hNs hMg hPm q₃ hSig hRc hP
    (xSamples_of_tests Zp Np (F0T o Zp Np cF) hT) hS
    (hN_of_plan (Sh.planAt Zp Np (F0T o Zp Np cF)) hT o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a)
      (F0T o Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay) (At.N Zp cF) (0, 0) (0, 0) fullLinks
      (First.flatPlaces true fullLinks true) r ((At.N Zp cF).treesAt none) 0 Ld hP)
    row0B

end P5J.L0

#print axioms P5J.L0.leads3_at_sh_tests
