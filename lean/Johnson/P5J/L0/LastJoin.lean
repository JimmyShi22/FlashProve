-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastJoin.lean: `leads3_at` (Johnson/P5J/L0/LastCall.lean) CALLED AT THE SHARED TABLE's
CONSTANT's OWN LETTERS: X := `Sh.X A 12` · oNo := `Sh.oNo A` · ms₂ := `Sh.ms A` · Ns := `numbersSh (Sh.t₁ A)
(Sh.layU A) (Sh.layO A) (0, 0) (0, 0)` · MgS := `Sh.mg A O` · Pm := `Sh.pm A O`, at A := `Sh.planAt Zp Np
(F0T o Zp Np cF)` and every filling O of that constant's open letters whose numbering of the tenants is
the first table's (`O.arr = At.arr Zp`).
  **`leads3_at_sh`**: the tower's field `leads3_last_chains_table` (as `Leads3`) at every 𝔏 whose six
    letters are these terms, from the last table's law's seven premises at them [their texts: that
    law's own, its letters replaced by program].
    [ONE PREMISE MORE, which this list leaves out: q₃ (the law's hflat):
    `(F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃`.]
THIS FILE IMPORTS ALL THREE CONES (the tower's, the shared constant's, the last
chain's).
Limits. A call: it pays no premise; NO MEMBER is known. Nothing on soundness, nothing on hiding.

-/
import Johnson.P5J.L0.LastCall
import Johnson.P5J.L0.LastForms
import Johnson.Desc.K14.Law.SharedConstAt

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
/-- **THE LAST TABLE's LAW AT THE TOWER's FIELD, AT THE SHARED TABLE's CONSTANT's LETTERS.** -/
theorem leads3_at_sh
    (O : ShOpen ProofFile.InstPub (ProofFile.InstPub × TS) (CellsM numsFull) At.Tok (Sh.planAt Zp Np (F0T o Zp Np cF)).Q)
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
    true fullLinks true) r ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld) (hX : XSamples
    (p14At Zp).codes (p14At Zp).S (Sh.X (Sh.planAt Zp Np (F0T o Zp Np cF)) 12)) (hS : ∀ q y, ocEnd
    (getL o Zp Np cF) (At.N Zp cF) M₁ fullLinks (First.flatPlaces true fullLinks true) q y → Rc q →
    ((getL o Zp Np cF) q).2.failed = none → ∀ f, firstOfS ((getL o Zp Np cF) q).2 = some f →
    SeatsNumber (At.seats Zp) f.book) (hN : ∀ x ∈ (mineOf (At.ms Zp Z.lay) (Sh.ms (Sh.planAt Zp Np
    (F0T o Zp Np cF))) (At.N Zp cF) (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF)))
    (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))) (0, 0)
    (0, 0))), seatOf x = ((D.at frS.P.T.a).t₁ + 1, 0) → ∀ d, (Sh.X (Sh.planAt Zp Np (F0T o Zp Np
    cF)) 12) d = true → (Sh.oNo (Sh.planAt Zp Np (F0T o Zp Np cF))) x = d.loc.oOmega) (row0B :
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
  leads3_at o Z D Zp Np cF (Sh.X (Sh.planAt Zp Np (F0T o Zp Np cF)) 12) (Sh.oNo (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF)))
    (Fence.numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))) (0, 0) (0, 0)) dB dt decT₁
    (Sh.decT₂ (Sh.planAt Zp Np (F0T o Zp Np cF)) O) M₁ (Sh.mg (Sh.planAt Zp Np (F0T o Zp Np cF)) O) (fun s : St => s.st)
    (fun s : St => shiftBook (Sh.nums (Sh.planAt Zp Np (F0T o Zp Np cF)) O).lo s.book) (Sh.pm (Sh.planAt Zp Np (F0T o Zp Np cF)) O) r Ld Rc 𝔏 hML hPL he hNs
    (hMg.trans (harr ▸ sh_mg_form (Sh.planAt Zp Np (F0T o Zp Np cF)) O)) (hPm.trans (sh_pm_form (Sh.planAt Zp Np (F0T o Zp Np cF)) O)) q₃ hSig hRc hP hX hS hN
    row0B

end P5J.L0

#print axioms P5J.L0.leads3_at_sh
