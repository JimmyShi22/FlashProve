-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastCall.lean: THE LAST TABLE's LAW, CALLED AT THE TOWER's FIELD
`leads3_last_chains_table` (Johnson/P5J/TowerEnd.lean), at every value 𝔏 of the tower's free letters
whose six letters ML, PLm, e₃, Ns, MgS, Pm are the meant terms, GENERAL IN THE SHARED TABLE's FOUR
(X · oNo · ms₂ · Ns: see Johnson/P5J/L0/Last.lean).
  `ttAt`: the tower's three rows of pieces at 𝔏 (its local notation TT, as a definition).
  `Leads3`: the field's sentence, general in the first table's meaning M₁ and in the condition Rc on
    what the first chain hands on.
  **`leads3_at`**: `Leads3` from the seven premises of `LLT25.own3_at_top_unpulled`
    (Johnson/LLT25R/LastUnpulled.lean:
    `LLT25.own3_at_top`'s statement at the description not pulled back), each at the
    closed letters [their texts: that theorem's own, its letters replaced by program, the tower's
    `F0T o Zp Np cF` for its `FU o mk Z N c`]: hSig · hRc · hP · hX · hS · hN · row0B.
    [ONE PREMISE MORE, which this list leaves out: q₃ (the law's hflat):
    `(F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃`.]
WHAT THE PROOF IS: one call. That law stands at `LLT25.FU o mk Z N c` := `ProofFile.fileDescBy o mk Z (seatK Z
N) (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c`; the field stands at the tower's own name
`F0T o Zp Np cF`. That Lean takes the call says that the two are one by unfolding, at mk :=
`ProofFile.pureRoad.links`.
Limits. A call: it pays no premise; NO MEMBER is known. The premise hSig speaks of M₁ at the later
tables' codes: at the tower's own meaning it wants the equation of the two codes. Nothing on
soundness, nothing on hiding.
-/
import Johnson.P5J.L0.Last
import Johnson.LLT25R.LastUnpulled
import Johnson.P5J.TopTablesR

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
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ToldDesc (p14At)
open LLT25

variable (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : Chain TS ProofFile.Cl) (X : St → Bool) (oNo : Mem → ℕ) (ms₂ : List Mem) (Ns : NumbersS)

/-- The tower's three rows of pieces at 𝔏. -/
def ttAt (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :=
  piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁)
    (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd

/-- **The tower's field `leads3_last_chains_table`, as a sentence of its own.** -/
def Leads3 (M₁ : Meaning ProofFile.InstPub W) (Rc : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ → Prop)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  EachOwn
    (onQ₃ (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃ (ttAt o D Zp Np cF 𝔏).ft₃)
      (tiedNumbers (At.N Zp cF) 𝔏.Ns) (tiedMeaning (getL o Zp Np cF) M₁ 𝔏.MgS) 𝔏.Pm 𝔏.PLm
      (ocR (getL o Zp Np cF) (At.N Zp cF) M₁ fullLinks At.ps Rc))
    (meansQ₃ (tiedNumbers (At.N Zp cF) 𝔏.Ns) (tiedMeaning (getL o Zp Np cF) M₁ 𝔏.MgS) 𝔏.ML)
    insQ₃ outsQ₃ (· ∈ startLast) 0 ((ttAt o D Zp Np cF 𝔏).p₃ :: (ttAt o D Zp Np cF 𝔏).l₃)

set_option maxHeartbeats 4000000 in
/-- **THE LAST TABLE's LAW AT THE TOWER's FIELD.** -/
theorem leads3_at (dB : RDT) (dt : List RDT)
    (decT₁ : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × First.S → Option (CellsM numsFull))
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsM numsFull))
    (M₁ : Meaning ProofFile.InstPub W) (MS : MeaningS St ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) W)
    (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St)
    (r : Fmt.M1.Stage → ℕ)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (Rc : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ → Prop)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (hML : 𝔏.ML = mlAt o D Zp Np cF) (hPL : 𝔏.PLm = plmAt o Zp Np cF X)
    (he : 𝔏.e₃ = e3At o Z D Zp Np cF oNo ms₂ Ns) (hNs : 𝔏.Ns = Ns)
    (hMg : 𝔏.MgS = meaningSigS (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp)
      (smpSt (p14At Zp).codes oNo stSh) ms₂ decT₂ MS)
    (hPm : 𝔏.Pm = promSigS (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At Zp).codes oNo stSh) ms₂ stOf bookOf
      Pm₀)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hSig : meaningSig (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpNamed (p14At Zp).codes
    (At.seats Zp)) (At.ms Zp Z.lay) decT₁ M₁ = M₁) (hRc : ∀ q y, ocEnd (getL o Zp Np cF) (At.N Zp
    cF) M₁ fullLinks (First.flatPlaces true fullLinks true) q y → Rc q → ((getL o Zp Np cF)
    q).2.failed = none → ToldDesc.rcLastB 0 (vAt Zp (At.N Zp cF)) Ld (p14At Zp).codes ((getL o Zp Np
    cF) q).2 = true) (hP : PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF)
    (At.arr Zp) dB dt (At.ms Zp Z.lay) ms₂ (At.N Zp cF) Ns fullLinks (First.flatPlaces true
    fullLinks true) r ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld) (hX : XSamples
    (p14At Zp).codes (p14At Zp).S X) (hS : ∀ q y, ocEnd (getL o Zp Np cF) (At.N Zp cF) M₁ fullLinks
    (First.flatPlaces true fullLinks true) q y → Rc q → ((getL o Zp Np cF) q).2.failed = none → ∀ f,
    firstOfS ((getL o Zp Np cF) q).2 = some f → SeatsNumber (At.seats Zp) f.book) (hN : ∀ x ∈
    (mineOf (At.ms Zp Z.lay) ms₂ (At.N Zp cF) Ns), seatOf x = ((D.at frS.P.T.a).t₁ + 1, 0) → ∀ d, X
    d = true → oNo x = d.loc.oOmega) (row0B : RowZeroOwed (tiedNumbers (At.N Zp cF) Ns) (tiedMeaning
    (getL o Zp Np cF) M₁ (meaningSigS (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp) (smpSt (p14At
    Zp).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Zp).codes (At.arr Zp) (D.at frS.P.T.a).t₁
    (D.at frS.P.T.a).t₂⟩ : MeaningL (F0T o Zp Np cF).S₃ (Wit (CellsM numsFull) At.Tok MsgT))
    (promSigS (p14At Zp).codes (F0T o Zp Np cF) (smpSt (p14At Zp).codes oNo stSh) ms₂ stOf bookOf
    Pm₀) (fillAt (p14At Zp) (c2 Np).rounds (fun q => firstOfS ((getL o Zp Np cF) q).2) (endedX X))
    (fun q y => ocEnd (getL o Zp Np cF) (At.N Zp cF) M₁ fullLinks (First.flatPlaces true fullLinks
    true) q y ∧ Rc q) (pieceZeroAt (F0T o Zp Np cF) (D.at frS.P.T.a) (c0 Zp) (restCap (extsLast (Tok
    := At.Tok) (F0T o Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF) (At.arr Zp)
    (smpLast (p14At Zp).codes (smpNamed (p14At Zp).codes (At.seats Zp)) (smpSt (p14At Zp).codes oNo
    stSh) (getL o Zp Np cF) Ns) (fun _ _ => none) At.c₀ (mineOf (At.ms Zp Z.lay) ms₂ (At.N Zp cF)
    Ns))))) :
    Leads3 o D Zp Np cF M₁ Rc 𝔏 := by
  obtain ⟨Q₀, c₀, Ns', MgS, ML, Pm, PLm, split, Q₂, rP, c₁, k₁, c₂, k₂, c₃, k₃, e₁, e₂, e₃, dW,
    wEnd⟩ := 𝔏
  dsimp only at hML hPL he hNs hMg hPm q₃
  subst hML hPL he hNs hMg hPm
  exact LLT25.own3_at_top_unpulled (At.seats Zp) oNo o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF)
    (At.arr Zp) dB dt (getL o Zp Np cF) (At.ms Zp Z.lay) ms₂ decT₁ decT₂ M₁ MS stOf bookOf
    Pm₀ (At.N Zp cF) Ns' fullLinks X r Ld (fun _ _ => none) At.c₀ c₁ k₁
    c₂ k₂ (restCap e₁) (restCap e₂) dW wEnd Rc hSig hRc hP hX hS hN row0B c₃ k₃ q₃

end P5J.L0

#print axioms P5J.L0.leads3_at
