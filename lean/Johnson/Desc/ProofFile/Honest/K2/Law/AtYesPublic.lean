-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AtYesPublic.lean: the kind "the code switch" (K2): SEVEN OF THE
TWENTY-ONE FIELDS OF THE RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), IN THE
RECORD's OWN TEXT, UNDER THE LIBRARY's HEAD AND THE OPENING, AT A SWITCH OF THE PLAN, AT A STATE
THAT THE VERIFIER's OWN FOLD OVER THE MEMBERS IN FRONT RETURNS: tables · groupRows · lengths · logC
· logZ · first · count. ALL SEVEN ARE PUBLIC. IT DOES NOT SAY THAT THE RECORD IS MET: fourteen
fields are not spoken of, the four on values among them. That file is not imported: the fields'
texts are copied. No definition; one closed fact by evaluation in Lean's kernel; lemmas: calls.

  `arm_after_kept`  the place's step behind keeps the tables and every group's open rows: by
                    `SwitchArm`, from the library's `out_opened`, `out_head`, `out_finish`
  `logsW`, `logs_le`   BY LEAN's KERNEL (no control): every written code's log-length is at most 32;
                    so at every number, also beyond the lists
  `seven_at_yes`    THE END

By, sealed, of other authors: `KeepsOut`, `Kept` (Johnson/Top/H0/K2Caller/DoorKeeps.lean) and the
three named (Johnson/P1K2R/SitsDoor.lean) · `AtYes` (Johnson/Top/H0/K2Hears/Whole.lean) ·
`front_tables` (K2Hears/SampleGood.lean) · `frontOf_iff` (Johnson/Top/H0/Tw/K2C/DebtsState.lean) ·
`notices_size` (Johnson/Top/H0/K2Hands/AtYes.lean). Ours: `SwitchArm`
(Honest/K2/Law/BlockAtHead.lean) · `fence_at_fold`, `arm_before` (SendsAtThread.lean) ·
`codes_switch`, `codesW`, `port_switch` (PublicMoreAtHead.lean) · `place_nums` (SentIsBlocks.lean) ·
`sendingPar_sent` (Counts.lean).

Limits. PUBLIC: codes, counts, tables' shapes, open rows: no coin, input or run occurs. THAT THERE
IS A YES IS A PREMISE (`AtYes`). The full size and the format's second hash function alone. The head and the
opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SendsAtThread
import Johnson.Top.H0.K2Hears.SampleGood
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H0.Tw.K2C.DebtsState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes SameTables front_tables frontOf_iff notices_size)
open VerifiableInference.Desc.First.K2Caller (Kept)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The place's step behind keeps the tables and every group's open rows.** -/
theorem arm_after_kept {Zp : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace} {st : First.K2.At}
    {before : S → Except String S} {after : S → S → Except String S} {s₁ u t : S}
    (hA : SwitchArm Zp G p st before after) (ha : after s₁ u = .ok t) : Kept u t := by
  rcases hA with ⟨-, -, -, -, -, -, fs, f, hfs, hff, -, rfl⟩ | ⟨-, -, -, -, HP, -, rfl⟩ |
    ⟨-, -, -, -, rfl⟩
  · exact P1K2.out_opened hfs hff s₁ u t ha
  · exact P1K2.out_head HP s₁ u t ha
  · exact P1K2.out_finish s₁ u t ha

set_option maxRecDepth 1000000 in
/-- Every written code's log-length is at most 32. -/
theorem logsW : (codesFull2.base.all fun c => decide (c.logN ≤ 32)) = true ∧
    (codesFull2.mask.all fun c => decide (c.logN ≤ 32)) = true := by
  decide +kernel

/-- So at every number, also beyond the list. -/
theorem logs_le {a : Array Code} (h : (a.all fun c => decide (c.logN ≤ 32)) = true) (i : Nat) :
    (a.getD i default).logN ≤ 32 := by
  rw [Array.getD_eq_getD_getElem?]
  cases e : a[i]? with
  | none => exact Nat.zero_le _
  | some c =>
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 e
    exact of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 h _ (Array.getElem_mem hi))

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **SEVEN FIELDS OF `MadeAsks`, IN ITS OWN TEXT**: tables · groupRows · lengths · logC · logZ ·
first · count, at Pr := the place's sending. hf: the verifier's own fold over the members in front
returns s. -/
theorem seven_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) {st : First.K2.At}
    {before : TS → Except String TS} {after : TS → TS → Except String TS}
    (hA : SwitchArm Zp Bs.G₀ p st before after)
    {z₀ : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {s s₁ t s' : TS}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (P5J.At.ps.findIdx (· == p.place))) (ProofFile.startS Zp z₀) R C =
      .ok (s, [], [])) (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    (ha : after s₁ t = .ok s') :
    SameTables t.st s'.st ∧
      (s'.st.groups[x.f.group]?).map (·.rows) = (t.st.groups[x.f.group]?).map (·.rows) ∧
      S3.codes.lengthsOk = true ∧
      (S3.codes.base.getD x.f.rows.code default).logN ≤ 32 ∧
      (S3.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32 ∧
      x.st.oracles.size = s.st.oracles.size ∧
      1 + x.T.kept.size ≤ (switchPar p).sent.size := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  obtain ⟨F1, F2⟩ := fence_at_fold h O hP hn hA hf hb nm
  obtain ⟨K1', K2'⟩ := arm_after_kept hA ha
  obtain ⟨e1, e2⟩ := front_tables A.front
  have hcod : S3.codes = (switchPar p).codes := by
    rw [A.same.codes, A.sent.codes, e1, F2]
    exact (codes_switch h O hp).symm
  have hfull : (switchPar p).codes = codesFull2 :=
    of_decide_eq_true (List.all_eq_true.1 codesW p hpW)
  have hport := port_switch h O hp
  unfold K1.condPort at hport
  rw [Bool.and_eq_true, Bool.and_eq_true] at hport
  refine ⟨K1', K2' _, by rw [hcod]; exact hport.1.2, ?_, ?_, ?_, ?_⟩
  · rw [hcod, hfull]
    exact logs_le logsW.1 _
  · rw [hcod, hfull]
    exact logs_le logsW.2 _
  · rw [e2]
    exact (arm_before hA hb).2.1
  · have e := F1 x (frontOf_iff.2 A.front)
    have e' : (switchPar p).sent = _root_.Tw.K2.switchNotices x.T x.others := by
      rw [e, place_nums hP hp hn]
      exact sendingPar_sent _ _
    rw [e', notices_size]
    omega

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.arm_after_kept
#print axioms ProofFile.Honest.K2.Law.logsW
#print axioms ProofFile.Honest.K2.Law.logs_le
#print axioms ProofFile.Honest.K2.Law.seven_at_yes
