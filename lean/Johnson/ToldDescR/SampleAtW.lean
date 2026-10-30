-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SampleAtW.lean: no soundness is claimed.
The premise E₂ of sampleTwoB_last_end | sampleTwoB_h4 (SampleTwoEnd.lean: at border 357 the test accepts W's message), carried from the seated sub-protocol's wrapped step to kind K1's own decision, where the earning (P2Law.sampleAtB_behind_ok, Johnson/P2LawR/SampleBehindOk.lean) speaks.
hSend has in front: the rounds fit · every factor's words are below the prime. Both come off the wrapped step. At every two rounds at which K1's decision accepts it would ask more than the earning can give: at a draw that does not fit, or at a factor whose words spell the prime, the decision may accept while the test rejects.
  at_356_fit     in scope, at the opening: a step's accept at c.blocksInOrder[356] is K13.atM4 (whereOf Z) w's decision's at the step's own rounds (digests struck), and these fit that sub-protocol's declared rounds (at_356, Johnson/IMR/LastFour.lean, ends in «∃ rs' gs»; the same road: back_of · back_numbers · yes_alone, with step_inv's first clause kept)
  **e2_of_send**  HandsBackB c.blocksInOrder Rc · hCount (at 356, fenced) · hSend ⇒ ∀ z s', Rc 357 (z, s') → sampleAtB cs sh s'.st nW = true
Does not show. hSend · hCount. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SmpWalk
import Johnson.ToldDescR.HandsBackB
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.K1.Law.OkView
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- A step's accept at W's sending, at the step's own rounds. -/
theorem at_356_fit (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[356]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) :
    ∃ w, K13.wBlock Z = some w ∧
      roundsFit (K13.atM4 (K13.whereOf Z) w : Block S Unit).rounds rs = true ∧
      ∃ gs, (K13.atM4 (K13.whereOf Z) w : Block S Unit).decide s (rs.map noDigest) gs = .ok s' := by
  obtain ⟨-, -, -, ⟨b3, b3', w, e3, -, hw, rfl, hla⟩⟩ := IM.back_of O
  obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 3 b3 e3).symm.trans hb)
  obtain ⟨hfit, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft _ s s' rs cols n hy
  obtain ⟨h1, -, -⟩ := (IM.yes_alone hla (by decide) s s' _ _).1 hd
  refine ⟨w, hw, ?_, _, h1⟩
  have e : b3.rounds = (K13.atM4 (K13.whereOf Z) w : Block S Unit).rounds := by
    rw [hla]
    rfl
  rw [← e]
  exact hfit

/-- **E₂, from kind K1's own decision at W's sending.** -/
theorem e2_of_send (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp : Type}
    {Rc : ℕ → Pp × S → Prop} (hb : HandsBackB c.blocksInOrder Rc) {cs : Codes} {sh : OracleShape} {nW : ℕ}
    (hCount : ∀ z s₁, Rc 356 (z, s₁) → s₁.failed = none → s₁.st.oracles.size = nW)
    (hSend : ∀ msg (s : S) (r₁ r₂ : Fmt.RoundView) ids d', linMessageW Z.first.lin = some msg →
      roundsFit (K1.rounds
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg))
        [r₁, r₂] = true →
      (∀ x ∈ K1.seedsOf
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) r₁,
        okE x.2 = true) →
      K1.decideSend (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)
        (K1.owedOf s) (K1.stateOf s (#[] : Array Nat)) [r₁, r₂] = .ok (ids, d') →
      sampleAtB cs sh d'.st s.st.oracles.size = true) :
    ∀ z s', Rc 357 (z, s') → sampleAtB cs sh s'.st nW = true := by
  intro z s' h
  obtain ⟨s₁, b₁, f1, R1, c1, m1, r1, hb1, y1⟩ := hb 356 z s' h
  obtain ⟨s₀, b₀, f0, R0, c0, m0, -, hb0, y0⟩ := hb.plain 355 z s₁ r1
  have hm : s₁.failed = none := (IM.at_355 hS hR O hb0 y0).2.1
  obtain ⟨y1', cv, hv⟩ := below_step y1
  obtain ⟨w, hw, hfit, gs, hd⟩ := at_356_fit hS hR O hb1 y1'
  obtain ⟨msg, hmsg, rfl⟩ := (K13.Law.wAt_is _ _ _ w).1 hw
  have hl := Keeps.fit_length _ _ hfit
  obtain ⟨q₁, q₂, rfl⟩ : ∃ q₁ q₂, R1 = [q₁, q₂] := by
    match R1, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨m, g₁, rs₂, g₂, h1, h2⟩ := K13.Law.atM4_mid hd
  obtain ⟨ids, d', hdS, est, -⟩ := K1.sendAtS_ok _ s₁ m _ g₁ h1
  have a := hSend msg s₁ (noDigest q₁) (noDigest q₂) ids d' hmsg hfit
    (K1.okView_factors _ _ _ (by simp) hv) hdS
  rw [← est, hCount z s₁ r1 hm] at a
  have k : SmpStay m.st s'.st :=
    K13.rowsB_keeps groundKeeps_smpStay.quiet K13.atS _ K13.atS_lensSt _ m _ _ s' h2
  exact sampleAtB_stay a k

end

end ToldDesc

#print axioms ToldDesc.at_356_fit
#print axioms ToldDesc.e2_of_send
