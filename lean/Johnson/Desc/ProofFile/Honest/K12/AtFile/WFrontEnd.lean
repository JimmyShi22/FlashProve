-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontEnd.lean: the three tests that read the rows, on entry
to the last chain's own test, under the head AtMgA at the older hash, from the folds of the two
earlier chains. The first chain's flat list has 358 members (flat_len): its fold here is the whole
list, bare, as EndsAre (WDoor.lean) holds it.

  sharedGood_at_end   the shared chain's fold keeps SharedGood from its first state
  tidy_of_fold        behind the whole first list the statement is tidy
  rows_at_folds       the statement, from SharedGood at the shared chain's record
  rows_at_file        the statement at the proof file's own description, with the folds and the start
                      as the description has them: every premise of rows_at_own (WFrontAsks.lean) is
                      paid

Premises.
- Both: hv: the rounds of the first chain's fold have their drawn elements in canonical form, no word
  on the columns. hf₁: the first fold. h₁, h₂: the block "K14, second part" and the way in.
- rows_at_folds: hG: SharedGood at the record d. hE: ended d = some e₂. h₀: the start at the two ends.
- rows_at_file: hf₂: the shared chain's fold. hs: the description's start of the last chain.

Limits.
- That a thread's stand meets these premises is not typed here.
- Nothing on the public test on the shape, nothing on a value of a row but what these three tests
  read. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontAsks
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontSamples
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontShared
import Johnson.Desc.AtSeats.Fit.TidyPaid
import Johnson.Desc.Tidy.Border2
import Johnson.P2R0R.SizedIsRead
import Johnson.Loose.H2K12.LaterSeatsN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open OnBytes.Slice.ProxRun (DenseRow)
open OnBytes.Means (Tidy InOrder)
open VerifiableInference.Desc (Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (OkDrawn)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart startAtEnds sharedOfEnd firstOfS)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open ProofFile.Honest.Sh (claimsB)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The shared chain's last record**, from its first, under the head. -/
theorem sharedGood_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (key : OnBytes.TableKey)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : Desc.K14.St × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 ((Desc.K14.chainOf Zp.p.chains
        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
        (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last).retype
        (Cl' := ProofFile.Cl)).blocksInOrder
      (Desc.K14.first (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes key) rs cols =
      .ok out) : SharedGood out.1.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hplan := (VerifiableInference.Desc.FileDescription.planOk_ok _).1 h.laid.planOk
  have hl : (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes.lengthsOk = true := by
    have hpl : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (Desc.K14.Law.seatZ Zp Np)
        (Desc.K14.Law.secondAt Zp Np) (fun s => s) (ProofFile.startS Zp) cF).planOk = true := by
      rw [← O.desc]
      exact h.laid.planOk
    rw [← P2R0.codes_p14Of O.pub (P2R0.front2_at_planOk _ _ _ _ _ _ _ _ _ _ _ _ _ hpl)]
    exact VerifiableInference.Desc.K13.Law.lengthsOk_of_pub O.pub
  exact carried_fold_shared _ _ Np (fun b hb => (hplan.blocks₂ b hb).1) 0 _ rs cols out hf
    (sharedGood_first _ key hl)

/-- **Behind the whole first list the statement is tidy.** -/
theorem tidy_of_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {r₁ r₀ : List Fmt.RoundView} {c₁ c₀ : List OpenedColumn}
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀)) : Tidy e₁.st := by
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf₁
  have hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 358 (pI, e₁) :=
    reach_of_fold 358 (by rw [hlen]) _ _ _ _ _ hfold
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Z', A', B', c', hZ', e', K⟩ := Meaning.K2.tidy_paid h.laid.value h.laid.planOk
  obtain rfl : Zp = Z' := Except.ok.inj (O.pub.symm.trans hZ')
  obtain rfl : cF = c' := P1K2.chain_of_desc (O.desc.symm.trans e')
  exact K 358 (pI, e₁) hreach

/-- **The three tests that read the rows at the last chain's own test**, from the two folds. -/
theorem rows_at_folds {Cl XiPub : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {pI : ProofFile.InstPub} {e₁ : S} {r₁ r₀ : List Fmt.RoundView} {c₁ c₀ : List OpenedColumn} (hv : ∀ y ∈ r₁, OkDrawn y)
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀)) (p : P₁₄) (ξ : XiPub)
    {d : Desc.K14.St} (hG : SharedGood d.st) {e₂ : Proof.SharedEnd}
    (hE : Desc.K14.ended d = some e₂) {s₀ s : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {t : T12} (h₀ : startAtEnds p ξ e₁ e₂ = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t) :
    stTidyB t.st = true ∧
      (∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r) ∧
      claimsB t = true := by
  have h0' : (match firstOfS e₁ with
      | none => Except.error "the first chain's end names no W"
      | some f => VerifiableInference.Desc.Third.start₃E p.codes p.S f.st f.book f.roots f.w f.own
          f.mask f.pending (sharedOfEnd e₂)) = .ok s₀ := h₀
  split at h0'
  · cases h0'
  · rename_i f hfo
    have hst : f.st = e₁.st := by
      unfold firstOfS at hfo
      cases he : e₁.firstEnd? with
      | none =>
        rw [he] at hfo
        cases hfo
      | some e =>
        rw [he] at hfo
        rw [← Option.some.inj hfo]
    have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
    have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀) := by
      rw [← hlen, List.take_length]
      exact hf₁
    have hT : Tidy f.st := by
      rw [hst]
      exact tidy_of_fold h hf₁
    have hA : OpenRowsPass f.st := by
      rw [hst]
      exact openRowsPass_reached h 358 0 pI r₁ c₁ (e₁, r₀, c₀) hfold
    have hO : Johnson.AtFull.Shape.OpenOrd f.st := by
      rw [hst]
      exact Johnson.AtFull.Shape.openOrd_reached h 358 0 pI r₁ c₁ (e₁, r₀, c₀) hfold
    have e₀ : s₀.st = e₁.st := by
      rw [VerifiableInference.Desc.Third.Law.start₃E_st _ _ _ _ _ _ _ _ _ _ _ h0', hst]
    have hst₂ : e₂.st = d.st := Desc.K14.ended_st hE
    obtain ⟨-, hTd, hRd⟩ := hG
    have hP₂ := samplesPlain_of_good (T := d.st) hRd
    exact rows_at_own p h0' h₁ h₂ hT (by show InOrder e₂.st; rw [hst₂]; exact hTd.inOrder) hA hO
      (fun _ _ m _ y hy row hrow =>
        samplesPlain_of_good (sampleGood_of_fold h hv hf₁) m y (by rw [← e₀]; exact hy) row hrow)
      (fun y hy row hrow => hP₂ _ y (by
        have hy' : e₂.st.oracles[e₂.lin.omega]? = some y := hy
        rw [hst₂] at hy'
        exact hy') row hrow)

/-- **The same at the proof file's own description**: two folds as EndsAre (WDoor.lean) holds them, and
the description's start of the last chain at their ends. -/
theorem rows_at_file {Cl : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pI : ProofFile.InstPub)
    {e₁ : S} {d : Desc.K14.St} {r₁ r₀ r₂ u : List Fmt.RoundView} {c₁ c₀ c₂ v : List OpenedColumn}
    (hv : ∀ y ∈ r₁, OkDrawn y)
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀))
    (hf₂ : foldBlocks 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ pI) r₂ c₂ = .ok (d, u, v)) {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) (H2K.JointK.p₁₄N Zp)).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok t) :
    stTidyB t.st = true ∧
      (∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r) ∧
      claimsB t = true := by
  have hG : SharedGood d.st := sharedGood_at_end h pI.key hf₂
  have hs' : (if !e₁.fin then (.error "the first chain does not stand at its end" :
        Except String S₃)
      else
        match Desc.K14.ended d with
        | none => .error "the shared chain has not ended"
        | some e => startAtEnds (H2K.JointK.p₁₄N Zp) pI e₁ e) = .ok s₀ := hs
  split at hs'
  · cases hs'
  · split at hs'
    · cases hs'
    · rename_i E₂ hE
      exact rows_at_folds h hv hf₁ _ pI hG hE hs' h₁ h₂

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.tidy_of_fold
#print axioms ProofFile.Honest.K12.AtFile.rows_at_file
#print axioms ProofFile.Honest.K12.AtFile.sharedGood_at_end
#print axioms ProofFile.Honest.K12.AtFile.rows_at_folds
