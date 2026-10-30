-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontFile.lean: the front's clauses on the own group, at the
proof file's own description, from the two chains' folds.

  startParts, start_noMark   the description's start of the last chain, taken apart
  firstOfS_parts   what the first chain's last record hands on
  wellSampled_at_end   the shared chain's fold
  frontL_at_file   the statement

Premises, beside the two folds, the start, the block and the way in.
- hix: IndexIs: indexMasks_at_end (WFrontEndIs.lean) pays it.
- htrees: the trees of the members and of the mask.

The head is AtMgA at the older hash.

Limits.
- frontL_at_file is one conjunct of what frontFive_at_own (WFrontAtOwn.lean) gives at the written
  parameters; it stands for the form with the trees as a premise.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontFit
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEnd
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open OnBytes.Means (Tidy)
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.K12 (T12 frontL)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart start₃E startAtEnds sharedOfEnd firstOfS
  FirstEnd₃)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The description's start of the last chain, taken apart.** -/
theorem startParts {pI : ProofFile.InstPub} {e₁ : S} {d : Desc.K14.St} {s₀ : S₃}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀) :
    ∃ (E₂ : Proof.SharedEnd) (f : FirstEnd₃), Desc.K14.ended d = some E₂ ∧ firstOfS e₁ = some f ∧
      start₃E (H2K.JointK.p₁₄N Zp).codes (H2K.JointK.p₁₄N Zp).S f.st f.book f.roots f.w f.own f.mask
        f.pending (sharedOfEnd E₂) = .ok s₀ := by
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
      have h0' : (match firstOfS e₁ with
          | none => Except.error "the first chain's end names no W"
          | some f => start₃E (H2K.JointK.p₁₄N Zp).codes (H2K.JointK.p₁₄N Zp).S f.st f.book f.roots
              f.w f.own f.mask f.pending (sharedOfEnd E₂)) = .ok s₀ := hs'
      split at h0'
      · cases h0'
      · rename_i f hfo
        exact ⟨E₂, f, hE, hfo, h0'⟩

/-- **A yes of the start has no mark at the first chain's end.** -/
theorem start_noMark {pI : ProofFile.InstPub} {e₁ : S} {d : Desc.K14.St} {s₀ : S₃}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀) : e₁.failed = none := by
  have hs' : (if !e₁.fin then (.error "the first chain does not stand at its end" :
        Except String S₃)
      else
        match Desc.K14.ended d with
        | none => .error "the shared chain has not ended"
        | some e => startAtEnds (H2K.JointK.p₁₄N Zp) pI e₁ e) = .ok s₀ := hs
  split at hs'
  · cases hs'
  · rename_i hc
    have hfin : e₁.fin = true := by simpa using hc
    unfold VerifiableInference.Desc.First.S.fin at hfin
    simp only [Bool.and_eq_true] at hfin
    exact Option.isNone_iff_eq_none.1 hfin.1.1

/-- **What the first chain's last record hands on.** -/
theorem firstOfS_parts {e₁ : S} {f : FirstEnd₃} (h : firstOfS e₁ = some f) :
    ∃ l : LinFirst, linAt e₁ = some l ∧ f.st = e₁.st ∧ f.book = e₁.book ∧ f.own = l.own ∧
      f.w = l.w ∧ f.mask = l.mask := by
  unfold firstOfS at h
  cases he : e₁.firstEnd? with
  | none =>
    rw [he] at h
    cases h
  | some e =>
    rw [he] at h
    obtain rfl := Option.some.inj h
    unfold S.firstEnd? at he
    split at he
    · rename_i a ha
      obtain ⟨l, hl, hw⟩ := Option.bind_eq_some_iff.1 he
      split at hw
      · obtain rfl := Option.some.inj hw
        refine ⟨l, ?_, rfl, rfl, rfl, rfl, rfl⟩
        unfold linAt
        rw [ha]
        exact hl
      · cases hw
    · cases he

/-- **Behind the shared chain's fold every sampled message has its count and the public pad.** -/
theorem wellSampled_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (key : OnBytes.TableKey)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : Desc.K14.St × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 ((Desc.K14.chainOf Zp.p.chains
        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
        (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last).retype
        (Cl' := ProofFile.Cl)).blocksInOrder
      (Desc.K14.first (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes key) rs cols =
      .ok out) : WellSampled out.1.st := by
  have hplan := (VerifiableInference.Desc.FileDescription.planOk_ok _).1 h.laid.planOk
  exact carried_fold_well _ _ Np (fun b hb => (hplan.blocks₂ b hb).1) 0 _ rs cols out hf
    (wellSampled_first _ key)

/-- **The front's clauses on the own group**, at the proof file's own description. -/
theorem frontL_at_file {Cl : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pI : ProofFile.InstPub)
    {e₁ : S} {d : Desc.K14.St} {r₁ r₀ r₂ u : List Fmt.RoundView} {c₁ c₀ c₂ v : List OpenedColumn}
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀))
    (hf₂ : foldBlocks 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ pI) r₂ c₂ = .ok (d, u, v)) {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) (H2K.JointK.p₁₄N Zp)).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok t) (hix : IndexIs Zp e₁)
    (htrees : ∀ G, t.st.groups[t.g]? = some G → ∀ o ∈ G.members.toList ++ t.mask.toList,
      ∃ (q : ℕ × ℕ) (T : OnBytes.Tree), t.book.place[o]? = some q ∧ t.book.trees[q.1]? = some T ∧
        (T.oneList = false ∨ T.lists = 0)) :
    ok (frontL t.st t.book t.g t.mask) = true := by
  obtain ⟨E₂, f, hE, hfo, h0⟩ := startParts hs
  obtain ⟨l, hl, e1, e2, e3, e4, e5⟩ := firstOfS_parts hfo
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf₁
  obtain ⟨id, hmask⟩ := maskNamed_at_end h hf₁ hl
  rw [e5, hmask] at h0
  have hF : MembersFacts e₁.st := membersFacts_reached h 358 0 pI r₁ c₁ (e₁, r₀, c₀) hfold
  have hG : SharedGood d.st := sharedGood_at_end h pI.key hf₂
  have hWd : WellSampled d.st := wellSampled_at_end h pI.key hf₂
  have hst₂ : E₂.st = d.st := Desc.K14.ended_st hE
  obtain ⟨msg, n, y, -, -, hy, -, m3⟩ := maskMessage_at_end h hf₁ hl hmask fun y hy =>
    (mask_of_start h0 (by rw [e1]; exact hy)).1
  have hI₂ : OnBytes.Means.InOrder (sharedOfEnd E₂).st := by
    show OnBytes.Means.InOrder E₂.st
    rw [hst₂]
    exact hG.2.1.inOrder
  have hΩ : WellSampled (sharedOfEnd E₂).st := by
    show WellSampled E₂.st
    rw [hst₂]
    exact hWd
  refine frontL_at_own _ h0 h₁ h₂ (by rw [e1]; exact tidy_of_fold h hf₁) hI₂
    (by rw [e1]; exact hF) (by rw [e1]; exact hy) m3 fun G hGt => ?_
  have hfit := membersFit_at_own _ h0 h₁ h₂ (fun G₁ hG₁ => by
      rw [e3, e1] at hG₁
      rw [e1]
      exact ownFit_at_end h hf₁ hl (split_at_head h) hix (wNotice_at_head h)
        (indexNotice_at_head h) hG₁)
    (by rw [e1]; exact hF.1) hΩ G hGt
  exact ⟨fun o ho y hy => (hfit o ho y hy).1, fun o ho y hy => (hfit o ho y hy).2,
    htrees G hGt⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.frontL_at_file
#print axioms ProofFile.Honest.K12.AtFile.startParts
#print axioms ProofFile.Honest.K12.AtFile.firstOfS_parts
