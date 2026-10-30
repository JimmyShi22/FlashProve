-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontOwn.lean: the own group at the end of the first chain's
fold, and W's sending there.

  rows_claim          the text behind W's commitment hands the claim on
  ownMembers_at_end   under the head: every member of the own group is W or the index masks' message,
                      where the shape does not split the row (hsp)
  sendW_at_end        under the head: a message of W's sending that counts an answer has its count and
                      the public pad

Limits.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontMask
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontIndex
import Johnson.LPFK9R.ThreeK13Fields
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (sendAtS)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open Johnson.Desc.First.Walk.Tied (reach_of_fold)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The text behind W's commitment hands the claim on. -/
theorem rows_claim {Sh : Params.LinShape} {claim : LinClaim} {ids : Array ℕ}
    {d : VerifiableInference.Desc.K13.St} {o : LinFirst × VerifiableInference.Desc.K13.St}
    (h : VerifiableInference.Desc.K13.rows Sh claim ids d = .ok o) : o.1.claim = claim := by
  simp only [VerifiableInference.Desc.K13.Law.rows_is, VerifiableInference.Desc.K13.Law.bind_ok,
    VerifiableInference.Desc.K13.Law.there_ok, VerifiableInference.Desc.K13.Law.pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  rfl

/-- **Every member of the own group is W or the index masks' message.** -/
theorem ownMembers_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) {l : LinFirst}
    (hl : linAt e₁ = some l) (hsp : (whereOf Zp).lin.ownSplitNeeded = false) {G : Group}
    (hG : e₁.st.groups[l.own]? = some G) :
    ∀ o ∈ G.members.toList, o = l.w ∨ o = e₁.out.indexMasks := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf
  have hreach := reach_of_fold (bs := cF.blocksInOrder) (start := ProofFile.startS Zp) (z := pI) 358
    (by rw [hlen]) _ _ _ _ _ hfold
  have hmasks := LPFK9.masks_reached h.scope h.reads O 358 (pI, e₁) hreach
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  obtain ⟨m₁, l₁, o, owed, hs₀, hl₁, hrows, es⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  have OL := VerifiableInference.Desc.K13.Honest.rows_ownLaid hrows
  have ehere : e₁.here = .mem ⟨m₁.msg, m₁.ids, some o.1⟩ := by rw [es]
  have est : e₁.st = o.2.st := by rw [es]
  have ell : o.1 = l := by
    have : linAt e₁ = some o.1 := by
      unfold linAt
      rw [ehere]
    exact Option.some.inj (this.symm.trans hl)
  subst ell
  obtain ⟨G₀, hG₀, hmem⟩ := OL.own
  rw [est] at hG
  obtain rfl := Option.some.inj (hG.symm.trans hG₀)
  intro a ha
  rcases (hmem a).1 ha with e | e | ⟨e, -⟩
  · exact Or.inl e
  · refine Or.inr ?_
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 e
    have hrow : VerifiableInference.Desc.First.rowOfClaim o.1.claim ∈ e₁.rows := by
      unfold VerifiableInference.Desc.First.S.rows
      rw [ehere]
      exact List.mem_singleton.2 rfl
    have hon := (VerifiableInference.Desc.K13.Law.pileMasksC_iff e₁).1 hmasks _ hrow
    have hc := rows_claim hrows
    rw [← hc] at hm
    exact hon _ (List.mem_map.2 ⟨m, hm, rfl⟩)
  · rw [hsp] at e
    cases e

/-- **A message of W's sending that counts an answer, at the end of the first chain's fold.** -/
theorem sendW_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) {l : LinFirst}
    (hl : linAt e₁ = some l) :
    ∃ msg : Array OracleNotice, linMessageW Zp.first.lin = some msg ∧
      ∀ (k : ℕ) (n : OracleNotice), msg[k]? = some n → n.shape.answers ≠ 0 →
        ∃ y : OnBytes.Oracle, e₁.st.oracles[l.w + k]? = some y ∧ y.shape = n.shape ∧
          y.sampled = true ∧ y.spentAsMask = false ∧ y.sampleRows.size = y.shape.answers ∧
          ∃ p, VerifiableInference.Desc.Own.padMade e₁.st.codes y.shape = some p ∧
            y.pad = p.map fun q => (q.part, q.index) := by
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  refine ⟨msg, hmsg, fun k n hn hans => ?_⟩
  obtain ⟨ids, d', h3, e3, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
  have hr : ∃ a b, R₁ = [a, b] := by
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  have hsent : (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent = msg := by
    simp [VerifiableInference.Desc.K1.Par.sent, VerifiableInference.Desc.K1.parW]
  obtain ⟨hkl, hkn⟩ := List.getElem?_eq_some_iff.1 (by simpa using hn : msg.toList[k]? = some n)
  have hk : k < (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg)).length := by
    simpa [VerifiableInference.Desc.K1.shapesOf, hsent] using hkl
  have hsh : (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg))[k] = n.shape := by
    simp only [VerifiableInference.Desc.K1.shapesOf, hsent, List.getElem_map]
    rw [hkn]
  obtain ⟨y, hy, e₁', e₂, hsp₀, e₃, p, hp, e₄⟩ := decideSend_newWell _ _ _ _ _ _ h3 k hk
    (by rw [hsh]; exact hans)
  obtain ⟨m, hm₁, hsz, hI⟩ := VerifiableInference.Desc.K13.Law.sendAtS_idsLast _ t mid a b G₁ h1
  obtain ⟨m₀, l₀, hm₀, hl₀, hmask⟩ := VerifiableInference.Desc.K13.Law.rowsB_mask h2
  rw [hm₁] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  obtain ⟨ew, -, -⟩ := hmask hI
  obtain ⟨-, -, -, new, hnew, hlist⟩ := VerifiableInference.Desc.K13.Law.sendAtS_full _ t mid a b G₁ h1
  obtain ⟨m₁, l₁, o, owed, hs₀, -, hrows, es⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  have est : e₁.st = o.2.st := by rw [es]
  have hstay : MessagesStay mid.st o.2.st :=
    VerifiableInference.Desc.K13.rows_keeps groundKeeps_messages.quiet _ _ _ _ _ hrows
  have hsz₁ : mid.st.oracles.size = t.st.oracles.size + msg.size := by
    rw [← Array.length_toList, hlist, List.length_append, hnew, Array.length_toList, hsent]
  have hcnt : e₁.st.oracles.size = mid.st.oracles.size := by
    rw [est]
    exact (VerifiableInference.Desc.K13.Honest.rows_ownLaid hrows).count
  have hw : l₀.w = t.st.oracles.size := by
    rw [ew, hsz, hsent, hcnt, hsz₁]
    omega
  have hy' : mid.st.oracles[t.st.oracles.size + k]? = some y := by
    rw [e3]
    exact hy
  obtain ⟨z, hz, f₁, f₂⟩ := hstay.2 _ y hy'
  obtain ⟨g₁, g₂, g₃, g₄⟩ := f₂ e₂
  refine ⟨z, by rw [est, hw]; exact hz, f₁.trans (e₁'.trans hsh), g₁, g₄.trans hsp₀, ?_, p, ?_, ?_⟩
  · rw [g₃, f₁]
    exact e₃
  · rw [est, hstay.1, f₁, e3]
    exact hp
  · rw [g₂]
    exact e₄

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.rows_claim
#print axioms ProofFile.Honest.K12.AtFile.ownMembers_at_end
#print axioms ProofFile.Honest.K12.AtFile.sendW_at_end
