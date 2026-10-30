-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontEndMsgs.lean: W's and the mask's messages at the end of
the first chain's fold, in numerals, under the head AtMgA at the older hash.

  sendAtS_wr, wr_groups, wr_shape, wr_fresh   a message behind a sending, as the sending writes it
  msg_written      W's message has two notices
  atW_numbers      W is message 197, the mask message 198; W's only group is the own one; the mask's
                   message has no sample row, no pad and no group
  claimMask_at_end the claim has a mask entry

Premises: no mark at the end; the mask's message is not sampled there.

Limits.
- The full size alone.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontPlan
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrowLines
import Johnson.Desc.K13.Law.RowMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (sendAtS)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **A message behind a sending, as the sending writes it.** -/
theorem sendAtS_wr {Cl : Type} (P : VerifiableInference.Desc.K1.Par) (s mid : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok mid) (k : ℕ)
    (hk : k < (VerifiableInference.Desc.K1.shapesOf P).length) :
    ∃ (seeds : List (List E × E)) (ys : List E),
      mid.st.oracles[s.st.oracles.size + k]? = some (VerifiableInference.Desc.K1.wr P.codes seeds
        (s.st.oracles.size + k) (VerifiableInference.Desc.K1.shapesOf P)[k] ys) := by
  obtain ⟨ids, d', h1, e1, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok P s mid [r₁, r₂] gs h
  obtain ⟨⟨_, _, _, _, hf⟩, _, rfl⟩ :=
    (VerifiableInference.Desc.K1.decideSend_iff P _ _ d' r₁ r₂ ids).1 h1
  obtain ⟨ys', -, hget⟩ := VerifiableInference.Desc.K1.outs_spec P.codes
    (VerifiableInference.Desc.K1.seedsOf P r₁) P.seeds (VerifiableInference.Desc.K1.shapesOf P)
    (VerifiableInference.Desc.K1.stateOf s (#[] : Array ℕ)).st.oracles.size
    (VerifiableInference.Desc.K1.answersIn r₂) hf k hk
  refine ⟨VerifiableInference.Desc.K1.seedsOf P r₁, ys', ?_⟩
  rw [e1]
  show (_ ++ VerifiableInference.Desc.K1.outs _ _ _ _ _).toArray[(VerifiableInference.Desc.K1.stateOf s
    (#[] : Array ℕ)).st.oracles.size + k]? = _
  rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
  simpa using hget

theorem wr_groups (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape) (ys : List E) :
    (VerifiableInference.Desc.K1.wr codes seeds o s ys).groups = [] := by
  unfold VerifiableInference.Desc.K1.wr
  split <;> rfl

theorem wr_shape (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape) (ys : List E) :
    (VerifiableInference.Desc.K1.wr codes seeds o s ys).shape = s := by
  unfold VerifiableInference.Desc.K1.wr
  split <;> rfl

theorem wr_fresh (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape) (ys : List E)
    (h : s.answers = 0) : VerifiableInference.Desc.K1.wr codes seeds o s ys = { shape := s } := by
  unfold VerifiableInference.Desc.K1.wr
  rw [if_pos h]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem msg_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {msg : Array OracleNotice}
    (hm : linMessageW Zp.first.lin = some msg) : msg.size = 2 := by
  rw [lin_at_head h] at hm
  have hk : ((linMessageW proofSizedFull.batch.shape).any fun m => m.size == 2) = true := by
    decide +kernel
  rw [hm] at hk
  simpa using hk

/-- **What W's sending and the text behind it leave at the end of the first chain's fold.** -/
theorem atW_numbers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) {l : LinFirst} (hl : linAt e₁ = some l) :
    l.w = 197 ∧ l.mask = some 198 ∧
      (∃ y : OnBytes.Oracle, e₁.st.oracles[197]? = some y ∧ y.groups = [l.own]) ∧
      ((∀ y : OnBytes.Oracle, e₁.st.oracles[198]? = some y → y.sampled = false) →
        ∃ y : OnBytes.Oracle, e₁.st.oracles[198]? = some y ∧ y.sampleRows.size = 0 ∧ y.pad = [] ∧
          y.groups = [] ∧ y.sampled = false ∧ y.spentAsMask = false) := by
  have EW := endWritten h hf hm
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  obtain ⟨ids, d', h3, -, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
  have hr : ∃ a b, R₁ = [a, b] := by
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  have hsize := msg_written h hmsg
  have hsent : (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent = msg := by
    simp [VerifiableInference.Desc.K1.Par.sent, VerifiableInference.Desc.K1.parW]
  have B := VerifiableInference.Desc.K1.sendAtS_booked _ t mid a b G₁ h1
  obtain ⟨m, hm₁, hsz, hI⟩ := VerifiableInference.Desc.K13.Law.sendAtS_idsLast _ t mid a b G₁ h1
  obtain ⟨m₀, l₀, hm₀, hl₀, hmask⟩ := VerifiableInference.Desc.K13.Law.rowsB_mask h2
  rw [hm₁] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  obtain ⟨ew, em, -⟩ := hmask hI
  obtain ⟨m₁, l₁, o', owed, hs₀, -, hrows, es⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  have est : e₁.st = o'.2.st := by rw [es]
  have OL := VerifiableInference.Desc.K13.Honest.rows_ownLaid hrows
  have hcnt : e₁.st.oracles.size = mid.st.oracles.size := by
    rw [est]
    exact OL.count
  have hmsgs := B.msgs
  rw [hsent, hsize] at hmsgs
  have h199 := EW.msgs
  have ht : t.st.oracles.size = 197 := by omega
  have ehere : e₁.here = .mem ⟨m₁.msg, m₁.ids, some o'.1⟩ := by rw [es]
  obtain rfl : o'.1 = l₀ := by
    have : linAt e₁ = some o'.1 := by
      unfold linAt
      rw [ehere]
    exact Option.some.inj (this.symm.trans hl)
  have hw : o'.1.w = 197 := by
    rw [ew, hsz, hsent, hsize, hcnt, hmsgs, ht]
  have hm' : o'.1.mask = some 198 := by
    rw [em (ahead_at_head h), h199]
  have hlen : (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg)).length = 2 := by
    simp [VerifiableInference.Desc.K1.shapesOf, hsent, hsize]
  refine ⟨hw, hm', ?_, fun hn => ?_⟩
  · obtain ⟨seeds, ys, hy⟩ := sendAtS_wr _ t mid a b G₁ h1 0 (by omega)
    rw [ht] at hy
    obtain ⟨y, hy', -, eg⟩ := OL.inn 197 _ hy (Or.inl hw.symm)
    refine ⟨y, by rw [est]; exact hy', ?_⟩
    rw [eg, wr_groups]
    rfl
  · obtain ⟨seeds, ys, hy⟩ := sendAtS_wr _ t mid a b G₁ h1 1 (by omega)
    rw [ht] at hy
    have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
      rw [← Johnson.AtFull.Shape.flat_len h, List.take_length]
      exact hf
    have hpass : OpenRowsPass e₁.st := openRowsPass_reached h 358 0 pI rs cols (e₁, r₀, c₀) hfold
    have hsame : o'.2.st.oracles[198]? = mid.st.oracles[198]? := by
      refine OL.out 198 fun hM => ?_
      obtain ⟨G, hG, hmem⟩ := OL.own
      obtain ⟨y, hy', hs₁⟩ := hpass.1 _ G (by rw [est]; exact hG) 198 ((hmem 198).2 hM)
      rw [hn y hy'] at hs₁
      cases hs₁
    have hy₁ := hy
    change mid.st.oracles[198]? = _ at hy₁
    rw [← hsame, ← est] at hy₁
    have hsh := EW.shape 198 (by omega)
    rw [hy₁, msgs_written.2.2] at hsh
    have hs : (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.parW Zp.first
        { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg))[1]'(by omega) =
        maskMsg.shape := by
      have e := Option.some.inj hsh
      dsimp only at e
      rw [wr_shape] at e
      exact e
    rw [hs, wr_fresh _ _ _ _ _ rfl] at hy₁
    exact ⟨_, hy₁, rfl, rfl, rfl, rfl, rfl⟩

/-- **The claim at the end of the first chain's fold has a mask entry.** -/
theorem claimMask_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) {l : LinFirst}
    (hl : linAt e₁ = some l) : l.claim.masks.toList ≠ [] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, r₁, c₁, f1, hmsg, h1, h2⟩ := atW_of_fold₂ h hf
  obtain ⟨t₅, R₅, C₅, f₅⟩ := Meaning.K2.fold_back (k := 355) f1
  obtain ⟨-, -, ⟨b₀, b', e1, -, rfl, hla⟩, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 2 b₀ e1
  obtain ⟨rs₅, gs₅, d⟩ := Meaning.K2.fold_next q f₅ f1
  have hy := ((IM.yes_alone hla (by simp) t₅ t _ _).1 d).1
  have key : ∀ (R : List Fmt.RoundView) (G : List (List (ℕ × List UInt64))),
      (((IM.k13Dress Zp) : Block S Unit).retype (Cl' := ProofFile.Cl)).decide t₅ R G = .ok t →
      (VerifiableInference.Desc.K13.atM3 (Cl := Unit) (whereOf Zp)).decide t₅ R G = .ok t :=
    fun R G hh => hh
  obtain ⟨row, hrow, -, hne⟩ := VerifiableInference.Desc.K13.Law.rowMasks _ _ _ _ _ (key _ _ hy)
  have hr : ∃ a b, R₁ = [a, b] := by
    obtain ⟨ids, d', h3, -, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  have e₂ := (VerifiableInference.Desc.K1.sendAtS_rows _ t mid a b G₁ h1).2
  have e₃ := VerifiableInference.Desc.K13.Law.rowsB_rows h2
  have hend : e₁.rows = [row] := by rw [e₃, e₂, hrow]
  obtain ⟨a', ha, hl'⟩ : ∃ a', e₁.here = .mem a' ∧ a'.lin = some l := by
    unfold linAt at hl
    split at hl
    · rename_i a' ha
      exact ⟨a', ha, hl⟩
    · cases hl
  have hrows : e₁.rows = [VerifiableInference.Desc.First.rowOfClaim l.claim] := by
    unfold VerifiableInference.Desc.First.S.rows
    rw [ha]
    simp only [hl']
  have e := hend.symm.trans hrows
  obtain rfl := List.head_eq_of_cons_eq e
  intro hz
  apply hne
  simp [VerifiableInference.Desc.First.rowOfClaim, hz]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.claimMask_at_end
#print axioms ProofFile.Honest.K12.AtFile.sendAtS_wr
#print axioms ProofFile.Honest.K12.AtFile.atW_numbers
