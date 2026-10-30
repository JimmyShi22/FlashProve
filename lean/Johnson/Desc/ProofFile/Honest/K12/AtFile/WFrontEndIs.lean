-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontEndIs.lean: the first chain's last record against the
closed shape narrowW, under the head AtMgA at the older hash: the messages 4, 197, 198, the own group.

  strip_of         two messages that agree in what the tests read
  indexMasks_at_end   the index masks' message is number 4, by the group's codes
  EndIs            what holds of the statement and the own group
  endIs            it holds at the end of the first chain's fold

Premises of endIs: no mark at the end; the mask's message is not sampled there.

Limits.
- Nothing on the trees: WFrontEndTrees.lean.
- The full size alone.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEndMsgs
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontOwnGroup
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- Two messages that agree in what the tests read. -/
theorem strip_of (y : OnBytes.Oracle) (m : OrcSh) (h1 : y.shape = m.shape) (h2 : y.sampled = m.sampled)
    (h3 : y.sampleRows.size = m.rows) (h4 : y.pad = m.pad) (h5 : y.spentAsMask = m.spent) :
    strip (orcSh y) = strip m := by
  cases m
  simp only [strip, orcSh] at *
  rw [h1, h2, h3, h4, h5]

/-- A rising list of two members. -/
theorem rising_two {a b : ℕ} (hab : a < b) : ∀ {l : List ℕ}, l.Pairwise (· < ·) →
    (∀ o, o ∈ l ↔ o = a ∨ o = b) → l = [a, b]
  | [], _, h => by
    have := (h a).2 (Or.inl rfl)
    cases this
  | [x], _, h => by
    have e₁ := List.mem_singleton.1 ((h a).2 (Or.inl rfl))
    have e₂ := List.mem_singleton.1 ((h b).2 (Or.inr rfl))
    omega
  | x :: y :: r, hp, h => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hp
    obtain ⟨h3, h4⟩ := List.pairwise_cons.1 h2
    have hxy := h1 y List.mem_cons_self
    have ex := (h x).1 List.mem_cons_self
    have ey := (h y).1 (List.mem_cons_of_mem _ List.mem_cons_self)
    have e₁ : x = a := by omega
    have e₂ : y = b := by omega
    subst e₁ e₂
    cases r with
    | nil => rfl
    | cons z r =>
      have hz := (h z).1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have h₁ := h1 z (List.mem_cons_of_mem _ List.mem_cons_self)
      have h₂ := h3 z List.mem_cons_self
      omega

/-- **What holds of the first chain's last statement.** g: the own group. -/
structure EndIs (st : Statement) (g : ℕ) : Prop where
  codes : st.codes = H2K.Member.codesFull
  msg₄ : ∃ y : OnBytes.Oracle, st.oracles[4]? = some y ∧ strip (orcSh y) = strip indexMsg
  msg₁₉₇ : ∃ y : OnBytes.Oracle, st.oracles[197]? = some y ∧ strip (orcSh y) = strip wMsg ∧
    y.groups = [g]
  msg₁₉₈ : ∃ y : OnBytes.Oracle, st.oracles[198]? = some y ∧ strip (orcSh y) = strip maskMsg
  group : ∃ (G : Group) (row : OnBytes.Row), st.groups[g]? = some G ∧ G.code = 11 ∧ G.maskCode = 12 ∧
    G.inRun = false ∧ G.members.toList = [4, 197] ∧ G.kept.toList = [false, false] ∧
    G.rows = #[row] ∧ row.kind = .plain

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem sent_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (VerifiableInference.Desc.K1.firstPar Zp.first (VerifiableInference.Desc.K1.gpOf Zp)).sent.size =
      5 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := Johnson.AtFull.Shape.firstPar_at_head h.toAtMg O
  rw [O.first] at e
  rw [e]
  decide +kernel

theorem codes_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) : e₁.st.codes = H2K.Member.codesFull := by
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf
  have hreach := reach_of_fold (bs := cF.blocksInOrder) (start := ProofFile.startS Zp) (z := pI) 358
    (by rw [hlen]) _ _ _ _ _ hfold
  have h' := h.toAtMg
  have F := ProofFile.Honest.FirstThread.foldFacts_raw h'
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ e => e) (P5J.laid_at_head h') (P5J.startB_at_head h')
    (P5J.sendsB_of_madeRow h' (P5J.madeRow_at_head h'))
  have Wr := H2K12.written354_of_pins h'.scope h'.laid.pub h'.pins.1
    (h'.laid.run ▸ LPFD.Full.laidPOf_of h'.laid.value h'.laid.planOk h'.laid.data h'.laid.asks)
  have e : e₁.st.codes = Zp.first.codes := F.codes 358 (pI, e₁) hreach hm
  rw [e, Wr.codes]
  exact codes_written

theorem own_codes : proofSizedFull.batch.shape.w.code = 11 ∧
    proofSizedFull.batch.shape.ownMaskCode = 12 := by
  decide +kernel

/-- **The index masks' message is number 4**: it is a member of the own group, so it sits under the
group's codes; of the written messages three do; the mask is not sampled, and W is no mask of the
claim's. -/
theorem indexMasks_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) {l : LinFirst} (hl : linAt e₁ = some l)
    (hn : ∀ y : OnBytes.Oracle, e₁.st.oracles[198]? = some y → y.sampled = false) :
    e₁.out.indexMasks = 4 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have EW := endWritten h hf hm
  obtain ⟨hw, -, -, -⟩ := atW_numbers h hf hm hl
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf
  have hreach := reach_of_fold (bs := cF.blocksInOrder) (start := ProofFile.startS Zp) (z := pI) 358
    (by rw [hlen]) _ _ _ _ _ hfold
  have hmasks := LPFK9.masks_reached h.scope h.reads O 358 (pI, e₁) hreach
  have hF : MembersFacts e₁.st := membersFacts_reached h 358 0 pI rs cols (e₁, r₀, c₀) hfold
  have hT : OnBytes.Means.Tidy e₁.st := tidy_of_fold h hf
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
  obtain ⟨G, row, hG, c1, c2, -, -, -, -⟩ := rows_group hrows (split_at_head h)
  have hlin : (whereOf Zp).lin = proofSizedFull.batch.shape := lin_at_head h
  rw [hlin] at c1 c2
  rw [own_codes.1] at c1
  rw [own_codes.2] at c2
  have hG' : e₁.st.groups[o.1.own]? = some G := by
    rw [est]
    exact hG
  obtain ⟨G₀, hG₀, hmem⟩ := OL.own
  obtain rfl := Option.some.inj (hG.symm.trans hG₀)
  have hne := claimMask_at_end h hf hl
  obtain ⟨m, hm'⟩ := List.exists_mem_of_ne_nil _ hne
  have hc := rows_claim hrows
  have hrow : VerifiableInference.Desc.First.rowOfClaim o.1.claim ∈ e₁.rows := by
    unfold VerifiableInference.Desc.First.S.rows
    rw [ehere]
    exact List.mem_singleton.2 rfl
  have hon : m.oracle = e₁.out.indexMasks :=
    (VerifiableInference.Desc.K13.Law.pileMasksC_iff e₁).1 hmasks _ hrow _
      (List.mem_map.2 ⟨m, hm', rfl⟩)
  have him : e₁.out.indexMasks ∈ G.members.toList := by
    refine (hmem _).2 (Or.inr (Or.inl ?_))
    rw [← hc]
    exact List.mem_map.2 ⟨m, hm', hon⟩
  obtain ⟨z, hz, hsamp⟩ := hF.1 _ G hG' _ him
  have hok := hT.inOrder.groups _ _ hG'
  have hlt : e₁.out.indexMasks < 199 := by
    have k := (Array.getElem?_eq_some_iff.1 hz).1
    rw [EW.msgs] at k
    exact k
  have hsh := EW.shape _ hlt
  rw [hz] at hsh
  have k₁ := hok.mainCode _ him z hz
  have k₂ := hok.maskCode _ him z hz
  rw [c1] at k₁
  rw [c2] at k₂
  have hfil : e₁.out.indexMasks ∈ (List.range 199).filter (fun o =>
      (OnBytes.Road.K4.mW[o]?).any fun s => (s.mainRows == 0 || s.code == 11) &&
        (s.maskRows == 0 || s.maskCode == 12)) := by
    refine List.mem_filter.2 ⟨List.mem_range.2 hlt, ?_⟩
    rw [← hsh]
    simp only [Option.map_some, Option.any_some, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact ⟨k₁, k₂⟩
  rw [ownCodes_written] at hfil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfil
  rcases hfil with e | e | e
  · exact e
  · exfalso
    have hap := rows_w_apart hrows m (by rw [← hc]; exact hm')
    exact hap (hon.trans (e.trans hw.symm))
  · exfalso
    rw [e] at hz
    rw [hn z hz] at hsamp
    cases hsamp

/-- **At the end of the first chain's fold.** -/
theorem endIs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) {l : LinFirst} (hl : linAt e₁ = some l)
    (hn : ∀ y : OnBytes.Oracle, e₁.st.oracles[198]? = some y → y.sampled = false) :
    EndIs e₁.st l.own := by
  have EW := endWritten h hf hm
  have hcod := codes_at_end h hf hm
  obtain ⟨hw, hmk, ⟨y₇, hy₇, hg₇⟩, hm₈⟩ := atW_numbers h hf hm hl
  obtain ⟨y₈, hy₈, a1, a2, -, a3, a4⟩ := hm₈ hn
  have h5 := sent_five h
  have hix' : e₁.out.indexMasks = 4 := indexMasks_at_end h hf hm hl hn
  refine ⟨hcod, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hk, hans⟩ := indexNotice_at_head h
    have hk' : 4 < (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp))).length := by
      rw [h5] at hk
      exact hk
    have hans' : (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)))[4].answers ≠ 0 := by
      simpa only [h5] using hans
    obtain ⟨y, hy, -, hs, hsp, hc, p, hp, ep⟩ := sentWell_at_end h hf 4 hk' hans'
    have hsh := EW.shape 4 (by omega)
    rw [hy, msgs_written.1] at hsh
    have esh : y.shape = indexMsg.shape := Option.some.inj hsh
    refine ⟨y, hy, strip_of y _ esh hs (by rw [hc, esh]; rfl) ?_ hsp⟩
    rw [hcod, esh] at hp
    have e := pads_written.1
    rw [hp] at e
    rw [ep]
    exact Option.some.inj e
  · obtain ⟨msg, hmsg, hall⟩ := sendW_at_end h hf hl
    obtain ⟨n, hn₀, hans⟩ := wNotice_at_head h msg hmsg
    obtain ⟨y, hy, -, hs, hsp, hc, p, hp, ep⟩ := hall 0 n hn₀ hans
    rw [hw] at hy
    obtain rfl := Option.some.inj (hy.symm.trans hy₇)
    have hsh := EW.shape 197 (by omega)
    rw [hy, msgs_written.2.1] at hsh
    have esh : y.shape = wMsg.shape := Option.some.inj hsh
    refine ⟨y, hy, strip_of y _ esh hs (by rw [hc, esh]; rfl) ?_ hsp, hg₇⟩
    rw [hcod, esh] at hp
    have e := pads_written.2.1
    rw [hp] at e
    rw [ep]
    exact Option.some.inj e
  · have hsh := EW.shape 198 (by omega)
    rw [hy₈, msgs_written.2.2] at hsh
    have esh : y₈.shape = maskMsg.shape := Option.some.inj hsh
    exact ⟨y₈, hy₈, strip_of y₈ _ esh (hn y₈ hy₈) a1 a2 a4⟩
  · obtain ⟨Bs, base, O⟩ := h.laid.opened
    have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
    have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
      rw [← hlen, List.take_length]
      exact hf
    have hreach := reach_of_fold (bs := cF.blocksInOrder) (start := ProofFile.startS Zp) (z := pI) 358
      (by rw [hlen]) _ _ _ _ _ hfold
    have hmasks := LPFK9.masks_reached h.scope h.reads O 358 (pI, e₁) hreach
    have hF : MembersFacts e₁.st := membersFacts_reached h 358 0 pI rs cols (e₁, r₀, c₀) hfold
    have hT : OnBytes.Means.Tidy e₁.st := tidy_of_fold h hf
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
    obtain ⟨G, row, hG, c1, c2, c3, c4, c5, c6⟩ := rows_group hrows (split_at_head h)
    have hlin : (whereOf Zp).lin = proofSizedFull.batch.shape := lin_at_head h
    rw [hlin] at c1 c2
    rw [own_codes.1] at c1
    rw [own_codes.2] at c2
    have hG' : e₁.st.groups[o.1.own]? = some G := by
      rw [est]
      exact hG
    obtain ⟨G₀, hG₀, hmem⟩ := OL.own
    obtain rfl := Option.some.inj (hG.symm.trans hG₀)
    have hon : ∀ m ∈ o.1.claim.masks.toList, m.oracle = 4 := by
      intro m hm'
      have hrow : VerifiableInference.Desc.First.rowOfClaim o.1.claim ∈ e₁.rows := by
        unfold VerifiableInference.Desc.First.S.rows
        rw [ehere]
        exact List.mem_singleton.2 rfl
      have k := (VerifiableInference.Desc.K13.Law.pileMasksC_iff e₁).1 hmasks _ hrow
      have k' := k _ (List.mem_map.2 ⟨m, hm', rfl⟩)
      rw [hix'] at k'
      exact k'
    have hne := claimMask_at_end h hf hl
    have hc := rows_claim hrows
    have hiff : ∀ a, a ∈ G.members.toList ↔ a = 4 ∨ a = 197 := by
      intro a
      constructor
      · intro ha
        rcases ownMembers_at_end h hf hl (split_at_head h) hG' a ha with e | e
        · exact Or.inr (e.trans hw)
        · exact Or.inl (e.trans hix')
      · rintro (rfl | rfl)
        · obtain ⟨m, hm'⟩ := List.exists_mem_of_ne_nil _ hne
          refine (hmem _).2 (Or.inr (Or.inl ?_))
          rw [← hc]
          exact List.mem_map.2 ⟨m, hm', hon m hm'⟩
        · exact (hmem _).2 (Or.inl hw.symm)
    have hmem₂ := rising_two (by omega : 4 < 197) (hF.2 _ _ hG').1 hiff
    have hmarks := (hT.inOrder.groups _ _ hG').marks
    refine ⟨G, row, hG', c1, c2, c3, hmem₂, ?_, c5, c6⟩
    have hl₂ : G.kept.toList.length = 2 := by
      rw [Array.length_toList, hmarks, ← Array.length_toList, hmem₂]
      rfl
    cases hk : G.kept.toList with
    | nil =>
      rw [hk] at hl₂
      cases hl₂
    | cons a l₂ =>
      cases l₂ with
      | nil =>
        rw [hk] at hl₂
        cases hl₂
      | cons b l₃ =>
        cases l₃ with
        | nil =>
          have ea := c4 a (by rw [hk]; exact List.mem_cons_self)
          have eb := c4 b (by rw [hk]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          rw [ea, eb]
        | cons c l₄ =>
          rw [hk] at hl₂
          simp at hl₂

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.indexMasks_at_end
#print axioms ProofFile.Honest.K12.AtFile.endIs
