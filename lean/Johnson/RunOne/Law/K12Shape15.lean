-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Shape15.lean: ROW 1.15 OF THE KEY FILE's TABLES (the first chain's block 15: the ranges' proximity test): THE BOOK-KEEPING's STEP: the fact (shape) of fwd_of_facts (Johnson/RunOne/Law/K12FwdFacts.lean): shape₁ at border 15 in front gives shape₁ at border 16 behind, at the block's own decide's yes. Statements with proofs.
OBJECT. shape₁ | core₁ (Johnson/Desc/Key/KeyShape.lean) at the first chain's readers and book (Johnson/RunOne/KeyReaders1.lean), and the block Key.rangesTest (Key.enterRanges one) Key.leaveRanges N.
USER. Whoever fills fwd_of_facts' hdec.
AT THE VERSION OF THE TABLES' FILES THAT HOLDS «THE BOOK IS IN ORDER»: moreB's last conjunct bookStepB 0 s.d.book s.d.roots is carried across the test by k12_bookStep (Johnson/Desc/K12/Coin/BookThrough.lean), which speaks at the place's own firstTree: so hft.
LETTERS. one N s s' rs gs: free. Premises, each named where it stands: hp: the block's test on the plan · h: its yes · hft: the place's first tree's number is 0 (public; the maker of the place's numbers lays 0: Johnson/Desc/Key/Ranges.lean) · hst: the test's own number of stages is the plan's · hS: the sampled messages stay (K1.SmpStay: paid by ranges_smpStay, Johnson/RunOne/KeySmpStay.lean, in another cone) · h15: the book-keeping in front · htr (the ties alone): how many trees stand behind: PAID BY NOBODY. (Where this and lean/THEOREM.md differ, the page holds.)

  out_of_yes: what a yes leaves: the state written out; the kind's files' three outright theorems (OutK | OutK2 | OutK3) at the record made of s; the seat's own "the test has run to its end".
  Ran15 | ran15_of: the same in the tables' readers' own terms.
  core_15_16: core₁'s step. ties_15_16: the ties' step. shape_15_16: both, by shape₁_step (Johnson/Desc/Key/KeyShape.lean).
Limits. A block that says no to all meets every statement. htr is a premise. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.KeyReaders1
import Johnson.RunOne.Law.RngAtKeyD
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Coin.BookThrough
import Johnson.Desc.Sound.BookInOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Shape15
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges lookupsOf)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.Sound (bookStepB BookStep bookStep_iff)
open Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngAnyCl Johnson.RunOne.Law.RngAtKeyD
open Johnson.RunOne.KeyRows1 (n₁ plan₁ readers₁ book₁ slots₁ ties₁ tiesA moreB sizesB counts₁ done₁)

variable {one : OneTime} {N : H2U.PlaceNums} {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

/-- **What a yes of the block leaves.** -/
theorem out_of_yes (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s') :
    ∃ tE G, s' = { s with d := { s.d with st := tE.st, book := tE.book, roots := tE.roots }, owed := none } ∧ testEnded tE = true ∧
      H2K.Out.OutK (recD s) tE ∧ H2K.Out.OutK2 (recD s) tE ((rangesParams N).nums.stages.length - 1) G ∧ H2K.Out.OutK3 (recD s) tE ∧
      (rangesParams N).nums.stages ≠ [] := by
  obtain ⟨_, he, ha, _, _⟩ := planOk_ok (plan_unit hp)
  obtain ⟨tE, _, _, hask, hd, hend, e⟩ := keyD_yes h
  have hd' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (recD s) rs gs = .ok tE := by
    rw [(same_k12 (A := Unit) (B := Claim) guardedProximityTestParts (rangesParams N)).decide]
    exact hd
  obtain ⟨G, k2⟩ := H2K.Out.k12_out2 _ he ha _ _ _ _ hd'
  obtain ⟨_, _, a, rest, _, _, hs, _⟩ := asksRecord_ok hask
  exact ⟨tE, G, e, hend, H2K.Out.k12_out _ he ha _ _ _ _ hd', k2, H2K.Out.k12_out3 _ he ha _ _ _ _ hd', by rw [hs]; exact List.cons_ne_nil _ _⟩

/-- **The book stays in order across the block.** -/
theorem book_of_yes (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s')
    (hft : (rangesParams N).nums.firstTree = 0) (hB : bookStepB 0 s.d.book s.d.roots = true) : bookStepB 0 s'.d.book s'.d.roots = true := by
  obtain ⟨_, he, ha, _, _⟩ := planOk_ok (plan_unit hp)
  obtain ⟨tE, _, _, _, hd, _, e⟩ := keyD_yes h
  have hd' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (recD s) rs gs = .ok tE := by
    rw [(same_k12 (A := Unit) (B := Claim) guardedProximityTestParts (rangesParams N)).decide]
    exact hd
  have k := VerifiableInference.Desc.K12.Coin.k12_bookStep (rangesParams N) he ha (recD s) tE rs gs hd' (by
    rw [hft]
    exact (bookStep_iff 0 s.d.book s.d.roots).1 hB)
  rw [hft] at k
  rw [e]
  exact (bookStep_iff 0 tE.book tE.roots).2 k

/-- **What the ties at border 15 say of the state in front.** -/
theorem front15 (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) :
    (lookupsOf one).length = 2 ∧ one.ranges.messageId = 1 ∧ s.d.st.codes = one.codes ∧ s.idx = 0 ∧
      (∃ G, s.d.st.groups[s.grp]? = some G ∧ G.members.toList = [1]) ∧ s.rider = some 2 ∧
      s.base.rows.length = 2 ∧ s.base.keys.length = 2 ∧ s.d.st.oracles.size = 3 ∧ s.d.st.groups.size = 1 ∧ s.d.book.trees.size = 2 ∧
      s.d.book.place.size = s.d.st.oracles.size ∧ bookStepB 0 s.d.book s.d.roots = true := by
  have ht : ties₁ one 15 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h15).1
  unfold ties₁ tiesA moreB sizesB at ht
  simp [counts₁, done₁] at ht
  obtain ⟨⟨⟨⟨⟨⟨hL, hMi⟩, hC⟩, hIx⟩, ⟨hMem, hRd⟩, _⟩, ⟨hR, hK⟩, hBS⟩, ⟨⟨hO, hG⟩, hT⟩, hPl⟩ := ht
  refine ⟨hL, hMi, hC, hIx, ?_, hRd, hR, hK, hO, hG, hT, hPl, hBS⟩
  cases hg : s.d.st.groups[s.grp]? with
  | none =>
    rw [hg] at hMem
    simp at hMem
  | some G =>
    rw [hg] at hMem
    exact ⟨G, rfl, by simpa using hMem⟩

/-- What a yes of the block leaves, in the tables' readers' own terms. -/
structure Ran15 (one : OneTime) (s s' : FirstState) : Prop where
  base : s'.base = s.base
  lin : s'.lin = s.lin
  idx : s'.idx = s.idx
  grp : s'.grp = s.grp
  codes : s'.d.st.codes = s.d.st.codes
  size : s'.d.st.oracles.size = 1 + 2 * one.ranges.stages.length
  groups : s'.d.st.groups.size = one.ranges.stages.length
  places : s'.d.book.place.size = s'.d.st.oracles.size
  begun : ∃ G, s'.d.st.groups[s.grp]? = some G ∧ G.inRun = true ∧ G.rows.size = 0
  ended : ((s'.d.st.groups.toList.drop s.grp).all fun G => G.inRun && G.rows.isEmpty) = true
  book : bookStepB 0 s'.d.book s'.d.roots = true

theorem ran15_of (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s')
    (hst : (rangesParams N).nums.stages.length = one.ranges.stages.length) (hft : (rangesParams N).nums.firstTree = 0)
    (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) : Ran15 one s s' := by
  obtain ⟨_, _, _, _, _, hRd, _, _, hO, hG, _, _, hBS⟩ := front15 h15
  have hbk := book_of_yes hp h hft hBS
  obtain ⟨tE, G, e, hend, k1, k2, k3, hne⟩ := out_of_yes hp h
  have hpos : 1 ≤ one.ranges.stages.length := by
    rw [← hst]
    exact Nat.pos_of_ne_zero fun h0 => hne (List.length_eq_zero_iff.1 h0)
  have hown : H2K.Out.own (recD s) = 0 := by
    have e1 : (recD s).mask = some 2 := hRd
    unfold H2K.Out.own
    rw [e1]
    rfl
  have o1 : tE.st.oracles.size = s.d.st.oracles.size + H2K.Out.own (recD s) + 2 * ((rangesParams N).nums.stages.length - 1) := k2.oraclesN
  have g1 : tE.st.groups.size = s.d.st.groups.size + ((rangesParams N).nums.stages.length - 1) := k2.groupsN
  have gE : tE.g = s.grp := k1.g
  have hend' : ((tE.st.groups.toList.drop tE.g).all fun G => G.inRun && G.rows.isEmpty) = true := by
    unfold testEnded at hend
    simp only [Bool.and_eq_true] at hend
    exact hend.1.2
  subst e
  exact
    { base := rfl, lin := rfl, idx := rfl, grp := rfl
      codes := k1.codes
      size := by
        show tE.st.oracles.size = _
        omega
      groups := by
        show tE.st.groups.size = _
        omega
      places := k3.step.symm
      begun := ⟨_, k2.begunG, rfl, rfl⟩
      ended := by
        rw [← gE]
        exact hend'
      book := hbk }

/-! ## The readers' Bools -/

theorem sentB_iff {k o : Nat} (t : FirstState) (ho : (plan₁ one).orc k = some o) :
    sentB (plan₁ one) (readers₁ one) t k = true ↔ ∃ x, t.d.st.oracles[o]? = some x ∧ x.sampled = true ∧ x.sampleRows.size ≠ 0 := by
  have e : sentB (plan₁ one) (readers₁ one) t k = (match t.d.st.oracles[o]? with
      | some x => x.sampled && x.sampleRows.size != 0
      | none => false) := by
    unfold sentB
    rw [ho]
    rfl
  rw [e]
  cases t.d.st.oracles[o]? with
  | none =>
    show false = true ↔ _
    exact ⟨fun h => (by cases h), fun ⟨_, hx, _⟩ => (by cases hx)⟩
  | some x =>
    show (x.sampled && x.sampleRows.size != 0) = true ↔ _
    rw [Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨x, rfl, h.1, bne_iff_ne.1 h.2⟩
    · rintro ⟨y, hy, h1, h2⟩
      cases hy
      exact ⟨h1, bne_iff_ne.2 h2⟩

theorem grp_there {r : Bool} {n : Nat} (t : FirstState) (h : groupB (readers₁ one) t r n = true) : t.grp ≠ noId := by
  intro e
  have e2 : groupB (readers₁ one) t r n = false := by
    simp [groupB, readers₁, KeyReaders.readers, e]
  rw [e2] at h
  cases h

theorem groupB_mk {r : Bool} {n : Nat} (t : FirstState) (hn : t.grp ≠ noId) (G : Group) (hG : t.d.st.groups[t.grp]? = some G)
    (h1 : G.inRun = r) (h2 : G.rows.size = n) : groupB (readers₁ one) t r n = true := by
  simp [groupB, readers₁, KeyReaders.readers, hn, hG, h1, h2]

theorem groupB_of {r : Bool} {n : Nat} (t : FirstState) (h : groupB (readers₁ one) t r n = true) :
    ∃ G, t.d.st.groups[t.grp]? = some G ∧ G.inRun = r ∧ G.rows.size = n := by
  have hn := grp_there t h
  cases hG : t.d.st.groups[t.grp]? with
  | none =>
    simp [groupB, readers₁, KeyReaders.readers, hn, hG] at h
  | some G =>
    simp [groupB, readers₁, KeyReaders.readers, hn, hG] at h
    exact ⟨G, rfl, h.1, h.2⟩

theorem core15_eq (t : FirstState) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 t =
    (sentB (plan₁ one) (readers₁ one) t 0 && sentB (plan₁ one) (readers₁ one) t 1 && ((book₁ one).ledger t).isNone && !(book₁ one).heard t &&
      doneB (plan₁ one) (readers₁ one) 2 2 t &&
      (groupB (readers₁ one) t false (rowsCount (readers₁ one) 2 t) && rowsCount (readers₁ one) 2 t != 0 && ((readers₁ one).pile t).isNone &&
        !sentB (plan₁ one) (readers₁ one) t 2)) := rfl

theorem core16_eq (t : FirstState) : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 t =
    (sentB (plan₁ one) (readers₁ one) t 0 && sentB (plan₁ one) (readers₁ one) t 1 && ((book₁ one).ledger t).isNone && !(book₁ one).heard t &&
      doneB (plan₁ one) (readers₁ one) 2 2 t &&
      (groupB (readers₁ one) t true 0 && ((readers₁ one).pile t).isNone && !sentB (plan₁ one) (readers₁ one) t 2)) := rfl

/-- **In front of the test the ranges' group is there, its test not begun, with an open row.** -/
theorem rows_15 (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) :
    ∃ g G, (readers₁ one).grpB s = some g ∧ s.d.st.groups[g]? = some G ∧ G.members.toList = [1] ∧ G.inRun = false ∧ G.rows.size ≠ 0 := by
  have hc := ((shape₁_iff _ _ _ _ _ _ _).1 h15).2
  rw [core15_eq] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨G, hG, g1, g2⟩ := groupB_of s hc.2.1.1.1
  obtain ⟨_, _, _, _, ⟨G', hG', hm⟩, _⟩ := front15 h15
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  have hn := grp_there s hc.2.1.1.1
  refine ⟨s.grp, G, ?_, hG, hm, g1, by rw [g2]; exact bne_iff_ne.1 hc.2.1.1.2⟩
  show (if s.grp == noId then none else some s.grp) = some s.grp
  rw [if_neg (fun e => hn (beq_iff_eq.1 e))]

/-- What reads the key file's own small record and the claim alone says the same of two states that agree on them. -/
theorem same_small (hb : s'.base = s.base) (hl : s'.lin = s.lin) :
    ((book₁ one).ledger s').isNone = ((book₁ one).ledger s).isNone ∧ (book₁ one).heard s' = (book₁ one).heard s ∧
      doneB (plan₁ one) (readers₁ one) 2 2 s' = doneB (plan₁ one) (readers₁ one) 2 2 s ∧ ((readers₁ one).pile s').isNone = ((readers₁ one).pile s).isNone := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (s'.base.fork.map _).isNone = (s.base.fork.map _).isNone
    rw [hb]
  · show s'.base.heard.isSome = s.base.heard.isSome
    rw [hb]
  · unfold doneB
    show ((List.range 2).all fun l => if l < 2 then (s'.base.rows[l]?).any (!·.isEmpty) && (match (s'.base.keys[l]?).bind (KeyReaders.pendingOf one l), (plan₁ one).lookups[l]? with | some ks, some L => ks.length == L.parts.length | _, _ => false) else (s'.base.rows[l]?).isNone && ((s'.base.keys[l]?).bind (KeyReaders.pendingOf one l)).isNone) = _
    rw [hb]
    rfl
  · show (s'.lin.map _).isNone = (s.lin.map _).isNone
    rw [hl]

/-- **core₁'s step across the ranges' test.** -/
theorem core_15_16 (H : Ran15 one s s') (hS : SmpStay s.d.st s'.d.st)
    (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) :
    core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s' = true := by
  have hc := ((shape₁_iff _ _ _ _ _ _ _).1 h15).2
  rw [core15_eq] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c0, c1⟩, cL⟩, cH⟩, cD⟩, ⟨⟨cG, _⟩, cP⟩, _⟩ := hc
  obtain ⟨eL, eH, eD, eP⟩ := same_small (one := one) H.base H.lin
  have stay : ∀ k o, (plan₁ one).orc k = some o → sentB (plan₁ one) (readers₁ one) s k = true → sentB (plan₁ one) (readers₁ one) s' k = true := by
    intro k o ho hk
    obtain ⟨x, hx, x1, x2⟩ := (sentB_iff s ho).1 hk
    obtain ⟨x', hx', _, y1, y2⟩ := hS.2 o x hx x1
    exact (sentB_iff s' ho).2 ⟨x', hx', y1, by rw [y2]; exact x2⟩
  have n2 : sentB (plan₁ one) (readers₁ one) s' 2 = false := by
    cases e : sentB (plan₁ one) (readers₁ one) s' 2 with
    | false => rfl
    | true =>
      obtain ⟨x, hx, _⟩ := (sentB_iff (o := 1 + 2 * one.ranges.stages.length) s' rfl).1 e
      rw [Array.getElem?_eq_none (Nat.le_of_eq H.size)] at hx
      cases hx
  obtain ⟨G, hG, g1, g2⟩ := H.begun
  have hn : s'.grp ≠ noId := by
    rw [H.grp]
    exact grp_there s cG
  have gB : groupB (readers₁ one) s' true 0 = true := groupB_mk s' hn G (by rw [H.grp]; exact hG) g1 g2
  rw [core16_eq, stay 0 0 rfl c0, stay 1 1 rfl c1, eL, cL, eH, cH, eD, cD, gB, eP, cP, n2]
  rfl

/-- **The ties' step**, at the tables as they lie in the still row of 107 files. htr: how many trees stand behind the test: A PREMISE. -/
theorem ties_15_16 (H : Ran15 one s s') (htr : s'.d.book.trees.size = one.ranges.stages.length + 1)
    (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) : ties₁ one 16 s' = true := by
  obtain ⟨hL, hMi, hC, hIx, _, _, hR, hK, _, _, _, _, _⟩ := front15 h15
  have d16 : done₁ 16 = 2 := rfl
  have c16 : counts₁ one 16 = (1 + 2 * one.ranges.stages.length, one.ranges.stages.length, one.ranges.stages.length + 1) := rfl
  unfold ties₁
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold tiesA
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨beq_iff_eq.2 hL, beq_iff_eq.2 hMi⟩, decide_eq_true (H.codes.trans hC)⟩, ?_⟩, ?_⟩
    · rw [Bool.or_eq_true]
      exact Or.inr (beq_iff_eq.2 (H.idx.trans hIx))
    · rw [Bool.or_eq_true]
      exact Or.inl rfl
  · unfold moreB
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, H.book⟩
    · rw [H.base, hR, d16]
      rfl
    · rw [H.base, hK, d16]
      rfl
    · rw [Bool.or_eq_true]
      exact Or.inl rfl
    · rw [Bool.or_eq_true]
      exact Or.inl rfl
    · rw [Bool.or_eq_true]
      refine Or.inr ?_
      rw [if_pos (by decide), H.grp]
      exact H.ended
  · unfold sizesB
    rw [c16]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨beq_iff_eq.2 H.size, beq_iff_eq.2 H.groups⟩, beq_iff_eq.2 htr⟩, beq_iff_eq.2 H.places⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      (rw [Bool.or_eq_true]; exact Or.inl rfl)

/-- **The book-keeping's step across the ranges' test**: at two lookups. -/
theorem shape_15_16 (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s')
    (hst : (rangesParams N).nums.stages.length = one.ranges.stages.length) (hft : (rangesParams N).nums.firstTree = 0) (hS : SmpStay s.d.st s'.d.st)
    (htr : s'.d.book.trees.size = one.ranges.stages.length + 1)
    (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) :
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s' = true :=
  have H := ran15_of hp h hst hft h15
  (shape₁_iff _ _ _ _ _ _ _).2 ⟨ties_15_16 H htr h15, core_15_16 H hS h15⟩

end Johnson.RunOne.Law.K12Shape15

#print axioms Johnson.RunOne.Law.K12Shape15.out_of_yes
#print axioms Johnson.RunOne.Law.K12Shape15.book_of_yes
#print axioms Johnson.RunOne.Law.K12Shape15.front15
#print axioms Johnson.RunOne.Law.K12Shape15.ran15_of
#print axioms Johnson.RunOne.Law.K12Shape15.rows_15
#print axioms Johnson.RunOne.Law.K12Shape15.core_15_16
#print axioms Johnson.RunOne.Law.K12Shape15.ties_15_16
#print axioms Johnson.RunOne.Law.K12Shape15.shape_15_16
