-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Shape32.lean: ROW 3.2 OF THE KEY FILE's TABLES (the last chain's block 2: the proximity test on the own group): THE BOOK-KEEPING's STEP: shape₃, and the tables' shapeB₃ over it, at border 2 in front give the same at border 3 behind, at a yes of the seated test. Statements with proofs.
OBJECT. LKFU.Shape23.shape₃ (thirteen named clauses) · Johnson.RunOne.KeyRows23.shapeB₃ (Johnson/RunOne/KeyRows23At.lean) · Seat.onOwn (proximityTestKind guardedProximityTestParts p) (Johnson/Desc/K12/Seat/Own.lean). USER. Johnson/RunOne/Law/K12Fwd32.lean.
LETTERS. S a n g t idx p s s' rs gs: free. Premises: early · answers = 1 · the yes · hst: the test's own number of stages is the shape's (S.testOwn.length) · ha1: the answers to a sample are 1 · h2: the book-keeping in front. NO PREMISE ON THE PLACE's FIRST TREE's NUMBER: shape₃ has no clause on the trees' numbers (at this place the maker lays the first chain's trees and one, not 0).
CLAUSE BY CLAUSE as at row 2.9 (Johnson/RunOne/Law/K12Shape29.lean). That W's number, the mask's and Omega's are three different messages is read off the clauses themselves: one message cannot be both sampled and without a sample (msgIs_excl).
Limits. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Shape29
import Johnson.Desc.K12.Seat.Own
import Johnson.RunOne.KeyRows23At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Shape32
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Third (S₃)
open H2K.JointK H2K.Out
open LKFU.Shape23
open Johnson.RunOne.Law.K12Tower (mk Tgt Rdr Grp Tower k12_tower begun_mk spent)
open Johnson.RunOne.Law.K12Trees (k12_trees k12_roots)
open Johnson.RunOne.Law.K12OneTree (oneTree_all)
open Johnson.RunOne.Law.K12Shape29

/-- One message is not both sampled and without a sample. -/
theorem msgIs_excl (st : Statement) (o a : ℕ) (f f' : Bool) (h : msgIs st o (some a) f = true) (h' : msgIs st o none f' = true) : False := by
  unfold msgIs at h h'
  cases hx : st.oracles[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h h'
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h h'
    rw [h.1.1] at h'
    cases h'.1.1

/-- **A yes of the test seated on the last chain, written out.** -/
theorem own_yes (p : P12) (s s' : S₃) (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onOwn (proximityTestKind guardedProximityTestParts p : Blk')).decide s rs gs = .ok s') :
    ∃ tE, (proximityTestKind guardedProximityTestParts p : Blk').decide { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing, mask := s.loc.mask } rs gs = .ok tE ∧
      s' = { s with st := tE.st, book := tE.book, roots := tE.roots } := by
  have h' : ((Seat.enterOwn s).bind fun t => ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leaveOwn s)) = .ok s' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  exact ⟨t', ht', rfl⟩

/-- The state that the seat hands the test. -/
abbrev recO (s : S₃) (g : ℕ) (m : Option ℕ) : T12 := { st := s.st, book := s.book, roots := s.roots, g := g, pass := .nothing, mask := m }

/-- **The book-keeping's step across the own test.** -/
theorem shape₃_2_3 (S : LinShape) (a n g t : ℕ) (idx : List ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1) (s s' : S₃) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onOwn (proximityTestKind guardedProximityTestParts p : Blk')).decide s rs gs = .ok s') (hst : p.nums.stages.length = S.testOwn.length)
    (ha1 : a = 1) (h2 : ok (shape₃ S a n g t idx 2 s) = true) : ok (shape₃ S a n g t idx 3 s') = true ∧ s'.loc = s.loc := by
  subst ha1
  simp [ok, shape₃] at h2
  obtain ⟨c1, c2, c3, c4, c5, ⟨⟨c6, c6'⟩, c6''⟩, c7, c8, c9, ⟨c10, c10'⟩, c11, c12⟩ := h2
  obtain ⟨tE, hy, rfl⟩ := own_yes p s s' rs gs h
  refine ⟨?_, rfl⟩
  have hy' : (proximityTestKind guardedProximityTestParts p : Blk').decide (recO s (g - 1) (some (n - 1))) rs gs = .ok tE := by
    have e : (recO s (g - 1) (some (n - 1))) = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing, mask := s.loc.mask } := by
      rw [c6', c6'']
    rw [e]
    exact hy
  obtain ⟨G, T⟩ := k12_tower p he ha (recO s (g - 1) (some (n - 1))) tE rs gs hy' (n - 1) rfl
  obtain ⟨G2, K2⟩ := k12_out2 p he ha (recO s (g - 1) (some (n - 1))) tE rs gs hy'
  obtain rfl : G = G2 := Option.some.inj (T.was.symm.trans K2.was)
  have tr : tE.book.trees.size = s.book.trees.size + (p.nums.stages.length - 1) :=
    k12_trees p he ha (recO s (g - 1) (some (n - 1))) tE rs gs hy' (fun nx last lay h => oneTree_all _ nx last lay h) (n - 1) rfl
  have ro : tE.roots = s.roots + (p.nums.stages.length - 1) :=
    k12_roots p he ha (recO s (g - 1) (some (n - 1))) tE rs gs hy' (fun nx last lay h => oneTree_all _ nx last lay h) (n - 1) rfl
  have o1 : tE.st.oracles.size = s.st.oracles.size + 0 + 2 * (p.nums.stages.length - 1) := K2.oraclesN
  have g1 : tE.st.groups.size = s.st.groups.size + (p.nums.stages.length - 1) := K2.groupsN
  have hwas : s.st.groups[g - 1]? = some G := T.was
  obtain ⟨G0, hG0, hmem⟩ := grpIs_members _ _ _ _ _ _ c12
  obtain rfl : G0 = G := Option.some.inj (hG0.symm.trans hwas)
  have oldmk : ∀ o, o < n + 1 → o ≠ n - 1 → (tE.st.oracles[o]?).map mk = (s.st.oracles[o]?).map mk := fun o ho hne => by
    rw [T.old o (by
      show o < s.st.oracles.size
      rw [c2]
      exact ho) hne]
    exact begun_mk _ _ _ _
  have hw : n - 2 ≠ n - 1 := fun e => msgIs_excl _ _ _ _ _ c10 (e ▸ c10')
  have hn : n ≠ n - 1 := fun e => msgIs_excl s.st n 1 false false c11 (by rw [e]; exact (by rw [← e]; exact e ▸ c10'))
  have later : ∀ i, i < S.testOwn.length - 1 → Tgt tE.st (n + 1 + 2 * i) ∧ Rdr tE.st (n + 1 + 2 * i + 1) true ∧ Grp tE.st (g + i) (n + 1 + 2 * i) := by
    intro i hi
    have k := T.later i (by rw [hst]; exact hi)
    have e1 : (recO s (g - 1) (some (n - 1))).st.oracles.size = n + 1 := c2
    have e2 : (recO s (g - 1) (some (n - 1))).st.groups.size = g := c3
    rw [e1, e2] at k
    exact k
  simp [ok, shape₃]
  refine ⟨c1, by omega, by omega, by omega, by omega, ⟨⟨c6, c6'⟩, c6''⟩, c7, c8, c9, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [msgIs_congr s.st tE.st (n - 2) _ _ (oldmk _ (by omega) hw)]
    exact c10
  · obtain ⟨x, hx, x1, x2, x3⟩ := rdr_of_msgIs _ _ _ c10'
    have e : ((begun s.st (g - 1) G0).oracles[n - 1]?).map mk = some (false, #[], false) := by
      rw [begun_mk, hx]
      show some (x.sampled, x.sampleRows, x.spentAsMask) = _
      rw [x1, x2, x3]
    obtain ⟨x', hx', y1, y2, _⟩ := Johnson.RunOne.Law.K12Tower.of_mk e
    refine msgIs_rdr _ _ _ ⟨spent x', ?_, y1, y2, rfl⟩
    have k : tE.st.oracles[n - 1]? = ((begun s.st (g - 1) G0).oracles[n - 1]?).map spent := T.mask
    rw [k, hx']
    rfl
  · rw [msgIs_congr s.st tE.st n _ _ (oldmk _ (by omega) hn)]
    exact c11
  · exact grpIs_begun _ _ _ G0 K2.begunG hmem
  · exact tower_of _ _ _ _ later

open Johnson.RunOne.KeyRows23 (shapeB₃ nOwn gOwn tOwn)

/-- **The tables' own Bool at the last chain: border 2 gives border 3.** -/
theorem shapeB₃_2_3 (S : LinShape) (K₁ : VerifiableInference.Desc.Key.KPlan) (a : ℕ) (idx : List ℕ) (src : S₃ → Bool) (t₁ : ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (s s' : S₃) (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onOwn (proximityTestKind guardedProximityTestParts p : Blk')).decide s rs gs = .ok s')
    (hst : p.nums.stages.length = S.testOwn.length) (ha1 : a = 1) (h2 : shapeB₃ S K₁ a idx src t₁ 2 s = true) : shapeB₃ S K₁ a idx src t₁ 3 s' = true := by
  unfold shapeB₃ at h2 ⊢
  simp only [Bool.and_eq_true] at h2 ⊢
  obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, _⟩, _⟩, _⟩ := h2
  obtain ⟨k, hl⟩ := shape₃_2_3 S a (nOwn s) (gOwn s) (tOwn s) idx p he ha s s' rs gs h hst ha1 b1
  have e1 : nOwn s' = nOwn s := by unfold nOwn; rw [hl]
  have e2 : gOwn s' = gOwn s := by unfold gOwn; rw [hl]
  have e3 : tOwn s' = tOwn s := by unfold tOwn; rw [hl]
  rw [e1, e2, e3, hl]
  exact ⟨⟨⟨⟨⟨k, b2⟩, b3⟩, rfl⟩, rfl⟩, rfl⟩

end Johnson.RunOne.Law.K12Shape32

#print axioms Johnson.RunOne.Law.K12Shape32.shape₃_2_3
#print axioms Johnson.RunOne.Law.K12Shape32.shapeB₃_2_3
