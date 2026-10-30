-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Shape210.lean: ROW 2.10 OF THE KEY FILE's TABLES (the shared chain's block 10: the proximity test on G_omega, whose first fold sends its own mask): THE BOOK-KEEPING's STEP: shape₂ at border 10 in front gives shape₂ at border 11 behind, at a yes of the seated test. One statement with its proof, and one helper.
OBJECT. LKFU.Shape23.shape₂ (at the tables' files, which ask «the book is in order») and Seat.onGomega (proximityTestKind guardedProximityTestParts p). USER. Johnson/RunOne/Law/K12Fwd210.lean.
LETTERS. S a p d d' rs gs: free. Premises: early · answers = 1 · the yes · hst: the test's own number of stages is the shape's (S.testOmega.length) · hft: the place's first tree's number is 0 · ha1: the answers to a sample are 1 · h10: the book-keeping in front.
CLAUSE BY CLAUSE as at row 2.9 (Johnson/RunOne/Law/K12Shape29.lean), but: one message and one tree more (the test's own first mask): Johnson/RunOne/Law/K12Tower.lean's second arm, K12Trees.lean's k12_trees_any with oneTreeMask_all · the tower that the test on G_u has left must STAND: tower_stays.
Limits. A block that says no to all meets the statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Shape29

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Shape210
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Out
open LKFU.Shape23
open VerifiableInference.Desc.Sound (bookStepB BookStep bookStep_iff)
open Johnson.RunOne.Law.K12Tower (mk Tgt Rdr Grp TowerOwn k12_tower_own begun_mk)
open Johnson.RunOne.Law.K12Trees (k12_trees_any k12_roots_any)
open Johnson.RunOne.Law.K12OneTree (oneTree_all oneTreeMask_all)
open Johnson.RunOne.Law.K12Shape29

/-- A tower stands where its messages keep their marks and its groups stand. -/
theorem tower_stays (st st' : Statement) (m₀ g₀ s a : ℕ)
    (hm : ∀ o, o < m₀ + 2 * (s - 1) → (st'.oracles[o]?).map mk = (st.oracles[o]?).map mk)
    (hg : ∀ g, g₀ ≤ g → g < g₀ + (s - 1) → st'.groups[g]? = st.groups[g]?) (h : towerIs st m₀ g₀ s a = true) : towerIs st' m₀ g₀ s a = true := by
  unfold towerIs at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have hj' := List.mem_range.1 hj
  rw [msgIs_congr st st' _ _ _ (hm _ (by omega)), msgIs_congr st st' _ _ _ (hm _ (by omega)), grpIs_congr st st' _ _ _ _ _ (hg _ (by omega) (by omega))]
  exact h j hj

/-- **The book-keeping's step across the test on G_omega.** -/
theorem shape₂_10_11 (S : LinShape) (a : ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') (hst : p.nums.stages.length = S.testOmega.length) (hft : p.nums.firstTree = 0)
    (ha1 : a = 1) (h10 : ok (shape₂ S a 10 d) = true) : ok (shape₂ S a 11 d') = true := by
  subst ha1
  have bk := (VerifiableInference.Desc.K12.Coin.onGomega_bookStep p he ha d d' rs gs h (by
    rw [hft]
    exact Johnson.RunOne.KeyRows23.bookStep_of_shape₂ S 1 10 d h10)).1
  rw [hft] at bk
  simp [ok, shape₂] at h10
  obtain ⟨c1, c2, c3, ⟨c4, c4'⟩, c5, c6, ⟨c7, c7'⟩, ⟨c8, c8'⟩, ⟨c9, c9'⟩, c10, ⟨c11, c11'⟩, c12, c13, c14, c15, c16, _⟩ := h10
  obtain ⟨tE, hy, rfl⟩ := seat_yes (·.gOmega) (fun _ => none) p d d' rs gs h
  have hy' : (proximityTestKind guardedProximityTestParts p : Blk').decide (recS d 1 none) rs gs = .ok tE := by
    have e : (recS d 1 none) = { st := d.st, book := d.book, roots := d.roots, g := d.loc.gOmega, pass := .nothing, mask := none } := by
      rw [c7']
    rw [e]
    exact hy
  obtain ⟨G, T⟩ := k12_tower_own p he ha (recS d 1 none) tE rs gs hy' rfl
  obtain ⟨G2, K2⟩ := k12_out2 p he ha (recS d 1 none) tE rs gs hy'
  obtain rfl : G = G2 := Option.some.inj (T.was.symm.trans K2.was)
  have K1 := k12_out p he ha (recS d 1 none) tE rs gs hy'
  have K3 := k12_out3 p he ha (recS d 1 none) tE rs gs hy'
  have tr : tE.book.trees.size = d.book.trees.size + 1 + (p.nums.stages.length - 1) :=
    k12_trees_any p he ha (recS d 1 none) tE rs gs hy' (fun nx last lay h => oneTree_all _ nx last lay h) (fun c L lay h => oneTreeMask_all _ c L lay h)
  have ro : tE.roots = d.roots + 1 + (p.nums.stages.length - 1) :=
    k12_roots_any p he ha (recS d 1 none) tE rs gs hy' (fun nx last lay h => oneTree_all _ nx last lay h) (fun c L lay h => oneTreeMask_all _ c L lay h)
  have o1 : tE.st.oracles.size = d.st.oracles.size + 1 + 2 * (p.nums.stages.length - 1) := K2.oraclesN
  have g1 : tE.st.groups.size = d.st.groups.size + (p.nums.stages.length - 1) := K2.groupsN
  have hwas : d.st.groups[1]? = some G := T.was
  obtain ⟨G0, hG0, hmem⟩ := grpIs_members _ _ _ _ _ _ c14
  obtain rfl : G0 = G := Option.some.inj (hG0.symm.trans hwas)
  have old : ∀ o, o < d.st.oracles.size → tE.st.oracles[o]? = (begun d.st 1 G0).oracles[o]? := fun o ho => T.old o ho
  have oldmk : ∀ o, o < d.st.oracles.size → (tE.st.oracles[o]?).map mk = (d.st.oracles[o]?).map mk := fun o ho => by
    rw [old o ho]
    exact begun_mk _ _ _ _
  have oldg : ∀ g, g < d.st.groups.size → g ≠ 1 → tE.st.groups[g]? = d.st.groups[g]? := fun g hg hne => K2.others g hg hne
  have later : ∀ i, i < S.testOmega.length - 1 → Tgt tE.st (4 + 2 * (S.testU.length - 1) + 1 + 2 * i) ∧
      Rdr tE.st (4 + 2 * (S.testU.length - 1) + 1 + 2 * i + 1) true ∧ Grp tE.st (2 + (S.testU.length - 1) + i) (4 + 2 * (S.testU.length - 1) + 1 + 2 * i) := by
    intro i hi
    have k := T.later i (by rw [hst]; exact hi)
    have e1 : (recS d 1 none).st.oracles.size = 4 + 2 * (S.testU.length - 1) := c2
    have e2 : (recS d 1 none).st.groups.size = 2 + (S.testU.length - 1) := c3
    rw [e1, e2] at k
    exact k
  have hown : Rdr tE.st (4 + 2 * (S.testU.length - 1)) true := by
    have k := T.own
    have e1 : (recS d 1 none).st.oracles.size = 4 + 2 * (S.testU.length - 1) := c2
    rw [e1] at k
    exact k
  simp [ok, shape₂]
  refine ⟨c1, by omega, by omega, ⟨by omega, by omega⟩, K3.step, c6, ⟨c7, c7'⟩, ⟨c8, c8'⟩, ⟨?_, ?_⟩, c10, ⟨?_, ?_⟩, c12, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [msgIs_congr d.st tE.st 0 _ _ (oldmk 0 (by omega))]
    exact c9
  · rw [msgIs_congr d.st tE.st 1 _ _ (oldmk 1 (by omega))]
    exact c9'
  · rw [msgIs_congr d.st tE.st 2 _ _ (oldmk 2 (by omega))]
    exact c11
  · rw [msgIs_congr d.st tE.st 3 _ _ (oldmk 3 (by omega))]
    exact c11'
  · rw [grpIs_congr d.st tE.st 0 _ _ _ _ (oldg 0 (by omega) (by omega))]
    exact c13
  · exact grpIs_begun _ _ _ G0 K2.begunG hmem
  · have e3 : tE.st.oracles[3]? = (d.st.oracles[3]?).map shut := by
      rw [old 3 (by omega)]
      show (closeLedgers d.st G0.members.toList).oracles[3]? = _
      rw [closeLedgers_get, hmem, if_pos (by simp)]
    have ec : tE.st.codes = d.st.codes := K1.codes
    rw [e3, ec]
    cases hx : d.st.oracles[3]? with
    | none =>
      rw [hx] at c15
      simp at c15
    | some x =>
      rw [hx] at c15
      cases hL : x.ledger with
      | none => simp [hL] at c15
      | some L =>
        simp [hL] at c15 ⊢
        exact c15.2
  · exact tower_stays d.st tE.st 4 2 _ 1 (fun o ho => oldmk o (by omega)) (fun g hg1 hg2 => oldg g (by omega) (by omega)) c16
  · exact msgIs_rdr _ _ _ hown
  · exact tower_of _ _ _ _ later
  · exact (bookStep_iff 0 _ _).2 bk

end Johnson.RunOne.Law.K12Shape210

#print axioms Johnson.RunOne.Law.K12Shape210.tower_stays
#print axioms Johnson.RunOne.Law.K12Shape210.shape₂_10_11
