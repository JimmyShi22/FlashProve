-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the sender's column against the job's, at one tie of coins.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesLCol.lean: what treesL lays (AtProof/JobL.lean) against
what the finish of the code switch sends: the written column over the job's two messages is the
column over the sender's, where the carrying message's rows are one and the fresh message's coins
are those of the job's carried stretch. No run here, no book, no law.

  flatMap_congr_mem, mapM_ok_at, column_congr, symG_congr, rowsAll_at, es_getD, hideAt_congr   small
                   facts on lists, columns, a sending's rows, coins
  fresh_rows       the rows of a fold's fresh message
  table_column, column_words_canonical, columnWidth, column_length   a table of the sender's form
                   against the written column: words
  firstStageOf, finishTrees, FitsFacts, fitsL_facts   what fitsL says
  messagesOfJob, finishSending, column_at_finish   the statement

By what. lay_is_packed (AtProof/FreshAtL.lean): so the order of a fold's coefficients cannot part here:
the sender's table and the test's state are one table by that theorem, at every list of coefficients.

Limits. Message 0's rows are taken to be one (h0): that is trees_first's work. No property of the
protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.SeamL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FreshAtL
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open Johnson.Prover.Send (col mainSyms maskSyms Rows)
open Johnson.Prover.Link (symG packedN PS)
open H2K.Pub (sgOf)
open OnBytes.Slice (GE ofE readE_ofTriple toE_ofE)

/-! ## 1 Lists -/

theorem flatMap_congr_mem {α β : Type} (f g : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]
    rw [h a (by simp), flatMap_congr_mem f g l fun b hb => h b (by simp [hb])]

/-- What a mapM over a list returned, by number. -/
theorem mapM_ok_at {ε α β : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (l : List β), xs.mapM f = .ok l →
      l.length = xs.length ∧ ∀ (i : ℕ) (hi : i < xs.length), ∃ y, l[i]? = some y ∧ f xs[i] = .ok y
  | [], l, h => by
    rw [List.mapM_nil] at h
    have e := Except.ok.inj h
    subst e
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | a :: xs, l, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e =>
      rw [ha] at h
      cases h
    | ok b =>
      rw [ha] at h
      have h' : (xs.mapM f >>= fun bs => pure (b :: bs)) = Except.ok l := h
      cases hl : xs.mapM f with
      | error e =>
        rw [hl] at h'
        cases h'
      | ok bs =>
        rw [hl] at h'
        have e : b :: bs = l := Except.ok.inj h'
        subst e
        obtain ⟨l1, l2⟩ := mapM_ok_at f xs bs hl
        refine ⟨by simp [l1], fun i hi => ?_⟩
        cases i with
        | zero => exact ⟨b, rfl, ha⟩
        | succ i =>
          obtain ⟨y, y1, y2⟩ := l2 i (by simpa using hi)
          exact ⟨y, by simpa using y1, by simpa using y2⟩

/-! ## 2 The written column -/

theorem column_congr (P : VerifiableInference.Desc.K1.Par) (V V' : ℕ → Rows) (t x : ℕ)
    (h : ∀ k < P.sent.size, mainSyms P V k x = mainSyms P V' k x ∧
      maskSyms P V k x = maskSyms P V' k x) :
    col P V t x = col P V' t x := by
  unfold col
  simp only
  congr 1
  · exact flatMap_congr_mem _ _ _ fun k hk =>
      (h k (List.mem_range.1 (List.mem_filter.1 hk).1)).1
  · exact flatMap_congr_mem _ _ _ fun k hk =>
      (h k (List.mem_range.1 (List.mem_filter.1 hk).1)).2

theorem symG_congr (C : Fmt.M1.Code) (x : ℕ) (m m' r r' : ℕ → GE)
    (hm : ∀ j < C.l, m j = m' j) (hr : ∀ q < C.r, r q = r' q) :
    symG C x m r = symG C x m' r' := by
  unfold symG
  congr 1
  · exact Finset.sum_congr rfl fun q hq => by rw [hr q (Finset.mem_range.1 hq)]
  · exact Finset.sum_congr rfl fun j hj => by rw [hm j (Finset.mem_range.1 hj)]

/-! ## 3 A sending's rows, by message -/

/-- What rowsAll returned, at one message. -/
theorem rowsAll_at {table : K2.FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (ℕ × ℕ)} {data : ℕ → ℕ → ℕ → Cb.Gl.E}
    {c : Cs (K2.sendingDue codes sent fresh)} {V : ℕ → Rows}
    (h : K2.rowsAll table codes sent fresh data c = .ok V) (k : ℕ) (hk : k < sent.size) :
    ∃ s, (K2.Stretch.of c).cut (K2.dueBefore codes sent fresh k)
        (K2.messageDue codes (sent.getD k default).shape (K2.foldAt fresh k)) = .ok s ∧
      K2.messageRows table codes (sent.getD k default).shape (K2.foldAt fresh k) (data k) s =
        .ok (V k) := by
  unfold K2.rowsAll at h
  split at h
  · cases h
  obtain ⟨l, hl, e⟩ := exMap_ok h
  obtain ⟨-, h2⟩ := mapM_ok_at _ _ _ hl
  obtain ⟨y, y1, y2⟩ := h2 k (by simpa using hk)
  simp only [List.getElem_range] at y2
  obtain ⟨s, s1, s2⟩ := exBind_ok y2
  refine ⟨s, s1, ?_⟩
  rw [s2, ← e]
  simp [List.getD_eq_getElem?_getD, y1]

/-- The entries of a stretch's es, by number. -/
theorem es_getD (s : K2.Stretch) (a n : ℕ) (arr : Array Cb.Gl.E) (h : s.es a n = .ok arr) (i : ℕ)
    (z : Cb.Gl.E) : arr.getD i z = if i < n then (stretchOf s.coins).e (a + i) else z := by
  unfold K2.Stretch.es at h
  obtain ⟨l, hl, e⟩ := exMap_ok h
  obtain ⟨l1, l2⟩ := mapM_ok_at _ _ _ hl
  subst e
  by_cases hi : i < n
  · rw [if_pos hi]
    obtain ⟨y, y1, y2⟩ := l2 i (by simpa using hi)
    have hy : l[i]? = some y := y1
    simp only [List.getElem_range] at y2
    unfold Cs.eAt at y2
    split at y2
    · rename_i hd
      have := Except.ok.inj y2
      simp only [stretchOf, dif_pos hd, this]
      simp [Array.getD_eq_getD_getElem?, hy]
    · cases y2
  · rw [if_neg hi]
    have : l.length ≤ i := by rw [l1]; simpa using hi
    simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_none this]

/-- The hiding polynomial's coefficients read 2 k + 1 numbers alone. -/
theorem hideAt_congr (k : ℕ) (c c' : ℕ → GE) (h : ∀ n < 2 * k + 1, c n = c' n) :
    hideAt k c = hideAt k c' := by
  have e1 := Light.coefU_byName k k rfl (fun n => OnBytes.E.ofTriple (ofE (c n))) c
    (fun n _ => by rw [readE_ofTriple, toE_ofE])
  have e2 := Light.coefU_byName k k rfl (fun n => OnBytes.E.ofTriple (ofE (c n))) c'
    (fun n hn => by rw [readE_ofTriple, toE_ofE]; exact h n hn)
  exact e1.symm.trans e2


/-! ## 4 The fresh message's rows -/

/-- The rows of a message that is a fold's fresh mask: its mask rows are the letter table at the
stretch's first 2 n + 1 coins, its tails the coins behind them. -/
theorem fresh_rows (table : K2.FreshTable) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (n : ℕ) (data : ℕ → ℕ → Cb.Gl.E) (k : K2.Stretch) (R : Rows)
    (h : K2.messageRows table codes s (some n) data k = .ok R) (hm0 : s.mainRows = 0)
    (hk0 : s.maskRows ≠ 0) :
    (∀ r i, r < s.maskRows → i < (codes.mask.getD s.maskCode default).ell →
      R.mask r i = table n (OnBytes.ceilLog2 s.maskRows)
        (fun j => if j < 2 * n + 1 then (stretchOf k.coins).e j else VerifiableInference.Desc.K2.Honest.zeroG) r i) ∧
    ∀ r q, r < s.maskRows → q < (codes.mask.getD s.maskCode default).r →
      R.maskTl r q = (stretchOf k.coins).e
        (2 * n + 1 + (r * (codes.mask.getD s.maskCode default).r + q)) := by
  have hp : (s.maskRows != 0) = true := by simpa using hk0
  unfold K2.messageRows at h
  dsimp only at h
  simp only [hm0, hp, Nat.zero_mul, Nat.zero_add, if_true, List.length_nil, ite_self] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := exBind_ok h
  obtain ⟨_, -, h⟩ := exBind_ok h
  obtain ⟨cF, eF, h⟩ := exBind_ok h
  obtain ⟨cE, eE, h⟩ := exBind_ok h
  obtain ⟨mC, eM, h⟩ := exBind_ok h
  obtain ⟨tC, eT, h⟩ := exBind_ok h
  split at h
  · cases h
  obtain ⟨_, -, h⟩ := exBind_ok h
  have hR := Except.ok.inj h
  subst hR
  refine ⟨fun r i hr hi => ?_, fun r q hr hq => ?_⟩
  · have e : (!(decide (r < s.maskRows) && decide (i < (codes.mask.getD s.maskCode default).ell))) =
        false := by rw [decide_eq_true hr, decide_eq_true hi]; rfl
    show (if _ then _ else _) = _
    rw [if_neg (by rw [e]; simp)]
    congr 1
    funext j
    rw [es_getD k 0 (2 * n + 1) mC eM j _, Nat.zero_add]
  · have e : (decide (r < s.maskRows) && decide (q < (codes.mask.getD s.maskCode default).r)) =
        true := by rw [decide_eq_true hr, decide_eq_true hq]; rfl
    show (if _ then _ else _) = _
    rw [if_pos e, es_getD k (2 * n + 1) _ tC eT _ _, if_pos]
    have h1 : (r + 1) * (codes.mask.getD s.maskCode default).r ≤
        s.maskRows * (codes.mask.getD s.maskCode default).r := Nat.mul_le_mul_right _ hr
    have h2 : (r + 1) * (codes.mask.getD s.maskCode default).r =
        r * (codes.mask.getD s.maskCode default).r + (codes.mask.getD s.maskCode default).r :=
      Nat.succ_mul r _
    omega

/-! ## 5 Words -/

/-- What a table of the sender's form shows of a position is the written column there. -/
theorem table_column (logN w : ℕ) (f : ℕ → List UInt64) (x : ℕ) (hlen : (f x).length = w)
    (hc : ∀ u ∈ f x, ∃ a, u = OnBytes.Slice.ofF a) :
    (⟨logN, w, fun x i => OnBytes.Slice.toF ((f x).getD i.val 0)⟩ : Table).col x = f x := by
  unfold Table.col
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn]
  have hi : i < (f x).length := h2
  rw [List.getD_eq_getElem _ _ hi]
  obtain ⟨a, ha⟩ := hc _ (List.getElem_mem hi)
  rw [ha, OnBytes.Slice.toF_ofF]

theorem column_words_canonical (Q : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (t x : ℕ) :
    ∀ u ∈ col Q V t x, ∃ a, u = OnBytes.Slice.ofF a := by
  intro u hu
  unfold col at hu
  simp only [List.mem_append, List.mem_flatMap] at hu
  rcases hu with ⟨k, -, hu⟩ | ⟨k, -, hu⟩
  · unfold mainSyms at hu
    simp only [List.mem_flatMap] at hu
    obtain ⟨r, -, hu⟩ := hu
    split at hu
    · simp only [Johnson.Prover.Link.words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · simp only [List.mem_singleton] at hu
      exact ⟨_, hu⟩
  · unfold maskSyms at hu
    simp only [List.mem_flatMap] at hu
    obtain ⟨r, -, hu⟩ := hu
    simp only [Johnson.Prover.Link.words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- How many words the written column of a tree has: a public number. -/
def columnWidth (Q : VerifiableInference.Desc.K1.Par) (t : ℕ) : ℕ :=
  let lay := (VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}
  let mine := (List.range Q.sent.size).filter fun k => lay.tree[k]? == some t
  (mine.map fun k => (Johnson.Prover.Send.shapeAt Q k).mainRows *
      (if (Johnson.Prover.Send.shapeAt Q k).mainDeg == 3 then 3 else 1)).sum +
    (mine.map fun k => (Johnson.Prover.Send.shapeAt Q k).maskRows * 3).sum

theorem column_length (Q : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (t x : ℕ) :
    (col Q V t x).length = columnWidth Q t := by
  have key : ∀ (f : ℕ → List UInt64) (g : ℕ → ℕ), (∀ k, (f k).length = g k) → ∀ l : List ℕ,
      (l.flatMap f).length = (l.map g).sum := by
    intro f g h l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, h, ih]
  unfold col columnWidth
  simp only [List.length_append]
  rw [key _ (fun k => (Johnson.Prover.Send.shapeAt Q k).mainRows *
      (if (Johnson.Prover.Send.shapeAt Q k).mainDeg == 3 then 3 else 1)) ?_,
    key _ (fun k => (Johnson.Prover.Send.shapeAt Q k).maskRows * 3) ?_]
  · intro k
    unfold maskSyms
    simp [List.length_flatMap, Johnson.Prover.Link.words3]
  · intro k
    unfold mainSyms
    by_cases h3 : ((Johnson.Prover.Send.shapeAt Q k).mainDeg == 3) = true
    · simp [List.length_flatMap, Johnson.Prover.Link.words3, h3]
    · simp [List.length_flatMap, h3]

/-! ## 6 The public test, clause by clause -/

/-- The test's first stage. -/
abbrev firstStageOf (q : VerifiableInference.Desc.K12.P12) : Fmt.M1.Stage := q.nums.stages.headD default

/-- The sender's trees. -/
abbrev finishTrees (p : K2.SwitchPlace) : OnBytes.TreeLay :=
  (VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}

/-- What fitsL says, as far as this file reads it. -/
structure FitsFacts (q : VerifiableInference.Desc.K12.P12) (p : K2.SwitchPlace) : Prop where
  two : (sentL p).size = 2
  own : q.nums.ownMask = false
  hk : (firstStageOf q).h ≤ (firstStageOf q).k
  fold : (firstStageOf q).k = p.foldVars
  maskRows : 2 ^ (firstStageOf q).h = (freshShapeL p).maskRows
  mainRows : (freshShapeL p).mainRows = 0
  zl : (firstStageOf q).Z.l = (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).ell
  zr : (firstStageOf q).Z.r = (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).r
  ride : K1.rideFits p.sizes.codes (freshShapeL p) ⟨(firstStageOf q).k, (firstStageOf q).h⟩ = true
  behind : q.place = ⟨p.place.chain, none, p.place.piece + 1, .K12⟩
  tree : q.nums.first.map (fun x => (x.1.a, x.1.W)) =
    (finishTrees p).shapes.toList.map fun t => (t.logN, t.mainWidth + t.maskWidth)
  alone : (finishTrees p).shapes.size = 1

theorem fitsL_facts {q : VerifiableInference.Desc.K12.P12} {p : K2.SwitchPlace}
    (h : fitsL q p = true) : FitsFacts q p := by
  unfold fitsL fitsLs at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨two, own, hk, ⟨⟨_, _⟩, _⟩, fold, ⟨n1, n2⟩, ⟨_, _⟩, ⟨z1, z2⟩, ride, _, _, _, _,
    ⟨beh, _⟩, tree, alone⟩ := h
  exact ⟨two, own, hk, fold, n1, n2, z1, z2, ride, beh, tree, alone⟩

/-! ## 7 The column at the finish -/

/-- The messages that treesL hands the written column. -/
def messagesOfJob (p : K2.SwitchPlace) (R₀ : Rows) (P : PS) : ℕ → Rows := fun k =>
  if k == 0 then R₀
  else if k == (sentL p).size - 1 then { K2.zeroMessage with mask := P.fM, maskTl := P.fT }
  else K2.zeroMessage

/-- The sending's public letter. -/
abbrev finishSending (p : K2.SwitchPlace) : VerifiableInference.Desc.K1.Par :=
  K2.sendingPar p.sizes.codes (sentL p)

theorem finishSending_sent (p : K2.SwitchPlace) : (finishSending p).sent = sentL p := by
  simp [VerifiableInference.Desc.K1.Par.sent, K2.sendingPar]

/-- **The column that the sender's messages give is the one that the job's give**, where message 0
is one and the fresh message's rows are made of a stretch whose coins the job's state was laid of. -/
theorem column_at_finish {q : VerifiableInference.Desc.K12.P12} {p : K2.SwitchPlace}
    (F : FitsFacts q p) (data : ℕ → ℕ → Cb.Gl.E) (VS : ℕ → Rows) (R₀ : Rows) (k₁ : K2.Stretch)
    (P : PS) (h0 : VS 0 = R₀)
    (h1 : K2.messageRows K2.freshTable p.sizes.codes (freshShapeL p) (some p.foldVars) data k₁ =
      .ok (VS 1))
    (hfM : P.fM = packedN (sgOf (firstStageOf q))
      (hideAt ((sgOf (firstStageOf q)).h + (sgOf (firstStageOf q)).g) (stretchOf k₁.coins).e))
    (hfT : P.fT = tailsIn (firstStageOf q) (stretchOf k₁.coins).e) (x : ℕ) :
    col (finishSending p) VS 0 x = col (finishSending p) (messagesOfJob p R₀ P) 0 x := by
  have hs := finishSending_sent p
  have hsh : Johnson.Prover.Send.shapeAt (finishSending p) 1 = freshShapeL p := by
    unfold Johnson.Prover.Send.shapeAt freshShapeL
    rw [hs, F.two]
  have hK : (sgOf (firstStageOf q)).h + (sgOf (firstStageOf q)).g = (firstStageOf q).k := by
    show (firstStageOf q).h + ((firstStageOf q).k - (firstStageOf q).h) = (firstStageOf q).k
    have := F.hk
    omega
  have hnz : (freshShapeL p).maskRows ≠ 0 := by
    rw [← F.maskRows]
    exact Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _)
  have hroom : 2 * (firstStageOf q).k + 1 ≤ (firstStageOf q).h + (firstStageOf q).Z.l := by
    have hr := F.ride
    unfold K1.rideFits at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    have := hr.2
    have := F.hk
    have := F.zl
    omega
  obtain ⟨m1, m2⟩ := fresh_rows K2.freshTable _ _ _ _ _ _ h1 F.mainRows hnz
  have hcl : OnBytes.ceilLog2 (freshShapeL p).maskRows = (firstStageOf q).h := by
    rw [← F.maskRows]
    exact OnBytes.Slice.ceilLog2_two_pow _
  refine column_congr _ _ _ _ _ fun k hk => ?_
  rw [hs, F.two] at hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · have e : VS 0 = messagesOfJob p R₀ P 0 := by simp [messagesOfJob, h0]
    exact ⟨by unfold mainSyms; simp only [e], by unfold maskSyms; simp only [e]⟩
  · have e : messagesOfJob p R₀ P 1 = { K2.zeroMessage with mask := P.fM, maskTl := P.fT } := by
      simp [messagesOfJob, F.two]
    refine ⟨?_, ?_⟩
    · unfold mainSyms
      simp only [hsh, F.mainRows]
      rfl
    · unfold maskSyms
      simp only [hsh, e]
      refine flatMap_congr_mem _ _ _ fun r hr => ?_
      have hr' := List.mem_range.1 hr
      have hb : r < 2 ^ (firstStageOf q).h := by rw [F.maskRows]; exact hr'
      rw [symG_congr _ _ ((VS 1).mask r) (P.fM r) ((VS 1).maskTl r) (P.fT r) (fun j hj => ?_) fun t ht => ?_]
      · have hj' : j < (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).ell := hj
        rw [m1 r j hr' hj', hfM, hcl, ← F.fold]
        show (⟨(firstStageOf q).k, (firstStageOf q).h⟩ : K1.Ride).lay _ r j = _
        rw [lay_is_packed (firstStageOf q) F.hk hroom _ r j hb (by rw [F.zl]; exact hj')]
        have e2 := hideAt_congr ((sgOf (firstStageOf q)).h + (sgOf (firstStageOf q)).g)
          (fun j => if j < 2 * (firstStageOf q).k + 1 then (stretchOf k₁.coins).e j
            else VerifiableInference.Desc.K2.Honest.zeroG) (stretchOf k₁.coins).e
          (fun n hn => if_pos (by rw [hK] at hn; exact hn))
        rw [e2]
      · have ht' : t < (p.sizes.codes.mask.getD (freshShapeL p).maskCode default).r := ht
        rw [m2 r t hr' ht', hfT, ← F.fold]
        unfold tailsIn
        rw [F.zr]
        exact congrArg _ (by omega)

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.column_at_finish
#print axioms ProofFile.Honest.K12.Sim2.column_length
#print axioms ProofFile.Honest.K12.Sim2.column_words_canonical
#print axioms ProofFile.Honest.K12.Sim2.table_column
#print axioms ProofFile.Honest.K12.Sim2.fresh_rows
#print axioms ProofFile.Honest.K12.Sim2.fitsL_facts
#print axioms ProofFile.Honest.K12.Sim2.column_congr
#print axioms ProofFile.Honest.K12.Sim2.symG_congr
#print axioms ProofFile.Honest.K12.Sim2.rowsAll_at
#print axioms ProofFile.Honest.K12.Sim2.es_getD
#print axioms ProofFile.Honest.K12.Sim2.hideAt_congr
