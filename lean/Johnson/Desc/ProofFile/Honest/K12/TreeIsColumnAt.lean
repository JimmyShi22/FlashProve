-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreeIsColumnAt.lean: at the jobs of the shared chain's two
proximity tests (`jobAtU`, `jobAtOmega`, JobShared.lean), the column of a tree that the first round
of positions opens is, at every position, the column of the table that the sending built
(`columnOf`, Johnson/Desc/ProofFile/Honest/K14/Sendings.lean): for both trees of `jobAtU` and the
first two of `jobAtOmega`. The job's side is taken as `TestJob.trees₀` gives it at
`TestJob.first` (Test.lean). It imports Mathlib.

  `mineOf`, `columnOf_mine`   the messages of a sending that lie in its tree number μ, by
                 `treesMade` (Johnson/Desc/Own/Trees.lean); `columnOf` over that list
  `colFitsU`, `colFitsOmega`   a public check on the sendings' data and the test's first stage:
                 which messages lie in which tree; the code that a member's own shape names is the
                 stage's, length too; the member with main rows has no mask row and its rows are
                 over the extension field; the other has no main row; each block lies within the
                 stage; h ≤ k
  `SameCut J k cs c`   a premise, on numbers: the sending's value number offset + i decodes to the
                 member's value number i, for i below the message's count
  `vecAt`        the vector that `memOfSending` hands to `laid`
  `trees₀_many`, `column_many`, `rows_many`, `first_many`   at a job with two members: a tree's
                 column from its pieces; the stage's lists; the first state's four tables
  `mems_atU`, `mems_atOmega`, `pieces_atU`, `pieces_atOmega`   the two makers' members and pieces
  `tree0_atU`, `tree1_atU`, `tree0_atOmega`, `tree1_atOmega`   the four statements

By what. TreeIsColumn.lean's `main_piece`, `mask_piece`, `fresh_piece` and `read_congr`;
`spot_perm_sent` (KeptLaw3.lean); for the first fresh table, which rides in o_u's tree, `fresh_atU`
(FreshAtJob.lean).

Limits.
- Three premises are not public and are shown nowhere here. `SameCut`, and `SameFresh`
  (FreshAtJob.lean) for the riding table: that a member's random values are the sender's, cut from
  the message's offset on, is up to the book of lent values. "The same vector": that the vector
  which the member carries is the one that the sender computed at its own state is up to the caller.
- Nothing on a tree's depth. Nothing on the third tree of `jobAtOmega`, the fold's own fresh table,
  which no sending builds.
- Nothing says that a table with these columns was sent, or that a run lists them.
- No definition evaluates the two checks. TreeIsColumnSmall.lean has them at the small plan.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumn
import Johnson.Desc.ProofFile.Honest.K12.FreshAtJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (zeroE)
open OnBytes.Slice (GE ofE toE readE readE_ofTriple toE_ofE)
open Fmt.M1 (Stage)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendJob SendPub jobU jobOmega laid dueOf offsetOf symbolsOf columnOf Ask
  sendingsFit)

variable {W X : Type}

/-! ## 1 The check and the premises -/

/-- The messages of a sending that lie in its tree number μ. -/
def mineOf (J : SendJob) (μ : ℕ) : List ℕ :=
  (List.range J.Q.sent.size).filter fun k =>
    ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).tree[k]? == some μ

theorem columnOf_mine (J : SendJob) (L : ℕ → ProofFile.Honest.K14.Laid) (μ x : ℕ) :
    columnOf J.Q.codes J.Q.sent L μ x =
      ((mineOf J μ).flatMap fun k =>
        symbolsOf (J.Q.codes.base.getD (shapeAt J k).code default) x (shapeAt J k).mainRows
          (L k).main (L k).mainTail) ++
      (mineOf J μ).flatMap fun k =>
        symbolsOf (J.Q.codes.mask.getD (shapeAt J k).maskCode default)
          (x % 2 ^ (J.Q.codes.mask.getD (shapeAt J k).maskCode default).logN)
          (shapeAt J k).maskRows (L k).mask (L k).maskTail := rfl

/-- What both checks ask of a test's two members: J0's message 0, with main rows; J1's message 1,
o_sp, with mask rows. -/
def pairFits (J0 : SendJob) (J1 : SendJob) (s : Stage) : Bool :=
  let o0 := shapeAt J0 0
  let o1 := shapeAt J1 1
  let fs := firstsOf [o0, o1]
  sameCode (J0.Q.codes.base.getD o0.code default) s.C &&
    sameCode (J1.Q.codes.mask.getD o1.maskCode default) s.Z &&
    o0.maskRows == 0 && o1.mainRows == 0 && o0.mainDeg != 1 &&
    decide ((fs.getD 0 (none, none)).1.getD 0 + o0.mainRows ≤ 2 ^ s.k) &&
    decide ((fs.getD 1 (none, none)).2.getD 0 + o1.maskRows ≤ 2 ^ s.h) && decide (s.h ≤ s.k)

/-- **The public check for the test on G_u.** -/
def colFitsU (A : SendPub) (p : P12) : Bool :=
  mineOf (jobU A) 0 == [0, 1] && mineOf (jobOmega A) 1 == [1] &&
    pairFits (jobU A) (jobOmega A) (stage₀ p)

/-- **The public check for the test on G_omega.** -/
def colFitsOmega (A : SendPub) (p : P12) : Bool :=
  mineOf (jobOmega A) 0 == [0] && mineOf (jobOmega A) 1 == [1] &&
    pairFits (jobOmega A) (jobOmega A) (stage₀ p)

/-- **"The member's values are the sender's, cut from the message's offset on, by its count."** cs:
the sending's own values. c: the member's. -/
def SameCut (J : SendJob) (k : ℕ) (cs : Array OnBytes.E) (c : Stretch) : Prop :=
  ∀ i < dueOf J.Q.codes (shapeAt J k) (J.sort k),
    readE (cs.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i) zeroE) = c.e i

/-- The vector that `memOfSending` hands to `laid`. -/
def vecAt (J : SendJob) (k : ℕ) (ask : W → Ask) (v? : Option (W → Front X → ℕ → OnBytes.E)) (w : W)
    (fr : Front X) : ℕ → OnBytes.E :=
  match v? with
  | some v => v w fr
  | none => J.data ⟨ask w, fr.heard, ()⟩ k

/-! ## 2 The entries -/

theorem wordsAt_append (sym : Sel → Fmt.M1.E) (a b : List Sel) :
    wordsAt sym (a ++ b) = wordsAt sym a ++ wordsAt sym b := by
  unfold wordsAt
  rw [List.flatMap_append]

theorem symbolsOf_none (c : OnBytes.Code) (x : ℕ) (row tail : ℕ → ℕ → OnBytes.E) :
    symbolsOf c x 0 row tail = [] := rfl

/-- A message that `mineOf` lists is one of the sending's. -/
theorem lt_of_mine {J : SendJob} {μ k : ℕ} (h : k ∈ mineOf J μ) : k < J.Q.sent.size :=
  List.mem_range.1 (List.mem_filter.1 h).1

/-- The entries of the member's rows and of the sender's, decoded, are the same at every tabulated
place. J: one of the two sendings at the plan Q. -/
theorem entries_same (Q : Desc.K14.P14) (hQ : sendingsFit Q = true) (J : SendJob)
    (hJ : J.Q = (jobU ⟨Q, 0⟩).Q ∧ J.sort = (jobU ⟨Q, 0⟩).sort ∨
      J.Q = (jobOmega ⟨Q, 0⟩).Q ∧ J.sort = (jobOmega ⟨Q, 0⟩).sort)
    (k : ℕ) (hk : k < J.Q.sent.size) (high : Bool) (hs : J.sort k = .plain high)
    (v : ℕ → OnBytes.E) (cs : Array OnBytes.E) (c : Stretch) (same : SameCut J k cs c) (x : Spot)
    (hx : x ∈ spotsOf J.Q.codes (shapeAt J k)) :
    readE ((laid J.Q.codes (shapeAt J k) v (fun i => OnBytes.E.ofTriple (ofE (c.e i)))
        (J.sort k)).read x) =
      readE ((laid J.Q.codes (shapeAt J k) v
        (fun i => cs.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i) zeroE) (J.sort k)).read
          x) := by
  have hp : ((spotsOf J.Q.codes (shapeAt J k)).filterMap (coinOf J.Q.codes (shapeAt J k))).Perm
      (List.range (dueOf J.Q.codes (shapeAt J k) (.plain high))) := by
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have := spot_perm_sent Q hQ (jobU ⟨Q, 0⟩) (.inl rfl) k (by rw [← e1]; exact hk) high
        (by rw [← e2]; exact hs)
      unfold shapeAt
      rw [e1]
      exact this
    · have := spot_perm_sent Q hQ (jobOmega ⟨Q, 0⟩) (.inr rfl) k (by rw [← e1]; exact hk) high
        (by rw [← e2]; exact hs)
      unfold shapeAt
      rw [e1]
      exact this
  unfold SameCut at same
  rw [hs] at same ⊢
  refine read_congr _ _ v _ _ high hp (fun i hi => ?_) x hx
  rw [readE_ofTriple, toE_ofE, same i hi]

theorem mem_main {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {r j : ℕ} (hr : r < s.mainRows)
    (hj : j < (codes.base.getD s.code default).ell) : Spot.main r j ∈ spotsOf codes s :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (mem_grid.2 ⟨r, hr, j, hj, rfl⟩)))

theorem mem_mainTail {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {r t : ℕ}
    (hr : r < s.mainRows) (ht : t < (codes.base.getD s.code default).r) :
    Spot.mainTail r t ∈ spotsOf codes s :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_grid.2 ⟨r, hr, t, ht, rfl⟩)))

theorem mem_mask {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {r j : ℕ} (hr : r < s.maskRows)
    (hj : j < (codes.mask.getD s.maskCode default).ell) : Spot.mask r j ∈ spotsOf codes s :=
  List.mem_append_left _ (List.mem_append_right _ (mem_grid.2 ⟨r, hr, j, hj, rfl⟩))

theorem mem_maskTail {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {r t : ℕ}
    (hr : r < s.maskRows) (ht : t < (codes.mask.getD s.maskCode default).r) :
    Spot.maskTail r t ∈ spotsOf codes s :=
  List.mem_append_right _ (mem_grid.2 ⟨r, hr, t, ht, rfl⟩)

/-! ## 3 The two pieces at a pair of members -/

section Pair
variable (Q : Desc.K14.P14) (hQ : sendingsFit Q = true) (J0 J1 : SendJob)
  (h0 : J0.Q = (jobU ⟨Q, 0⟩).Q ∧ J0.sort = (jobU ⟨Q, 0⟩).sort ∨
    J0.Q = (jobOmega ⟨Q, 0⟩).Q ∧ J0.sort = (jobOmega ⟨Q, 0⟩).sort)
  (h1 : J1.Q = (jobU ⟨Q, 0⟩).Q ∧ J1.sort = (jobU ⟨Q, 0⟩).sort ∨
    J1.Q = (jobOmega ⟨Q, 0⟩).Q ∧ J1.sort = (jobOmega ⟨Q, 0⟩).sort)
  (s : Stage) (hf : pairFits J0 J1 s = true) (a0 a1 : Addr) (ask : W → Ask)
  (v? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (c0 c1 : Stretch)

/-- The member with main rows, as both makers lay it. -/
def memA : Mem W X :=
  memOfSending J0 a0 0 ((firstsOf [shapeAt J0 0, shapeAt J1 1]).getD 0 (none, none)) ask v?

/-- o_sp as a member, as both makers lay it. -/
def memB : Mem W X :=
  memOfSending J1 a1 1 ((firstsOf [shapeAt J0 0, shapeAt J1 1]).getD 1 (none, none)) ask none

/-- The stage's lists at these two members. -/
def pairRows : Fmt.M1.Own.PSt :=
  layFirst s [((memA J0 J1 a0 ask v?).shape, (memA J0 J1 a0 ask v?).rows w fr c0),
    ((memB (X := X) J0 J1 a1 ask).shape, (memB J0 J1 a1 ask).rows w fr c1)]

include hQ h0 hf in
/-- Member 0's main rows against the sender's. -/
theorem pair_main (k0 : 0 < J0.Q.sent.size) (high : Bool) (hs : J0.sort 0 = .plain high)
    (P : Johnson.Prover.Link.PS)
    (hP : P.tabM = (readPS s (pairRows J0 J1 s a0 a1 ask v? w fr c0 c1)).tabM)
    (hT : P.tM = (readPS s (pairRows J0 J1 s a0 a1 ask v? w fr c0 c1)).tM)
    (st : State Ask Unit) (cs : Array OnBytes.E) (same : SameCut J0 0 cs c0)
    (hv : vecAt J0 0 ask v? w fr = J0.data st 0) (x : ℕ) :
    wordsAt (symOf s P x)
        (selsOf s [(memA J0 J1 a0 ask v?).shape, (memB (X := X) J0 J1 a1 ask).shape] (.main 0)) =
      symbolsOf (J0.Q.codes.base.getD (shapeAt J0 0).code default) x (shapeAt J0 0).mainRows
        (J0.rows st cs 0).main (J0.rows st cs 0).mainTail := by
  unfold pairFits at hf
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, _⟩, _⟩, _⟩, hd⟩, hin⟩, _⟩, hk⟩ := hf
  have hb : ((shapeAt J0 0).mainDeg == 1) = false := by
    simpa using hd
  refine main_piece s hk _ hC _ _ _ _
    (laid J0.Q.codes (shapeAt J0 0) (vecAt J0 0 ask v? w fr)
      (fun i => OnBytes.E.ofTriple (ofE (c0.e i))) (J0.sort 0)) (J0.rows st cs 0)
    (shapeAt J0 0).mainRows P x rfl rfl rfl hb hin hP hT (fun r hr j hj => ?_) fun r hr t ht => ?_
  · have e := entries_same Q hQ J0 h0 0 k0 high hs (vecAt J0 0 ask v? w fr) cs c0 same
      (.main r j) (mem_main hr hj)
    rw [hv] at e ⊢
    exact e
  · have e := entries_same Q hQ J0 h0 0 k0 high hs (vecAt J0 0 ask v? w fr) cs c0 same
      (.mainTail r t) (mem_mainTail hr ht)
    rw [hv] at e ⊢
    exact e

include hQ h1 hf in
/-- Member 1's mask rows against the sender's. -/
theorem pair_mask (k1 : 1 < J1.Q.sent.size) (high : Bool) (hs : J1.sort 1 = .plain high)
    (P : Johnson.Prover.Link.PS)
    (hP : P.tabZ = (readPS s (pairRows J0 J1 s a0 a1 ask v? w fr c0 c1)).tabZ)
    (hT : P.tZ = (readPS s (pairRows J0 J1 s a0 a1 ask v? w fr c0 c1)).tZ)
    (st : State Ask Unit) (cs : Array OnBytes.E) (same : SameCut J1 1 cs c1) (x : ℕ) :
    wordsAt (symOf s P x)
        (selsOf s [(memA J0 J1 a0 ask v?).shape, (memB (X := X) J0 J1 a1 ask).shape] (.mask 1)) =
      symbolsOf (J1.Q.codes.mask.getD (shapeAt J1 1).maskCode default)
        (x % 2 ^ (J1.Q.codes.mask.getD (shapeAt J1 1).maskCode default).logN)
        (shapeAt J1 1).maskRows (J1.rows st cs 1).mask (J1.rows st cs 1).maskTail := by
  unfold pairFits at hf
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hZ⟩, hm0⟩, _⟩, _⟩, _⟩, hin⟩, _⟩ := hf
  refine mask_piece s _ hZ _ _ _ _
    (laid J1.Q.codes (shapeAt J1 1) (J1.data st 1)
      (fun i => OnBytes.E.ofTriple (ofE (c1.e i))) (J1.sort 1)) (J1.rows st cs 1)
    (shapeAt J1 1).maskRows P x ?_ ?_ hm0 rfl hin hP hT (fun r hr j hj => ?_) fun r hr t ht => ?_
  · exact tabE_congr _ _ _ _ fun r hr j hj => by
      rw [hs]
      rfl
  · exact tabE_congr _ _ _ _ fun r hr t ht => by
      rw [hs]
      rfl
  · exact entries_same Q hQ J1 h1 1 k1 high hs (J1.data st 1) cs c1 same (.mask r j)
      (mem_mask hr hj)
  · exact entries_same Q hQ J1 h1 1 k1 high hs (J1.data st 1) cs c1 same (.maskTail r t)
      (mem_maskTail hr ht)

end Pair

/-! ## 4 A job with these two members -/

section Many
variable (B : ManyJob W X) (mA mB : Mem W X) (hm : B.mems = [mA, mB]) (w : W) (fr : Front X)

/-- The trees of the `TestJob`, from the pieces. -/
theorem trees₀_many (mem : ℕ → Stretch) (P : Johnson.Prover.Link.PS) :
    B.toRun.toTest.trees₀ w fr mem P =
      B.trees.map fun T =>
        treeOf B.s₀ (T.1, T.2.flatMap (selsOf B.s₀ (B.mems.map (·.shape)))) P := by
  show (treesOf B.s₀ (B.mems.map (·.shape)) B.trees).map (fun T => treeOf B.s₀ T P) = _
  unfold treesOf
  rw [List.map_map]
  rfl

include hm in
/-- Tree number i's column, from its pieces. -/
theorem column_many (mem : ℕ → Stretch) (P : Johnson.Prover.Link.PS) (i d : ℕ)
    (ps : List Piece) (ht : B.trees[i]? = some (d, ps)) (x : ℕ) :
    ((B.toRun.toTest.trees₀ w fr mem P).getD i (0, fun _ => [])).2 x =
      wordsAt (symOf B.s₀ P x) (ps.flatMap (selsOf B.s₀ [mA.shape, mB.shape])) := by
  rw [trees₀_many, List.getD_eq_getElem?_getD, List.getElem?_map, ht, hm]
  rfl

include hm in
/-- The stage's lists at the two members. -/
theorem rows_many (mem : ℕ → Stretch) :
    B.toRun.rows w fr mem =
      layFirst B.s₀ [(mA.shape, mA.rows w fr (mem 0)), (mB.shape, mB.rows w fr (mem 1))] := by
  show layFirst B.s₀ (B.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem m.2))) = _
  rw [hm]
  rfl

include hm in
/-- The first state's four tables are read off these lists. -/
theorem first_many (C : TestCoins) :
    (B.toRun.toTest.first w fr C).tabM = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1))])).tabM ∧
      (B.toRun.toTest.first w fr C).tM = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1))])).tM ∧
      (B.toRun.toTest.first w fr C).tabZ = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1))])).tabZ ∧
      (B.toRun.toTest.first w fr C).tZ = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1))])).tZ := by
  rw [← rows_many B mA mB hm w fr C.mem]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Many

/-! ## 5 The two jobs' members and pieces -/

section Jobs
variable (A : SendPub) (p : P12) (door : W → Front X → T12)
  (weights : W → Weights) (rand : W → TableRand) (v? : Option (W → Front X → ℕ → OnBytes.E))

theorem mems_atU : (jobAtU A p door weights rand v?).mems =
    [memA (jobU A) (jobOmega A) ⟨ProofFile.Honest.K14.sendPlace 2, 0⟩ (askOf A weights rand) v?,
      memB (jobU A) (jobOmega A) ⟨ProofFile.Honest.K14.sendPlace 5, 0⟩ (askOf A weights rand)] := rfl

theorem mems_atOmega : (jobAtOmega A p door weights rand v?).mems =
    [memA (jobOmega A) (jobOmega A) ⟨ProofFile.Honest.K14.sendPlace 5, 0⟩ (askOf A weights rand) v?,
      memB (jobOmega A) (jobOmega A) ⟨ProofFile.Honest.K14.sendPlace 5, 0⟩ (askOf A weights rand)] := rfl

theorem pieces_atU : ∃ d0 d1, (jobAtU A p door weights rand v?).trees =
    [(d0, [.main 0, .fresh]), (d1, [.mask 1])] := ⟨_, _, rfl⟩

theorem pieces_atOmega : ∃ d0 d1 d2, (jobAtOmega A p door weights rand v?).trees =
    [(d0, [.main 0]), (d1, [.mask 1]), (d2, [.fresh])] := ⟨_, _, _, rfl⟩

/-! ## 6 The four statements -/

variable (hQ : sendingsFit A.P = true) (w : W) (fr : Front X) (C : TestCoins)
  (st : State Ask Unit) (cs : Array OnBytes.E) (x : ℕ)

include hQ in
/-- **o_u's tree, with the first fresh table that rides in it.** st, cs: the state and the values of
"send o_u". -/
theorem tree0_atU (hc : colFitsU A p = true) (hfr : freshFitsU A p = true)
    (hroom : 2 * (stage₀ p).k + 1 ≤ (stage₀ p).h + (stage₀ p).Z.l)
    (cut : SameCut (jobU A) 0 cs (C.mem 0))
    (ride : SameFresh (stage₀ p) (fun i =>
      cs.getD (offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1 + i) zeroE) C)
    (hv : vecAt (jobU A) 0 (askOf A weights rand) v? w fr = (jobU A).data st 0) :
    (((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtU A p door weights rand v?).toRun.toTest.first w fr C)).getD 0 (0, fun _ => [])).2 x =
      columnOf (jobU A).Q.codes (jobU A).Q.sent ((jobU A).rows st cs) 0 x := by
  unfold colFitsU at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hm0, _⟩, hf⟩ := hc
  have k0 : 0 < (jobU A).Q.sent.size := lt_of_mine (μ := 0) (by rw [hm0]; simp)
  have hf' := hf
  unfold pairFits at hf'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hk0⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hf'
  have hfr' := hfr
  unfold freshFitsU at hfr'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfr'
  obtain ⟨⟨⟨⟨⟨_, hr0⟩, hr1⟩, hz⟩, _⟩, _⟩ := hfr'
  obtain ⟨fm, ft⟩ := fresh_atU A p hfr hroom door weights rand v? w fr C ((jobU A).data st 1) _ ride
  obtain ⟨d0, d1, ht⟩ := pieces_atU A p door weights rand v?
  obtain ⟨t1, t2, _, _⟩ := first_many _ _ _ (mems_atU A p door weights rand v?) w fr C
  rw [column_many _ _ _ (mems_atU A p door weights rand v?) w fr C.mem _ 0 d0 [.main 0, .fresh]
    (by rw [ht]; rfl) x, columnOf_mine, hm0]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hr0, hk0, symbolsOf_none, symbolsOf_none, List.append_nil, List.nil_append, hr1,
    wordsAt_append]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact pair_main A.P hQ (jobU A) (jobOmega A) (.inl ⟨rfl, rfl⟩) (stage₀ p) hf _ _ _ v? w fr
      (C.mem 0) (C.mem 1) k0 _ rfl _ t1 t2 st cs cut hv x
  · exact fresh_piece (stage₀ p) _ hz _ ((jobU A).rows st cs 1) _ x fm ft

include hQ in
/-- **o_sp's tree, at the test on G_u.** st, cs: the state and the values of "send o_omega". -/
theorem tree1_atU (hc : colFitsU A p = true) (cut : SameCut (jobOmega A) 1 cs (C.mem 1)) :
    (((jobAtU A p door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtU A p door weights rand v?).toRun.toTest.first w fr C)).getD 1 (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent ((jobOmega A).rows st cs) 1 x := by
  unfold colFitsU at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨_, hm1⟩, hf⟩ := hc
  have k1 : 1 < (jobOmega A).Q.sent.size := lt_of_mine (μ := 1) (by rw [hm1]; simp)
  have hf' := hf
  unfold pairFits at hf'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hr0⟩, _⟩, _⟩, _⟩, _⟩ := hf'
  obtain ⟨d0, d1, ht⟩ := pieces_atU A p door weights rand v?
  obtain ⟨_, _, t3, t4⟩ := first_many _ _ _ (mems_atU A p door weights rand v?) w fr C
  rw [column_many _ _ _ (mems_atU A p door weights rand v?) w fr C.mem _ 1 d1 [.mask 1]
    (by rw [ht]; rfl) x, columnOf_mine, hm1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hr0, symbolsOf_none, List.nil_append]
  exact pair_mask A.P hQ (jobU A) (jobOmega A) (.inr ⟨rfl, rfl⟩) (stage₀ p) hf _ _ _ v? w fr
    (C.mem 0) (C.mem 1) k1 _ rfl _ t3 t4 st cs cut x

include hQ in
/-- **o_omega's tree.** st, cs: the state and the values of "send o_omega". -/
theorem tree0_atOmega (hc : colFitsOmega A p = true) (cut : SameCut (jobOmega A) 0 cs (C.mem 0))
    (hv : vecAt (jobOmega A) 0 (askOf A weights rand) v? w fr = (jobOmega A).data st 0) :
    (((jobAtOmega A p door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtOmega A p door weights rand v?).toRun.toTest.first w fr C)).getD 0
        (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent ((jobOmega A).rows st cs) 0 x := by
  unfold colFitsOmega at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hm0, _⟩, hf⟩ := hc
  have k0 : 0 < (jobOmega A).Q.sent.size := lt_of_mine (μ := 0) (by rw [hm0]; simp)
  have hf' := hf
  unfold pairFits at hf'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hk0⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hf'
  obtain ⟨d0, d1, d2, ht⟩ := pieces_atOmega A p door weights rand v?
  obtain ⟨t1, t2, _, _⟩ := first_many _ _ _ (mems_atOmega A p door weights rand v?) w fr C
  rw [column_many _ _ _ (mems_atOmega A p door weights rand v?) w fr C.mem _ 0 d0 [.main 0]
    (by rw [ht]; rfl) x, columnOf_mine, hm0]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hk0, symbolsOf_none, List.append_nil]
  exact pair_main A.P hQ (jobOmega A) (jobOmega A) (.inr ⟨rfl, rfl⟩) (stage₀ p) hf _ _ _ v? w fr
    (C.mem 0) (C.mem 1) k0 _ rfl _ t1 t2 st cs cut hv x

include hQ in
/-- **o_sp's tree, at the test on G_omega.** -/
theorem tree1_atOmega (hc : colFitsOmega A p = true) (cut : SameCut (jobOmega A) 1 cs (C.mem 1)) :
    (((jobAtOmega A p door weights rand v?).toRun.toTest.trees₀ w fr C.mem
      ((jobAtOmega A p door weights rand v?).toRun.toTest.first w fr C)).getD 1
        (0, fun _ => [])).2 x =
      columnOf (jobOmega A).Q.codes (jobOmega A).Q.sent ((jobOmega A).rows st cs) 1 x := by
  unfold colFitsOmega at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨_, hm1⟩, hf⟩ := hc
  have k1 : 1 < (jobOmega A).Q.sent.size := lt_of_mine (μ := 1) (by rw [hm1]; simp)
  have hf' := hf
  unfold pairFits at hf'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hr0⟩, _⟩, _⟩, _⟩, _⟩ := hf'
  obtain ⟨d0, d1, d2, ht⟩ := pieces_atOmega A p door weights rand v?
  obtain ⟨_, _, t3, t4⟩ := first_many _ _ _ (mems_atOmega A p door weights rand v?) w fr C
  rw [column_many _ _ _ (mems_atOmega A p door weights rand v?) w fr C.mem _ 1 d1 [.mask 1]
    (by rw [ht]; rfl) x, columnOf_mine, hm1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hr0, symbolsOf_none, List.nil_append]
  exact pair_mask A.P hQ (jobOmega A) (jobOmega A) (.inr ⟨rfl, rfl⟩) (stage₀ p) hf _ _ _ v? w fr
    (C.mem 0) (C.mem 1) k1 _ rfl _ t3 t4 st cs cut x

end Jobs

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.mineOf
#print axioms ProofFile.Honest.K12.Light.columnOf_mine
#print axioms ProofFile.Honest.K12.Light.pairFits
#print axioms ProofFile.Honest.K12.Light.colFitsU
#print axioms ProofFile.Honest.K12.Light.colFitsOmega
#print axioms ProofFile.Honest.K12.Light.SameCut
#print axioms ProofFile.Honest.K12.Light.vecAt
#print axioms ProofFile.Honest.K12.Light.wordsAt_append
#print axioms ProofFile.Honest.K12.Light.symbolsOf_none
#print axioms ProofFile.Honest.K12.Light.lt_of_mine
#print axioms ProofFile.Honest.K12.Light.entries_same
#print axioms ProofFile.Honest.K12.Light.mem_main
#print axioms ProofFile.Honest.K12.Light.mem_mainTail
#print axioms ProofFile.Honest.K12.Light.mem_mask
#print axioms ProofFile.Honest.K12.Light.mem_maskTail
#print axioms ProofFile.Honest.K12.Light.memA
#print axioms ProofFile.Honest.K12.Light.memB
#print axioms ProofFile.Honest.K12.Light.pairRows
#print axioms ProofFile.Honest.K12.Light.pair_main
#print axioms ProofFile.Honest.K12.Light.pair_mask
#print axioms ProofFile.Honest.K12.Light.trees₀_many
#print axioms ProofFile.Honest.K12.Light.column_many
#print axioms ProofFile.Honest.K12.Light.rows_many
#print axioms ProofFile.Honest.K12.Light.first_many
#print axioms ProofFile.Honest.K12.Light.mems_atU
#print axioms ProofFile.Honest.K12.Light.mems_atOmega
#print axioms ProofFile.Honest.K12.Light.pieces_atU
#print axioms ProofFile.Honest.K12.Light.pieces_atOmega
#print axioms ProofFile.Honest.K12.Light.tree0_atU
#print axioms ProofFile.Honest.K12.Light.tree1_atU
#print axioms ProofFile.Honest.K12.Light.tree0_atOmega
#print axioms ProofFile.Honest.K12.Light.tree1_atOmega
