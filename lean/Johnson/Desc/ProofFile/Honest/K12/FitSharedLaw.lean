-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FitSharedLaw.lean: what the public checks of FitShared.lean give
at the jobs of the shared chain's two proximity tests (`jobAtU`, `jobAtOmega`, JobShared.lean). It
imports Mathlib.

  `rowsFit_atU`, `rowsFit_atOmega`   where `sharedFitsU` (`sharedFitsOmega`) is true,
                 `RunJob.rowsFit` is true at the job for every state function, every pair of
                 readers, every vector passed in, every input, whatever precedes the test, and all
                 random values
  `freshFitsU_says`   the clauses of `freshFitsU` as equations
  `freshFits_atU`, `freshFits_atOmega`   `TestJob.freshFits` (Test.lean) is true at the job
  `freshDue_atU`   the sender's count of the fresh table's random values (`dueOf`) is the test's
                 (`dueFresh`, Coins.lean)
  `freshCoef_atU`, `freshTail_atU`   the sender's side: its fresh rows are `freshRow` at its values
                 number `coefAt k l t`, and tail entry q of row b is value number 2 * k + 1 + b *
                 Z.r + q, with k and Z the first stage's
  `freshTest_atU`, `restCoins_tails`, `tailsIn_eq`   the test's side, at the job: the first state's
                 fresh table is `packedN` of `byName` at the values number `coefAt k l t` of
                 `C.hide`, for any C; the tails of `restCoins J c` (Parts.lean) are `tailsIn` of its
                 `hide`; `tailsIn` reads number 2 * k + 1 + b * Z.r + q
  `coinsOf_W0`, `freshSums_atU`   the test's side, the second reading: field `W` of `coinsOf`
                 (Coins.lean) at stage 0, from which the first fold's rounds are computed, is
                 `byName` at the same numbers of `C.hide`
  `freshTails_atU`   the first state's tails of the fresh table are `C.tails`
  `hideAt_coef`  `hideAt k` (Coins.lean) reads the numbers `coefAt k`, for any k
  `layFits_pub`, `layFits_congr`   `ManyJob.layFits` equals `layFitsPub` at the state's public part,
                 so it has the same value at two states with the same public part
  `layFits_all`  where a job's state on entry has the public part P for every input and whatever
                 precedes the test, and `layFitsPub` is true at P, `layFits` is true at all of them
  `layFits_noState`   `layFits` is false at `noState` (JobShared.lean)
  `pubOf_stateOfPub`, `pubOf_doorOf`, `layFits_atDoor`   the public part of `stateOfPub P` is P; at
                 `doorOf` (JobShared.lean) with `fall := stateOfPub P` the state on entry has the
                 public part P for every input and whatever precedes the test, if the fold over the
                 blocks before the test and `enter` give such a state wherever both return; so
                 `layFits` is true at all of them where `layFitsPub` is true at P

By what. A row of `layRows` is a member's row, whose length is its code's, or a list of zeros of the
stage's length (`sized_layRows`, `length_tabE`). The test calls `hideAt` at h + (k - h), which is k
where h ≤ k. `Statement.layout` (OnBytes/Iop/Ground.lean) reads a statement's codes, a group's
numbers and the oracle messages' shapes (`layout_pub`).

Limits. Those of FitShared.lean, which also lists what is not proved of the first fresh table. The
theorems speak of lengths, counts and numbers of random values, not of the values. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitShared
import Johnson.Desc.ProofFile.Honest.K12.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendJob SendPub jobU jobOmega laid dueOf Ask)
open H2K.Pub (sgOf)
open Johnson.Prover.Link (packedN)

variable {W X : Type}

/-! ## 1 The members' rows -/

theorem s₀_many (A : ManyJob W X) : A.s₀ = stage₀ A.p := rfl

theorem s₀_run (R : RunJob W X) : R.s₀ = stage₀ R.p := rfl

theorem s₀_test (J : TestJob W X) : J.s₀ = stage₀ J.p := rfl

theorem length_tabE (r n : ℕ) (f : ℕ → ℕ → OnBytes.E) (i : ℕ) (h : i < r) :
    ((tabE r n f).getD i []).length = n := by
  simp [tabE, List.getD_eq_getElem?_getD, h]

/-- Where each block's rows have len entries, `layRows` gives n rows of len entries. The blocks may
overlap or run beyond n. -/
theorem sized_layRows (n len : ℕ) (bs : List RowBlock)
    (h : ∀ B ∈ bs, ∀ i < B.count, (B.rows.getD i []).length = len) :
    sized n len (layRows n len bs) = true := by
  unfold sized layRows
  simp only [List.length_map, List.length_range, beq_self_eq_true, Bool.true_and, List.all_eq_true,
    List.mem_map, List.mem_range, beq_iff_eq]
  rintro _ ⟨b, -, rfl⟩
  cases hf : bs.findSome? (fun B =>
      if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) [])
      else none) with
  | none => simp
  | some r =>
    obtain ⟨B, hB, hr⟩ := List.exists_of_findSome?_eq_some hf
    split at hr
    · rename_i hc
      cases hr
      exact h B hB _ (by omega)
    · cases hr

/-- A member's four lists have the stage's lengths, for the rows that its shape counts. -/
structure RowsOk (s : Stage) (m : MemShape) (q : PSt) : Prop where
  main : ∀ i < m.mainRows, (q.M.getD i []).length = s.C.l
  mainTail : ∀ i < m.mainRows, (q.Rh.getD i []).length = s.C.r
  mask : ∀ i < m.maskRows, (q.W.getD i []).length = s.Z.l
  maskTail : ∀ i < m.maskRows, (q.Sg.getD i []).length = s.Z.r

theorem firstSized_layFirst (s : Stage) (ms : List (MemShape × PSt))
    (h : ∀ x ∈ ms, RowsOk s x.1 x.2) : firstSized s (layFirst s ms) = true := by
  unfold firstSized layFirst
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨sized_layRows _ _ _ ?_, sized_layRows _ _ _ ?_⟩, sized_layRows _ _ _ ?_⟩,
    sized_layRows _ _ _ ?_⟩
  · intro B hB i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hB
    exact (h x hx).main i hi
  · intro B hB i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hB
    exact (h x hx).mainTail i hi
  · intro B hB i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hB
    exact (h x hx).mask i hi
  · intro B hB i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hB
    exact (h x hx).maskTail i hi

theorem rowsOk_mem (J : SendJob) (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ) (ask : W → Ask)
    (v? : Option (W → Front X → ℕ → OnBytes.E)) (s : Stage)
    (h : memFits J.Q.codes (shapeAt J k) s = true) (w : W) (fr : Front X) (c : Stretch) :
    RowsOk s (memOfSending J at_ k fs ask v?).shape
      ((memOfSending J at_ k fs ask v?).rows w fr c) := by
  unfold memFits at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hm⟩, hz⟩ := h
  constructor
  · intro i hi
    have hi' : i < (shapeAt J k).mainRows := hi
    rcases hm with h0 | ⟨h1, -⟩
    · omega
    · exact (length_tabE _ _ _ _ hi').trans h1
  · intro i hi
    have hi' : i < (shapeAt J k).mainRows := hi
    rcases hm with h0 | ⟨-, h2⟩
    · omega
    · exact (length_tabE _ _ _ _ hi').trans h2
  · intro i hi
    have hi' : i < (shapeAt J k).maskRows := hi
    rcases hz with h0 | ⟨h1, -⟩
    · omega
    · exact (length_tabE _ _ _ _ hi').trans h1
  · intro i hi
    have hi' : i < (shapeAt J k).maskRows := hi
    rcases hz with h0 | ⟨-, h2⟩
    · omega
    · exact (length_tabE _ _ _ _ hi').trans h2

theorem rowsFit_atU (A : SendPub) (p : P12) (h : sharedFitsU A p = true) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (mem : ℕ → Stretch) :
    (jobAtU A p door weights rand u?).toRun.rowsFit w fr mem = true := by
  unfold sharedFitsU at h
  simp only [Bool.and_eq_true] at h
  refine firstSized_layFirst (stage₀ p) _ ?_
  intro x hx
  simp only [jobAtU, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · dsimp only
    exact rowsOk_mem _ _ _ _ _ _ _ h.1 _ _ _
  · dsimp only
    exact rowsOk_mem _ _ _ _ _ _ _ h.2 _ _ _

theorem rowsFit_atOmega (A : SendPub) (p : P12) (h : sharedFitsOmega A p = true)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (mem : ℕ → Stretch) :
    (jobAtOmega A p door weights rand omega?).toRun.rowsFit w fr mem = true := by
  unfold sharedFitsOmega at h
  simp only [Bool.and_eq_true] at h
  refine firstSized_layFirst (stage₀ p) _ ?_
  intro x hx
  simp only [jobAtOmega, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · dsimp only
    exact rowsOk_mem _ _ _ _ _ _ _ h.1 _ _ _
  · dsimp only
    exact rowsOk_mem _ _ _ _ _ _ _ h.2 _ _ _

/-! ## 2 The first fresh table -/

theorem freshFitsU_says (A : SendPub) (p : P12) (h : freshFitsU A p = true) :
    (jobU A).sort 1 = .fresh (stage₀ p).k (stage₀ p).h ∧ (shapeAt (jobU A) 1).mainRows = 0 ∧
      (shapeAt (jobU A) 1).maskRows = 2 ^ (stage₀ p).h ∧
      sameCode ((jobU A).Q.codes.mask.getD (shapeAt (jobU A) 1).maskCode default) (stage₀ p).Z =
        true ∧ p.nums.ownMask = false ∧ (stage₀ p).h ≤ (stage₀ p).k := by
  unfold freshFitsU at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨?_, h2, h3, h4, h5, h6⟩
  cases hs : (jobU A).sort 1 with
  | plain b => rw [hs] at h1; cases h1
  | fresh k h' =>
    rw [hs] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    rw [h1.1, h1.2]

theorem freshFits_atU (A : SendPub) (p : P12) (h : freshFitsU A p = true)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtU A p door weights rand u?).toRun.toTest.freshFits = true := by
  have h5 := (freshFitsU_says A p h).2.2.2.2.1
  show ((some _ : Option (Addr × ℕ)).isNone == p.nums.ownMask) = true
  rw [h5]
  rfl

theorem freshFits_atOmega (A : SendPub) (p : P12) (h : freshFitsOmega p = true)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtOmega A p door weights rand omega?).toRun.toTest.freshFits = true := by
  have h5 : p.nums.ownMask = true := h
  show ((none : Option (Addr × ℕ)).isNone == p.nums.ownMask) = true
  rw [h5]
  rfl

theorem freshDue_atU (A : SendPub) (p : P12) (h : freshFitsU A p = true) :
    dueOf (jobU A).Q.codes (shapeAt (jobU A) 1) ((jobU A).sort 1) = dueFresh (stage₀ p) := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := freshFitsU_says A p h
  unfold sameCode at h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h4
  rw [h1]
  show 2 * (stage₀ p).k + 1 + (shapeAt (jobU A) 1).maskRows * _ = _
  rw [h3, h4.2]
  rfl

theorem hideAt_coef (k : ℕ) (c : ℕ → OnBytes.Slice.GE) :
    hideAt k c = byName k (fun l t => c (coefAt k l t)) (c (2 * (k - 1))) := rfl

theorem freshCoef_atU (A : SendPub) (p : P12) (h : freshFitsU A p = true) (v cs : ℕ → OnBytes.E)
    (r j : ℕ) :
    (laid (jobU A).Q.codes (shapeAt (jobU A) 1) v cs ((jobU A).sort 1)).mask r j =
      OnBytes.E.ofTriple ((Fmt.M1.FoldOwn.freshRow .two (stage₀ p).k (stage₀ p).h
        ⟨fun l t => (cs (coefAt (stage₀ p).k l t)).triple, (cs (2 * ((stage₀ p).k - 1))).triple⟩
        r).getD j Fmt.Fld.zeroE) := by
  rw [(freshFitsU_says A p h).1]
  rfl

theorem freshTail_atU (A : SendPub) (p : P12) (h : freshFitsU A p = true) (v cs : ℕ → OnBytes.E)
    (b q : ℕ) :
    (laid (jobU A).Q.codes (shapeAt (jobU A) 1) v cs ((jobU A).sort 1)).maskTail b q =
      cs (2 * (stage₀ p).k + 1 + b * (stage₀ p).Z.r + q) := by
  obtain ⟨h1, -, -, h4, -, -⟩ := freshFitsU_says A p h
  unfold sameCode at h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h4
  rw [h1]
  show cs (2 * (stage₀ p).k + 1 + b * _ + q) = _
  rw [h4.2]

/-- The test's side, at the job: the first state's fresh table is `packedN` of `byName` at the
values number `coefAt k l t` of `C.hide`, with the constant at number 2 * (k - 1), k the first
stage's. The index of `byName` stays h + (k - h), as the test has it; it equals k by the clause
h ≤ k. -/
theorem freshTest_atU (A : SendPub) (p : P12) (h : freshFitsU A p = true)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (u? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (C : TestCoins) :
    ((jobAtU A p door weights rand u?).toRun.toTest.first w fr C).fM =
      packedN (sgOf (stage₀ p)) (byName ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g)
        (fun l t => C.hide (coefAt (stage₀ p).k l t)) (C.hide (2 * ((stage₀ p).k - 1)))) := by
  have hk := (freshFitsU_says A p h).2.2.2.2.2
  have hK : (sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g = (stage₀ p).k := by
    show (stage₀ p).h + ((stage₀ p).k - (stage₀ p).h) = (stage₀ p).k
    omega
  have e1 : (fun l t => C.hide (coefAt ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g) l t)) =
      fun l t => C.hide (coefAt (stage₀ p).k l t) := by rw [hK]
  have e2 : C.hide (2 * ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g - 1)) =
      C.hide (2 * ((stage₀ p).k - 1)) := by rw [hK]
  show packedN (sgOf (stage₀ p))
      (hideAt ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g) C.hide) = _
  rw [hideAt_coef, e1, e2]

theorem coinsOf_W0 (stages : List Stage) (hide c : ℕ → OnBytes.Slice.GE) (s : OnBytes.Slice.Sg) :
    (coinsOf stages hide c).W s 0 = hideAt (s.h + s.g) hide := rfl

/-- The test's side, the second reading: what the first fold's rounds are computed from. -/
theorem freshSums_atU (A : SendPub) (p : P12) (h : freshFitsU A p = true) (C : TestCoins) :
    (coinsOf p.nums.stages C.hide C.rest).W (sgOf (stage₀ p)) 0 =
      byName ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g)
        (fun l t => C.hide (coefAt (stage₀ p).k l t)) (C.hide (2 * ((stage₀ p).k - 1))) := by
  have hk := (freshFitsU_says A p h).2.2.2.2.2
  have hK : (sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g = (stage₀ p).k := by
    show (stage₀ p).h + ((stage₀ p).k - (stage₀ p).h) = (stage₀ p).k
    omega
  have e1 : (fun l t => C.hide (coefAt ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g) l t)) =
      fun l t => C.hide (coefAt (stage₀ p).k l t) := by rw [hK]
  have e2 : C.hide (2 * ((sgOf (stage₀ p)).h + (sgOf (stage₀ p)).g - 1)) =
      C.hide (2 * ((stage₀ p).k - 1)) := by rw [hK]
  rw [coinsOf_W0, hideAt_coef, e1, e2]

theorem freshTails_atU (A : SendPub) (p : P12) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X)
    (C : TestCoins) :
    ((jobAtU A p door weights rand u?).toRun.toTest.first w fr C).fT = C.tails := rfl

theorem tailsIn_eq (s : Stage) (c : ℕ → OnBytes.Slice.GE) (b q : ℕ) :
    tailsIn s c b q = c (2 * s.k + 1 + b * s.Z.r + q) := rfl

/-- The tails of `restCoins J c` are `tailsIn` of its `hide`: coefficients and tails come from one
list of values. -/
theorem restCoins_tails (J : TestJob W X)
    (c : Handed ⟨0, dueRest J.p.nums.stages⟩ [] (memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J])) :
    (restCoins J c).tails = tailsIn J.s₀ (restCoins J c).hide := rfl

/-! ## 3 What `layFits` reads of a state -/

theorem oracle_pub (S : OnBytes.Statement) (o : ℕ) :
    (pubSt S).st.oracles[o]? = (S.oracles[o]?).map fun x => { shape := x.shape } := by
  simp only [pubSt, PubState.st, Array.getElem?_map, Option.map_map]
  rfl

theorem group_pub (S : OnBytes.Statement) (g : ℕ) :
    (pubSt S).st.groups[g]? = (S.groups[g]?).map fun G =>
      { code := G.code, maskCode := G.maskCode, members := G.members, kept := G.kept } := by
  simp only [pubSt, PubState.st, Array.getElem?_map, Option.map_map]
  rfl

theorem has_pub (S : OnBytes.Statement) (o : ℕ) (part : OnBytes.Part) :
    (pubSt S).st.has o part = S.has o part := by
  unfold OnBytes.Statement.has
  rw [oracle_pub]
  cases S.oracles[o]? <;> rfl

theorem rowBits_pub (S : OnBytes.Statement) (o : ℕ) (part : OnBytes.Part) :
    (pubSt S).st.rowBits o part = S.rowBits o part := by
  unfold OnBytes.Statement.rowBits
  rw [oracle_pub]
  cases S.oracles[o]? <;> rfl

theorem shape_pub (S : OnBytes.Statement) (o : ℕ) :
    ((pubSt S).st.oracles.getD o default).shape = (S.oracles.getD o default).shape := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, oracle_pub]
  cases S.oracles[o]? <;> rfl

/-- `Statement.layout` has the same value at a statement and at its public part. -/
theorem layout_pub (S : OnBytes.Statement) (g : ℕ) : (pubSt S).st.layout g = S.layout g := by
  unfold OnBytes.Statement.layout
  rw [group_pub]
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    simp only [Option.map_some, has_pub, rowBits_pub]
    rfl

theorem layFits_pub (A : ManyJob W X) (t : T12) : A.layFits t = layFitsPub A (pubOf t) := by
  unfold layFitsPub stateOfPub ManyJob.layFits pubOf
  simp only [layout_pub, group_pub, shape_pub]
  cases t.st.layout t.g <;> cases t.st.groups[t.g]? <;> rfl

theorem layFits_congr (A : ManyJob W X) (t t' : T12) (h : pubOf t = pubOf t') :
    A.layFits t = A.layFits t' := by
  rw [layFits_pub, layFits_pub, h]

/-- Where the state on entry has the public part P for every input and whatever precedes the test,
one evaluation of `layFitsPub` gives `layFits` at all of them. -/
theorem layFits_all (A : ManyJob W X) (P : PubState × ℕ)
    (hP : ∀ (w : W) (fr : Front X), pubOf (A.rec₀ w fr) = P) (h : layFitsPub A P = true) (w : W)
    (fr : Front X) : A.layFits (A.rec₀ w fr) = true := by
  rw [layFits_pub, hP, h]

theorem layFits_noState (A : ManyJob W X) : A.layFits noState = false := rfl

/-- The public part of `stateOfPub P` is P. -/
theorem pubOf_stateOfPub (P : PubState × ℕ) : pubOf (stateOfPub P) = P := by
  obtain ⟨⟨c, g, s⟩, n⟩ := P
  simp only [pubOf, stateOfPub, pubSt, PubState.st, Array.map_map]
  congr 2
  · exact Array.map_id' g
  · exact Array.map_id' s

section Door
variable {S₀ : Type} (bs : List (VerifiableInference.Desc.Block S₀ Unit)) (s₀ : W → S₀)
  (enter : S₀ → Except String T12) (cols : W → Front X → List VerifiableInference.Desc.OpenedColumn)

/-- **The public part of the state on entry is P for every input and whatever precedes the test**,
at `doorOf` with `fall := stateOfPub P`, if the fold over the blocks before the test and `enter`,
wherever both return, give a state with the public part P. No statement that this state is the
verifier's. -/
theorem pubOf_doorOf (P : PubState × ℕ)
    (h : ∀ w fr x t, VerifiableInference.Desc.foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) =
      .ok x → enter x.1 = .ok t → pubOf t = P) (w : W) (fr : Front X) :
    pubOf (doorOf bs s₀ enter cols (stateOfPub P) w fr) = P := by
  unfold doorOf
  cases hx : VerifiableInference.Desc.foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) with
  | error _ => exact pubOf_stateOfPub P
  | ok x =>
    show pubOf ((enter x.1).toOption.getD (stateOfPub P)) = P
    cases ht : enter x.1 with
    | error _ => exact pubOf_stateOfPub P
    | ok t => exact h w fr x t hx ht

/-- `layFits` at the state on entry, for every input and whatever precedes the test, at a job whose
state on entry is that `doorOf`: from one evaluation of `layFitsPub` and the same hypothesis. No
statement that this state is the verifier's. -/
theorem layFits_atDoor (A : ManyJob W X) (P : PubState × ℕ)
    (hA : A.rec₀ = doorOf bs s₀ enter cols (stateOfPub P))
    (h : ∀ w fr x t, VerifiableInference.Desc.foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) =
      .ok x → enter x.1 = .ok t → pubOf t = P)
    (hP : layFitsPub A P = true) (w : W) (fr : Front X) : A.layFits (A.rec₀ w fr) = true :=
  layFits_all A P (fun w fr => by rw [hA]; exact pubOf_doorOf bs s₀ enter cols P h w fr) hP w fr

end Door

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.s₀_many
#print axioms ProofFile.Honest.K12.Light.s₀_run
#print axioms ProofFile.Honest.K12.Light.s₀_test
#print axioms ProofFile.Honest.K12.Light.length_tabE
#print axioms ProofFile.Honest.K12.Light.sized_layRows
#print axioms ProofFile.Honest.K12.Light.firstSized_layFirst
#print axioms ProofFile.Honest.K12.Light.rowsOk_mem
#print axioms ProofFile.Honest.K12.Light.rowsFit_atU
#print axioms ProofFile.Honest.K12.Light.rowsFit_atOmega
#print axioms ProofFile.Honest.K12.Light.freshFitsU_says
#print axioms ProofFile.Honest.K12.Light.freshFits_atU
#print axioms ProofFile.Honest.K12.Light.freshFits_atOmega
#print axioms ProofFile.Honest.K12.Light.freshDue_atU
#print axioms ProofFile.Honest.K12.Light.hideAt_coef
#print axioms ProofFile.Honest.K12.Light.freshCoef_atU
#print axioms ProofFile.Honest.K12.Light.freshTail_atU
#print axioms ProofFile.Honest.K12.Light.freshTest_atU
#print axioms ProofFile.Honest.K12.Light.coinsOf_W0
#print axioms ProofFile.Honest.K12.Light.freshSums_atU
#print axioms ProofFile.Honest.K12.Light.freshTails_atU
#print axioms ProofFile.Honest.K12.Light.tailsIn_eq
#print axioms ProofFile.Honest.K12.Light.restCoins_tails
#print axioms ProofFile.Honest.K12.Light.oracle_pub
#print axioms ProofFile.Honest.K12.Light.group_pub
#print axioms ProofFile.Honest.K12.Light.has_pub
#print axioms ProofFile.Honest.K12.Light.rowBits_pub
#print axioms ProofFile.Honest.K12.Light.shape_pub
#print axioms ProofFile.Honest.K12.Light.layout_pub
#print axioms ProofFile.Honest.K12.Light.layFits_pub
#print axioms ProofFile.Honest.K12.Light.layFits_congr
#print axioms ProofFile.Honest.K12.Light.layFits_all
#print axioms ProofFile.Honest.K12.Light.layFits_noState
#print axioms ProofFile.Honest.K12.Light.pubOf_stateOfPub
#print axioms ProofFile.Honest.K12.Light.pubOf_doorOf
#print axioms ProofFile.Honest.K12.Light.layFits_atDoor
#print axioms ProofFile.Honest.K12.Light.RowsOk
