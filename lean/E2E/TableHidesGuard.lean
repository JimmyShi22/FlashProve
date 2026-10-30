-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TableHidesGuard.lean: the number of E2E/TableHides.lean cannot be raised by one: at r + 1
columns the encoder's joint clause fails: there are an OOD seed and two matrices at which, AT EVERY
SET OF r + 1 POSITIONS, the law of (OOD answers, these columns of the committed table), over uniform
pads and encoding randomness, is not the same. Statements and proofs.

What is shown.
  `DifferAt C Q s i i'`: at the set Q of positions and the OOD seed s the joint law is not the same
    at the indices i and i'. `Differ C b i i'`: so it is at some Q of at most b positions and some
    s.
  **`differ_at`**, **`differ_at_full`**: at EVERY set Q of r + 1 positions (at the full size:
    44,040,192), at the OOD seed `seedOne`: of the matrix with the one cell 1 in row 0 and column 0
    and the matrix 0. `differ_succ`, `differ_full`: so `Differ` at that number.
  `SameAt L Q s i i'`, `DifferAt.obj`: the same in the words of the clause `hidE`, at `F.withProvers P`.
  **`not_hides_succ`**: for a code of at most 2^32 positions with at least r + 1 positions, a row's
    message whose last three entries are its pad and which has an entry before the pad, an OOD point
    of at least one coordinate and a matrix with at least one row: the configuration of a committed
    table (`confCells`, E2E/TableMasked.lean) has NOT the library's property `ConfigurationWithOutOfDomainSample.Hides` at r + 1.
  **`not_hides_full`**: so at the full size: not at 44,040,192.
  **`not_hidE_full`**: so the clause `hidE` of `HolographicProtocol.ReadsR` (`HidE`, E2E/TableHides.lean) fails at
    44,040,192 at the object `F.withProvers P`, for all three protocols F over the full size's configuration
    and all provers P.

How. Take any r + 1 positions; the matrix 0 and the matrix with the one cell 1 that the format lays
at entry 0 of row number 0; and the OOD seed whose point has all coordinates 1, so that entry 0
has the weight 0 in a row's OOD answer. If the two laws were one, what the second matrix shows at
pads 0 and encoding randomness 0 would also be shown by the first at some pads η and encoding
randomness ρ. The OOD answers of row number 0 are then the same with the same share of the entries
before the pad (0 on both sides), so that row's pad is 0 (the map from a pad to the answer is one to
one). Then row number 0 of the first table is the polynomial with the coefficients ρ alone, of
degree below r, and it agrees with X^r at r + 1 distinct points. A polynomial of degree r that is
not 0 has at most r zeros (the library's `Code.RS.card_zeros_lt`).

Why it is here. With E2E/TableHides.lean it says that r is exactly the largest number b at which the
clause (every OOD seed, every two matrices) holds: in that sense a budget of r columns has no slack.

Limits.
- SOME OOD seed, SOME two matrices; every set of r + 1 positions. The OOD seed is a corner: its
  point is the vertex (1, ..., 1) of the cube. At the full size every entry before the pad has the
  weight 0 there (402,653,181 entries, and the vertex has the number 2^29 - 1), so at that OOD seed
  the OOD answers are made of the pads alone and read no cell of any matrix (by the equality
  polynomial's text; typed for entry 0 alone: `weight_zero`). Of an OOD seed that reads the matrix
  nothing is said; nor of every OOD seed, nor of one sampled uniformly. It states no size of the
  difference: the two laws differ, by how much is not said. So "no slack" is typed for the clause's
  form with ALL OOD seeds alone: of the like clause at a set of OOD seeds without this one nothing
  is shown at one column more.
- The clause is a PREMISE of the library's theorem on the whole object. That the result itself fails
  at one column more is typed by no environment.
- It is typed at r + 1 alone. (At a larger number the clause fails too, since it speaks of every set
  of at most that size; that line is not typed.)
- That the two matrices are in range at the full size is in E2E/TableHidesGuardAtFiles.lean. That
  they are the matrices of two sets of weights is not shown.
- It is on the committer's side alone: no verifier, no prover, no hash function.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.

`DifferAt`, `Differ` and `SameAt` may be read as part of a goal (what the encoder does not hide).
They are not among this library's goals.


-/
import E2E.TableHides
import E2E.TableStrongGuard

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Table
open Iop Prob Hiop
open OnBytes.Flat (relationsAndEncodingOfClaims Coding codingCells cellWords PadsOf MatrixNums claimsLedgerOnAt Cells
  rowWords tailWords Files)
open VerifiableInference.OnPublicFiles (numsRef)
open OnBytes.Slice (Sz GF GE toF ofF ptOf honestTab honestMsgs recZ padZ entryEquiv frS frZ)

/-! ## 0. Two indices with different laws -/

/-- At the set Q of positions and the OOD seed s, the joint law of (OOD answers, the table at these
positions), over uniform pads and encoding randomness, is not the same at the indices i and i'. -/
def DifferAt (C : ConfigurationWithOutOfDomainSample) (Q : Finset (Fin C.n)) (s : C.Seed) (i i' : C.I) : Prop :=
  (unif (C.Pad × C.Rnd)).map
      (fun r => (C.smp s (C.hold i r.1), fun p : Q => C.enc (C.hold i r.1) r.2 p)) ≠
    (unif (C.Pad × C.Rnd)).map
      (fun r => (C.smp s (C.hold i' r.1), fun p : Q => C.enc (C.hold i' r.1) r.2 p))

/-- So it is at some set of at most b positions and some OOD seed. -/
def Differ (C : ConfigurationWithOutOfDomainSample) (b : ℕ) (i i' : C.I) : Prop :=
  ∃ (Q : Finset (Fin C.n)) (s : C.Seed), Q.card ≤ b ∧ DifferAt C Q s i i'

/-- Then the configuration has not the library's property. -/
theorem Differ.not_hides {C : ConfigurationWithOutOfDomainSample} {b : ℕ} {i i' : C.I} (h : Differ C b i i') : ¬ C.Hides b :=
  fun H => by
    obtain ⟨Q, s, hQ, hne⟩ := h
    exact hne (H Q hQ s i i')

/-! ## 1. No polynomial of degree below r is X^r at r + 1 points -/

/-- General in the code's numbers: the last step of E2E/TableStrongGuard.lean, apart. -/
theorem no_tail_is_power (a r : ℕ) (ha : a ≤ 32) (Q : Finset (Fin (2 ^ a))) (hQ : Q.card = r + 1)
    (c : Fin r → GF)
    (h : ∀ p : Q, Code.RS.gen (ptOf a) (fun t : Fin r => (t : ℕ)) c p = ptOf a p ^ r) : False := by
  classical
  let v : Fin (r + 1) → GF := Fin.snoc c (-1)
  have hv : v ≠ 0 := by
    intro h0
    have h1 : v (Fin.last r) = 0 := congrFun h0 _
    rw [show v (Fin.last r) = -1 from Fin.snoc_last _ _] at h1
    exact one_ne_zero (neg_eq_zero.1 h1)
  have hz : ∀ p : Q, Code.RS.gen (fun q : Q => ptOf a q) (fun t : Fin (r + 1) => (t : ℕ)) v p =
      0 := by
    intro p
    rw [Code.RS.gen_apply, Fin.sum_univ_castSucc]
    have h1 := h p
    rw [Code.RS.gen_apply] at h1
    show (∑ i : Fin r, v i.castSucc * ptOf a p ^ (i : ℕ)) + v (Fin.last r) * ptOf a p ^ r = 0
    rw [show v (Fin.last r) = -1 from Fin.snoc_last _ _]
    simp only [show ∀ i : Fin r, v i.castSucc = c i from fun i => Fin.snoc_castSucc _ _ i]
    rw [h1]
    ring
  have hx : Function.Injective fun q : Q => ptOf a q :=
    fun q q' hq => Subtype.ext (OnBytes.Slice.ptOf_inj a ha hq)
  have hc := Code.RS.card_zeros_lt hx (ex := fun t : Fin (r + 1) => (t : ℕ))
    Fin.val_injective (k := r + 1) (fun i => i.isLt) hv
  have hall : Nat.card {j : Q // Code.RS.gen (fun q : Q => ptOf a q)
      (fun t : Fin (r + 1) => (t : ℕ)) v j = 0} = r + 1 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hz), Nat.card_eq_fintype_card, Fintype.card_coe, hQ]
  omega

/-! ## 2. The entries of row number 0 -/

section
variable (S : Sz) (cut : ℕ) (N : MatrixNums) (Z : Cb.Ood.Sample GE S.En)

/-- The vertex of row number 0. -/
def k₀ : S.ix.Row := fun _ => false

/-- The matrix with the one cell 1, in row 0 and column 0. -/
def oneCell : Cells (S.toDecR Z cut) N := fun y c => if y.val = 0 ∧ c.val = 0 then 1 else 0

/-- Entry j of row number 0 of the message that holds a matrix, as an element of the base field:
before the cut the cell that the format lays there, or 0; from the cut on the pad's element. -/
def entry₀ (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (j : S.En) : GF :=
  toF (OnBytes.Flat.cellEntryAt N.rows N.kLo S.P.v cut S.P.T.l (fun y c => (M y c).c0) η 0 j.val)

theorem hold_val (M : Cells (S.toDecR Z cut) N) (η : PadsOf S cut) (j : S.En) :
    honestMsgs S (cellWords S Z cut N M η) (k₀ S, j) =
      algebraMap GF GE (entry₀ S cut N Z M η j) := by
  show algebraMap GF GE
    (toF ((cellWords S Z cut N M η (OnBytes.Slice.Sz.rowNo (k₀ S))).getD j.val 0)) = _
  rw [OnBytes.Flat.cellWords_getD S Z cut N M η _ _ j.isLt,
    show OnBytes.Slice.Sz.rowNo (k₀ S) = 0 from OnBytes.Slice.Sz.rowNo_false _]
  rfl

/-- The matrix 0 under pads that are 0 in row number 0: every entry of that row is 0. -/
theorem entry₀_zero (η : PadsOf S cut) (hη : η ⟨0, Nat.two_pow_pos _⟩ = 0) (j : S.En) :
    entry₀ S cut N Z (fun _ _ => 0) η j = 0 := by
  unfold entry₀ OnBytes.Flat.cellEntryAt
  split
  · split
    · exact OnBytes.Slice.toF_ofF _
    · exact OnBytes.Slice.toF_zero
  · split
    · rw [OnBytes.Slice.toF_ofF, hη]
      rfl
    · exact OnBytes.Slice.toF_zero

/-- The matrix with the one cell 1 under pads 0: entry 0 of row number 0 is 1, all others are 0. -/
theorem entry₀_one (hcut : 0 < cut) (hrows : 0 < N.rows) (j : S.En) :
    entry₀ S cut N Z (oneCell S cut N Z) (fun _ _ => 0) j = if j.val = 0 then 1 else 0 := by
  unfold entry₀ OnBytes.Flat.cellEntryAt
  by_cases hj : j.val = 0
  · rw [if_pos hj, hj, if_pos hcut, dif_pos ⟨by simpa using hrows, by simp⟩,
      OnBytes.Slice.toF_ofF]
    show (if _ then (1 : GE) else 0).c0 = 1
    rw [if_pos ⟨by simp, by simp⟩]
    rfl
  · rw [if_neg hj]
    split
    · split
      · rw [OnBytes.Slice.toF_ofF]
        show (if j.val / 2 ^ N.kLo = 0 ∧ 0 * 2 ^ N.kLo + j.val % 2 ^ N.kLo = 0 then (1 : GE)
          else 0).c0 = 0
        rw [if_neg]
        · rfl
        · rintro ⟨h1, h2⟩
          apply hj
          have := Nat.div_add_mod j.val (2 ^ N.kLo)
          rw [h1] at this
          omega
      · exact OnBytes.Slice.toF_zero
    · split
      · exact OnBytes.Slice.toF_ofF _
      · exact OnBytes.Slice.toF_zero

end

/-! ## 3. An OOD seed that gives entry 0 the weight 0 -/

section
variable (S : Sz) (cut lg : ℕ)

/-- The OOD seed with the point (1, ..., 1) and the factor 1. -/
def seedOne : (recZ S.P.T.l lg 1).D := fun _ => (fun _ => 1, ⟨1, one_ne_zero⟩)

/-- At that OOD seed entry 0 has the weight 0, if the point has a coordinate. -/
theorem weight_zero (hlg : 0 < lg) (j : Fin (S.P.T.l - 3 * 1)) (hj : j.val = 0) :
    (padZ S.P.T.l lg 1).mat (seedOne S lg) (0 : Fin 1) (Sum.inl j) = 0 := by
  show Alg.eqk (fun _ : Fin lg => (1 : GE)) (fun t : Fin lg => j.val.testBit t.val) = 0
  unfold Alg.eqk
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, hlg⟩ : Fin lg)) ?_
  rw [hj]
  simp

/-- So a row that is 0 but at entry 0 gives 0 to its OOD answer, before the pad. -/
theorem before_zero (hlg : 0 < lg) (hc : cut + 3 = S.P.T.l) (row : S.En → GE)
    (h : ∀ j : S.En, j.val ≠ 0 → row j = 0) : before S cut lg hc (seedOne S lg) row = 0 := by
  unfold before
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j.val = 0
  · rw [weight_zero S lg hlg j hj, zero_mul]
  · rw [h _ (show j.val ≠ 0 from hj), mul_zero]

end

/-! ## 4. The encoder's joint clause fails at r + 1 -/

section
variable (S : Sz) (cut lg : ℕ) (N : MatrixNums) {X : Type} (pp : Inst.Model.ScalesAndPolicy)
  (req : X → Inst.Model.Instance Inst.Model.ppref)

/- The elaboration of the next proof is heavy: it compares the configuration's fields with the
encoder's own terms by unfolding. The default number of heartbeats leaves it little room; so the
number is raised here. -/
set_option maxHeartbeats 1000000 in
/-- **At EVERY set Q of r + 1 positions**, at the OOD seed `seedOne`, the matrix with the one cell 1
and the matrix 0 have different joint laws of OOD answers and columns. -/
theorem differ_at (ha : S.P.T.a ≤ 32) (hc : cut + 3 = S.P.T.l) (hlg : 0 < lg) (hcut : 0 < cut)
    (hrows : 0 < N.rows) (Q : Finset S.Pos) (hQ : Q.card = S.P.T.r + 1) :
    DifferAt (confCells S cut lg N pp req) Q (seedOne S lg)
      (oneCell S cut N (recZ S.P.T.l lg 1)) (fun _ _ => 0) := by
  classical
  intro h
  have hl : 0 < S.P.T.l := by omega
  let M₀ : Cells (S.toDecR (recZ S.P.T.l lg 1) cut) N := fun _ _ => 0
  let M₁ : Cells (S.toDecR (recZ S.P.T.l lg 1) cut) N := oneCell S cut N (recZ S.P.T.l lg 1)
  let η₀ : PadsOf S cut := fun _ _ => 0
  let ρ₀ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF := fun _ _ => 0
  let hold := fun (M : Cells (S.toDecR (recZ S.P.T.l lg 1) cut) N) (η : PadsOf S cut) =>
    honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M η)
  have e : (unif (PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF))).map
        (fun x => ((confCells S cut lg N pp req).smp (seedOne S lg) (hold M₁ x.1),
          fun p : Q => honestTab S (rowWords S (hold M₁ x.1)) (tailWords S x.2) p)) =
      (unif (PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF))).map
        (fun x => ((confCells S cut lg N pp req).smp (seedOne S lg) (hold M₀ x.1),
          fun p : Q => honestTab S (rowWords S (hold M₀ x.1)) (tailWords S x.2) p)) := h
  -- what the second matrix shows at pads 0 and encoding randomness 0 is shown by the first
  have hmem : ((confCells S cut lg N pp req).smp (seedOne S lg) (hold M₁ η₀),
      fun p : Q => honestTab S (rowWords S (hold M₁ η₀)) (tailWords S ρ₀) p) ∈
      ((unif (PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF))).map
        (fun x => ((confCells S cut lg N pp req).smp (seedOne S lg) (hold M₀ x.1),
          fun p : Q => honestTab S (rowWords S (hold M₀ x.1)) (tailWords S x.2) p))).support := by
    rw [← e]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨(η₀, ρ₀), PMF.mem_support_uniformOfFintype _, rfl⟩
  obtain ⟨⟨η, ρ⟩, -, hηρ⟩ := (PMF.mem_support_map_iff _ _ _).1 hmem
  have hA : (confCells S cut lg N pp req).smp (seedOne S lg) (hold M₀ η) =
      (confCells S cut lg N pp req).smp (seedOne S lg) (hold M₁ η₀) := congrArg Prod.fst hηρ
  have hE : (fun p : Q => honestTab S (rowWords S (hold M₀ η)) (tailWords S ρ) p) =
      fun p : Q => honestTab S (rowWords S (hold M₁ η₀)) (tailWords S ρ₀) p :=
    congrArg Prod.snd hηρ
  -- the OOD answers of row number 0 give: that row's pad is 0
  have La := rowsOf_laws S cut lg N pp req hc
  have a0 := La.smp_hold (seedOne S lg) M₀ η (k₀ S)
  have a1 := La.smp_hold (seedOne S lg) M₁ η₀ (k₀ S)
  have row0 : ∀ j : S.En, j.val ≠ 0 → hold M₀ η₀ (k₀ S, j) = 0 := fun j _ => by
    show honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M₀ η₀) (k₀ S, j) = 0
    rw [hold_val, entry₀_zero S cut N _ η₀ rfl j, map_zero]
  have row1 : ∀ j : S.En, j.val ≠ 0 → hold M₁ η₀ (k₀ S, j) = 0 := fun j hj => by
    show honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M₁ η₀) (k₀ S, j) = 0
    rw [hold_val, entry₀_one S cut N _ hcut hrows j, if_neg hj, map_zero]
  have same : ∀ pad : Fin (S.P.T.l - cut) → GF,
      (recZ S.P.T.l lg 1).val (seedOne S lg)
          (withPads S cut (fun j => hold M₁ η₀ (k₀ S, j)) pad) (0 : Fin 1) =
        (recZ S.P.T.l lg 1).val (seedOne S lg)
          (withPads S cut (fun j => hold M₀ η₀ (k₀ S, j)) pad) (0 : Fin 1) := fun pad => by
    rw [answer_withPads S cut lg hc, answer_withPads S cut lg hc,
      before_zero S cut lg hlg hc _ row1, before_zero S cut lg hlg hc _ row0]
  have hpad : η ⟨OnBytes.Slice.Sz.rowNo (k₀ S), OnBytes.Slice.rowNo_lt (k₀ S)⟩ =
      η₀ ⟨OnBytes.Slice.Sz.rowNo (k₀ S), OnBytes.Slice.rowNo_lt (k₀ S)⟩ := by
    refine (answer_bijective S cut lg hc (seedOne S lg) (fun j => hold M₀ η₀ (k₀ S, j))).1 ?_
    show (recZ S.P.T.l lg 1).val (seedOne S lg) (withPads S cut (fun j => hold M₀ η₀ (k₀ S, j))
        (η ⟨OnBytes.Slice.Sz.rowNo (k₀ S), OnBytes.Slice.rowNo_lt (k₀ S)⟩)) (0 : Fin 1) =
      (recZ S.P.T.l lg 1).val (seedOne S lg) (withPads S cut (fun j => hold M₀ η₀ (k₀ S, j))
        (η₀ ⟨OnBytes.Slice.Sz.rowNo (k₀ S), OnBytes.Slice.rowNo_lt (k₀ S)⟩)) (0 : Fin 1)
    exact (a0.symm.trans
      ((congrArg (fun u => (rowsOf S cut lg N pp req).answers u (k₀ S)) hA).trans a1)).trans
      (same _)
  have hη : η ⟨0, Nat.two_pow_pos _⟩ = 0 := by
    have e0 : (⟨OnBytes.Slice.Sz.rowNo (k₀ S), OnBytes.Slice.rowNo_lt (k₀ S)⟩ :
        Fin (2 ^ S.P.v)) = ⟨0, Nat.two_pow_pos _⟩ := Fin.ext (OnBytes.Slice.Sz.rowNo_false _)
    rw [e0] at hpad
    exact hpad
  -- the columns of row number 0
  let a₀ : Fin (2 ^ S.P.v) := ⟨0, Nat.two_pow_pos _⟩
  have hk : (fun t : Fin S.P.v => a₀.val.testBit t.val) = k₀ S :=
    funext fun t => Nat.zero_testBit _
  refine no_tail_is_power S.P.T.a S.P.T.r ha Q hQ (ρ a₀) fun p => ?_
  have h1 := congrFun hE p
  rw [honestTab_col S (hold M₀ η) ρ p, honestTab_col S (hold M₁ η₀) ρ₀ p] at h1
  have h2 := congrFun (colOf_inj S p _ _ h1) a₀
  have s0 : share S (hold M₀ η) a₀ p = 0 := by
    rw [share_eq]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hk]
    show _ * (honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M₀ η) (k₀ S, j)).c0 = 0
    rw [hold_val, entry₀_zero S cut N _ η hη j, map_zero]
    exact mul_zero _
  have s1 : share S (hold M₁ η₀) a₀ p = ptOf S.P.T.a p ^ S.P.T.r := by
    rw [share_eq, Finset.sum_eq_single (⟨0, hl⟩ : Fin S.P.T.l)]
    · rw [hk]
      show _ * (honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M₁ η₀) (k₀ S, _)).c0 = _
      rw [hold_val, entry₀_one S cut N _ hcut hrows, if_pos rfl, map_one]
      show ptOf S.P.T.a p ^ (S.P.T.r + 0) * 1 = _
      rw [Nat.add_zero, mul_one]
    · intro j _ hj
      have hj' : ¬ j.val = 0 := fun h0 => hj (Fin.ext h0)
      rw [hk]
      show _ * (honestMsgs S (cellWords S (recZ S.P.T.l lg 1) cut N M₁ η₀) (k₀ S, j)).c0 = 0
      rw [hold_val, entry₀_one S cut N _ hcut hrows, if_neg hj', map_zero]
      exact mul_zero _
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  have g0 : Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (ρ₀ a₀) p = 0 := by
    show Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) 0 p = 0
    rw [map_zero]
    rfl
  rw [s0, s1, g0, zero_add, add_zero] at h2
  exact h2

/-- **At r + 1 columns the two matrices differ**, if the code has so many positions. -/
theorem differ_succ (ha : S.P.T.a ≤ 32) (hc : cut + 3 = S.P.T.l)
    (hn : S.P.T.r + 1 ≤ 2 ^ S.P.T.a) (hlg : 0 < lg) (hcut : 0 < cut) (hrows : 0 < N.rows) :
    Differ (confCells S cut lg N pp req) (S.P.T.r + 1) (oneCell S cut N (recZ S.P.T.l lg 1))
      (fun _ _ => 0) := by
  obtain ⟨Q, -, hQ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset S.Pos))
    (n := S.P.T.r + 1) (by rw [Finset.card_univ, Fintype.card_fin]; exact hn)
  exact ⟨Q, seedOne S lg, hQ.le, differ_at S cut lg N pp req ha hc hlg hcut hrows Q hQ⟩

/-- **At r + 1 columns the joint law of OOD answers and columns hangs on the matrix.** -/
theorem not_hides_succ (ha : S.P.T.a ≤ 32) (hc : cut + 3 = S.P.T.l)
    (hn : S.P.T.r + 1 ≤ 2 ^ S.P.T.a) (hlg : 0 < lg) (hcut : 0 < cut) (hrows : 0 < N.rows) :
    ¬ (confCells S cut lg N pp req).Hides (S.P.T.r + 1) :=
  (differ_succ S cut lg N pp req ha hc hn hlg hcut hrows).not_hides

end

/-! ## 5. At the full size -/

/-- **At the full size, at EVERY set of 44,040,192 positions.** -/
theorem differ_at_full (X : Type) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) (Q : Finset frS.Pos)
    (hQ : Q.card = 44040192) :
    DifferAt (OnBytes.Slice.DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req))) Q (seedOne frS 29)
      (oneCell frS 402653181 numsRef frZ) (fun _ _ => 0) :=
  differ_at frS 402653181 29 numsRef pp req (Nat.le_refl 32) rfl (by norm_num) (by norm_num)
    (by show 0 < numsRef.rows; decide) Q hQ

/-- **At the full size**: the matrix with the one cell 1 and the matrix 0 differ at 44,040,192
columns. -/
theorem differ_full (X : Type) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) :
    Differ (OnBytes.Slice.DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req))) 44040192
      (oneCell frS 402653181 numsRef frZ) (fun _ _ => 0) :=
  differ_succ frS 402653181 29 numsRef pp req (Nat.le_refl 32) rfl
    (by show 44040191 + 1 ≤ 2 ^ 32; norm_num) (by norm_num) (by norm_num)
    (by show 0 < numsRef.rows; decide)

/-- **At the full size**: not at 44,040,192 columns. -/
theorem not_hides_full (X : Type) (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) :
    ¬ (OnBytes.Slice.DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req))).Hides 44040192 :=
  (differ_full X pp req).not_hides

/-- In the words of the clause `hidE`: at the set Q, the OOD seed s and the indices i, i' the two
laws of the clause are one. (`HidE L b` says it of all Q of at most b positions and all s, i, i'.)
-/
def SameAt {I X : Type} (L : HolographicProtocol I X) (Q : Finset (Fin L.wordLength)) (s : L.OutOfDomainSeed) (i i' : I) : Prop :=
  (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i r s, fun p : Q => L.encodeIndex i r p)) =
    (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i' r s, fun p : Q => L.encodeIndex i' r p))

/-- What differs at the configuration differs at `F.withProvers P`, in the clause's own words. General in
the configuration. -/
theorem DifferAt.obj {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) {Q : Finset (Fin C.n)} {s : C.Seed}
    {i i' : C.I} (h : DifferAt C Q s i i') : ¬ SameAt (F.withProvers P) Q s i i' := h

/-- The clause `hidE` at `F.withProvers P` gives back the property of the configuration: the converse of
`obj_hidE` (E2E/TableHides.lean). General in the configuration. -/
theorem hides_of_hidE {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) {b : ℕ} (h : HidE (F.withProvers P) b) :
    C.Hides b :=
  fun Q hQ s i i' => h Q hQ s i i'

/-- **The clause `hidE` fails at 44,040,192**, at the object of all three protocols over the full
size's configuration and all provers. -/
theorem not_hidE_full {X : Type} (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref)
    (F : Files (OnBytes.Slice.DecR.configurationOfStoredTable
      (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers) :
    ¬ HidE (F.withProvers P) 44040192 :=
  fun h => not_hides_full X pp req (hides_of_hidE F P h)

end AtPublicFiles.Table

#print axioms AtPublicFiles.Table.no_tail_is_power
#print axioms AtPublicFiles.Table.entry₀_zero
#print axioms AtPublicFiles.Table.entry₀_one
#print axioms AtPublicFiles.Table.weight_zero
#print axioms AtPublicFiles.Table.before_zero
#print axioms AtPublicFiles.Table.differ_at
#print axioms AtPublicFiles.Table.differ_succ
#print axioms AtPublicFiles.Table.differ_at_full
#print axioms AtPublicFiles.Table.DifferAt.obj
#print axioms AtPublicFiles.Table.not_hides_succ
#print axioms AtPublicFiles.Table.differ_full
#print axioms AtPublicFiles.Table.not_hides_full
#print axioms AtPublicFiles.Table.hides_of_hidE
#print axioms AtPublicFiles.Table.not_hidE_full
