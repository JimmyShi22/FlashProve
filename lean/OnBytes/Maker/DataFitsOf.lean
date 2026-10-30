-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/DataFitsOf.lean: the plain data of a file's three chains fit the descriptions under
which the program reads the chains (`DataFits`, `FileFits`: OnBytes/Maker/TablesFit.lean), if the
test `Three.Whole.fits` says yes of the three lists of rounds from which the data were made.

Statements and proofs. `Three.Whole.fits` (OnBytes/Three/Data.lean) is a test on three lists of
rounds. Two of its clauses are used: every name of an opening stands for a tree; every opened tree
is in the table, with the shape under which it is opened.

Main names:
  `fits_named`, `fits_trees`: the two clauses.
  `chain_data`: one chain: the data made from a list of rounds fit that list.
  `dataFits₁`, `dataFits₂`, `dataFits₃`: at the three chains of `Three.Whole.of`.
  `dataFits_alike`, `map_keyOf`: `DataFits` sees of a list of rounds only the opened trees' shapes
    and the stored tables; so it goes over to a list that has the same.
  `described_zip`, `describeWith_plan`: the rounds and the plan of a description that is returned.
  `fileFits_of`: `FileFits` at three descriptions made by `Params.describeWith`: the first two from
    the data's own lists, the third from a list with the shapes and stored tables of the data's
    third.
Limits: that the test says yes is a premise; so are the one number of bytes of a salt in the three
plans and the stored tables' depth and item. That the third description's rounds have the shapes and
stored tables of the data's third list, which is made at made-up names, is a premise here. Nothing
on soundness.


-/
import OnBytes.Maker.TablesFit
import OnBytes.Maker.ReadSpecs

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Three (named wholeNo opensOf rdOf rdsFromL)

/-! ## The test's two clauses -/

/-- Every name of an opening stands for a tree. -/
theorem fits_named {R₁ R₂ R₃ : Params.Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ x ∈ [(0, R₁), (1, R₂), (2, R₃)], ∀ r ∈ x.2, ∀ o ∈ r.1.opens, ∃ y, named x.1 o.2 = some y := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, c2⟩, -⟩, -⟩, -⟩, -⟩ := h
  intro x hx r hr o ho
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 c2 x hx) r hr) o ho
  cases hn : named x.1 o.2 with
  | none => rw [hn] at h1; cases h1
  | some y => exact ⟨y, rfl⟩

/-- Every opened tree is in the table, with the shape under which it is opened. -/
theorem fits_trees {R₁ R₂ R₃ : Params.Rounds} {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ z ∈ (Three.Whole.of R₁ R₂ R₃).opens, TreeIs (Three.Whole.of R₁ R₂ R₃) z.2.1 z.1 := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, c3⟩, -⟩, -⟩, -⟩ := h
  intro z hz
  have h1 := List.all_eq_true.1 c3 z hz
  cases ht : (Three.Whole.of R₁ R₂ R₃).table[z.1]? with
  | none => rw [ht] at h1; cases h1
  | some t =>
    rw [ht] at h1
    exact ⟨t, ht, eq_of_beq (Bool.and_eq_true _ _ ▸ h1 : _ ∧ _).2⟩

/-! ## One chain -/

/-- A member of a list stands in the list with numbers. -/
theorem mem_zipIdx_of {α : Type} : ∀ (l : List α) (k : ℕ) (x : α), x ∈ l → ∃ i, (x, i) ∈ l.zipIdx k
  | [], _, _, h => by cases h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := mem_zipIdx_of l (k + 1) x h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

/-- One round's openings. -/
theorem opens_data (W : Three.Whole) (t₁ t₂ here : ℕ) : ∀ l : List (Fmt.Shape × Fmt.Src),
    (∀ o ∈ l, ∃ y, named here o.2 = some y ∧ TreeIs W o.1 (wholeNo t₁ t₂ y)) →
    List.Forall₂ (TreeIs W) (l.map (·.1))
      (l.filterMap fun o => (named here o.2).map (wholeNo t₁ t₂))
  | [], _ => .nil
  | o :: l, h => by
    obtain ⟨y, h1, h2⟩ := h o List.mem_cons_self
    rw [List.map_cons, List.filterMap_cons, h1]
    exact .cons h2 (opens_data W t₁ t₂ here l fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))

theorem zipWith_data (W : Three.Whole) (all : List (ℕ × Fmt.Shape × ℕ × ℕ))
    (t₁ t₂ here base first : ℕ) : ∀ (R : Params.Rounds) (L : List ℕ), L.length = R.length →
    (∀ r ∈ R, ∀ n, RoundData W (keyOf r) (rdOf all t₁ t₂ here base first r n)) →
    List.Forall₂ (RoundData W) (R.map keyOf) (List.zipWith (rdOf all t₁ t₂ here base first) R L)
  | [], _, _, _ => by
    rw [List.map_nil, List.zipWith_nil_left]
    exact .nil
  | _ :: _, [], e, _ => by cases e
  | r :: R, n :: L, e, h => by
    rw [List.map_cons, List.zipWith_cons_cons]
    exact .cons (h r List.mem_cons_self n)
      (zipWith_data W all t₁ t₂ here base first R L (Nat.succ.inj e)
        fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))

/-- **One chain: the data made from a list of rounds fit that list.** -/
theorem chain_data (W : Three.Whole) (all : List (ℕ × Fmt.Shape × ℕ × ℕ))
    (t₁ t₂ here base first : ℕ) (R : Params.Rounds)
    (hn : ∀ r ∈ R, ∀ o ∈ r.1.opens, ∃ y, named here o.2 = some y)
    (h3 : ∀ z ∈ opensOf t₁ t₂ here R, TreeIs W z.2.1 z.1) :
    DataFits W R (rdsFromL all t₁ t₂ here base first R) := by
  refine zipWith_data W all t₁ t₂ here base first R _ (sentBefore_length R) fun r hr n => ⟨rfl, ?_⟩
  refine opens_data W t₁ t₂ here r.1.opens fun o ho => ?_
  obtain ⟨y, hy⟩ := hn r hr o ho
  obtain ⟨i, hi⟩ := mem_zipIdx_of R 0 r hr
  refine ⟨y, hy, h3 (wholeNo t₁ t₂ y, o.1, here, i) ?_⟩
  unfold opensOf
  exact List.mem_flatMap.2 ⟨(r, i), hi, List.mem_filterMap.2 ⟨o, ho, by rw [hy]; rfl⟩⟩

/-! ## The three chains -/

section
variable {R₁ R₂ R₃ : Params.Rounds} {m : ℕ}

theorem dataFits₁ (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    DataFits (Three.Whole.of R₁ R₂ R₃) R₁ (Three.Whole.of R₁ R₂ R₃).ds₁ :=
  chain_data _ _ _ _ 0 _ _ R₁ (fits_named h (0, R₁) (by simp))
    fun z hz => fits_trees h z (List.mem_append_left _ hz)

theorem dataFits₂ (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    DataFits (Three.Whole.of R₁ R₂ R₃) R₂ (Three.Whole.of R₁ R₂ R₃).ds₂ :=
  chain_data _ _ _ _ 1 _ _ R₂ (fits_named h (1, R₂) (by simp))
    fun z hz => fits_trees h z (List.mem_append_right _ (List.mem_append_left _ hz))

theorem dataFits₃ (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    DataFits (Three.Whole.of R₁ R₂ R₃) R₃ (Three.Whole.of R₁ R₂ R₃).ds₃ :=
  chain_data _ _ _ _ 2 _ _ R₃ (fits_named h (2, R₃) (by simp))
    fun z hz => fits_trees h z (List.mem_append_right _ (List.mem_append_right _ hz))

end

/-- `DataFits` goes over to a list of rounds with the same shapes and stored tables. -/
theorem dataFits_alike {W : Three.Whole} {xs R : Params.Rounds} {ds : List Three.RDL}
    (h : xs.map keyOf = R.map keyOf) (F : DataFits W R ds) : DataFits W xs ds := by
  unfold DataFits at F ⊢
  rw [h]
  exact F

/-- The same shapes and the same stored tables, round by round. -/
theorem map_keyOf : ∀ (xs R : Params.Rounds),
    xs.map (fun x => x.1.opens.map (·.1)) = R.map (fun x => x.1.opens.map (·.1)) →
    xs.map (·.2) = R.map (·.2) → xs.map keyOf = R.map keyOf
  | [], [], _, _ => rfl
  | [], _ :: _, e, _ => by cases e
  | _ :: _, [], e, _ => by cases e
  | x :: xs, r :: R, e1, e2 => by
    rw [List.map_cons, List.map_cons] at e1 e2 ⊢
    obtain ⟨a1, a2⟩ := List.cons.inj e1
    obtain ⟨b1, b2⟩ := List.cons.inj e2
    rw [map_keyOf xs R a2 b2]
    exact congrArg (· :: _) (Prod.ext a1 b1)

/-! ## Descriptions -/

/-- The rounds of a description that is returned, with their stored tables, are the argument. -/
theorem described_zip {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.rounds.zip S.stored = R := by
  obtain ⟨f1, f2, -⟩ := describeWith_facts h
  rw [f1, f2]
  exact zip_fst_snd R

/-- The plan of a description that is returned is that of the parameter bytes. -/
theorem describeWith_plan {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.plan = g.plan := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

/-- **What the tables ask of three descriptions and the data**, from the test on the data. R₃': the
rounds from which the third description is made. -/
theorem fileFits_of {R₁ R₂ R₃ R₃' : Params.Rounds} {m sb a : ℕ}
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true)
    {g₁ g₂ g₃ : Params.Given} {l₁ l₂ l₃ f₁ f₂ f₃ : ℕ} {st₁ st₂ st₃ : ByteArray}
    {rd₁ rd₂ rd₃ : Fmt.Rand} {S₁ S₂ S₃ : Fmt.SpecX}
    (h₁ : Params.describeWith g₁ l₁ st₁ rd₁ R₁ f₁ = some S₁)
    (h₂ : Params.describeWith g₂ l₂ st₂ rd₂ R₂ f₂ = some S₂)
    (h₃ : Params.describeWith g₃ l₃ st₃ rd₃ R₃' f₃ = some S₃)
    (hsh : R₃'.map (fun x => x.1.opens.map (·.1)) = R₃.map (fun x => x.1.opens.map (·.1)))
    (hst : StoredAlike R₃' R₃)
    (s₁ : g₁.plan.salt = sb) (s₂ : g₂.plan.salt = sb) (s₃ : g₃.plan.salt = sb)
    (a₁ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₁) (a₂ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₂)
    (a₃ : StoredAt a (Three.Whole.of R₁ R₂ R₃).ds₃) :
    FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ where
  d₁ := by rw [described_zip h₁]; exact dataFits₁ hf
  d₂ := by rw [described_zip h₂]; exact dataFits₂ hf
  d₃ := by rw [described_zip h₃]; exact dataFits_alike (map_keyOf _ _ hsh hst) (dataFits₃ hf)
  s₁ := by rw [describeWith_plan h₁]; exact s₁
  s₂ := by rw [describeWith_plan h₂]; exact s₂
  s₃ := by rw [describeWith_plan h₃]; exact s₃
  a₁ := a₁
  a₂ := a₂
  a₃ := a₃

end OnBytes.Maker
