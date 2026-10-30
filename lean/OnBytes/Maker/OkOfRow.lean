-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfRow.lean: the makers' test `rowFitAt` (OnBytes/Maker/RowFit.lean) from the
record of a file's reading, but for one of its five clauses; and the makers' tests on three lists
of rounds (`okAt`, OnBytes/Maker/Files.lean) in a fourth form.

The first two chains open trees of their own alone, and by the format's own test an own tree that
is opened has been sent. So the numbers over the whole file under which they open trees lie where
`RowFit` asks (its clauses o₁, o₂); and the second chain opens no tree of the first, so the clause
on such openings (l₁) asks nothing. The last clause (l₂₁) holds by the table of trees alone.

Main names:
  `own_of_ok`: in a description that passes the format's test the number of an own tree that is
    opened is below the number of roots that the entries count. `rootsIn_of_ok`: that number is
    `Three.rootsIn` of the list.
  `opensNo_own`: the numbers over the whole file under which a chain that opens its own trees
    alone opens them.
  `table_first`, `left_left`: the clause l₂₁. `RowLeft`: the clause that is left (l₂).
    `rowFitAt_of_read`: the test.
  `fits_of_read`: `Three.Whole.fits` at two roots a message, from the reading and what is left of
    it.
  `LeftOf4`: what is left. `okAt_of_read4`: the whole test.

Limits: `LeftOf4` is a premise, shown of no lists; so are `OwnAlone R₁`, `PlainRounds R₁` and
`OwnBook`. `RowLeft` reads the one table of trees and the data alone, no file and no block: it is
shown by lists alone in OnBytes/Maker/OkOfLeft.lean (`rowLeft_of_fits`), not here. The lists are
those of this reading's own dry runs. Nothing on soundness.
-/
import OnBytes.Maker.OkOfPlain
import OnBytes.Maker.TableChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK OnBytes.Tie.Pv.Keeps.Plain
open OnBytes.Three (rootsIn)
open OnBytes.Params (Rounds)

/-! ### An own tree that is opened has been sent -/

theorem own_of_roundsOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true →
      ∀ r ∈ rs, ∀ o ∈ r.opens, ∀ n, o.2 = .own n → n < sent + (rs.map (·.entry.roots)).sum
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, x, hx => by
    unfold Fmt.roundsOk at h
    rw [Bool.and_eq_true] at h
    intro o ho n e
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := h.1
      unfold Fmt.Round.ok at h1
      simp only [Bool.and_eq_true, List.all_eq_true] at h1
      have h2 := (h1.2 o ho).2
      rw [e] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      have h3 : n < sent + x.entry.roots := h2.1.1.1
      omega
    · have := own_of_roundsOk P noRand firstTree rs _ _ h.2 x hx' o ho n e
      omega

/-- In a description that passes the format's test the number of an own tree that is opened is below
the number of roots that the chain's entries count. -/
theorem own_of_ok {S : Fmt.Spec} (h : S.ok = true) :
    ∀ r ∈ S.rounds, ∀ o ∈ r.opens, ∀ n, o.2 = .own n → n < (S.rounds.map (·.entry.roots)).sum := by
  have h0 := h
  unfold Fmt.Spec.ok at h0
  simp only [Bool.and_eq_true] at h0
  intro r hr o ho n e
  have := own_of_roundsOk _ _ _ S.rounds _ _ h0.1.1.2 r hr o ho n e
  omega

/-- The entries of a description that passes the format's test count as many roots as its messages
have items "root". -/
theorem rootsIn_of_ok {S : Fmt.Spec} {R : Rounds} (h : S.ok = true) (e : S.rounds = R.map (·.1)) :
    (S.rounds.map (·.entry.roots)).sum = rootsIn R := by
  unfold Three.rootsIn
  rw [e, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  exact (of_rounds e (fun z => z.items.countP (· == .root) = z.entry.roots) (roots_of_ok h) x
    hx).symm

theorem mem_zipWith'' {α β γ : Type} (f : α → β → γ) :
    ∀ (l : List α) (l' : List β) (x : γ), x ∈ List.zipWith f l l' → ∃ u ∈ l, ∃ v, f u v = x
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | u :: l, v :: l', x, h => by
    rw [List.zipWith_cons_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨u, List.mem_cons_self .., v, rfl⟩
    · obtain ⟨u', hu, v', e⟩ := mem_zipWith'' f l l' x h
      exact ⟨u', List.mem_cons_of_mem _ hu, v', e⟩

/-- The numbers over the whole file under which a chain that opens its own trees alone opens them:
behind the earlier chains' trees, and below the chain's own count. -/
theorem opensNo_own (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ) (R : Rounds)
    (o : OwnAlone R) (N : ℕ)
    (hN : ∀ x ∈ R, ∀ u ∈ x.1.opens, ∀ n, u.2 = .own n → n < N) :
    ∀ d ∈ Three.rdsFromL all t₁ t₂ here base first R, ∀ j ∈ d.opens,
      ∃ n, n < N ∧ j = Three.wholeNo t₁ t₂ (here, n) := by
  intro d hd j hj
  unfold Three.rdsFromL at hd
  obtain ⟨x, hx, k, rfl⟩ := mem_zipWith'' _ _ _ _ hd
  obtain ⟨u, hu, e⟩ := List.mem_filterMap.1 hj
  obtain ⟨n, en⟩ := o x hx u hu
  rw [en] at e
  exact ⟨n, hN x hx u hu n en, (Option.some.inj e).symm⟩

/-- A tree of the table whose number over the whole file is below the first chain's count is the
first chain's. -/
theorem table_first (R₁ R₂ R₃ : Rounds) (t : Three.Tree × ℕ)
    (ht : t ∈ (Three.Whole.of R₁ R₂ R₃).table.zipIdx) (h : t.2 < rootsIn R₁) : t.1.chain = 0 := by
  obtain ⟨hl, e⟩ := List.mem_zipIdx' ht
  have lA : (Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
      (Three.Whole.of R₁ R₂ R₃).ds₁).length = rootsIn R₁ := trees_count _ _ _ _ _ _ _ _ R₁
  have e' : t.1 = (Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
      (Three.Whole.of R₁ R₂ R₃).ds₁ ++
      (Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
        (Three.Whole.of R₁ R₂ R₃).ds₂ ++
      Three.treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
        (Three.Whole.of R₁ R₂ R₃).ds₃))[t.2]'hl := e
  rw [List.getElem_append_left (by rw [lA]; exact h)] at e'
  exact treesOfChain_chain _ _ _ _ t.1 (e' ▸ List.getElem_mem _)

/-- **A tree of the first chain that is left behind the second chain was left behind the first**, at
the same depth: the last clause of `RowFit`, by the table alone. -/
theorem left_left (R₁ R₂ R₃ : Rounds) :
    ∀ l ∈ leftAfter (Three.Whole.of R₁ R₂ R₃) 1, l.no < rootsIn R₁ →
      ∃ l' ∈ leftAfter (Three.Whole.of R₁ R₂ R₃) 0, l'.no = l.no ∧ l.a ≤ l'.a := by
  intro l hl hlt
  unfold leftAfter at hl
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hm, hc⟩ := List.mem_filter.1 ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  obtain ⟨_, o, ho, h1⟩ := hc
  refine ⟨⟨t.2, t.1.shape.a⟩, ?_, rfl, le_refl _⟩
  unfold leftAfter
  refine List.mem_map.2 ⟨t, List.mem_filter.2 ⟨hm, ?_⟩, rfl⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  exact ⟨le_of_eq (table_first R₁ R₂ R₃ t hm hlt), o, ho, by omega⟩

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- What is left of `RowFit` (OnBytes/Maker/RowFit.lean): a tree of an earlier chain that the third
chain opens stands in the list of trees left behind the second, at the depth that the data give
it. -/
def RowLeft (D : WholeD) (L₂ : List LeftT) : Prop :=
  ∀ d ∈ D.ds₃, ∀ j ∈ d.opens, j < D.t₁ + D.t₂ → (L₂.find? (·.no == j)).map (·.a) = D.depth j

variable (a : ℕ)

/-- **`rowFitAt` from the reading**, `Three.Whole.fits` and one clause on the list of trees left:
the first two chains open trees of their own that they have sent; so the second opens none of the
first's, and the clause on such openings asks nothing. -/
theorem rowFitAt_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁) (R₃ : Rounds) {n : ℕ}
    (hf : Three.Whole.fits R₁ R₂ R₃ n = true)
    (L : RowLeft (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) (leftAfter (Three.Whole.of R₁ R₂ R₃) 1)) :
    rowFitAt a (Three.Whole.of R₁ R₂ R₃) = true := by
  obtain ⟨⟨k₁, e₁⟩, ⟨k₂, e₂⟩, _⟩ := read_ok T hS₁
  have o₂ := (shared_own p r.key T.shared_dry).1
  have hc := countsFit_of_fits a hf
  unfold countsFit at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  have t₁ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₁ = rootsIn R₁ := hc.1
  have t₂ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₂ = rootsIn R₂ := hc.2
  have N₁ : ∀ x ∈ R₁, ∀ u ∈ x.1.opens, ∀ m, u.2 = .own m → m < rootsIn R₁ := by
    rw [← rootsIn_of_ok k₁ e₁]
    exact of_rounds e₁ (fun z => ∀ u ∈ z.opens, ∀ m, u.2 = .own m →
      m < (S₁.base.rounds.map (·.entry.roots)).sum) (own_of_ok k₁)
  have N₂ : ∀ x ∈ R₂, ∀ u ∈ x.1.opens, ∀ m, u.2 = .own m → m < rootsIn R₂ := by
    rw [← rootsIn_of_ok k₂ e₂]
    exact of_rounds e₂ (fun z => ∀ u ∈ z.opens, ∀ m, u.2 = .own m →
      m < (S₂.base.rounds.map (·.entry.roots)).sum) (own_of_ok k₂)
  refine (rowFitB_iff _ _ _).2
    ⟨fun d hd j hj => ?_, fun d hd j hj => ?_, fun d hd j hj hlt => ?_, L,
      fun l hl hlt => left_left R₁ R₂ R₃ l hl (t₁ ▸ hlt)⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    obtain ⟨m, hm, rfl⟩ := opensNo_own _ _ _ 0 0 0 R₁ o₁ _ N₁ x (List.mem_of_mem_dropLast hx) j hj
    rw [t₁]
    show 0 + m < _
    omega
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    obtain ⟨m, hm, rfl⟩ := opensNo_own _ _ _ 1 _ 0 R₂ o₂ _ N₂ x hx j hj
    rw [t₁, t₂]
    show rootsIn R₁ + m < _
    omega
  · exfalso
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    obtain ⟨m, hm, rfl⟩ := opensNo_own _ _ _ 1 _ 0 R₂ o₂ _ N₂ x hx j hj
    rw [t₁] at hlt
    have h' : rootsIn R₁ + m < rootsIn R₁ := hlt
    omega

/-- What of the makers' tests is not shown to follow from a reading: the fourth form. -/
structure LeftOf4 (a : ℕ) (R₁ R₂ R₃ : Rounds) : Prop where
  /-- no message has more than two roots: the format has no such bound -/
  few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ 2
  c3 : fits3 R₁ R₂ R₃ = true
  c4 : fits4 R₁ R₂ R₃ = true
  seal₁ : SealAt R₁
  seal₂ : SealAt R₂
  c6 : fits6 R₁ R₂ R₃ = true
  stored : storedFit a (Three.Whole.of R₁ R₂ R₃) = true
  /-- the first chain has a round beside its last -/
  two : 2 ≤ R₁.length
  row : RowLeft (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) (leftAfter (Three.Whole.of R₁ R₂ R₃) 1)

/-- `Three.Whole.fits` at two roots a message, from the reading and what is left of it. -/
theorem fits_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁)
    (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ 2)
    (c3 : fits3 R₁ R₂ R₃ = true) (c4 : fits4 R₁ R₂ R₃ = true) (s₁ : SealAt R₁) (s₂ : SealAt R₂)
    (c6 : fits6 R₁ R₂ R₃ = true) : Three.Whole.fits R₁ R₂ R₃ 2 = true := by
  obtain ⟨⟨k₁, e₁⟩, k₂, e₂⟩ := read_okX T hS₁
  have c2 := names_of_read T hS₁ o₁ b₁ R₃ hd
  have c5 : ([R₁, R₂].all fun R => match R.getLast? with
      | some r => r.1.kind == .sealed && r.1.opens.isEmpty && r.1.entry.roots == 0 &&
          r.2.isEmpty && r.1.items.isEmpty && r.1.entry.work == 0 && r.1.entry.drawE == 0 &&
          r.1.entry.drawNZ == 0 && r.1.entry.poss == 0 && r.1.entry.trits == 0
      | none => false) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨seal_clause k₁ e₁ s₁, seal_clause k₂ e₂ s₂⟩
  have rest : fitsRest R₁ R₂ R₃ = true := by
    simp only [fitsRest, Bool.and_eq_true]
    exact ⟨⟨⟨⟨c2, c3⟩, c4⟩, c5⟩, c6⟩
  exact fits_of_parts few (roots_of_read T hS₁ b₁ R₃ hd) rest

/-- **The makers' tests pass at the lists of a file that was read, if what is left holds: the fourth
form.** Of `rowFitAt`'s five clauses one is left. -/
theorem okAt_of_read4
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁) (pl₁ : PlainRounds R₁)
    (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (L : LeftOf4 a R₁ R₂ R₃) :
    okAt a (some (R₁, R₂, R₃)) = true :=
  okAt_of_read3 a T hS₁ o₁ pl₁ b₁ R₃ hd
    ⟨L.few, L.c3, L.c4, L.seal₁, L.seal₂, L.c6, L.stored, L.two,
      rowFitAt_of_read a T hS₁ o₁ R₃
        (fits_of_read T hS₁ o₁ b₁ R₃ hd L.few L.c3 L.c4 L.seal₁ L.seal₂ L.c6) L.row⟩

end Read

end OnBytes.Maker

#print axioms OnBytes.Maker.own_of_ok
#print axioms OnBytes.Maker.left_left
#print axioms OnBytes.Maker.rowFitAt_of_read
#print axioms OnBytes.Maker.fits_of_read
#print axioms OnBytes.Maker.okAt_of_read4
