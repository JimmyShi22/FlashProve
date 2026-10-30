-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfRead.lean: where the program has read a file's three chains, a part of the
makers' tests on the three lists of rounds (`okAt`, OnBytes/Maker/Files.lean) has passed: what
follows from the reading, and what is left, by name.

Why. Where `okAt` says no, a file's reduction stands at three empty chains and accepts nothing. So
a statement "the program's yes gives the typed verifier's yes" needs `okAt`'s yes. The program's
reader returns nothing unless a chain's description passes the format's own test
(`readChain_read`, OnBytes/Maker/ReadFacts.lean), and that test holds a part of what `okAt` asks.
The first two lists are the reading's own. The third list at which `okAt` is asked is the dry
run's, with made-up names for the earlier chains' trees; the format's test holds of the reading's
own third list; what it says of entries, items and shapes is carried along `named_of_read`
(OnBytes/Maker/OwesOfRead.lean).

Main names:
  `work_of_ok`, `depth_of_ok`, `rounds_of_ok`: in a description that passes the format's test: at
    most 64 bits of work a round; no opening of a tree deeper than 48; a round.
  `workFit_of_entries`, `depthFit_of_opens`: the two tests from the three lists. `shapeAt_mem`,
    `opensOf_mem`, `trees_depth`: a tree's shape in the data is the stand-in's or that of an
    opening of a round.
  `read_ok`: the three descriptions of a reading pass the format's test, and their rounds are the
    lists.
  `workFit_of_read`, `depthFit_of_read`, `roots_of_read`, `third_of_read`: from the record of the
    reading (`ThreeRead`).
  `fitsRest`, `fits_of_parts`: `Three.Whole.fits` from its first clause, in two halves, and its
    other five.
  `LeftOf a R₁ R₂ R₃`: what is not shown to follow. `okAt_of_read`: the whole test from the
    reading and `LeftOf`.

Limits: `LeftOf` is a premise; it is shown of no lists. It holds one bound that the format does
not have (two roots a message), five clauses of `Three.Whole.fits` whole, `storedFit`, `runFit`,
`rowFitAt`, and that the first chain has two rounds; parts of these may follow from the format's
test or from the blocks' texts: not shown here. `fitsRest` says the text of
OnBytes/Three/Data.lean again: if that turns, `fits_of_parts` breaks. The lists are those of this
reading's own dry runs: that a description's sample has the same lists is not shown here.
`OwnBook` of the first block's book is a premise. Nothing on soundness.
-/
import OnBytes.Maker.OkOfFormat
import OnBytes.Maker.OwesOfRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-! ### What the format's test says of a round -/

theorem work_of_roundsOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true → ∀ r ∈ rs, r.entry.work ≤ 64
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, x, hx => by
    unfold Fmt.roundsOk at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := h.1
      unfold Fmt.Round.ok at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      tauto
    · exact work_of_roundsOk P noRand firstTree rs _ _ h.2 x hx'

/-- In a description that passes the format's test no round has more than 64 bits of work. -/
theorem work_of_ok {S : Fmt.Spec} (h : S.ok = true) : ∀ r ∈ S.rounds, r.entry.work ≤ 64 := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true] at h
  exact work_of_roundsOk _ _ _ S.rounds _ _ h.1.1.2

/-- No opening is of a tree deeper than 48. -/
theorem depth_of_ok {S : Fmt.Spec} (h : S.ok = true) :
    ∀ r ∈ S.rounds, ∀ o ∈ r.opens, o.1.a ≤ 48 := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true] at h
  have h1 := h.1.2
  simp only [List.all_eq_true, Fmt.depthOK, decide_eq_true_eq] at h1
  exact h1

/-- It has a round. -/
theorem rounds_of_ok {S : Fmt.Spec} (h : S.ok = true) : S.rounds ≠ [] := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  tauto

/-! ### From lists to the data -/

/-- What holds of all members of one list under g holds of all of another under f, if the two
images are one list. -/
theorem forall_of_map {α β γ : Type} {l : List α} {l' : List β} (f : α → γ) (g : β → γ)
    (p : γ → Prop) (e : l.map f = l'.map g) (h : ∀ y ∈ l', p (g y)) : ∀ x ∈ l, p (f x) := by
  intro x hx
  have h1 : f x ∈ l'.map g := e ▸ List.mem_map_of_mem hx
  obtain ⟨y, hy, ey⟩ := List.mem_map.1 h1
  exact ey ▸ h y hy

section Data
variable (a : ℕ) (R₁ R₂ R₃ : Rounds)

/-- **`workFit` from the entries of the three lists.** -/
theorem workFit_of_entries (h₁ : ∀ r ∈ R₁, r.1.entry.work ≤ 64) (h₂ : ∀ r ∈ R₂, r.1.entry.work ≤ 64)
    (h₃ : ∀ r ∈ R₃, r.1.entry.work ≤ 64) :
    (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).workFit = true := by
  unfold WholeD.workFit
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_append]
  have k₁ := forall_of_map (fun d : Three.RDL => d.entry)
    (fun r : Fmt.Round × List Fmt.Stored => r.1.entry) (fun e : Fmt.Entry => e.work ≤ 64)
    (entries_ds₁ R₁ R₂ R₃) h₁
  have k₂ := forall_of_map (fun d : Three.RDL => d.entry)
    (fun r : Fmt.Round × List Fmt.Stored => r.1.entry) (fun e : Fmt.Entry => e.work ≤ 64)
    (entries_ds₂ R₁ R₂ R₃) h₂
  have k₃ := forall_of_map (fun d : Three.RDL => d.entry)
    (fun r : Fmt.Round × List Fmt.Stored => r.1.entry) (fun e : Fmt.Entry => e.work ≤ 64)
    (entries_ds₃ R₁ R₂ R₃) h₃
  rintro d (hd | hd | hd)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact k₁ x (List.mem_of_mem_dropLast hx)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact k₂ x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact k₃ x hx

/-- The shape under which a tree stands in the data is the stand-in's, or that of an opening. -/
theorem shapeAt_mem (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (j : ℕ) (dflt : Fmt.Shape) :
    Three.shapeAt all j dflt = dflt ∨ ∃ x ∈ all, Three.shapeAt all j dflt = x.2.1 := by
  unfold Three.shapeAt
  cases h : all.find? (·.1 == j) with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, List.mem_of_find?_eq_some h, rfl⟩

/-- An opening in the list of all openings of a chain is an opening of one of its rounds. -/
theorem opensOf_mem (t₁ t₂ here : ℕ) (R : Rounds) (x : ℕ × Fmt.Shape × ℕ × ℕ)
    (h : x ∈ Three.opensOf t₁ t₂ here R) : ∃ r ∈ R, ∃ o ∈ r.1.opens, x.2.1 = o.1 := by
  unfold Three.opensOf at h
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 h
  obtain ⟨o, ho, e⟩ := List.mem_filterMap.1 hx
  obtain ⟨y, _, ey⟩ := Option.map_eq_some_iff.1 e
  exact ⟨r.1, (List.mem_zipIdx' hr).2 ▸ List.getElem_mem _, o, ho, by rw [← ey]⟩

theorem mem_zipWith' {α β γ : Type} (f : α → β → γ) :
    ∀ (l : List α) (l' : List β) (x : γ), x ∈ List.zipWith f l l' → ∃ u v, f u v = x
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | u :: l, v :: l', x, h => by
    rw [List.zipWith_cons_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨u, v, rfl⟩
    · exact mem_zipWith' f l l' x h

/-- Every tree of a chain's data has the depth 0 or that of an opening of the file. -/
theorem trees_depth (n : ℕ) (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (hall : ∀ x ∈ all, x.2.1.a ≤ n)
    (t₁ t₂ here base first : ℕ) (R : Rounds) :
    ∀ d ∈ Three.rdsFromL all t₁ t₂ here base first R, ∀ s ∈ d.trees, s.a ≤ n := by
  intro d hd s hs
  unfold Three.rdsFromL at hd
  obtain ⟨r, k, rfl⟩ := mem_zipWith' _ _ _ _ hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
  rcases shapeAt_mem all (base + k + i) (Three.bareShape first (k + i)) with e | ⟨x, hx, e⟩
  · rw [e]
    exact Nat.zero_le _
  · rw [e]
    exact hall x hx

/-- **`depthFit` from the openings of the three lists.** -/
theorem depthFit_of_opens (h₁ : ∀ r ∈ R₁, ∀ o ∈ r.1.opens, o.1.a ≤ 63)
    (h₂ : ∀ r ∈ R₂, ∀ o ∈ r.1.opens, o.1.a ≤ 63) (h₃ : ∀ r ∈ R₃, ∀ o ∈ r.1.opens, o.1.a ≤ 63) :
    (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).depthFit = true := by
  have hall : ∀ x ∈ (Three.Whole.of R₁ R₂ R₃).opens, x.2.1.a ≤ 63 := by
    intro x hx
    have hx' : x ∈ Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 0 R₁ ++
        (Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 1 R₂ ++
          Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 2 R₃) := hx
    rcases List.mem_append.1 hx' with h | h
    · obtain ⟨r, hr, o, ho, e⟩ := opensOf_mem _ _ _ _ x h
      exact e ▸ h₁ r hr o ho
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨r, hr, o, ho, e⟩ := opensOf_mem _ _ _ _ x h
        exact e ▸ h₂ r hr o ho
      · obtain ⟨r, hr, o, ho, e⟩ := opensOf_mem _ _ _ _ x h
        exact e ▸ h₃ r hr o ho
  unfold WholeD.depthFit
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_append]
  rintro d (hd | hd | hd) s hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact trees_depth 63 _ hall _ _ _ _ _ R₁ x (List.mem_of_mem_dropLast hx) s hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact trees_depth 63 _ hall _ _ _ _ _ R₂ x hx s hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact trees_depth 63 _ hall _ _ _ _ _ R₃ x hx s hs

end Data

/-! ### From the record of the three chains' reading -/

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

theorem base_ok {S : Fmt.SpecX} (h : S.ok = true) : S.base.ok = true := by
  unfold Fmt.SpecX.ok at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- **The three descriptions under which a file's chains were read pass the format's test**, and
their rounds are the three lists; the third is the reading's own. -/
theorem read_ok (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) :
    (S₁.base.ok = true ∧ S₁.base.rounds = R₁.map (·.1)) ∧
      (S₂.base.ok = true ∧ S₂.base.rounds = R₂.map (·.1)) ∧
      (S₃.base.ok = true ∧ S₃.base.rounds = R₃'.map (·.1)) := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (secondFirstTree r.first) = some S₃ :=
    T.second_spec
  exact ⟨⟨base_ok (readChain_read _ _ _ _ _ _ T.first_read).1,
      (describeWith_facts hS₁).1⟩,
    ⟨base_ok (readChain_read _ _ _ _ _ _ T.shared_read).1,
      (describeWith_facts hS₂).1⟩,
    ⟨base_ok (readChain_read _ _ _ _ _ _ T.second_read).1,
      (describeWith_facts hS₃).1⟩⟩

/-- What holds of every round of a description holds of every member of the list of which it is
made. -/
theorem of_rounds {S : Fmt.Spec} {R : Rounds} (e : S.rounds = R.map (·.1)) (q : Fmt.Round → Prop)
    (h : ∀ x ∈ S.rounds, q x) : ∀ x ∈ R, q x.1 := fun x hx =>
  h x.1 (e ▸ List.mem_map_of_mem hx)

variable (a : ℕ)

/-- **`workFit` from the reading.** The third list is the dry run's. -/
theorem workFit_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).workFit = true := by
  obtain ⟨⟨o₁, e₁⟩, ⟨o₂, e₂⟩, o₃, e₃⟩ := read_ok T hS₁
  have A := named_of_read T hS₁ b₁ R₃ hd
  refine workFit_of_entries a R₁ R₂ R₃ (of_rounds e₁ (·.entry.work ≤ 64) (work_of_ok o₁))
    (of_rounds e₂ (·.entry.work ≤ 64) (work_of_ok o₂)) ?_
  exact forall_of_map (fun x : Fmt.Round × List Fmt.Stored => x.1.entry)
    (fun x : Fmt.Round × List Fmt.Stored => x.1.entry) (fun e : Fmt.Entry => e.work ≤ 64)
    (alike_entries A).symm (of_rounds e₃ (·.entry.work ≤ 64) (work_of_ok o₃))

/-- **`depthFit` from the reading.** -/
theorem depthFit_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).depthFit = true := by
  obtain ⟨⟨o₁, e₁⟩, ⟨o₂, e₂⟩, o₃, e₃⟩ := read_ok T hS₁
  have A := named_of_read T hS₁ b₁ R₃ hd
  have w : ∀ {S : Fmt.Spec} {R : Rounds}, S.ok = true → S.rounds = R.map (·.1) →
      ∀ x ∈ R, ∀ s ∈ x.1.opens.map (·.1), s.a ≤ 63 := fun o e x hx s hs => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    exact le_trans (of_rounds e (fun z => ∀ o ∈ z.opens, o.1.a ≤ 48) (depth_of_ok o) x hx y hy)
      (by norm_num)
  have u : ∀ {R : Rounds}, (∀ x ∈ R, ∀ s ∈ x.1.opens.map (·.1), s.a ≤ 63) →
      ∀ x ∈ R, ∀ o ∈ x.1.opens, o.1.a ≤ 63 := fun h x hx o ho =>
    h x hx o.1 (List.mem_map_of_mem ho)
  refine depthFit_of_opens a R₁ R₂ R₃ (u (w o₁ e₁)) (u (w o₂ e₂)) (u ?_)
  exact forall_of_map (fun x : Fmt.Round × List Fmt.Stored => x.1.opens.map (·.1))
    (fun x : Fmt.Round × List Fmt.Stored => x.1.opens.map (·.1))
    (fun l : List Fmt.Shape => ∀ s ∈ l, s.a ≤ 63) (alike_shapes A).symm (w o₃ e₃)

/-- **In all three lists every message has as many items "root" as its entry says**: the second half
of the first clause of `Three.Whole.fits`. -/
theorem roots_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) = x.1.entry.roots := by
  obtain ⟨⟨o₁, e₁⟩, ⟨o₂, e₂⟩, o₃, e₃⟩ := read_ok T hS₁
  have A := named_of_read T hS₁ b₁ R₃ hd
  have k₃ : ∀ x ∈ R₃, x.1.items.countP (· == .root) = x.1.entry.roots :=
    forall_of_map (fun x : Fmt.Round × List Fmt.Stored => (x.1.items, x.1.entry))
      (fun x : Fmt.Round × List Fmt.Stored => (x.1.items, x.1.entry))
      (fun y : List Fmt.Item × Fmt.Entry => y.1.countP (· == .root) = y.2.roots)
      (alike_map A (fun x => (x.1.items, x.1.entry)) fun _ _ k => Prod.ext k.items k.entry).symm
      (of_rounds e₃ (fun z => z.items.countP (· == .root) = z.entry.roots) (roots_of_ok o₃))
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact of_rounds e₁ (fun z => z.items.countP (· == .root) = z.entry.roots) (roots_of_ok o₁) x h
  · rcases List.mem_append.1 h with h | h
    · exact of_rounds e₂ (fun z => z.items.countP (· == .root) = z.entry.roots) (roots_of_ok o₂) x
        h
    · exact k₃ x h

/-- **The third list has a round**: the second half of `someFit`. -/
theorem third_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) : R₃ ≠ [] := by
  obtain ⟨_, _, o₃, e₃⟩ := read_ok T hS₁
  have A := named_of_read T hS₁ b₁ R₃ hd
  have h := rounds_of_ok o₃
  intro e
  apply h
  have l := alike_length A
  rw [e, List.length_nil] at l
  rw [e₃, List.length_eq_zero_iff.1 l]
  rfl

/-! ### The whole test, from the reading and what is left -/

/-- The clauses (2) to (6) of `Three.Whole.fits`, which do not hang on the bound on the roots. -/
def fitsRest (R₁ R₂ R₃ : Rounds) : Bool :=
  let W := Three.Whole.of R₁ R₂ R₃
  let Rs := [(0, R₁), (1, R₂), (2, R₃)]
  (Rs.all fun x => x.2.all fun r => r.1.opens.all fun o =>
    match Three.named x.1 o.2 with
    | none => false
    | some y => (x.1 == 2 || y.1 == x.1) && decide (y.1 ≤ x.1)) &&
  (W.opens.all fun o =>
    match W.table[o.1]? with
    | none => false
    | some t => Three.Whole.notLater (t.chain, t.round) o.2.2 && t.shape == o.2.1) &&
  (W.table.zipIdx.all fun t =>
    t.1.openedAt.isEmpty ||
      t.1.shape.tree == (match t.1.chain with
        | 0 => t.2
        | 1 => t.2 - W.t₁
        | _ => Three.first₃ W.t₁ + (t.2 - (W.t₁ + W.t₂)))) &&
  ([R₁, R₂].all fun R => match R.getLast? with
    | some r => r.1.kind == .sealed && r.1.opens.isEmpty && r.1.entry.roots == 0 && r.2.isEmpty &&
        r.1.items.isEmpty && r.1.entry.work == 0 && r.1.entry.drawE == 0 && r.1.entry.drawNZ == 0 &&
        r.1.entry.poss == 0 && r.1.entry.trits == 0
    | none => false) &&
  ([R₁.dropLast, R₂.dropLast, R₃].all fun R => R.all fun r => r.1.kind != .sealed)

/-- `Three.Whole.fits` from its first clause, in two halves, and the rest. -/
theorem fits_of_parts {R₁ R₂ R₃ : Rounds} {n : ℕ}
    (few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ n)
    (cnt : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) = x.1.entry.roots)
    (rest : fitsRest R₁ R₂ R₃ = true) : Three.Whole.fits R₁ R₂ R₃ n = true := by
  simp only [fitsRest, Bool.and_eq_true] at rest
  obtain ⟨⟨⟨⟨c2, c3⟩, c4⟩, c5⟩, c6⟩ := rest
  simp only [Three.Whole.fits, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun x hx => ⟨few x (List.mem_append_left _ hx), cnt x (List.mem_append_left _ hx)⟩,
    fun x hx => ⟨few x (List.mem_append_right _ (List.mem_append_left _ hx)),
      cnt x (List.mem_append_right _ (List.mem_append_left _ hx))⟩,
    fun x hx => ⟨few x (List.mem_append_right _ (List.mem_append_right _ hx)),
      cnt x (List.mem_append_right _ (List.mem_append_right _ hx))⟩⟩

/-- What of the makers' tests is not shown to follow from a reading. -/
structure LeftOf (a : ℕ) (R₁ R₂ R₃ : Rounds) : Prop where
  /-- no message has more than two roots: the format has no such bound -/
  few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ 2
  /-- the clauses (2) to (6) of `Three.Whole.fits` -/
  rest : fitsRest R₁ R₂ R₃ = true
  stored : storedFit a (Three.Whole.of R₁ R₂ R₃) = true
  run : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).runFit = true
  /-- the first chain has a round beside its last -/
  two : 2 ≤ R₁.length
  row : rowFitAt a (Three.Whole.of R₁ R₂ R₃) = true

/-- **The makers' tests pass at the lists of a file that was read, if what is left holds.** The
third list is the dry run's. Of the eight tests three are gone (`countsFit`, `workFit`,
`depthFit`), and a half of two (`Three.Whole.fits`' first clause, `someFit`). -/
theorem okAt_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (L : LeftOf a R₁ R₂ R₃) :
    okAt a (some (R₁, R₂, R₃)) = true := by
  have f := fits_of_parts L.few (roots_of_read T hS₁ b₁ R₃ hd) L.rest
  have s : someFit (R₁, R₂, R₃) = true := by
    unfold someFit
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    exact ⟨L.two, third_of_read T hS₁ b₁ R₃ hd⟩
  simp only [okAt, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨f, L.stored⟩, countsFit_of_fits a f⟩, workFit_of_read a T hS₁ b₁ R₃ hd⟩,
    depthFit_of_read a T hS₁ b₁ R₃ hd⟩, L.run⟩, s⟩, L.row⟩

end Read

end OnBytes.Maker

#print axioms OnBytes.Maker.read_ok
#print axioms OnBytes.Maker.workFit_of_read
#print axioms OnBytes.Maker.depthFit_of_read
#print axioms OnBytes.Maker.roots_of_read
#print axioms OnBytes.Maker.third_of_read
#print axioms OnBytes.Maker.fits_of_parts
#print axioms OnBytes.Maker.okAt_of_read
