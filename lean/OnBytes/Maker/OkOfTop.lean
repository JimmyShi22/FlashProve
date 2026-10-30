-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfTop.lean: the makers' tests on three lists of rounds (`okAt`,
OnBytes/Maker/Files.lean) from the record of a file's reading and what is left, in a second form
with less left than in OnBytes/Maker/OkOfRead.lean.

Main names:
  `fits3`, `fits4`, `fits6`: three clauses of `Three.Whole.fits` (OnBytes/Three/Data.lean), each
    under a name.
  `SealAt R`: the last round of R is of the kind "sealed", its message has no item, and it asks
    for no work. `seal_clause`: with the format's test that is the whole clause on a chain's last
    round.
  `read_okX`: the first two descriptions of a reading pass `Fmt.SpecX.ok` and are made of the
    first two lists.
  `LeftOf2`: what is left. `okAt_of_read2`: the whole test.

Limits: `LeftOf2` is a premise, shown of no lists; so are `OwnAlone R₁` and `OwnBook`. `fits3`,
`fits4`, `fits6` and the clause in `seal_clause` say the text of OnBytes/Three/Data.lean again: if
that turns, the proofs break. The lists are those of this reading's own dry runs. Nothing on
soundness.
-/
import OnBytes.Maker.OkOfSeal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- The third clause of `Three.Whole.fits`: an opened tree stands in the table, was sent no later
than it is opened, and has the table's shape. -/
def fits3 (R₁ R₂ R₃ : Rounds) : Bool :=
  (Three.Whole.of R₁ R₂ R₃).opens.all fun o =>
    match (Three.Whole.of R₁ R₂ R₃).table[o.1]? with
    | none => false
    | some t => Three.Whole.notLater (t.chain, t.round) o.2.2 && t.shape == o.2.1

/-- The clause on the number in an opened tree's label. -/
def fits4 (R₁ R₂ R₃ : Rounds) : Bool :=
  (Three.Whole.of R₁ R₂ R₃).table.zipIdx.all fun t =>
    t.1.openedAt.isEmpty ||
      t.1.shape.tree == (match t.1.chain with
        | 0 => t.2
        | 1 => t.2 - (Three.Whole.of R₁ R₂ R₃).t₁
        | _ => Three.first₃ (Three.Whole.of R₁ R₂ R₃).t₁ +
            (t.2 - ((Three.Whole.of R₁ R₂ R₃).t₁ + (Three.Whole.of R₁ R₂ R₃).t₂)))

/-- No round but the last of the first two lists is of the kind "sealed". -/
def fits6 (R₁ R₂ R₃ : Rounds) : Bool :=
  [R₁.dropLast, R₂.dropLast, R₃].all fun R => R.all fun r => r.1.kind != .sealed

/-- What is left of the clause on a chain's last round: it is of the kind "sealed", its message has
no item, and it asks for no work. -/
def SealAt (R : Rounds) : Prop :=
  ∃ r, R.getLast? = some r ∧ r.1.kind = .sealed ∧ r.1.items = [] ∧ r.1.entry.work = 0

/-- The clause on a chain's last round, from the format's test and `SealAt`. -/
theorem seal_clause {S : Fmt.SpecX} {R : Rounds} (h : S.ok = true)
    (e : S.base.rounds.zip S.stored = R) (s : SealAt R) :
    (match R.getLast? with
      | some r => r.1.kind == .sealed && r.1.opens.isEmpty && r.1.entry.roots == 0 &&
          r.2.isEmpty && r.1.items.isEmpty && r.1.entry.work == 0 && r.1.entry.drawE == 0 &&
          r.1.entry.drawNZ == 0 && r.1.entry.poss == 0 && r.1.entry.trits == 0
      | none => false) = true := by
  obtain ⟨r, hr, hk, hi, hw⟩ := s
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    seal_fields h r (e ▸ List.mem_of_getLast? hr) hk
  rw [hr]
  simp only [hk, a1, a2, a3, a4, a5, a6, a7, hi, hw, List.isEmpty_nil, beq_self_eq_true,
    Bool.and_self]

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- The first two descriptions of a reading pass the format's test with the stored tables, and are
made of the first two lists. -/
theorem read_okX (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) :
    (S₁.ok = true ∧ S₁.base.rounds.zip S₁.stored = R₁) ∧
      (S₂.ok = true ∧ S₂.base.rounds.zip S₂.stored = R₂) := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  obtain ⟨f1, f2, -⟩ := describeWith_facts hS₁
  obtain ⟨g1, g2, -⟩ := describeWith_facts hS₂
  exact ⟨⟨(readChain_read _ _ _ _ _ _ T.first_read).1, by rw [f1, f2]; exact zip_fst_snd R₁⟩,
    ⟨(readChain_read _ _ _ _ _ _ T.shared_read).1, by rw [g1, g2]; exact zip_fst_snd R₂⟩⟩

/-- What of the makers' tests is not shown to follow from a reading: the second form. -/
structure LeftOf2 (a : ℕ) (R₁ R₂ R₃ : Rounds) : Prop where
  /-- no message has more than two roots: the format has no such bound -/
  few : ∀ x ∈ R₁ ++ (R₂ ++ R₃), x.1.items.countP (· == .root) ≤ 2
  c3 : fits3 R₁ R₂ R₃ = true
  c4 : fits4 R₁ R₂ R₃ = true
  seal₁ : SealAt R₁
  seal₂ : SealAt R₂
  c6 : fits6 R₁ R₂ R₃ = true
  stored : storedFit a (Three.Whole.of R₁ R₂ R₃) = true
  /-- no opening of the three lists bears the mark "stored" -/
  plain : ∀ x ∈ R₁ ++ (R₂ ++ R₃), ∀ o ∈ x.1.opens, o.1.stored = false
  /-- the first chain has a round beside its last -/
  two : 2 ≤ R₁.length
  row : rowFitAt a (Three.Whole.of R₁ R₂ R₃) = true

variable (a : ℕ)

/-- **The makers' tests pass at the lists of a file that was read, if what is left holds: the second
form.** Beyond `okAt_of_read`: the clause on names is gone, if the first chain opens its own trees
alone; of the ten fields of the clause on a chain's last round three are left; `runFit` is brought
down to the openings. -/
theorem okAt_of_read2
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁)
    (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (L : LeftOf2 a R₁ R₂ R₃) :
    okAt a (some (R₁, R₂, R₃)) = true := by
  obtain ⟨⟨k₁, e₁⟩, k₂, e₂⟩ := read_okX T hS₁
  have c2 := names_of_read T hS₁ o₁ b₁ R₃ hd
  have c5 : ([R₁, R₂].all fun R => match R.getLast? with
      | some r => r.1.kind == .sealed && r.1.opens.isEmpty && r.1.entry.roots == 0 &&
          r.2.isEmpty && r.1.items.isEmpty && r.1.entry.work == 0 && r.1.entry.drawE == 0 &&
          r.1.entry.drawNZ == 0 && r.1.entry.poss == 0 && r.1.entry.trits == 0
      | none => false) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨seal_clause k₁ e₁ L.seal₁, seal_clause k₂ e₂ L.seal₂⟩
  have rest : fitsRest R₁ R₂ R₃ = true := by
    simp only [fitsRest, Bool.and_eq_true]
    exact ⟨⟨⟨⟨c2, L.c3⟩, L.c4⟩, c5⟩, L.c6⟩
  exact okAt_of_read a T hS₁ b₁ R₃ hd
    ⟨L.few, rest, L.stored,
      runFit_of_opens a R₁ R₂ R₃ (fun x hx => L.plain x (List.mem_append_left _ hx))
        (fun x hx => L.plain x (List.mem_append_right _ (List.mem_append_left _ hx)))
        (fun x hx => L.plain x (List.mem_append_right _ (List.mem_append_right _ hx))),
      L.two, L.row⟩

end Read

end OnBytes.Maker

#print axioms OnBytes.Maker.seal_clause
#print axioms OnBytes.Maker.okAt_of_read2
