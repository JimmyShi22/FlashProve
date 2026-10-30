-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/RunLaws.lean: what a "yes" of a file's description is made of, both ways. Theorems on
the general functions of Johnson/Desc/Block.lean: a block's step, the fold over a chain's blocks, a
chain's fold, the decision's course, the decision. They hold of EVERY description: no kind, no file
and no plan is named. It imports that file alone. THE MAIN LAWS ARE EQUIVALENCES: the text of a
function on the left, what it is made of on the right; three readings of `Except` and three
corollaries of `FileDescription.run_ok` go one way. The laws that go one way and carry a property or a
relation along a fold (a fold's last block; a fold over two lists; the course read back), and the
laws on the chains' end's one text, are the matter of other files of this folder: none of them is
stated again here.

Why. A law of soundness about a description starts from `F.run x v₁ v₂ v₃ = true`. Each writer would
have to open the decision's course anew to reach the tests, the folds and the ends that this yes is
made of. Here that is done once.

The laws, in the file's order.

  1 Readings of `Except`: `error_ne_ok`, `bind_eq_ok`, `need_eq_ok`.

  2 A step: `Block.step_ok`: a step goes well just if `roundsFit` and the test on the columns say
  yes, the block's `decide` goes well at the rounds without the sealed digest and at the columns
  regrouped, and as many columns are taken as are read. `Block.lift_decide`: a block that is lifted
  to a wider record decides at its part.

  3 The fold: `foldBlocks_cons_ok`: what a fold over b :: l that goes well is made of.
  `foldBlocks_append_ok`: a fold over l₁ ++ l₂ goes well just if the fold over l₁ does and the fold
  over l₂ does from where that one ends.

  4 A chain's fold: `chainAt_ok`: it gives an end just if the chain has a block and the fold ends
  there with no round and no column left.

  5 The decision: `runCore_ok`: the course gives three ends just if the tests on the plan have no
  word to say, the test on the instance says yes, every word of the three views is below the prime,
  each chain's fold gives its end, the second chain's start gives its first state at the first two
  ends, and the last test says yes at the three ends. `FileDescription.run_ok`: the same of a description,
  in its own fields, from its yes. `FileDescription.planOk_of_run`, `FileDescription.okStart_of_run`.

  6 The tests on the plan: `FileDescription.PlanOk`: what they ask, as a structure of fifteen named
  propositions; `FileDescription.planOk_ok`: they say yes just if it holds. So the blocks' rounds in a row
  ARE the plan's declared rounds, as equations, and every block of the three flat lists has passed
  its own test on the plan and is shaped.

Limits. A law here says what a yes is made of, not that any part of it is right: what `decide`,
`fin`, `fileOk` and `okStart` ask is each description's own. Nothing on soundness, on an honest
prover or on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

universe u v

/-! ## 1 Readings of Except -/

theorem error_ne_ok {ε : Type u} {α : Type v} {e : ε} {a : α}
    (h : (Except.error e : Except ε α) = .ok a) : False := by cases h

/-- A bind that goes well: its first part went well, and the rest did at what that gave. -/
theorem bind_eq_ok {ε : Type u} {α β : Type v} {a : Except ε α} {f : α → Except ε β} {y : β}
    (h : (a >>= f) = .ok y) : ∃ x, a = .ok x ∧ f x = .ok y := by
  cases a with
  | error e => exact (error_ne_ok h).elim
  | ok x => exact ⟨x, rfl, h⟩

theorem need_eq_ok {name : String} {b : Bool} {t : Unit} (h : need name b = .ok t) : b = true := by
  cases b with
  | true => rfl
  | false => exact (error_ne_ok h).elim

variable {S Cl : Type}

/-! ## 2 A step -/

/-- **What a step that goes well is made of.** -/
theorem Block.step_ok {ft : Nat} {b : Block S Cl} {s e : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {k : Nat} : b.step ft s rs cols = .ok (e, k) ↔
    roundsFit b.rounds rs = true ∧
      ((cols.take k).map fun c => (c.1, c.2.1, c.2.2.length)) =
        (groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id ∧
      b.decide s (rs.map noDigest)
        (regroup ((groupsOf ft b.rounds (rs.map (·.drawn))).map (·.length)) (cols.take k)) = .ok e ∧
      k = ((groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id).length := by
  constructor
  · intro h
    unfold Block.step at h
    obtain ⟨_, h1, h⟩ := bind_eq_ok h
    obtain ⟨_, h2, h⟩ := bind_eq_ok h
    obtain ⟨s', hd, h⟩ := bind_eq_ok h
    have he := Except.ok.inj h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hs, hk⟩ := he
    subst hs hk
    exact ⟨need_eq_ok h1, by simpa using need_eq_ok h2, hd, rfl⟩
  · rintro ⟨h1, h2, hd, hk⟩
    subst hk
    unfold Block.step
    simp only [h1, h2, hd, need, bind, Except.bind, pure, Except.pure, beq_self_eq_true, if_true]

/-- **A lifted block decides at its part**: it gives t' just if the block gives some e at `get t`,
and t' is t with e laid back. -/
theorem Block.lift_decide {T : Type} {get : T → S} {set : T → S → T} {b : Block S Cl} {t t' : T}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} :
    (b.lift get set).decide t rs gs = .ok t' ↔
      ∃ e, b.decide (get t) rs gs = .ok e ∧ t' = set t e := by
  show (b.decide (get t) rs gs).map (set t) = .ok t' ↔ _
  cases b.decide (get t) rs gs with
  | error e =>
    constructor
    · intro h; exact (error_ne_ok h).elim
    · rintro ⟨_, h, _⟩; exact (error_ne_ok h).elim
  | ok e =>
    constructor
    · intro h; exact ⟨e, rfl, (Except.ok.inj h).symm⟩
    · rintro ⟨e', h, ht⟩
      rw [ht, ← Except.ok.inj h]
      rfl

/-! ## 3 The fold -/

/-- **What a fold over b :: l that goes well is made of.** -/
theorem foldBlocks_cons_ok {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn} :
    foldBlocks ft (b :: l) s rs cols = .ok r ↔
      (rs.take b.rounds.length).length = b.rounds.length ∧
        ∃ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
          foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok r := by
  simp only [foldBlocks, List.splitAt_eq]
  constructor
  · intro h
    split at h
    · exact (error_ne_ok h).elim
    · rename_i hl
      split at h
      · exact (error_ne_ok h).elim
      · rename_i s' k hs
        exact ⟨by simpa using hl, s', k, hs, h⟩
  · rintro ⟨hl, s', k, hs, h⟩
    rw [if_neg (by simpa using hl), hs]
    exact h

/-- **A fold over l₁ ++ l₂** goes well just if the fold over l₁ does, and the fold over l₂ does from
where that one ends. -/
theorem foldBlocks_append_ok {ft : Nat} (l₂ : List (Block S Cl)) :
    ∀ (l₁ : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (r : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft (l₁ ++ l₂) s rs cols = .ok r ↔
        ∃ s' rs' cols', foldBlocks ft l₁ s rs cols = .ok (s', rs', cols') ∧
          foldBlocks ft l₂ s' rs' cols' = .ok r := by
  intro l₁
  induction l₁ with
  | nil =>
    intro s rs cols r
    constructor
    · intro h
      exact ⟨s, rs, cols, rfl, h⟩
    · rintro ⟨s', rs', cols', h1, h2⟩
      have := Except.ok.inj h1
      simp only [Prod.mk.injEq] at this
      obtain ⟨a, b, c⟩ := this
      subst a b c
      exact h2
  | cons b l ih =>
    intro s rs cols r
    rw [List.cons_append, foldBlocks_cons_ok]
    constructor
    · rintro ⟨hl, s', k, hs, h⟩
      obtain ⟨t, rs', cols', h1, h2⟩ := (ih _ _ _ _).1 h
      exact ⟨t, rs', cols', foldBlocks_cons_ok.2 ⟨hl, s', k, hs, h1⟩, h2⟩
    · rintro ⟨t, rs', cols', h1, h2⟩
      obtain ⟨hl, s', k, hs, h⟩ := foldBlocks_cons_ok.1 h1
      exact ⟨hl, s', k, hs, (ih _ _ _ _).2 ⟨t, rs', cols', h, h2⟩⟩

/-! ## 4 A chain's fold -/

/-- **A chain's fold gives an end** just if the chain has a block and the fold over its blocks ends
there with no round and no column left. -/
theorem chainAt_ok {name : String} {ft : Nat} {bs : List (Block S Cl)} {s e : S} {v : Fmt.View} :
    chainAt name ft bs s v = .ok e ↔
      bs.isEmpty = false ∧ foldBlocks ft bs s v.rounds v.opened = .ok (e, [], []) := by
  unfold chainAt
  constructor
  · intro h
    split at h
    · exact (error_ne_ok h).elim
    · rename_i hb
      split at h
      · rename_i s' hf
        exact ⟨by simpa using hb, (Except.ok.inj h) ▸ hf⟩
      · exact (error_ne_ok h).elim
      · exact (error_ne_ok h).elim
  · rintro ⟨hb, hf⟩
    rw [if_neg (by simp [hb]), hf]

/-! ## 5 The decision -/

/-- **What the decision's course is made of.** -/
theorem runCore_ok {S₁ S₂ S₃ : Type} {planWord : Option String} {okStart : Bool} {s₁ : S₁}
    {s₂ : S₂} {start₃ : S₁ → S₂ → Except String S₃} {firstTree₃ : Nat} {b₁ : List (Block S₁ Cl)}
    {b₂ : List (Block S₂ Cl)} {b₃ : List (Block S₃ Cl)} {fin : S₁ → S₂ → S₃ → Bool}
    {v₁ v₂ v₃ : Fmt.View} {e₁ : S₁} {e₂ : S₂} {e₃ : S₃} :
    runCore planWord okStart s₁ s₂ start₃ firstTree₃ b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ↔
      planWord = none ∧ okStart = true ∧
        viewWordsBelowPrime v₁ = true ∧ viewWordsBelowPrime v₂ = true ∧ viewWordsBelowPrime v₃ = true ∧
        chainAt "the first chain" 0 b₁ s₁ (withEmptySealRound v₁) = .ok e₁ ∧
        chainAt "the shared chain" 0 b₂ s₂ v₂ = .ok e₂ ∧
        (∃ s₃, start₃ e₁ e₂ = .ok s₃ ∧ chainAt "the second chain" firstTree₃ b₃ s₃ v₃ = .ok e₃) ∧
        fin e₁ e₂ e₃ = true := by
  constructor
  · intro h
    unfold runCore at h
    cases planWord with
    | some w => exact (error_ne_ok h).elim
    | none =>
      obtain ⟨_, _, h⟩ := bind_eq_ok h
      obtain ⟨_, h1, h⟩ := bind_eq_ok h
      obtain ⟨_, h2, h⟩ := bind_eq_ok h
      obtain ⟨_, h3, h⟩ := bind_eq_ok h
      obtain ⟨_, h4, h⟩ := bind_eq_ok h
      obtain ⟨a, h5, h⟩ := bind_eq_ok h
      obtain ⟨b, h6, h⟩ := bind_eq_ok h
      cases hs : start₃ a b with
      | error e => rw [hs] at h; exact (error_ne_ok h).elim
      | ok s₃ =>
        rw [hs] at h
        obtain ⟨y, hy, h⟩ := bind_eq_ok h
        have hy' : s₃ = y := Except.ok.inj hy
        subst hy'
        obtain ⟨c, h8, h⟩ := bind_eq_ok h
        obtain ⟨_, h9, h⟩ := bind_eq_ok h
        have he : (a, b, c) = (e₁, e₂, e₃) := Except.ok.inj h
        simp only [Prod.mk.injEq] at he
        obtain ⟨ha, hb, hc⟩ := he
        subst ha hb hc
        exact ⟨rfl, need_eq_ok h1, need_eq_ok h2, need_eq_ok h3, need_eq_ok h4, h5, h6,
          ⟨s₃, hs, h8⟩, need_eq_ok h9⟩
  · rintro ⟨hp, ho, w1, w2, w3, c1, c2, ⟨s₃, hs, c3⟩, hf⟩
    subst hp
    unfold runCore
    rw [ho, w1, w2, w3, c1, c2]
    simp only [need, bind, Except.bind, pure, Except.pure, hs, c3, hf, if_true]

variable {Xi : Type}

/-- **What a description's yes is made of**, in its own fields. -/
theorem FileDescription.run_ok (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) :
    F.run x v₁ v₂ v₃ = true ↔
      ∃ (e₁ : F.S₁) (e₂ : F.S₂) (e₃ : F.S₃), F.planOk = true ∧ F.okStart x = true ∧
        viewWordsBelowPrime v₁ = true ∧ viewWordsBelowPrime v₂ = true ∧ viewWordsBelowPrime v₃ = true ∧
        chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v₁) = .ok e₁ ∧
        chainAt "the shared chain" 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) v₂ = .ok e₂ ∧
        (∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
          chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ v₃ = .ok e₃) ∧
        F.fin x e₁ e₂ e₃ = true := by
  have hw : F.planWord = none ↔ F.planOk = true := by
    unfold FileDescription.planWord
    cases hp : F.planOk <;> simp
  unfold FileDescription.run
  constructor
  · intro h
    cases hr : F.runEnd x v₁ v₂ v₃ with
    | error e => rw [hr] at h; exact Bool.noConfusion h
    | ok e =>
      obtain ⟨e₁, e₂, e₃⟩ := e
      obtain ⟨h0, h1⟩ := runCore_ok.1 hr
      exact ⟨e₁, e₂, e₃, hw.1 h0, h1⟩
  · rintro ⟨e₁, e₂, e₃, h0, h1⟩
    have : F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) := runCore_ok.2 ⟨hw.2 h0, h1⟩
    rw [this]
    rfl

theorem FileDescription.planOk_of_run {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) : F.planOk = true := by
  obtain ⟨_, _, _, hp, _⟩ := (F.run_ok x v₁ v₂ v₃).1 h
  exact hp

theorem FileDescription.okStart_of_run {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) : F.okStart x = true := by
  obtain ⟨_, _, _, _, ho, _⟩ := (F.run_ok x v₁ v₂ v₃).1 h
  exact ho

/-! ## 6 The tests on the plan -/

theorem blocksOk_ok {bs : List (Block S Cl)} :
    blocksOk bs = true ↔ ∀ b ∈ bs, b.planOk = true ∧ b.shaped = true := by
  unfold blocksOk
  simp only [List.all_eq_true, Bool.and_eq_true]

/-- **What the tests on the plan ask**, clause by clause. Where a clause is a test of Block.lean's
with a name of its own, it stands here as that test's yes. -/
structure FileDescription.PlanOk (F : FileDescription Xi) : Prop where
  fileOk : F.fileOk = true
  /-- every block has passed its own test on the plan and is shaped -/
  blocks₁ : ∀ b ∈ F.first.blocksInOrder, b.planOk = true ∧ b.shaped = true
  blocks₂ : ∀ b ∈ F.shared.blocksInOrder, b.planOk = true ∧ b.shaped = true
  blocks₃ : ∀ b ∈ F.second.blocksInOrder, b.planOk = true ∧ b.shaped = true
  /-- the blocks' rounds in a row are the plan's declared rounds, whole -/
  decl₁ : F.roundsDeclaredByBlocks.1 = F.plans.1
  decl₂ : F.roundsDeclaredByBlocks.2.1 = F.plans.2.1
  decl₃ : F.roundsDeclaredByBlocks.2.2 = F.plans.2.2
  /-- every stored part that is opened has the stored table's depth -/
  depth : ∀ r ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ r.stored, t.sh.a = F.tableDepth
  labels : F.labelsOk = true
  places : F.placesOk = true
  before : F.beforeOk = true
  book : F.treeSharingOk = true
  reads : F.readsOk = true
  /-- what `oracles` says of a tree where it is sent agrees with the shape at every opening of it,
  and every tree that is sent is opened somewhere -/
  opened : ([sentOf F.first.blocksInOrder, sentOf F.shared.blocksInOrder, sentOf F.second.blocksInOrder].zipIdx.all fun c =>
      let opened := openedOwn F.roundsDeclaredByBlocks c.2
      opened.all (fun o => c.1[o.1]? == some (o.2.1, o.2.2)) &&
        (List.range c.1.length).all fun n => opened.any fun o => o.1 == n) = true
  sealLast : F.sealLast = true

/-- **The tests on the plan say yes just if `PlanOk` holds.** -/
theorem FileDescription.planOk_ok (F : FileDescription Xi) : F.planOk = true ↔ F.PlanOk := by
  have hd : ((F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2).all
      (fun r => r.stored.all (·.sh.a == F.tableDepth))) = true ↔
      ∀ r ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ r.stored, t.sh.a = F.tableDepth := by
    simp only [List.all_eq_true, beq_iff_eq]
  unfold FileDescription.planOk FileDescription.planOkCore
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
      h14⟩, h15⟩
    exact ⟨h1, blocksOk_ok.1 h2, blocksOk_ok.1 h3, blocksOk_ok.1 h4, beq_iff_eq.1 h5,
      beq_iff_eq.1 h6, beq_iff_eq.1 h7, hd.1 h8, h9, h10, h11, h12, h13, h14, h15⟩
  · intro p
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨p.fileOk, blocksOk_ok.2 p.blocks₁⟩, blocksOk_ok.2 p.blocks₂⟩,
      blocksOk_ok.2 p.blocks₃⟩, beq_iff_eq.2 p.decl₁⟩, beq_iff_eq.2 p.decl₂⟩,
      beq_iff_eq.2 p.decl₃⟩, hd.2 p.depth⟩, p.labels⟩, p.places⟩, p.before⟩, p.book⟩, p.reads⟩,
      p.opened⟩, p.sealLast⟩

/-- A description's yes gives `PlanOk`. -/
theorem FileDescription.planOk_parts_of_run {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) : F.PlanOk :=
  (F.planOk_ok).1 (FileDescription.planOk_of_run h)

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.Block.step_ok
#print axioms VerifiableInference.Desc.foldBlocks_append_ok
#print axioms VerifiableInference.Desc.chainAt_ok
#print axioms VerifiableInference.Desc.runCore_ok
#print axioms VerifiableInference.Desc.FileDescription.run_ok
#print axioms VerifiableInference.Desc.FileDescription.planOk_ok
#print axioms VerifiableInference.Desc.Block.lift_decide
