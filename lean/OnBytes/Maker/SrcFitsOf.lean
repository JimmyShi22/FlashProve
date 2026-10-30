-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/SrcFitsOf.lean: the names under which the three descriptions of a file open their
trees stand for the numbers that the plain data give to these trees (`SrcFits`,
OnBytes/Maker/OneRoot.lean); so, where the program's reader has read the three chains, two openings
of one tree give one value to each vertex.

Statements and proofs. The first two chains open their own trees alone, and the data number an own
tree by its chain and its number in the chain. The third chain also opens trees that it takes over.
Its description names such a tree by the root and the run's value that were read; the data are made
from the same block's rounds at made-up names (`Three.tagChain`). The law on dry runs
(`second_rounds_alike`, OnBytes/TypedOracleCompiler/Laws/LawDry.lean) is called here at the relation `NamesGo`,
which pairs the name of the n-th tree of a chain as read with the made-up name of the n-th tree.

Main names:
  `OwnAlone R`: the rounds R open own trees alone. `OwnBook B`: the book B holds own trees alone.
  `ownAlone_of_noGiven`: from rounds that are alike to themselves where no given source is met.
  `srcFits_own`: `SrcFits` at a chain whose rounds open own trees alone.
  `NamesGo first shared N₁ N₂`: the relation. `tag_named`, `real_named`, `names_go`: a made-up name
    that stands for a tree stands for the tree whose root and run's value the other name holds.
  `srcFits_alike`: `SrcFits` at the third chain.
  `second_named`: the third chain's rounds at what was read and at made-up names go together under
    `NamesGo`.
  `srcFits_of_read`: `SrcFits` at the three chains, from `ThreeRead` (OnBytes/Maker/ThreeRead.lean).
  `one_table_of_read`: so `one_table`'s conclusion.
  `key_own`, `shared_own`: `OwnAlone` and `OwnBook` at a key's one-time chain and at a shared chain.
`srcFits_of_read` and `one_table_of_read` ask `OwnAlone` and `OwnBook` of the shared chain too;
`shared_own` gives both from the record's own dry run (so does OnBytes/Maker/OwesOfRead.lean).
Limits: at a proof's first chain `OwnAlone` and `OwnBook` are premises: its block holds the caller's
links (for the program's own blocks: OnBytes/Maker/ProofOwn.lean). That the test `Three.Whole.fits`
says yes is a premise. Nothing on opening-form binding, no two openings of a commitment, correctness
of extraction or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.OneRoot
import OnBytes.Maker.RoundsAtTags
import OnBytes.Maker.DataFitsOf
import OnBytes.Maker.ReadRuns
import OnBytes.Maker.ThreeRead

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Three (named wholeNo rdOf rdsFromL tagChain tagRoot tagRun)
open OnBytes.Params (Rounds)
open _root_.Run.PQ (bytes_beq_self)

/-! ## Own trees alone -/

/-- The rounds open own trees alone. -/
def OwnAlone (R : Rounds) : Prop := ∀ x ∈ R, ∀ o ∈ x.1.opens, ∃ n, o.2 = .own n

/-- The book holds own trees alone: it is alike to itself under every relation of given sources. -/
def OwnBook (B : TreeBook) : Prop :=
  ∀ G : ByteArray → ByteArray → ByteArray → ByteArray → Prop, BookAlike G B B

theorem lalike_diag {α : Type} {P : α → α → Prop} : ∀ {l l' : List α}, LAlike P l l' → l = l' →
    ∀ x ∈ l, P x x
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons (a := a) (b := b) p t, e, x, hx => by
    obtain ⟨e1, e2⟩ := List.cons.inj e
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [← e1] at p
      exact p
    · exact lalike_diag t e2 x hx

theorem src_own {a b : Fmt.Src} (h : SrcAlike NoGiven a b) : ∃ n, a = .own n := by
  cases h with
  | own n => exact ⟨n, rfl⟩
  | given k => exact k.elim

theorem ownAlone_of_noGiven {R : Rounds} (h : LAlike (RoundAlike NoGiven) R R) : OwnAlone R :=
  fun x hx o ho => src_own (lalike_diag (lalike_diag h rfl x hx).opens rfl o ho).2

/-- A list made by `zipWith` from l and a list that is as long, against l. -/
theorem forall₂_zipWith_right {α β γ : Type} {P : α → γ → Prop} (f : α → β → γ) :
    ∀ (l : List α) (m : List β), m.length = l.length → (∀ a ∈ l, ∀ b, P a (f a b)) →
    List.Forall₂ P l (List.zipWith f l m)
  | [], _, _, _ => by
    rw [List.zipWith_nil_left]
    exact .nil
  | _ :: _, [], e, _ => by cases e
  | a :: l, b :: m, e, h => by
    rw [List.zipWith_cons_cons]
    exact .cons (h a List.mem_cons_self b)
      (forall₂_zipWith_right f l m (Nat.succ.inj e) fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))

theorem opens_own (W : Three.Whole) (r : TailRead) (c : ℕ) : ∀ l : List (Fmt.Shape × Fmt.Src),
    (∀ o ∈ l, ∃ n, o.2 = .own n) →
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) j => SrcNames W r c s.2 j) l
      (l.filterMap fun o => (named c o.2).map (wholeNo W.t₁ W.t₂))
  | [], _ => .nil
  | o :: l, h => by
    obtain ⟨n, hn⟩ := h o List.mem_cons_self
    have e : named c o.2 = some (c, n) := by rw [hn]; rfl
    rw [List.filterMap_cons, e]
    refine .cons ?_ (opens_own W r c l fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    show SrcNames W r c o.2 _
    rw [hn]
    rfl

/-- **`SrcFits` at a chain whose rounds open own trees alone.** -/
theorem srcFits_own (W : Three.Whole) (r : TailRead) (c : ℕ) (all : List (ℕ × Fmt.Shape × ℕ × ℕ))
    (base first : ℕ) (R : Rounds) (h : OwnAlone R) :
    SrcFits W r c R (rdsFromL all W.t₁ W.t₂ c base first R) :=
  forall₂_zipWith_right _ R _ (sentBefore_length R) fun x hx _ =>
    ⟨rfl, opens_own W r c x.1.opens (h x hx)⟩

/-! ## Names that go together -/

/-- The name of the n-th tree of a chain as read, with the made-up name of the n-th tree. -/
def NamesGo (first shared : ChainRead) (N₁ N₂ : ℕ) :
    ByteArray → ByteArray → ByteArray → ByteArray → Prop :=
  fun ρ σ ρ' σ' =>
    (∃ n, treesOf first n = .given ρ σ ∧ treesOf (tagChain 1 N₁) n = .given ρ' σ') ∨
      ∃ n, treesOf shared n = .given ρ σ ∧ treesOf (tagChain 2 N₂) n = .given ρ' σ'

theorem treesOf_given (r : ChainRead) (n : ℕ) : ∃ a b, treesOf r n = .given a b := by
  unfold treesOf ChainRead.tree
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- What a name of a chain as read holds, for a number below the chain's count of roots. -/
theorem real_named (c : ChainRead) (n : ℕ) (ρ σ : ByteArray) (h : treesOf c n = .given ρ σ)
    (hn : n < c.roots.length) (hr : ∃ x, c.out.run = some x) :
    c.roots[n]? = some ρ ∧ c.out.run = some σ := by
  obtain ⟨x, hx⟩ := hr
  have e : c.roots[n]? = some c.roots[n] := List.getElem?_eq_getElem hn
  unfold treesOf ChainRead.tree at h
  rw [e, hx] at h
  have h' : Fmt.Src.given c.roots[n] x = .given ρ σ := h
  injection h' with h1 h2
  rw [e, hx, h1, h2]
  exact ⟨rfl, rfl⟩

theorem tagChain_rootsList (c : UInt8) (N : ℕ) :
    (tagChain c N).roots = (List.range N).map tagRoot := by
  unfold ChainRead.roots Three.tagChain
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold rootsT
  rw [List.filterMap_map]
  simp

theorem tagRoot_size (n : ℕ) : (tagRoot n).size = n + 1 := by
  show (Array.replicate (n + 1) (0 : UInt8)).size = n + 1
  simp

/-- What a made-up name with a root that is not empty holds. -/
theorem tag_named (c : UInt8) (N n : ℕ) (ρ' σ' : ByteArray)
    (h : treesOf (tagChain c N) n = .given ρ' σ') (hs : ρ'.size ≠ 0) :
    n < N ∧ ρ' = tagRoot n ∧ σ' = tagRun c := by
  by_cases hn : n < N
  · have hl : n < (tagChain c N).roots.length := by
      rw [tagChain_rootsList, List.length_map, List.length_range]
      exact hn
    obtain ⟨h1, h2⟩ := real_named (tagChain c N) n ρ' σ' h hl ⟨tagRun c, rfl⟩
    rw [tagChain_rootsList, List.getElem?_map, List.getElem?_range hn] at h1
    exact ⟨hn, (Option.some.inj h1).symm, (Option.some.inj h2).symm⟩
  · exfalso
    have e : (tagChain c N).roots[n]? = none := by
      rw [tagChain_rootsList]
      exact List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)
    unfold treesOf ChainRead.tree at h
    rw [e] at h
    have h' : Fmt.Src.given ByteArray.empty ByteArray.empty = .given ρ' σ' := h
    injection h' with h1 _
    rw [← h1] at hs
    exact hs rfl

/-- **A made-up name that stands for a tree stands for the tree whose root and run's value the name
that goes with it holds.** -/
theorem names_go (W : Three.Whole) (r : TailRead) (R : RunsThere r) {ρ σ ρ' σ' : ByteArray}
    (g : NamesGo r.first r.shared r.first.roots.length r.shared.roots.length ρ σ ρ' σ')
    {y : ℕ × ℕ} (hy : named 2 (.given ρ' σ') = some y) :
    TreeAt W r (wholeNo W.t₁ W.t₂ y) ρ σ := by
  have hy' : (if ρ'.size = 0 then none
    else if σ' == tagRun 1 then some (0, ρ'.size - 1)
    else if σ' == tagRun 2 then some (1, ρ'.size - 1)
    else none) = some y := hy
  by_cases hz : ρ'.size = 0
  · rw [if_pos hz] at hy'
    cases hy'
  · rw [if_neg hz] at hy'
    rcases g with ⟨n, g1, g2⟩ | ⟨n, g1, g2⟩
    · obtain ⟨hn, rfl, rfl⟩ := tag_named 1 _ n ρ' σ' g2 hz
      rw [if_pos (bytes_beq_self _), tagRoot_size] at hy'
      obtain rfl := Option.some.inj hy'
      obtain ⟨a1, a2⟩ := real_named r.first n ρ σ g1 hn R.1
      exact ⟨0, n, rfl, by omega, a1, a2⟩
    · obtain ⟨hn, rfl, rfl⟩ := tag_named 2 _ n ρ' σ' g2 hz
      rw [if_neg (by rw [beq_false_of_ne (by decide)]; exact Bool.false_ne_true),
        if_pos (bytes_beq_self _), tagRoot_size] at hy'
      obtain rfl := Option.some.inj hy'
      obtain ⟨a1, a2⟩ := real_named r.shared n ρ σ g1 hn R.2.1
      exact ⟨1, n, rfl, by omega, a1, a2⟩

/-! ## The third chain -/

theorem opens_alike (W : Three.Whole) (r : TailRead) (R : RunsThere r) :
    ∀ {l l' : List (Fmt.Shape × Fmt.Src)},
    LAlike (OpenAlike (NamesGo r.first r.shared r.first.roots.length r.shared.roots.length)) l l' →
    (∀ o ∈ l', ∃ y, named 2 o.2 = some y) →
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) j => SrcNames W r 2 s.2 j) l
      (l'.filterMap fun o => (named 2 o.2).map (wholeNo W.t₁ W.t₂))
  | _, _, .nil, _ => .nil
  | _, _, .cons (a := s) (b := s') p t, h => by
    obtain ⟨y, hy⟩ := h s' List.mem_cons_self
    rw [List.filterMap_cons, hy]
    refine .cons ?_ (opens_alike W r R t fun o ho => h o (List.mem_cons_of_mem _ ho))
    show SrcNames W r 2 s.2 (wholeNo W.t₁ W.t₂ y)
    obtain ⟨s1, s2⟩ := s
    obtain ⟨s1', s2'⟩ := s'
    have q : SrcAlike _ s2 s2' := p.2
    cases q with
    | own n =>
      obtain rfl : (2, n) = y := Option.some.inj hy
      rfl
    | given k => exact names_go W r R k hy

/-- **`SrcFits` at the third chain**: l: the rounds of the description; l': the rounds at made-up
names, from which the data are made. -/
theorem srcFits_alike (W : Three.Whole) (r : TailRead) (R : RunsThere r)
    (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (base first : ℕ) :
    ∀ {l l' : Rounds} (_ : LAlike (RoundAlike
      (NamesGo r.first r.shared r.first.roots.length r.shared.roots.length)) l l') (L : List ℕ),
    L.length = l'.length → (∀ x ∈ l', ∀ o ∈ x.1.opens, ∃ y, named 2 o.2 = some y) →
    SrcFits W r 2 l (List.zipWith (rdOf all W.t₁ W.t₂ 2 base first) l' L)
  | _, _, .nil, _, _, _ => by
    unfold SrcFits
    rw [List.zipWith_nil_left]
    exact .nil
  | _, _, .cons _ _, [], e, _ => by cases e
  | _, _, .cons (a := x) (b := x') p t, n :: L, e, h => by
    unfold SrcFits
    rw [List.zipWith_cons_cons]
    exact .cons ⟨congrArg List.length p.stored, opens_alike W r R p.opens (h x' List.mem_cons_self)⟩
      (srcFits_alike W r R all base first t L (Nat.succ.inj e)
        fun x'' hx'' => h x'' (List.mem_cons_of_mem _ hx''))

/-- **The third chain's rounds at what was read and at made-up names go together.** -/
theorem second_named (p : TailPublic) (dry : FirstEnd) (end2 : SharedEnd) (first shared : ChainRead)
    (N₂ : ℕ) (b₁ : OwnBook dry.book) (b₂ : OwnBook end2.book) :
    OptAlike (LAlike (RoundAlike (NamesGo first shared first.roots.length N₂)))
      ((secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first))
      ((secondBlock p.lin dry.lin (end2.goesOn (tagChain 2 N₂))).rounds
        (secondStart p dry (tagChain 1 first.roots.length))) :=
  second_rounds_alike p ⟨rfl, b₁ _, ⟨rfl, rfl, rfl, rfl⟩⟩ ⟨rfl, b₂ _, rfl⟩ first _ shared _
    (fun n => by
      obtain ⟨a, b, e⟩ := treesOf_given first n
      obtain ⟨a', b', e'⟩ := treesOf_given (tagChain 1 first.roots.length) n
      rw [e, e']
      exact .given (Or.inl ⟨n, e, e'⟩))
    (fun n => by
      obtain ⟨a, b, e⟩ := treesOf_given shared n
      obtain ⟨a', b', e'⟩ := treesOf_given (tagChain 2 N₂) n
      rw [e, e']
      exact .given (Or.inr ⟨n, e, e'⟩))
    (tagChain_roots 1 _).symm

/-! ## From the record of the three chains' reading -/

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **`SrcFits` at the three chains, and the two counts of roots.** -/
theorem srcFits_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (o₂ : OwnAlone R₂) (b₁ : OwnBook dry.book) (b₂ : OwnBook dry2.book)
    (R₃ : Rounds) (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) :
    SrcFits (Three.Whole.of R₁ R₂ R₃) r 0 (S₁.base.rounds.zip S₁.stored)
        (Three.Whole.of R₁ R₂ R₃).ds₁ ∧
      SrcFits (Three.Whole.of R₁ R₂ R₃) r 1 (S₂.base.rounds.zip S₂.stored)
        (Three.Whole.of R₁ R₂ R₃).ds₂ ∧
      SrcFits (Three.Whole.of R₁ R₂ R₃) r 2 (S₃.base.rounds.zip S₃.stored)
        (Three.Whole.of R₁ R₂ R₃).ds₃ ∧
      (Three.Whole.of R₁ R₂ R₃).t₁ = r.first.roots.length ∧
      (Three.Whole.of R₁ R₂ R₃).t₂ = r.shared.roots.length := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (secondFirstTree r.first) = some S₃ :=
    T.second_spec
  have c₁ : r.first.roots.length = Three.rootsIn R₁ :=
    readChain_roots hS₁ [] file i r.first T.first_read
  have c₂ : r.shared.roots.length = Three.rootsIn R₂ :=
    readChain_roots hS₂ r.first.out.seen file r.place.next r.shared T.shared_read
  have RT : RunsThere r :=
    runsThere_of S₁ S₂ S₃ r file [] r.first.out.seen r.shared.out.seen i r.place.next
      r.shared.next r.first.next r.shared.next r.second.next T.first_read T.shared_read
      T.second_read (by rw [describeWith_rand hS₁]; exact hn) (shared_rand T.shared_spec)
      (second_rand T.second_spec)
  have hx : (secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 r.shared.roots.length))).rounds
      (secondStart p dry (tagChain 1 r.first.roots.length)) = some R₃ := by
    unfold Three.dry3 at hd
    rw [T.shared_dry] at hd
    rw [c₁, c₂]
    cases hX : (secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (Three.rootsIn R₂)))).rounds
        (secondStart p dry (tagChain 1 (Three.rootsIn R₁))) with
    | none =>
      have hd' : (((secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (Three.rootsIn R₂)))).rounds
        (secondStart p dry (tagChain 1 (Three.rootsIn R₁)))).bind fun R₃ =>
          some (R₁, R₂, R₃)) = some (R₁, R₂, R₃) := hd
      rw [hX] at hd'
      cases hd'
    | some Y =>
      have hd' : (((secondBlock p.lin dry.lin (dry2.goesOn (tagChain 2 (Three.rootsIn R₂)))).rounds
        (secondStart p dry (tagChain 1 (Three.rootsIn R₁)))).bind fun R₃ =>
          some (R₁, R₂, R₃)) = some (R₁, R₂, R₃) := hd
      rw [hX] at hd'
      have e : (R₁, R₂, Y) = (R₁, R₂, R₃) := Option.some.inj hd'
      rw [(Prod.mk.inj (Prod.mk.inj e).2).2]
  have A := second_named p dry dry2 r.first r.shared r.shared.roots.length b₁ b₂
  rw [T.second_rounds, hx] at A
  refine ⟨?_, ?_, ?_, c₁.symm, c₂.symm⟩
  · rw [described_zip hS₁]
    exact srcFits_own _ r 0 _ _ _ R₁ o₁
  · rw [described_zip hS₂]
    exact srcFits_own _ r 1 _ _ _ R₂ o₂
  · rw [described_zip hS₃]
    cases A with
    | some q =>
      exact srcFits_alike _ r RT _ _ _ q _ (sentBefore_length R₃) (fits_named hf (2, R₃) (by simp))

/-- **One table of vertices a tree, from the record of the three chains' reading.** -/
theorem one_table_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none)
    (o₁ : OwnAlone R₁) (o₂ : OwnAlone R₂) (b₁ : OwnBook dry.book) (b₂ : OwnBook dry2.book)
    (R₃ : Rounds) (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (m : ℕ)
    (hf : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ z ∈ ownRowsW (Three.Whole.of R₁ R₂ R₃) r, ∀ z' ∈ ownRowsW (Three.Whole.of R₁ R₂ R₃) r,
      z.1 = z'.1 → z.2.2.2.root = z'.2.2.2.root ∧ ∀ (d q : ℕ) (a a' : ByteArray),
        (d ≠ 0 ∨ q = 0) → _root_.Run.seenAt z.2.2.2.seen d q = some a →
        _root_.Run.seenAt z'.2.2.2.seen d q = some a' → a = a' := by
  obtain ⟨F₁, F₂, F₃, h₁, h₂⟩ := srcFits_of_read T hS₁ hn o₁ o₂ b₁ b₂ R₃ hd m hf
  intro z hz z' hz' e
  have O := own_treeAt _ S₁ S₂ S₃ r file _ _ _ _ _ _ _ _ _ T.first_read T.shared_read T.second_read
    F₁ F₂ F₃
  exact ⟨one_root h₁ h₂ (O z hz) (O z' hz') e,
    one_table _ S₁ S₂ S₃ r file _ _ _ _ _ _ T.first_read T.shared_read T.second_read F₁ F₂ F₃ h₁ h₂
      z hz z' hz' e⟩

end

/-! ## Where the premises are paid -/

/-- A key's one-time chain. -/
theorem key_own (p : Params.OneTime) {R : Rounds} {e : FirstEnd}
    (h : (Key.oneTime p).dryRun (Key.startOf p) = some (R, e)) : OwnAlone R ∧ OwnBook e.book := by
  have k := (carries_oneTime (G := NoGiven) (d := true) p).dryRun (startOf_alike p)
  rw [h] at k
  cases k with
  | some q => exact ⟨ownAlone_of_noGiven q.1, fun _ => q.2.book.of_noGiven⟩

/-- A shared chain. -/
theorem shared_own (p : TailPublic) (key : TableKey) {R : Rounds} {e : SharedEnd}
    (h : (sharedBlock p.lin key).dryRun (sharedStart p) = some (R, e)) :
    OwnAlone R ∧ OwnBook e.book := by
  have s2 : StartAlike NoGiven (sharedStart p) (sharedStart p) :=
    ⟨rfl, rfl, rfl, rfl, ⟨ArrAlike.empty _, rfl⟩⟩
  have k := (carries_sharedBlock (G := NoGiven) (d := true) p.lin key).dryRun s2
  rw [h] at k
  cases k with
  | some q => exact ⟨ownAlone_of_noGiven q.1, fun _ => q.2.book.of_noGiven⟩

end OnBytes.Maker
