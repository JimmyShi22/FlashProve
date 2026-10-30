-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenedStep.lean: what a `Before` holds for the reads of
declared rounds (`HeldAt`, Honest/Law/Rule/OpenedAt.lean), from one sub-protocol of a chain to the
next: the declared rounds grow by the sub-protocol's own, and the columns by those that it has read.

  1  `preOf_at`   `preOf` (Honest/Rule.lean) at a sub-protocol of a list, written out
  2  `Before.colAt_eq`, `Before.opened_eq`   `Before.opened` (Honest/Side.lean) is `colsOff`
     (Honest/Law/Rule/Session.lean); `colsOff_append`
  3  `readsBefore_grow`, `Before.drawnOf_own`, `pairs_drawn`   small lemmas
     `HeldAt.grow`   **the law**, general in the `Before`
  4  `TieAt`, `TieAt.member`, `TieAt.next`   what the lemmas on a chain carry between two
     sub-protocols; what it gives at the sub-protocol's parts; it is preserved
  5  `FaithOwn`   a definition: `FaithAll` (Honest/Law/Rule/ChainModel.lean) at what a simulator of
     the chain itself is given
     `lays_opened`   the rounds of a sub-protocol leave the field

Limits.
  * `FaithOwn` is a hypothesis. It is paid in Honest/Law/Rule/FaithOwnFile.lean (`faithOwn_of`), not
    here. `FaithAll` speaks of `Laid.front 2`, whatever the chain; `Good.exact` and `partShows` are
    applied at the chain's own `Laid.front ch` (`Act.shows`, `Act.tells`,
    Honest/Law/Rule/Real.lean). For the second chain the two are one term.
  * Nothing here says that `TieAt` holds at a chain's start: Honest/Law/Rule/OpenedStart.lean,
    Honest/Law/Rule/OpenedFile.lean.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.Bare
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl W Y : Type}

/-! ## 1 `preOf`, written out -/

/-- `hp`: no sub-protocol before `b` is at its place. -/
theorem preOf_at (ch ft : Nat) (earlier : List (Nat × Nat × List Fmt.DeclaredRound))
    (passed : List (Block S Cl)) (b : Block S Cl) (rest : List (Block S Cl))
    (hp : ∀ p ∈ passed, p.place ≠ b.place) :
    preOf ch ft earlier (passed ++ b :: rest) b.place =
      earlier ++ [(ch, ft, passed.flatMap (·.rounds))] := by
  have htw : (passed ++ b :: rest).takeWhile (fun p => p.place != b.place) = passed := by
    rw [List.takeWhile_append_of_pos (fun p hpm => by simpa using hp p hpm)]
    simp
  unfold preOf
  rw [htw]

/-! ## 2 `Before.opened` is `colsOff` -/

theorem Before.colAt_eq (f : Before) (q : Read) :
    f.colAt q = (f.wordsAt q).map fun w => ((q.key, q.pos, w) : OpenedColumn) := by
  unfold Before.colAt Before.wordsAt
  cases hi : q.item with
  | some i =>
    show ((f.stored.find? fun c => c.1 == i && c.2.1 == q.pos).map fun c =>
        ((q.key, q.pos, c.2.2) : OpenedColumn)) =
      ((f.stored.find? fun c => c.1 == i && c.2.1 == q.pos).map (·.2.2)).map fun w =>
        ((q.key, q.pos, w) : OpenedColumn)
    cases (f.stored.find? fun c => c.1 == i && c.2.1 == q.pos) <;> rfl
  | none =>
    cases hs : q.src with
    | none => rfl
    | some p =>
      obtain ⟨ch, n⟩ := p
      show ((f.treeCols ch n).bind fun cols =>
          (cols.find? fun c => c.1 == q.pos).map fun c => ((q.key, q.pos, c.2) : OpenedColumn)) =
        ((f.treeCols ch n).bind fun cols => (cols.find? fun c => c.1 == q.pos).map (·.2)).map
          fun w => ((q.key, q.pos, w) : OpenedColumn)
      cases f.treeCols ch n with
      | none => rfl
      | some cols =>
        show ((cols.find? fun c => c.1 == q.pos).map fun c => ((q.key, q.pos, c.2) : OpenedColumn)) =
          ((cols.find? fun c => c.1 == q.pos).map (·.2)).map fun w => ((q.key, q.pos, w) : OpenedColumn)
        cases (cols.find? fun c => c.1 == q.pos) <;> rfl

theorem Before.opened_eq (f : Before) : ∀ qs : List Read, f.opened qs = colsOff f qs
  | [] => by
    unfold Before.opened
    rw [List.mapM_nil]
    rfl
  | q :: qs => by
    have ih := Before.opened_eq f qs
    unfold Before.opened at ih ⊢
    rw [List.mapM_cons, ih, f.colAt_eq q]
    show _ = (f.wordsAt q).bind fun w => (colsOff f qs).map fun l => (q.key, q.pos, w) :: l
    cases f.wordsAt q with
    | none => rfl
    | some w => cases colsOff f qs <;> rfl

/-- `colsOff` over two lists of reads, one behind the other. -/
theorem colsOff_append (f : Before) : ∀ a b : List Read,
    colsOff f (a ++ b) = (colsOff f a).bind fun x => (colsOff f b).map fun y => x ++ y
  | [], b => by
    show colsOff f b = (colsOff f b).map fun y => [] ++ y
    cases colsOff f b <;> rfl
  | q :: a, b => by
    show ((f.wordsAt q).bind fun w =>
        (colsOff f (a ++ b)).map fun l => ((q.key, q.pos, w) : OpenedColumn) :: l) =
      ((f.wordsAt q).bind fun w => (colsOff f a).map fun l => ((q.key, q.pos, w) : OpenedColumn) :: l).bind
        fun x => (colsOff f b).map fun y => x ++ y
    rw [colsOff_append f a b]
    cases f.wordsAt q with
    | none => rfl
    | some w =>
      cases colsOff f a with
      | none => rfl
      | some x => cases colsOff f b <;> rfl

/-! ## 3 The declared rounds grow -/

/-- `A`, `B`: the chain's challenges in `f`, cut behind those of `done`. -/
theorem readsBefore_grow (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (ch ft : Nat)
    (done new : List Fmt.DeclaredRound) (f : Before) (A B : List Fmt.Drawn)
    (hd : f.drawnOf ch = A ++ B) (hl : done.length = A.length) :
    readsBefore (earlier ++ [(ch, ft, done ++ new)]) f =
      readsBefore (earlier ++ [(ch, ft, done)]) f ++
        readsOf ch ft (fun _ _ => none) (fun _ => none) new B := by
  unfold readsBefore
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  rw [hd, readsOf_append ch ft _ _ done new A B hl, readsOf_cap ch ft _ _ done (A ++ B), hl,
    List.take_left]

/-- Rounds that carry the chain's number, laid behind: their challenges are laid behind the chain's.
-/
theorem Before.drawnOf_own (f : Before) (ch : Nat) (a : List (Shown × Fmt.Drawn)) :
    (f.more (a.map fun z => (ch, z.1, z.2))).drawnOf ch = f.drawnOf ch ++ a.map (·.2) := by
  have e : ((a.map fun z => ((ch, z.1, z.2) : Nat × Shown × Fmt.Drawn)).filter
      fun r => r.1 == ch) = a.map fun z => (ch, z.1, z.2) := by
    refine List.filter_eq_self.2 fun r hr => ?_
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hr
    exact beq_self_eq_true ch
  unfold Before.drawnOf Before.more
  show (((f.rounds ++ a.map fun z => ((ch, z.1, z.2) : Nat × Shown × Fmt.Drawn)).filter
    fun r => r.1 == ch).map (·.2.2)) = _
  rw [List.filter_append, List.map_append, e, List.map_map]
  rfl

theorem pairs_drawn (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    (pairsBy tree l n).map (·.2) = l.map (·.drawn)
  | [], _ => rfl
  | p :: l, n => congrArg (p.drawn :: ·) (pairs_drawn tree l (n + p.tables.length))

/-- **From one sub-protocol to the next.** `f`: what has been produced before the sub-protocol. `l`:
its rounds. `own`: its challenges. `new`: its declared rounds. `hE`, `hO`: `f` holds a challenge for
each declared round of the earlier chains, and just as many of the chain itself as `done` has
rounds. `hc`: the longer `Before` holds `cols` for the reads of the sub-protocol's own rounds. -/
theorem HeldAt.grow {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {ch ft : Nat}
    {done new : List Fmt.DeclaredRound} {f : Before} {cs cols : List OpenedColumn}
    (l : List (Nat × Shown × Fmt.Drawn)) (own : List Fmt.Drawn)
    (hE : ∀ x ∈ earlier, x.2.2.length ≤ (f.drawnOf x.1).length)
    (hO : (f.drawnOf ch).length = done.length)
    (hd : (f.more l).drawnOf ch = f.drawnOf ch ++ own)
    (hc : colsOff (f.more l) (readsOf ch ft (fun _ _ => none) (fun _ => none) new own) = some cols)
    (h : HeldAt (earlier ++ [(ch, ft, done)]) f cs) :
    HeldAt (earlier ++ [(ch, ft, done ++ new)]) (f.more l) (cs ++ cols) := by
  have h1 : ∀ x ∈ earlier ++ [(ch, ft, done)], x.2.2.length ≤ (f.drawnOf x.1).length := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hE x hx
    · obtain rfl := List.mem_singleton.1 hx
      exact Nat.le_of_eq hO.symm
  have hT := h.more l h1
  unfold HeldAt at hT ⊢
  rw [Before.opened_eq] at hT ⊢
  rw [readsBefore_grow earlier ch ft done new (f.more l) (f.drawnOf ch) own hd hO.symm,
    colsOff_append, hT, hc]
  rfl

/-! ## 4 Between two sub-protocols -/

/-- **What the lemmas on a chain carry between two sub-protocols.** `done`: the declared rounds of
the chain's sub-protocols so far. `mid`: the state of the prover's run, or `none` after a rejection.
`f`: what a simulator of the chain is given of what has been produced. A definition, meant as a
hypothesis. -/
structure TieAt (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (ch ft : Nat)
    (done : List Fmt.DeclaredRound) (mid : Option (Mid W Y)) (f : Before) : Prop where
  /-- the state's field is `some` of the columns that `f` holds for the reads so far -/
  held : ∀ m, mid = some m →
    ∃ cs : List OpenedColumn, m.opened = some cs ∧ HeldAt (earlier ++ [(ch, ft, done)]) f cs
  /-- `f` holds a challenge for each declared round of the earlier chains -/
  early : ∀ x ∈ earlier, x.2.2.length ≤ (f.drawnOf x.1).length
  /-- and just as many of the chain itself as `done` has rounds -/
  level : (f.drawnOf ch).length = done.length

/-- What `member_lay` (Honest/Law/Rule/MemberLay.lean) and `RowInv` (Honest/Law/Rule/RowHere.lean)
ask. -/
theorem TieAt.member {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {ch ft : Nat}
    {done : List Fmt.DeclaredRound} {mid : Option (Mid W Y)} {f : Before}
    (h : TieAt earlier ch ft done mid f) :
    ∀ m, mid = some m → ∃ cs : List OpenedColumn, m.opened = some cs ∧
      HeldAt (earlier ++ [(ch, ft, done)]) f cs ∧
      ∀ x ∈ earlier ++ [(ch, ft, done)], x.2.2.length ≤ (f.drawnOf x.1).length := by
  intro m hm
  obtain ⟨cs, hW, hF⟩ := h.held m hm
  refine ⟨cs, hW, hF, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact h.early x hx
  · obtain rfl := List.mem_singleton.1 hx
    exact Nat.le_of_eq h.level.symm

/-- **Over one sub-protocol.** `a`: what its rounds show, each with its challenge. `mid'`: the state
after it: where there is one, its field is the earlier state's with `cols` behind. `hc`: as in
`HeldAt.grow`. `hlen`: as many rounds shown as declared. -/
theorem TieAt.next {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {ch ft : Nat}
    {done : List Fmt.DeclaredRound} {mid : Option (Mid W Y)} {f : Before}
    (h : TieAt earlier ch ft done mid f) (new : List Fmt.DeclaredRound)
    (a : List (Shown × Fmt.Drawn)) (cols : List OpenedColumn) (mid' : Option (Mid W Y))
    (hlen : a.length = new.length)
    (hmid : ∀ m₁, mid' = some m₁ → ∃ m, mid = some m ∧ m₁.opened = m.opened.map (· ++ cols))
    (hc : colsOff (f.more (a.map fun z => (ch, z.1, z.2)))
      (readsOf ch ft (fun _ _ => none) (fun _ => none) new (a.map (·.2))) = some cols) :
    TieAt earlier ch ft (done ++ new) mid' (f.more (a.map fun z => (ch, z.1, z.2))) where
  held := by
    intro m₁ h₁
    obtain ⟨m, hm, ho⟩ := hmid m₁ h₁
    obtain ⟨cs, hW, hF⟩ := h.held m hm
    refine ⟨cs ++ cols, ?_, hF.grow _ _ h.early h.level (f.drawnOf_own ch a) hc⟩
    rw [ho, hW]
    rfl
  early := fun x hx => Nat.le_trans (h.early x hx) (f.drawnOf_more _ x.1).length_le
  level := by
    rw [f.drawnOf_own ch a, List.length_append, h.level, List.length_append, List.length_map, hlen]

/-! ## 5 The hypothesis on the columns, and the field over a sub-protocol's rounds -/

/-- **Each read's words are found in what a simulator of the chain itself is given**, sub-protocol
by sub-protocol, whatever rounds l the chain has produced: the text of `FaithAll`
(Honest/Law/Rule/ChainModel.lean) with `Laid.front ch` for `Laid.front 2`. A definition, meant as a
hypothesis. -/
def FaithOwn (ch ft : Nat) (st : List (Nat × Nat × List UInt64)) (tree : Nat → List Nat) (L : Lay)
    (Z₀ : Laid) : List (Block S Cl) → List Fmt.Drawn → Prop
  | [], _ => True
  | b :: bs, ds =>
    (∀ l : List Played,
      ∀ q ∈ readsOf ch ft L.stored (L.tree l) b.rounds (ds.take b.rounds.length), ∀ w,
        q.words = some w →
        ((Z₀.add ch (pairsBy tree l 0)).front ch st).wordsAt q.bare = some w) ∧
      FaithOwn ch ft st tree L Z₀ bs (ds.drop b.rounds.length)

/-- The rounds of a sub-protocol that was played leave the field as it was. `hp`: as in `lays_live`
(Honest/Law/Rule/WalkLaw.lean). -/
theorem lays_opened {l : List (Step W Y)} {ds : List Fmt.Drawn} {m : Mid W Y}
    {y : List Played × Option (Mid W Y)}
    (hp : ∀ s ∈ l, s.move.isSome = false → s.addr.part = 0) (h : lays l ds (some m) = .ok y) :
    ∃ m', y.2 = some m' ∧ m'.opened = m.opened := by
  obtain ⟨m', e, hpl⟩ := lays_live l ds m y hp h
  exact ⟨m', e, play_opened _ _ _ _ _ hpl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.preOf_at
#print axioms ProofFile.Honest.Before.colAt_eq
#print axioms ProofFile.Honest.Before.opened_eq
#print axioms ProofFile.Honest.colsOff_append
#print axioms ProofFile.Honest.readsBefore_grow
#print axioms ProofFile.Honest.Before.drawnOf_own
#print axioms ProofFile.Honest.pairs_drawn
#print axioms ProofFile.Honest.HeldAt.grow
#print axioms ProofFile.Honest.TieAt
#print axioms ProofFile.Honest.TieAt.member
#print axioms ProofFile.Honest.TieAt.next
#print axioms ProofFile.Honest.FaithOwn
#print axioms ProofFile.Honest.lays_opened
