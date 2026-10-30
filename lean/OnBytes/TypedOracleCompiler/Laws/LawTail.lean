-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawTail.lean: law 2 ("blind") for what a key file and a proof file have in common
after their first chain (OnBytes/Proof/Tail.lean): `firstEnd`, `sharedBlock`, `secondBlock`, and the
decision `tailRefusal`; with the routines of OnBytes/Iop/Lin.lean that name the book of trees or a
source. Each law on a block holds for every G and d, so it is also the half of law 1 in which the
two texts differ in books alone. `judge_alike`, `treesOf_any` and `tailRefusal_blind` stand at fixed
G or d.

Main names.
  `linAlone_alike`       `linAloneInItsTree` reads a tree's parts alone
  `same_linSharedVerify` one text, equal values (it reads the book once, through
                         `linAloneInItsTree`)
  `carries_linAdopt`     two books that are alike: of a tree's source the constructor alone is
                         tested
  `carries_linSecondVerify`, `carries_secondBlock`, `carries_firstEnd`, `carries_sharedBlock`
  `FirstEndAlike G`, `SharedEndAlike G`   what the blocks return: equal but for the book's given
                         sources
  `BookAlike.goesOn`     the book as a later chain holds it
  `tailRefusal_blind`    the decision on a tail does not hang on: the digests drawn in the two
                         views; the roots and run values of the first and of the shared chain; given
                         sources in what the first chain's block has returned. It does hang on the
                         table's key and on the number of roots of the first chain (two hypotheses
                         here).

Not claimed. Nothing on `readTail`. Nothing on the first chain's block but its closing.

-/
import OnBytes.TypedOracleCompiler.Laws.LawIop
import OnBytes.TypedOracleCompiler.Laws.LawRun
import OnBytes.Proof.Tail

namespace OnBytes.TwoLaws

open OnBytes OnBytes.Proof

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

/-- Whether an oracle message has a tree to itself is read off places and parts. -/
theorem linAlone_alike {B B' : TreeBook} (hB : BookAlike G B B') (o : Nat) :
    linAloneInItsTree B o = linAloneInItsTree B' o := by
  unfold linAloneInItsTree
  rw [hB.place]
  cases B'.place[o]? with
  | none => rfl
  | some p =>
    have h := hB.trees p.1
    simp only [Option.bind_some]
    generalize B.trees[p.1]? = x at h ⊢
    generalize B'.trees[p.1]? = y at h ⊢
    cases h with
    | none => rfl
    | some k => simp only [k.parts]

/-- A text that takes the book and goes on alike from books that are alike. -/
theorem same_of_theBook {β : Type} {f : TreeBook → Blk β}
    (hf : ∀ B B', BookAlike G B B' → Carries (Alike G d) Eq (f B) (f B')) :
    Same (Alike G d) (Blk.theBook >>= f) :=
  ⟨Carries.bind carries_theBook hf⟩

/-- The tactic walk, and before a bind: the book is taken and read through linAloneInItsTree. -/
macro "walkB" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | (with_reducible refine same_of_close _ _ _ (fun _ _ _ _ _ => ?_); try dsimp only
         refine Carries.of_same ?_)
      | (with_reducible refine same_of_theBook (fun _ _ hB => ?_); simp only [linAlone_alike hB]
         refine Carries.of_same ?_)
      | with_reducible apply Same.bind
      | split
      | dsimp only)

instance same_linSharedVerify (S : Params.LinShape) (key : TableKey) :
    Same (Alike G d) (linSharedVerify S key) := by
  unfold linSharedVerify; walkB

theorem carries_linAdopt (st : Statement) {B B' : TreeBook} (hB : BookAlike G B B')
    (theirs lc : Nat) :
    Carries (Alike G d) Eq (linAdopt st B theirs lc) (linAdopt st B' theirs lc) := by
  unfold linAdopt
  rw [linAlone_alike hB, hB.place]
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun place => ?_
  refine Carries.bind (carries_get (hB.trees place.1) _) fun t t' ht => ?_
  obtain ⟨sh, nu, sr, pa, ol, li⟩ := t
  obtain ⟨sh', nu', sr', pa', ol', li'⟩ := t'
  obtain ⟨e1, e2, hs, e4, e5, e6⟩ := ht
  dsimp only at e1 e2 hs e4 e5 e6
  subst e1 e2 e4 e5 e6
  have hg : ArrAlike (fun x y : Nat × Fmt.Src => x.1 = y.1 ∧ SrcAlike G x.2 y.2) #[(nu, sr)]
      #[(nu, sr')] := (ArrAlike.empty _).push ⟨rfl, hs⟩
  cases hs <;>
  · dsimp only
    refine Carries.bind_same fun _ => ?_
    refine Carries.bind_same fun x => ?_
    refine Carries.bind (carries_adoptOracles _ hg) fun ids _ e => ?_
    subst e
    exact Carries.of_same (by walk)

theorem carries_linSecondVerify (S : Params.LinShape) (first : LinFirst) (st : Statement)
    {B B' : TreeBook} (hB : BookAlike G B B') (shared : LinShared) :
    Carries (Alike G d) Eq (linSecondVerify S first st B shared)
      (linSecondVerify S first st B' shared) := by
  unfold linSecondVerify
  refine Carries.bind (carries_linAdopt st hB _ _) fun o _ e => ?_
  subst e
  exact Carries.of_same (by walk)

/-- What a first chain's block returns: equal but for the book's given sources. -/
structure FirstEndAlike (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop)
    (a b : FirstEnd) : Prop where
  st : a.st = b.st
  book : BookAlike G a.book b.book
  lin : a.lin = b.lin

/-- What a shared chain's block returns: equal but for the book's given sources. -/
structure SharedEndAlike (G : ByteArray → ByteArray → ByteArray → ByteArray → Prop)
    (a b : SharedEnd) : Prop where
  st : a.st = b.st
  book : BookAlike G a.book b.book
  lin : a.lin = b.lin

theorem carries_firstEnd (lin : LinFirst) :
    Carries (Alike G d) (FirstEndAlike G) (firstEnd lin) (firstEnd lin) := by
  unfold firstEnd
  refine Carries.bind (carries_close _ _ _) fun _ _ _ => ?_
  refine Carries.bind carries_handOver fun h h' hh => ?_
  exact Carries.pure ⟨hh.1, hh.2, rfl⟩

theorem carries_sharedBlock (S : Params.LinShape) (key : TableKey) :
    Carries (Alike G d) (SharedEndAlike G) (sharedBlock S key) (sharedBlock S key) := by
  unfold sharedBlock
  refine Carries.bind_same fun x => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind (carries_close _ _ _) fun _ _ _ => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind carries_handOver fun h h' hh => ?_
  exact Carries.pure ⟨hh.1, hh.2, rfl⟩

theorem carries_secondBlock (S : Params.LinShape) (first : LinFirst) {e e' : SharedEnd}
    (he : SharedEndAlike G e e') :
    Carries (Alike G d) Eq (secondBlock S first e) (secondBlock S first e') := by
  unfold secondBlock
  rw [he.st, he.lin]
  refine Carries.bind (carries_linSecondVerify S first _ he.book _) fun x _ h => ?_
  subst h
  exact Carries.of_same (by walk)

/-- The book as a later chain holds it: own trees get sources that go together. -/
theorem BookAlike.goesOn {B B' : TreeBook} (hB : BookAlike G B B') {src src' : Nat → Fmt.Src}
    (hs : ∀ n, SrcAlike G (src n) (src' n)) : BookAlike G (B.goesOn src) (B'.goesOn src') := by
  refine ⟨fun i => ?_, hB.place⟩
  unfold TreeBook.goesOn
  dsimp only
  rw [Array.getElem?_map, Array.getElem?_map]
  refine (hB.trees i).map fun a b h => ?_
  obtain ⟨sh, nu, sr, pa, ol, li⟩ := a
  obtain ⟨sh', nu', sr', pa', ol', li'⟩ := b
  obtain ⟨e1, e2, hsr, e4, e5, e6⟩ := h
  dsimp only at e1 e2 hsr e4 e5 e6
  subst e1 e2 e4 e5 e6
  cases hsr with
  | own n => exact ⟨rfl, rfl, hs n, rfl, rfl, rfl⟩
  | given k => exact ⟨rfl, rfl, .given k, rfl, rfl, rfl⟩

/-- How a later chain names an earlier chain's trees: always as given. -/
theorem treesOf_any (r r' : ChainRead) (n : Nat) : SrcAlike AnyGiven (treesOf r n) (treesOf r' n) := by
  have h : ∀ r : ChainRead, ∃ a b, treesOf r n = .given a b := by
    intro r
    unfold treesOf ChainRead.tree
    split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  obtain ⟨a, b, e⟩ := h r
  obtain ⟨a', b', e'⟩ := h r'
  rw [e, e']
  exact .given trivial

theorem judge_alike {α : Type} {Q : α → α → Prop} {b b' : Blk α}
    (h : Carries (Alike G false) Q b b') {s s' : Start} (hs : StartAlike G s s')
    {v v' : Fmt.View} (hv : ViewAlike v v') (front : String) :
    (∃ why, judge front b s v = .error why ∧ judge front b' s' v' = .error why) ∨
      ∃ x y, judge front b s v = .ok x ∧ judge front b' s' v' = .ok y ∧ Q x y := by
  have k := h.runOn hs hv
  unfold judge
  generalize b.runOn s v = x at k
  generalize b'.runOn s' v' = y at k
  cases k with
  | ok q => exact Or.inr ⟨_, _, rfl, rfl, q⟩
  | error e => exact Or.inl ⟨_, rfl, rfl⟩

/-- Law 2 at the tail's decision. -/
theorem tailRefusal_blind (p : TailPublic) {real real' : FirstEnd}
    (hr : FirstEndAlike AnyGiven real real') (r r' : TailRead) (hk : r.key = r'.key)
    (h2 : ViewAlike r.shared.view r'.shared.view) (h3 : ViewAlike r.second.view r'.second.view)
    (hn : r.first.roots.length = r'.first.roots.length) :
    tailRefusal p real r = tailRefusal p real' r' := by
  unfold tailRefusal
  rw [← hk]
  have s2 : StartAlike AnyGiven (sharedStart p) (sharedStart p) :=
    ⟨rfl, rfl, rfl, rfl, ⟨ArrAlike.empty _, rfl⟩⟩
  rcases judge_alike (carries_sharedBlock p.lin r.key) s2 h2 "shared-chain-" with
    ⟨why, e1, e2⟩ | ⟨x, y, e1, e2, q⟩
  · rw [e1, e2]
  · rw [e1, e2]
    dsimp only
    have q' : SharedEndAlike AnyGiven (x.goesOn r.shared) (y.goesOn r'.shared) :=
      ⟨q.st, q.book.goesOn (treesOf_any _ _), q.lin⟩
    have s3 : StartAlike AnyGiven (secondStart p real r.first) (secondStart p real' r'.first) :=
      ⟨rfl, rfl, by unfold secondStart secondFirstTree; rw [hn], hr.st,
        hr.book.goesOn (treesOf_any _ _)⟩
    rw [← hr.lin]
    rcases judge_alike (carries_secondBlock p.lin real.lin q') s3 h3 "second-chain-" with
      ⟨why, e1, e2⟩ | ⟨x, y, e1, e2, q⟩
    · rw [e1, e2]

    · rw [e1, e2]

#print axioms tailRefusal_blind

end OnBytes.TwoLaws
