-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WNarrow.lean: what the test frontFiveB reads of the shape on
entry to a proximity test. Two shapes that agree on what is read give the same answer.

  strip, stripT, openedAt, sharesAt   a message without its ledger and its list of groups; a tree
                   without where its root comes from and the two numbers on its opening; the guards
                   on its openings and on its parts' groups
  SameRead A c d   two shapes agree at the messages numbered in A: their codes, their counts of messages
                   and places, each such message, its place, its tree, that guard, and the roots
  SameCore A g g' c d   the same, and group g of c is group g' of d: so a shape can hold one group
  frontFive_same   the statement
  tsLen_same, manyFitsB_book, manyFits_same   the two further public tests on the shape, the same way

What it is for. c is the shape of a run, d one closed shape: the test can then be evaluated at d. The
statement has the test's pass at nothing, a mask that has come, and p.early as a premise.

Limits.
- Nothing is said here of any run.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.ManyFits
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (Clauses on has ok)
open ProofFile.Honest.K12.Thin (frontPubB)
open ProofFile.Honest.K12.Light (manyFitsS manyFitsB treeFitsB tsLenOf MemShape Piece)
open ProofFile.Honest.Sh (ThinSh batThin PlainS gpOfS gpLS TestSh thinOf seatOfS frontLS commonB cameB
  batOwesB frontOwesB gpOkS labelsOkS gpAllS labelsLS keyAtS logAtS widthAtS numAtS maskThin
  readPubB)

/-- A message without its ledger and its list of groups. -/
def strip (x : OrcSh) : OrcSh := { x with ledger := none, groups := [] }

/-- A tree without where its root comes from and without the two numbers on its opening. -/
def stripT (T : TreeSh) : TreeSh := { T with src := .given, oneList := false, lists := 0 }

/-- The guard on a tree's openings. -/
def openedAt (T : TreeSh) : Bool := !T.oneList || T.lists == 0

/-- The guard on a tree's parts' groups. -/
def sharesAt (a : StSh) (T : TreeSh) : Bool :=
  sharesOk (T.parts.filterMap fun o => (a.oracles[o]?).bind fun x =>
    if x.shape.answers == 0 then none else some x.groups) T.oneList

/-- **Two shapes agree at the messages numbered in A.** -/
structure SameRead (A : List ℕ) (c d : CoreSh) : Prop where
  codes : d.st.codes = c.st.codes
  length : d.st.oracles.length = c.st.oracles.length
  msg : ∀ o ∈ A, (d.st.oracles[o]?).map strip = (c.st.oracles[o]?).map strip
  place : ∀ o ∈ A, d.book.place[o]? = c.book.place[o]?
  placeLength : d.book.place.length = c.book.place.length
  tree : ∀ o ∈ A, ∀ q, c.book.place[o]? = some q →
    (d.book.trees[q.1]?).map stripT = (c.book.trees[q.1]?).map stripT
  opened : ∀ o ∈ A, ∀ q, c.book.place[o]? = some q →
    (d.book.trees[q.1]?).map openedAt = (c.book.trees[q.1]?).map openedAt
  shares : ∀ o ∈ A, ∀ q, c.book.place[o]? = some q →
    (d.book.trees[q.1]?).map (sharesAt d.st) = (c.book.trees[q.1]?).map (sharesAt c.st)
  roots : d.roots = c.roots

/-- **The same, and the group g of c is the group g' of d.** -/
structure SameCore (A : List ℕ) (g g' : ℕ) (c d : CoreSh) : Prop extends SameRead A c d where
  group : d.st.groups[g']? = c.st.groups[g]?
  members : ∀ G, c.st.groups[g]? = some G → ∀ o ∈ G.members, o ∈ A
  knows : ∀ o ∈ A, (d.st.oracles[o]?).map (·.groups.contains g') =
    (c.st.oracles[o]?).map (·.groups.contains g)

section Read
variable {A : List ℕ} {c d : CoreSh}

/-- **A reader that does not read the ledger reads the same.** -/
theorem SameRead.read {β : Type} (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) (f : OrcSh → β)
    (hf : ∀ x, f (strip x) = f x) : (d.st.oracles[o]?).map f = (c.st.oracles[o]?).map f := by
  have e : ∀ z : Option OrcSh, z.map f = (z.map strip).map f := by
    intro z
    cases z with
    | none => rfl
    | some x => exact congrArg some (hf x).symm
  rw [e, e (c.st.oracles[o]?), h.msg o ho]

theorem SameRead.on (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) (f : OrcSh → Bool)
    (hf : ∀ x, f (strip x) = f x) : on d.st.oracles[o]? f = on c.st.oracles[o]? f := by
  unfold VerifiableInference.Desc.Ground.on
  rw [h.read ho f hf]

theorem SameRead.has (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) (f : OrcSh → Bool)
    (hf : ∀ x, f (strip x) = f x) : has d.st.oracles[o]? f = has c.st.oracles[o]? f := by
  unfold VerifiableInference.Desc.Ground.has
  rw [h.read ho f hf]

theorem SameRead.any (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) (f : OrcSh → Bool)
    (hf : ∀ x, f (strip x) = f x) : (d.st.oracles[o]?).any f = (c.st.oracles[o]?).any f := by
  have e : ∀ z : Option OrcSh, z.any f = (z.map f).getD false := by
    intro z
    cases z <;> rfl
  rw [e, e, h.read ho f hf]

theorem SameRead.isSome (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) :
    (d.st.oracles[o]?).isSome = (c.st.oracles[o]?).isSome := by
  have e : ∀ z : Option OrcSh, z.isSome = (z.map fun _ => true).getD false := by
    intro z
    cases z <;> rfl
  rw [e, e, h.read ho (fun _ => true) fun _ => rfl]

/-- **A reader of a tree that does not read the source reads the same.** -/
theorem SameRead.readT {β : Type} (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) {q : ℕ × ℕ}
    (hq : c.book.place[o]? = some q) (f : TreeSh → β) (hf : ∀ T, f (stripT T) = f T) :
    (d.book.trees[q.1]?).map f = (c.book.trees[q.1]?).map f := by
  have e : ∀ z : Option TreeSh, z.map f = (z.map stripT).map f := by
    intro z
    cases z with
    | none => rfl
    | some x => exact congrArg some (hf x).symm
  rw [e, e (c.book.trees[q.1]?), h.tree o ho q hq]

/-- A message in A is there in both or in neither, and the same but for its ledger. -/
theorem SameRead.cases (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) :
    (c.st.oracles[o]? = none ∧ d.st.oracles[o]? = none) ∨
      ∃ x y, c.st.oracles[o]? = some x ∧ d.st.oracles[o]? = some y ∧ strip y = strip x := by
  have e := h.msg o ho
  cases hx : c.st.oracles[o]? with
  | none =>
    rw [hx] at e
    cases hy : d.st.oracles[o]? with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some y =>
      rw [hy] at e
      cases e
  | some x =>
    rw [hx] at e
    cases hy : d.st.oracles[o]? with
    | none =>
      rw [hy] at e
      cases e
    | some y =>
      rw [hy] at e
      exact Or.inr ⟨x, y, rfl, rfl, Option.some.inj e⟩

theorem SameRead.seat (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) : seatOfS d o = seatOfS c o := by
  unfold seatOfS
  have e1 := h.read ho (·.shape) fun _ => rfl
  rw [h.place o ho]
  cases hx : c.st.oracles[o]? with
  | none =>
    rw [hx] at e1
    cases hy : d.st.oracles[o]? with
    | none => rfl
    | some y =>
      rw [hy] at e1
      cases e1
  | some x =>
    rw [hx] at e1
    cases hy : d.st.oracles[o]? with
    | none =>
      rw [hy] at e1
      cases e1
    | some y =>
      rw [hy] at e1
      have es : y.shape = x.shape := Option.some.inj e1
      simp only [Option.bind_some]
      cases hq : c.book.place[o]? with
      | none => rfl
      | some q =>
        simp only [Option.bind_some]
        rw [es]
        exact h.readT ho hq (fun T => (⟨o, x.shape, q.1, q.2, T.shape, T.number⟩ : H2K.First.Seat1))
          fun _ => rfl

/-- A place's tree reads the same. -/
theorem SameRead.treeAt (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) {β : Type} (f : TreeSh → β)
    (hf : ∀ T, f (stripT T) = f T) :
    (((d.book.place[o]?).bind fun p => d.book.trees[p.1]?).map f) =
      (((c.book.place[o]?).bind fun p => c.book.trees[p.1]?).map f) := by
  rw [h.place o ho]
  cases hq : c.book.place[o]? with
  | none => rfl
  | some q => exact h.readT ho hq f hf

end Read

theorem all_same {α : Type} {l : List α} {f f' : α → Bool} (h : ∀ a ∈ l, f a = f' a) :
    l.all f = l.all f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

section Front
variable {A : List ℕ} {g g' : ℕ} {c d : CoreSh}

/-- **The front's clauses read the same.** -/
theorem frontLS_same (h : SameCore A g g' c d) {mask : Option ℕ}
    (hm : ∀ m, mask = some m → m ∈ A) : frontLS d g' mask = frontLS c g mask := by
  have hr := h.toSameRead
  have each : ∀ f : ℕ → OrcSh → Bool, (∀ o x, f o (strip x) = f o x) →
      on c.st.groups[g]? (fun G => G.members.all fun o => on d.st.oracles[o]? (f o)) =
        on c.st.groups[g]? (fun G => G.members.all fun o => on c.st.oracles[o]? (f o)) := by
    intro f hf
    cases hG : c.st.groups[g]? with
    | none => rfl
    | some G =>
      show (G.members.all _) = (G.members.all _)
      exact all_same fun o ho => hr.on (h.members G hG o ho) (f o) (hf o)
  have there : on c.st.groups[g]? (fun G => G.members.all fun o => (d.st.oracles[o]?).isSome) =
      on c.st.groups[g]? (fun G => G.members.all fun o => (c.st.oracles[o]?).isSome) := by
    cases hG : c.st.groups[g]? with
    | none => rfl
    | some G =>
      show (G.members.all _) = (G.members.all _)
      exact all_same fun o ho => hr.isSome (h.members G hG o ho)
  have em : ∀ f : OrcSh → Bool, (∀ x, f (strip x) = f x) →
      on (mask.bind fun m => d.st.oracles[m]?) f = on (mask.bind fun m => c.st.oracles[m]?) f := by
    intro f hf
    cases mask with
    | none => rfl
    | some m => exact hr.on (hm m rfl) f hf
  have ems : (mask.bind fun m => d.st.oracles[m]?).isSome =
      (mask.bind fun m => c.st.oracles[m]?).isSome := by
    cases mask with
    | none => rfl
    | some m => exact hr.isSome (hm m rfl)
  have et : ∀ G, c.st.groups[g]? = some G → ∀ o ∈ G.members ++ mask.toList, o ∈ A := by
    intro G hG o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact h.members G hG o ho
    · cases mask with
      | none => cases ho
      | some m =>
        obtain rfl := List.mem_singleton.1 ho
        exact hm _ rfl
  have tg : ∀ (z : Option TreeSh), z.isSome = (z.map fun _ => true).getD false := by
    intro z
    cases z <;> rfl
  have t1 : on c.st.groups[g]? (fun G => (G.members ++ mask.toList).all fun o =>
        ((d.book.place[o]?).bind fun p => d.book.trees[p.1]?).isSome) =
      on c.st.groups[g]? (fun G => (G.members ++ mask.toList).all fun o =>
        ((c.book.place[o]?).bind fun p => c.book.trees[p.1]?).isSome) := by
    cases hG : c.st.groups[g]? with
    | none => rfl
    | some G =>
      show (List.all _ _) = (List.all _ _)
      exact all_same fun o ho => by
        rw [tg, tg, hr.treeAt (et G hG o ho) (fun _ => true) fun _ => rfl]
  have t2 : on c.st.groups[g]? (fun G => (G.members ++ mask.toList).all fun o =>
        on ((d.book.place[o]?).bind fun p => d.book.trees[p.1]?) fun t =>
          !t.oneList || t.lists == 0) =
      on c.st.groups[g]? (fun G => (G.members ++ mask.toList).all fun o =>
        on ((c.book.place[o]?).bind fun p => c.book.trees[p.1]?) fun t =>
          !t.oneList || t.lists == 0) := by
    cases hG : c.st.groups[g]? with
    | none => rfl
    | some G =>
      show (List.all _ _) = (List.all _ _)
      refine all_same fun o ho => ?_
      have ho' := et G hG o ho
      unfold VerifiableInference.Desc.Ground.on
      rw [hr.place o ho']
      cases hq : c.book.place[o]? with
      | none => rfl
      | some q =>
        have e := hr.opened o ho' q hq
        simp only [Option.bind_some]
        exact congrArg (fun y => Option.getD y true) e
  have kn : on c.st.groups[g]? (fun G => G.members.all fun o =>
        on d.st.oracles[o]? fun y => y.groups.contains g') =
      on c.st.groups[g]? (fun G => G.members.all fun o =>
        on c.st.oracles[o]? fun y => y.groups.contains g) := by
    cases hG : c.st.groups[g]? with
    | none => rfl
    | some G =>
      show (List.all _ _) = (List.all _ _)
      exact all_same fun o ho => by
        unfold VerifiableInference.Desc.Ground.on
        rw [h.knows o (h.members G hG o ho)]
  unfold frontLS
  dsimp only
  rw [h.group, h.codes, h.length, h.placeLength]
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  exact ⟨there, each _ (fun _ _ => rfl), kn, each _ (fun _ _ => rfl),
    each _ (fun _ _ => rfl), by rw [ems], em _ (fun _ => rfl), em _ (fun _ => rfl),
    em _ (fun _ => rfl), t1, t2⟩

end Front

theorem map_range_same {β : Type} (n : ℕ) (f f' : ℕ → β) (h : ∀ i, i < n → f i = f' i) :
    (Array.range n).map f = (Array.range n).map f' := by
  rw [← Array.toList_inj]
  simp only [Array.toList_map, Array.toList_range]
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

section Layout
variable {A : List ℕ} {c d : CoreSh}

theorem blockBitsS_same (h : SameRead A c d) {G : GrpSh} (hA : ∀ o ∈ G.members, o ∈ A)
    (part : OnBytes.Part) : blockBitsS d.st G part = blockBitsS c.st G part := by
  unfold blockBitsS
  refine map_range_same _ _ _ fun i hi => ?_
  have hm : G.members.getD i noId ∈ A := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hA _ (List.getElem_mem hi)
  rcases h.cases hm with ⟨hx, hy⟩ | ⟨x, y, hx, hy, e⟩
  · simp only [hx, hy]
  · have es : y.shape = x.shape := by
      have e' := congrArg OrcSh.shape e
      exact e'
    simp only [hx, hy, es, Option.any_some]

theorem layoutS_same (h : SameRead A c d) {G : GrpSh} (hA : ∀ o ∈ G.members, o ∈ A) :
    layoutS d.st G = layoutS c.st G := by
  unfold layoutS
  rw [blockBitsS_same h hA, blockBitsS_same h hA, h.codes]

theorem runCountS_same (h : SameRead A c d) {G : GrpSh} (hA : ∀ o ∈ G.members, o ∈ A) :
    runCountS d.st G = runCountS c.st G := by
  unfold runCountS
  have e : (G.members.map fun o => ((d.st.oracles[o]?).map (·.rows)).getD 0) =
      G.members.map fun o => ((c.st.oracles[o]?).map (·.rows)).getD 0 :=
    List.map_congr_left fun o ho => by rw [h.read (hA o ho) (·.rows) fun _ => rfl]
  rw [e]

theorem modAt_ne {α : Type} (l : List α) (i : ℕ) (f : α → α) {j : ℕ} (hj : j ≠ i) :
    (modAt l i f)[j]? = l[j]? := by
  unfold modAt
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases l[j]? with
  | none => rfl
  | some x => simp [hj]

theorem modAt_length {α : Type} (l : List α) (i : ℕ) (f : α → α) :
    (modAt l i f).length = l.length := by
  simp [modAt]

theorem fold_shut {β : Type} (f : OrcSh → β) (hf : ∀ x, f (shutS x) = f x) :
    ∀ (ms : List ℕ) (os : List OrcSh) (j : ℕ),
    ((ms.foldl (fun os o => modAt os o shutS) os)[j]?).map f = (os[j]?).map f
  | [], _, _ => rfl
  | m :: ms, os, j => by
    rw [List.foldl_cons, fold_shut f hf ms]
    by_cases e : j = m
    · subst e
      rw [modAt_get]
      cases os[j]? with
      | none => rfl
      | some x => exact congrArg some (hf x)
    · rw [modAt_ne _ _ _ e]

/-- A guard on a tree's parts does not read a ledger. -/
theorem sharesAt_shut (a : StSh) (ms : List ℕ) (T : TreeSh) :
    sharesAt { a with oracles := ms.foldl (fun os o => modAt os o shutS) a.oracles } T =
      sharesAt a T := by
  unfold sharesAt
  have e : ∀ (l : List ℕ), (l.filterMap fun o =>
      ((ms.foldl (fun os o => modAt os o shutS) a.oracles)[o]?).bind fun x =>
        if x.shape.answers == 0 then none else some x.groups) =
      l.filterMap fun o => (a.oracles[o]?).bind fun x =>
        if x.shape.answers == 0 then none else some x.groups := by
    intro l
    have eb : ∀ z : Option OrcSh, (z.bind fun x =>
        if x.shape.answers == 0 then none else some x.groups) =
        (z.map fun x => if x.shape.answers == 0 then none else some x.groups).getD none := by
      intro z
      cases z <;> rfl
    refine List.filterMap_congr fun o _ => ?_
    rw [eb, eb, fold_shut (fun x => if x.shape.answers == 0 then none else some x.groups)
      (fun _ => rfl)]
  show sharesOk (T.parts.filterMap _) T.oneList = _
  rw [e]

theorem fold_shut_length : ∀ (ms : List ℕ) (os : List OrcSh),
    (ms.foldl (fun os o => modAt os o shutS) os).length = os.length
  | [], _ => rfl
  | m :: ms, os => by
    rw [List.foldl_cons, fold_shut_length ms, modAt_length]

end Layout

section Begin
variable {A : List ℕ} {g g' : ℕ} {c d : CoreSh}

theorem beginRunG_same (h : SameCore A g g' c d) : beginRunG d.st g' = beginRunG c.st g := by
  unfold beginRunG
  rw [h.group, h.length]

/-- **The beginning of a test reads the same.** -/
theorem beginRunS_same (h : SameCore A g g' c d) :
    (beginRunS d g').map (·.1) = (beginRunS c g).map (·.1) ∧
      ∀ x y, beginRunS c g = some x → beginRunS d g' = some y → SameRead A x.2 y.2 := by
  have hr := h.toSameRead
  unfold beginRunS
  rw [beginRunG_same h, h.group]
  by_cases hb : beginRunG c.st g = true
  · rw [if_pos hb, if_pos hb]
    cases hG : c.st.groups[g]? with
    | none => exact ⟨rfl, fun x y hx => by cases hx⟩
    | some G =>
      have hA := h.members G hG
      simp only [Option.map_some, Option.some.injEq]
      refine ⟨by rw [layoutS_same hr hA, runCountS_same hr hA], ?_⟩
      rintro x y rfl rfl
      refine ⟨hr.codes, ?_, fun o ho => ?_, hr.place, hr.placeLength, hr.tree, hr.opened,
        fun o ho q hq => ?_, hr.roots⟩
      · show (G.members.foldl (fun os o => modAt os o shutS) d.st.oracles).length =
          (G.members.foldl (fun os o => modAt os o shutS) c.st.oracles).length
        rw [fold_shut_length, fold_shut_length, hr.length]
      · show ((G.members.foldl (fun os o => modAt os o shutS) d.st.oracles)[o]?).map strip =
          ((G.members.foldl (fun os o => modAt os o shutS) c.st.oracles)[o]?).map strip
        rw [fold_shut _ (fun _ => rfl), fold_shut _ (fun _ => rfl), hr.msg o ho]
      · have key : ∀ (a : StSh) (j : ℕ), sharesAt (begunS a j G) = sharesAt a := fun a j =>
          funext fun T => sharesAt_shut a G.members T
        show ((d.book.trees[q.1]?).map (sharesAt (begunS d.st g' G))) =
          (c.book.trees[q.1]?).map (sharesAt (begunS c.st g G))
        rw [key, key]
        exact hr.shares o ho q hq
  · rw [if_neg hb, if_neg hb]
    exact ⟨rfl, fun x y hx => by cases hx⟩

theorem commonB_same (h : SameCore A g g' c d) (p : P12) (cur nxt : Fmt.M1.Stage) (i n : ℕ × ℕ) :
    commonB p cur nxt d g' i n = commonB p cur nxt c g i n := by
  have hr := h.toSameRead
  unfold commonB
  rw [h.group, h.codes]
  cases hG : c.st.groups[g]? with
  | none => rfl
  | some G =>
    have hA := h.members G hG
    have e : (G.members.any fun o => (d.st.oracles[o]?).any fun x => decide (0 < x.shape.mainRows)) =
        G.members.any fun o => (c.st.oracles[o]?).any fun x => decide (0 < x.shape.mainRows) := by
      have : ∀ {l : List ℕ}, (∀ o ∈ l, o ∈ A) →
          (l.any fun o => (d.st.oracles[o]?).any fun x => decide (0 < x.shape.mainRows)) =
            l.any fun o => (c.st.oracles[o]?).any fun x => decide (0 < x.shape.mainRows) := by
        intro l
        induction l with
        | nil => exact fun _ => rfl
        | cons a l ih =>
          intro hl
          simp only [List.any_cons]
          rw [hr.any (hl a List.mem_cons_self) _ fun _ => rfl,
            ih fun b hb => hl b (List.mem_cons_of_mem _ hb)]
      exact this hA
    show (_ && _) = (_ && _)
    rw [layoutS_same hr hA, e]

theorem cameB_same (h : SameCore A g g' c d) (cur : Fmt.M1.Stage) (i : ℕ × ℕ) {id : ℕ}
    (hid : id ∈ A) : cameB cur d g' i id = cameB cur c g i id := by
  have hr := h.toSameRead
  unfold cameB
  rw [h.group]
  cases hG : c.st.groups[g]? with
  | none => rfl
  | some G =>
    show has d.st.oracles[id]? _ = has c.st.oracles[id]? _
    exact hr.has hid _ fun _ => rfl

end Begin

section Gp
variable {A : List ℕ} {c d : CoreSh}

theorem mem_insertN {a x : ℕ} : ∀ {l : List ℕ}, a ∈ Fmt.insertIntoIncreasingList x l → a = x ∨ a ∈ l
  | [], h => by
    simpa [Fmt.insertIntoIncreasingList] using h
  | y :: l, h => by
    unfold Fmt.insertIntoIncreasingList at h
    split at h
    · rcases List.mem_cons.1 h with e | e
      · exact Or.inl e
      · exact Or.inr e
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.1 h with e | e
        · exact Or.inr (e ▸ List.mem_cons_self)
        · rcases mem_insertN e with e' | e'
          · exact Or.inl e'
          · exact Or.inr (List.mem_cons_of_mem _ e')

theorem mem_listOf {a : ℕ} : ∀ {l : List ℕ}, a ∈ Fmt.listOf l → a ∈ l
  | [], h => h
  | x :: l, h => by
    have h' : a ∈ Fmt.insertIntoIncreasingList x (Fmt.listOf l) := h
    rcases mem_insertN h' with e | e
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_listOf e)

theorem mapM_seat (h : SameRead A c d) : ∀ {l : List ℕ}, (∀ o ∈ l, o ∈ A) →
    l.mapM (seatOfS d) = l.mapM (seatOfS c)
  | [], _ => rfl
  | a :: l, hl => by
    simp only [List.mapM_cons]
    rw [h.seat (hl a List.mem_cons_self), mapM_seat h fun b hb => hl b (List.mem_cons_of_mem _ hb)]

theorem seat_place {o : ℕ} {m : H2K.First.Seat1} (h : seatOfS c o = some m) :
    ∃ q, c.book.place[o]? = some q ∧ q.1 = m.t := by
  unfold seatOfS at h
  obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨T, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨q, hq, rfl⟩

theorem mapM_mem : ∀ {l : List ℕ} {ms : List H2K.First.Seat1},
    l.mapM (seatOfS c) = some ms → ∀ m ∈ ms, ∃ o ∈ l, seatOfS c o = some m
  | [], ms, h, m, hm => by
    have : ms = [] := (Option.some.inj h).symm
    subst this
    cases hm
  | a :: l, ms, h, m, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact ⟨a, List.mem_cons_self, hx⟩
    · obtain ⟨o, ho, e⟩ := mapM_mem hxs m hm'
      exact ⟨o, List.mem_cons_of_mem _ ho, e⟩

/-- **The plain data read the same, but for the book.** -/
theorem gpOfS_same (h : SameRead A c d) (p : P12) (s : Fmt.M1.Stage) (L : GroupLayout) {g g' : ℕ}
    {pa pb : ProofFile.Honest.Sh.ThinPass} {id : ℕ} (hid : id ∈ A) (hL : ∀ o ∈ L.members.toList, o ∈ A) :
    gpOfS p ⟨d, g', pb, some id⟩ s L =
      (gpOfS p ⟨c, g, pa, some id⟩ s L).map fun D => { D with book := d.book } := by
  unfold gpOfS
  cases stageAt p 0 s with
  | none => rfl
  | some cu =>
    simp only [Option.bind_some, maskThin]
    rw [mapM_seat h hL, h.seat hid, h.codes]
    cases L.members.toList.mapM (seatOfS c) with
    | none => rfl
    | some ms =>
      simp only [Option.bind_some]
      cases seatOfS c id with
      | none => rfl
      | some f => rfl

theorem gpOfS_ts {p : P12} {s : Fmt.M1.Stage} {L : GroupLayout} {g : ℕ}
    {pa : ProofFile.Honest.Sh.ThinPass} {id : ℕ} (hid : id ∈ A) (hL : ∀ o ∈ L.members.toList, o ∈ A)
    {D : PlainS} (h : gpOfS p ⟨c, g, pa, some id⟩ s L = some D) :
    D.book = c.book ∧ ∀ t ∈ D.ts, ∃ o ∈ A, ∃ q, c.book.place[o]? = some q ∧ q.1 = t := by
  unfold gpOfS at h
  obtain ⟨cu, -, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [maskThin, Option.bind_some] at h
  obtain ⟨ms, hms, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨rfl, fun t ht => ?_⟩
  have ht' := mem_listOf ht
  rcases List.mem_append.1 ht' with e | e
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 e
    obtain ⟨o, ho, em⟩ := mapM_mem hms m hm
    obtain ⟨q, hq, eq⟩ := seat_place em
    exact ⟨o, hL o ho, q, hq, eq⟩
  · obtain rfl := List.mem_singleton.1 e
    obtain ⟨q, hq, eq⟩ := seat_place hf
    exact ⟨id, hid, q, hq, eq⟩

theorem gpLS_book (p : P12) (a : Fmt.M1.Stage) (kept : ℕ) (D : PlainS) (b : BookSh)
    (h : ∀ t ∈ D.ts, (b.trees[t]?).map stripT = (D.book.trees[t]?).map stripT) :
    gpLS p a kept { D with book := b } = gpLS p a kept D := by
  have rd : ∀ {β : Type} (f : TreeSh → β), (∀ T, f (stripT T) = f T) → ∀ t ∈ D.ts,
      (b.trees[t]?).map f = (D.book.trees[t]?).map f := by
    intro β f hf t ht
    have e : ∀ z : Option TreeSh, z.map f = (z.map stripT).map f := by
      intro z
      cases z with
      | none => rfl
      | some x => exact congrArg some (hf x).symm
    rw [e, e (D.book.trees[t]?), h t ht]
  have e1 : D.ts.map (keyAtS p.nums.firstTree b) = D.ts.map (keyAtS p.nums.firstTree D.book) :=
    List.map_congr_left fun t ht => by
      unfold keyAtS
      rw [rd (·.number) (fun _ => rfl) t ht]
  have e2 : D.ts.map (logAtS b) = D.ts.map (logAtS D.book) :=
    List.map_congr_left fun t ht => by
      unfold logAtS
      rw [rd (·.shape.logN) (fun _ => rfl) t ht]
  have e3 : D.ts.map (widthAtS b) = D.ts.map (widthAtS D.book) :=
    List.map_congr_left fun t ht => by
      unfold widthAtS
      rw [rd (fun T => T.shape.mainWidth + T.shape.maskWidth) (fun _ => rfl) t ht]
  unfold gpLS
  dsimp only
  rw [e1, e2, e3]

/-- The plain data's book, where the data are made. -/
theorem trees_same (h : SameRead A c d) {D : PlainS}
    (hb : D.book = c.book) (ht : ∀ t ∈ D.ts, ∃ o ∈ A, ∃ q, c.book.place[o]? = some q ∧ q.1 = t) :
    ∀ t ∈ D.ts, (d.book.trees[t]?).map stripT = (D.book.trees[t]?).map stripT := by
  intro t htt
  obtain ⟨o, ho, q, hq, rfl⟩ := ht t htt
  rw [hb]
  exact h.tree o ho q hq

theorem gpOkS_same (h : SameRead A c d) (p : P12) {g g' : ℕ} (cl cl' : ProofFile.Honest.Sh.ClaimSh)
    (e₁ : cl'.lay = cl.lay) (e₂ : cl'.kept = cl.kept) {id : ℕ}
    (hid : id ∈ A) (hL : ∀ o ∈ cl.lay.members.toList, o ∈ A) :
    gpOkS p ⟨d, g', .claim cl', some id⟩ = gpOkS p ⟨c, g, .claim cl, some id⟩ := by
  unfold gpOkS gpAllS
  cases p.nums.stages with
  | nil => rfl
  | cons s l =>
    show H2K.First.ok (match gpOfS p ⟨d, g', .claim cl'.lay, some id⟩ s cl'.lay with
        | some D => gpLS p s cl'.kept D
        | none => _) =
      H2K.First.ok (match gpOfS p ⟨c, g, .claim cl.lay, some id⟩ s cl.lay with
        | some D => gpLS p s cl.kept D
        | none => _)
    rw [e₁, e₂, gpOfS_same h p s cl.lay (g := g) (pa := .claim cl.lay) hid hL]
    cases hD : gpOfS p ⟨c, g, .claim cl.lay, some id⟩ s cl.lay with
    | none => rfl
    | some D =>
      obtain ⟨hb, ht⟩ := gpOfS_ts hid hL hD
      show H2K.First.ok (gpLS p s cl.kept { D with book := d.book }) = _
      rw [gpLS_book _ _ _ _ _ (trees_same h hb ht)]

theorem labelsOkS_same (h : SameRead A c d) (p : P12) {g g' : ℕ} (cl cl' : ProofFile.Honest.Sh.ClaimSh)
    (e₁ : cl'.lay = cl.lay) {id : ℕ} (hid : id ∈ A) (hL : ∀ o ∈ cl.lay.members.toList, o ∈ A) :
    labelsOkS p ⟨d, g', .claim cl', some id⟩ = labelsOkS p ⟨c, g, .claim cl, some id⟩ := by
  unfold labelsOkS labelsLS
  cases p.nums.stages with
  | nil => rfl
  | cons s l =>
    show H2K.First.ok (match gpOfS p ⟨d, g', .claim cl'.lay, some id⟩ s cl'.lay with
        | some D => _
        | none => _) =
      H2K.First.ok (match gpOfS p ⟨c, g, .claim cl.lay, some id⟩ s cl.lay with
        | some D => _
        | none => _)
    rw [e₁, gpOfS_same h p s cl.lay (g := g) (pa := .claim cl.lay) hid hL]
    cases hD : gpOfS p ⟨c, g, .claim cl.lay, some id⟩ s cl.lay with
    | none => rfl
    | some D =>
      obtain ⟨hb, ht⟩ := gpOfS_ts hid hL hD
      have e : D.ts.map (numAtS d.book) = D.ts.map (numAtS D.book) :=
        List.map_congr_left fun t htt => by
          unfold numAtS
          have hs := trees_same h hb ht t htt
          have ez : ∀ z : Option TreeSh, z.map (·.number) = (z.map stripT).map (·.number) := by
            intro z
            cases z <;> rfl
          rw [ez, ez (D.book.trees[t]?), hs]
      show H2K.First.ok [("opens.tree", D.opens.map (·.1.tree) == D.ts.map (numAtS d.book))] = _
      rw [e]

end Gp

section Pub
variable {A : List ℕ} {c d : CoreSh}

theorem mapM_place (h : SameRead A c d) : ∀ {l : List ℕ}, (∀ o ∈ l, o ∈ A) →
    (l.mapM fun o => d.book.place[o]?) = l.mapM fun o => c.book.place[o]?
  | [], _ => rfl
  | a :: l, hl => by
    simp only [List.mapM_cons]
    rw [h.place a (hl a List.mem_cons_self),
      mapM_place h fun b hb => hl b (List.mem_cons_of_mem _ hb)]

theorem mapM_place_mem : ∀ {l : List ℕ} {qs : List (ℕ × ℕ)},
    (l.mapM fun o => c.book.place[o]?) = some qs → ∀ q ∈ qs, ∃ o ∈ l, c.book.place[o]? = some q
  | [], qs, h, q, hq => by
    have : qs = [] := (Option.some.inj h).symm
    subst this
    cases hq
  | a :: l, qs, h, q, hq => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact ⟨a, List.mem_cons_self, hx⟩
    · obtain ⟨o, ho, e⟩ := mapM_place_mem hxs q hq'
      exact ⟨o, List.mem_cons_of_mem _ ho, e⟩

theorem openG_same (h : SameRead A c d) {o : ℕ} (ho : o ∈ A) {q : ℕ × ℕ}
    (hq : c.book.place[o]? = some q) (logN : ℕ) :
    openG d.st d.book d.book logN q.1 = openG c.st c.book c.book logN q.1 := by
  have e₁ := h.shares o ho q hq
  have e₂ := h.readT ho hq (fun T => decide (T.shape.logN ≤ logN)) fun _ => rfl
  have e₃ := h.opened o ho q hq
  unfold openG
  cases hT : c.book.trees[q.1]? with
  | none =>
    rw [hT] at e₁
    cases hU : d.book.trees[q.1]? with
    | none => rfl
    | some U =>
      rw [hU] at e₁
      cases e₁
  | some T =>
    rw [hT] at e₁ e₂ e₃
    cases hU : d.book.trees[q.1]? with
    | none =>
      rw [hU] at e₁
      cases e₁
    | some U =>
      rw [hU] at e₁ e₂ e₃
      have a₁ : sharesAt d.st U = sharesAt c.st T := Option.some.inj e₁
      have a₂ : decide (U.shape.logN ≤ logN) = decide (T.shape.logN ≤ logN) := Option.some.inj e₂
      have a₃ : openedAt U = openedAt T := Option.some.inj e₃
      show (sharesAt d.st U && openedAt U && decide (U.shape.logN ≤ logN)) =
        (sharesAt c.st T && openedAt T && decide (T.shape.logN ≤ logN))
      rw [a₁, a₂, a₃]

/-- **The test on the reading reads the same.** -/
theorem readPubB_same (h : SameRead A c d) (r : ProofFile.Honest.Sh.SingleSh) (logN : ℕ)
    (hA : ∀ o ∈ ProofFile.Honest.Sh.idsS r, o ∈ A) : readPubB d r logN = readPubB c r logN := by
  unfold readPubB
  rw [mapM_place h hA]
  cases hP : (ProofFile.Honest.Sh.idsS r).mapM fun o => c.book.place[o]? with
  | none => rfl
  | some places =>
    have hmem : ∀ t ∈ OnBytes.listOfT (places.map (·.1)), ∃ o ∈ ProofFile.Honest.Sh.idsS r, ∃ q,
        c.book.place[o]? = some q ∧ q.1 = t := by
      intro t ht
      rw [OnBytes.listOfT_eq] at ht
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (mem_listOf ht)
      obtain ⟨o, ho, e⟩ := mapM_place_mem hP q hq
      exact ⟨o, ho, q, e, rfl⟩
    have e1 := all_same (l := OnBytes.listOfT (places.map (·.1)))
      (f := fun t => (((d.book.trees[t]?).map (·.parts)).getD []).all fun o =>
        (ProofFile.Honest.Sh.idsS r).contains o)
      (f' := fun t => (((c.book.trees[t]?).map (·.parts)).getD []).all fun o =>
        (ProofFile.Honest.Sh.idsS r).contains o) fun t ht => by
        obtain ⟨o, ho, q, hq, rfl⟩ := hmem t ht
        show ((((d.book.trees[q.1]?).map (·.parts)).getD []).all _) = _
        rw [h.readT (hA o ho) hq (·.parts) fun _ => rfl]
    have e2 := all_same (l := OnBytes.listOfT (places.map (·.1)))
      (f := fun t => openG d.st d.book d.book logN t)
      (f' := fun t => openG c.st c.book c.book logN t) fun t ht => by
        obtain ⟨o, ho, q, hq, rfl⟩ := hmem t ht
        exact openG_same h (hA o ho) hq logN
    have e3 := all_same (l := ProofFile.Honest.Sh.idsS r) (f := fun o => (d.st.oracles[o]?).isSome)
      (f' := fun o => (c.st.oracles[o]?).isSome) fun o ho => h.isSome (hA o ho)
    have e4 := all_same (l := List.range r.lay.members.size) (f := ProofFile.Honest.Sh.memberS d r)
      (f' := ProofFile.Honest.Sh.memberS c r) fun w hw => by
        have hw' : w < r.lay.members.size := List.mem_range.1 hw
        have hm : r.lay.members.getD w 0 ∈ A := by
          refine hA _ (List.mem_append_left _ ?_)
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw']
          exact Array.mem_toList_iff.2 (Array.getElem_mem hw')
        unfold ProofFile.Honest.Sh.memberS
        rcases h.cases hm with ⟨hx, hy⟩ | ⟨x, y, hx, hy, e⟩
        · simp only [hx, hy]
        · have es : y.shape = x.shape := by
            have e' := congrArg OrcSh.shape e
            exact e'
          simp only [hx, hy, es]
    have hf : r.fresh ∈ A := hA _ (List.mem_append_right _ List.mem_cons_self)
    dsimp only
    rw [e1, e2, e3, e4]
    rcases h.cases hf with ⟨hx, hy⟩ | ⟨x, y, hx, hy, e⟩
    · simp only [hx, hy]
    · have es : y.shape = x.shape := by
        have e' := congrArg OrcSh.shape e
        exact e'
      simp only [hx, hy, es]

theorem spendS_same (h : SameRead A c d) {id : ℕ} (hid : id ∈ A) :
    (spendS d id).isSome = (spendS c id).isSome ∧
      ∀ x y, spendS c id = some x → spendS d id = some y → SameRead A x y := by
  have hg : spendG d.st id = spendG c.st id := by
    unfold spendG
    exact h.any hid _ fun _ => rfl
  unfold spendS
  rw [hg]
  by_cases hb : spendG c.st id = true
  · rw [if_pos hb, if_pos hb]
    refine ⟨rfl, ?_⟩
    rintro x y ⟨⟩ ⟨⟩
    refine ⟨h.codes, ?_, fun o ho => ?_, h.place, h.placeLength, h.tree, h.opened,
      fun o ho q hq => ?_, h.roots⟩
    · show (modAt d.st.oracles id fun x => { x with spent := true }).length =
        (modAt c.st.oracles id fun x => { x with spent := true }).length
      rw [modAt_length, modAt_length, h.length]
    · show ((modAt d.st.oracles id fun x => { x with spent := true })[o]?).map strip =
        ((modAt c.st.oracles id fun x => { x with spent := true })[o]?).map strip
      by_cases e : o = id
      · subst e
        rw [modAt_get, modAt_get]
        have em : ∀ z : Option OrcSh, (z.map fun x : OrcSh => { x with spent := true }).map strip =
            (z.map strip).map fun x : OrcSh => { x with spent := true } := by
          intro z
          cases z <;> rfl
        rw [em, em, h.msg o ho]
      · rw [modAt_ne _ _ _ e, modAt_ne _ _ _ e, h.msg o ho]
    · have key : ∀ a : StSh, sharesAt { a with
          oracles := modAt a.oracles id fun x => { x with spent := true } } = sharesAt a := by
        intro a
        funext T
        unfold sharesAt
        have e : ∀ (l : List ℕ), (l.filterMap fun o =>
            ((modAt a.oracles id fun x : OrcSh => { x with spent := true })[o]?).bind fun x =>
              if x.shape.answers == 0 then none else some x.groups) =
            l.filterMap fun o => (a.oracles[o]?).bind fun x =>
              if x.shape.answers == 0 then none else some x.groups := by
          intro l
          refine List.filterMap_congr fun o _ => ?_
          by_cases e : o = id
          · subst e
            rw [modAt_get]
            cases a.oracles[o]? <;> rfl
          · rw [modAt_ne _ _ _ e]
        show sharesOk (T.parts.filterMap _) T.oneList = _
        rw [e]
      show (d.book.trees[q.1]?).map (sharesAt { d.st with oracles := _ }) =
        (c.book.trees[q.1]?).map (sharesAt { c.st with oracles := _ })
      rw [key d.st, key c.st]
      exact h.shares o ho q hq
  · rw [if_neg hb, if_neg hb]
    exact ⟨rfl, fun x y hx => by cases hx⟩

theorem newGroupS_same (h : SameRead A c d) (code maskCode : ℕ) :
    (newGroupS d code maskCode).isSome = (newGroupS c code maskCode).isSome ∧
      ∀ x y, newGroupS c code maskCode = some x → newGroupS d code maskCode = some y →
        SameRead A x.2 y.2 := by
  unfold newGroupS
  rw [h.codes]
  by_cases hb : ok (VerifiableInference.Desc.Ground.groupL c.st.codes code maskCode) = true
  · rw [if_pos hb, if_pos hb]
    refine ⟨rfl, ?_⟩
    rintro x y ⟨⟩ ⟨⟩
    exact ⟨h.codes, h.length, h.msg, h.place, h.placeLength, h.tree, h.opened, h.shares, h.roots⟩
  · rw [if_neg hb, if_neg hb]
    exact ⟨rfl, fun x y hx => by cases hx⟩

end Pub

section Five
variable {A : List ℕ} {g g' : ℕ} {c d : CoreSh}

theorem beginRun_lay {x : (GroupLayout × ℕ) × CoreSh} (h : SameCore A g g' c d)
    (hx : beginRunS c g = some x) : ∀ o ∈ x.1.1.members.toList, o ∈ A := by
  unfold beginRunS at hx
  split at hx
  · obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hx
    intro o ho
    exact h.members G hG o (by simpa [layoutS] using ho)
  · cases hx

theorem beginRun_both (h : SameCore A g g' c d) :
    (beginRunS c g = none ∧ beginRunS d g' = none) ∨
      ∃ u x y, beginRunS c g = some (u, x) ∧ beginRunS d g' = some (u, y) ∧ SameRead A x y := by
  obtain ⟨h1, h2⟩ := beginRunS_same h
  cases hx : beginRunS c g with
  | none =>
    rw [hx] at h1
    cases hy : beginRunS d g' with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some y =>
      rw [hy] at h1
      cases h1
  | some x =>
    rw [hx] at h1
    cases hy : beginRunS d g' with
    | none =>
      rw [hy] at h1
      cases h1
    | some y =>
      rw [hy] at h1
      have e : y.1 = x.1 := Option.some.inj h1
      obtain ⟨u, x'⟩ := x
      obtain ⟨v, y'⟩ := y
      obtain rfl : v = u := e
      exact Or.inr ⟨v, x', y', rfl, rfl, h2 _ _ hx hy⟩

theorem batOwesB_same (h : SameCore A g g' c d) (p : P12) (cut : List Fmt.DeclaredRound)
    (pass : ProofFile.Honest.Sh.PassSh) {id : ℕ} (hid : id ∈ A) :
    batOwesB p cut ⟨d, g', pass, some id⟩ = batOwesB p cut ⟨c, g, pass, some id⟩ := by
  unfold batOwesB
  dsimp only
  rw [h.codes]
  rcases beginRun_both h with ⟨hx, hy⟩ | ⟨u, x, y, hx, hy, hs⟩
  · rw [hx, hy]
  · have hL := beginRun_lay h hx
    rw [hx, hy]
    dsimp only
    rw [gpOkS_same hs p (g := g) ⟨u.1, g, 0, 0, true, true⟩ ⟨u.1, g', 0, 0, true, true⟩ rfl rfl hid hL,
      labelsOkS_same hs p (g := g) ⟨u.1, g, 0, 0, true, true⟩ ⟨u.1, g', 0, 0, true, true⟩ rfl hid hL]

theorem frontOwesB_same (h : SameCore A g g' c d) (p : P12) (pass : ProofFile.Honest.Sh.PassSh) {id : ℕ}
    (hid : id ∈ A) :
    frontOwesB p ⟨d, g', pass, some id⟩ = frontOwesB p ⟨c, g, pass, some id⟩ := by
  unfold frontOwesB
  dsimp only
  rw [h.roots, h.codes, frontLS_same h (mask := some id) fun m e => by
    obtain rfl := Option.some.inj e
    exact hid]

theorem frontPlain_same (h : SameCore A g g' c d) (p : P12) (he : p.early = true) {id : ℕ}
    (hid : id ∈ A) :
    frontPlainB₀ p ⟨d, g', .nothing, some id⟩ = frontPlainB₀ p ⟨c, g, .nothing, some id⟩ := by
  unfold frontPlainB₀ batThin
  cases hi : p.idx with
  | nil => rfl
  | cons i is =>
    dsimp only
    rcases beginRun_both h with ⟨hx, hy⟩ | ⟨u, x, y, hx, hy, hs⟩
    · rw [hx, hy]
      rfl
    · have hL := beginRun_lay h hx
      rw [hx, hy]
      simp only [Option.map_some, he, if_true]
      rw [gpOfS_same hs p (stA p) u.1 (g := g) (g' := g') (pa := .claim u.1) hid hL]
      cases hD : gpOfS p ⟨x, g, .claim u.1, some id⟩ (stA p) u.1 with
      | none => rfl
      | some D =>
        obtain ⟨hb, ht⟩ := gpOfS_ts hid hL hD
        show (ok (gpLS p (stA p) 0 { D with book := y.book }) && _ && _) = _
        rw [gpLS_book _ _ _ _ _ (trees_same hs hb ht)]
        rfl

theorem frontPub_same (h : SameCore A g g' c d) (p : P12) (he : p.early = true) {id : ℕ}
    (hid : id ∈ A) :
    frontPubB p ⟨d, g', .nothing, some id⟩ = frontPubB p ⟨c, g, .nothing, some id⟩ := by
  unfold frontPubB batThin
  cases hi : p.idx with
  | nil => rfl
  | cons i is =>
    dsimp only
    rcases beginRun_both h with ⟨hx, hy⟩ | ⟨u, x, y, hx, hy, hs⟩
    · rw [hx, hy]
      rfl
    · have hL := beginRun_lay h hx
      rw [hx, hy]
      simp only [Option.map_some, he, if_true]
      obtain ⟨s1, s2⟩ := spendS_same hs hid
      cases h1 : spendS x id with
      | none =>
        rw [h1] at s1
        cases h2 : spendS y id with
        | none => rfl
        | some w =>
          rw [h2] at s1
          cases s1
      | some x₁ =>
        cases h2 : spendS y id with
        | none =>
          rw [h1, h2] at s1
          cases s1
        | some y₁ =>
          have hs2 := s2 x₁ y₁ h1 h2
          dsimp only
          obtain ⟨n1, n2⟩ := newGroupS_same hs2 (lettersOf p (stA p) (stN p)).n.code
            (lettersOf p (stA p) (stN p)).n.maskCode
          cases h3 : newGroupS x₁ (lettersOf p (stA p) (stN p)).n.code
              (lettersOf p (stA p) (stN p)).n.maskCode with
          | none =>
            rw [h3] at n1
            cases h4 : newGroupS y₁ (lettersOf p (stA p) (stN p)).n.code
                (lettersOf p (stA p) (stN p)).n.maskCode with
            | none => rfl
            | some v =>
              rw [h4] at n1
              cases n1
          | some z =>
            cases h4 : newGroupS y₁ (lettersOf p (stA p) (stN p)).n.code
                (lettersOf p (stA p) (stN p)).n.maskCode with
            | none =>
              rw [h3, h4] at n1
              cases n1
            | some v =>
              refine readPubB_same (n2 z v h3 h4) _ _ fun o ho => ?_
              rcases List.mem_append.1 ho with ho | ho
              · exact hL o ho
              · obtain rfl := List.mem_singleton.1 ho
                exact hid

theorem doorB_same (h : SameCore A g g' c d) (p : P12) (cur nxt : Fmt.M1.Stage)
    (cut : List Fmt.DeclaredRound) (i n : ℕ × ℕ) {id : ℕ} (hid : id ∈ A) :
    ProofFile.Honest.Sh.doorB p cur nxt cut i n ⟨d, g', .nothing, some id⟩ =
      ProofFile.Honest.Sh.doorB p cur nxt cut i n ⟨c, g, .nothing, some id⟩ := by
  unfold ProofFile.Honest.Sh.doorB
  dsimp only
  rw [commonB_same h, batOwesB_same h p _ _ hid, frontOwesB_same h p _ hid, cameB_same h _ _ hid]

/-- **The count of trees reads the same.** -/
theorem tsLen_same (h : SameCore A g g' c d) (p : P12) (he : p.early = true) {id : ℕ} (hid : id ∈ A) :
    tsLenOf p ⟨d, g', .nothing, some id⟩ = tsLenOf p ⟨c, g, .nothing, some id⟩ := by
  unfold tsLenOf batThin
  cases hi : p.idx with
  | nil => rfl
  | cons i is =>
    dsimp only
    rcases beginRun_both h with ⟨hx, hy⟩ | ⟨u, x, y, hx, hy, hs⟩
    · rw [hx, hy]
      rfl
    · have hL := beginRun_lay h hx
      rw [hx, hy]
      simp only [Option.map_some, he, if_true]
      rw [gpOfS_same hs p (stA p) u.1 (g := g) (g' := g') (pa := .claim u.1) hid hL]
      cases gpOfS p ⟨x, g, .claim u.1, some id⟩ (stA p) u.1 <;> rfl

theorem manyFitsB_book (s : Fmt.M1.Stage) (ms : List MemShape) (trees : List (ℕ × List Piece))
    (D : PlainS) (b : BookSh)
    (h : ∀ t ∈ D.ts, (b.trees[t]?).map stripT = (D.book.trees[t]?).map stripT) :
    manyFitsB s ms trees { D with book := b } = manyFitsB s ms trees D := by
  have rd : ∀ {β : Type} (f : TreeSh → β), (∀ T, f (stripT T) = f T) → ∀ t ∈ D.ts,
      (b.trees[t]?).map f = (D.book.trees[t]?).map f := by
    intro β f hf t ht
    have e : ∀ z : Option TreeSh, z.map f = (z.map stripT).map f := by
      intro z
      cases z with
      | none => rfl
      | some x => exact congrArg some (hf x).symm
    rw [e, e (D.book.trees[t]?), h t ht]
  have e : ((trees.zip D.ts).all fun y => treeFitsB s ms { D with book := b } y.1 y.2) =
      (trees.zip D.ts).all fun y => treeFitsB s ms D y.1 y.2 := by
    refine all_same fun y hy => ?_
    have ht : y.2 ∈ D.ts := (List.of_mem_zip (a := y.1) (b := y.2) hy).2
    unfold treeFitsB logAtS widthAtS
    dsimp only
    rw [rd (·.shape.logN) (fun _ => rfl) _ ht,
      rd (fun T => T.shape.mainWidth + T.shape.maskWidth) (fun _ => rfl) _ ht]
  unfold manyFitsB
  dsimp only
  rw [e]

/-- **The test on a job's members and trees reads the same.** -/
theorem manyFits_same (h : SameCore A g g' c d) (p : P12) (he : p.early = true)
    (ms : List MemShape) (trees : List (ℕ × List Piece)) {id : ℕ} (hid : id ∈ A) :
    manyFitsS p ms trees ⟨d, g', .nothing, some id⟩ = manyFitsS p ms trees ⟨c, g, .nothing, some id⟩ := by
  unfold manyFitsS batThin
  cases hi : p.idx with
  | nil => rfl
  | cons i is =>
    dsimp only
    rcases beginRun_both h with ⟨hx, hy⟩ | ⟨u, x, y, hx, hy, hs⟩
    · rw [hx, hy]
      rfl
    · have hL := beginRun_lay h hx
      rw [hx, hy]
      simp only [Option.map_some, he, if_true]
      rw [gpOfS_same hs p (stA p) u.1 (g := g) (g' := g') (pa := .claim u.1) hid hL]
      cases hD : gpOfS p ⟨x, g, .claim u.1, some id⟩ (stA p) u.1 with
      | none => rfl
      | some D =>
        obtain ⟨hb, ht⟩ := gpOfS_ts hid hL hD
        show manyFitsB (stA p) ms trees { D with book := y.book } = manyFitsB (stA p) ms trees D
        exact manyFitsB_book _ _ _ _ _ (trees_same hs hb ht)

/-- **The test frontFiveB reads the same at two shapes that agree.** -/
theorem frontFive_same (h : SameCore A g g' c d) (p : P12) (K : Codes) (he : p.early = true)
    {id : ℕ} (hid : id ∈ A) :
    frontFiveB p K ⟨d, g', .nothing, some id⟩ = frontFiveB p K ⟨c, g, .nothing, some id⟩ := by
  unfold frontFiveB
  dsimp only
  rw [h.codes, doorB_same h p _ _ _ _ _ hid]
  show (_ && _ && _ && _ && frontPlainB₀ p ⟨d, g', .nothing, some id⟩ &&
    frontPubB p ⟨d, g', .nothing, some id⟩) =
    (_ && _ && _ && _ && frontPlainB₀ p ⟨c, g, .nothing, some id⟩ &&
    frontPubB p ⟨c, g, .nothing, some id⟩)
  rw [frontPlain_same h p he hid, frontPub_same h p he hid]

end Five

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.SameRead.seat
#print axioms ProofFile.Honest.K12.AtFile.frontLS_same
#print axioms ProofFile.Honest.K12.AtFile.beginRunS_same
#print axioms ProofFile.Honest.K12.AtFile.commonB_same
#print axioms ProofFile.Honest.K12.AtFile.cameB_same
#print axioms ProofFile.Honest.K12.AtFile.gpOkS_same
#print axioms ProofFile.Honest.K12.AtFile.labelsOkS_same
#print axioms ProofFile.Honest.K12.AtFile.readPubB_same
#print axioms ProofFile.Honest.K12.AtFile.frontFive_same
#print axioms ProofFile.Honest.K12.AtFile.tsLen_same
#print axioms ProofFile.Honest.K12.AtFile.manyFits_same
