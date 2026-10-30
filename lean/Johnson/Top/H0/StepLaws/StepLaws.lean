-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/StepLaws/StepLaws.lean: what Block.step's yes says, of any block, and through
three of the four ways in which Johnson/Desc/Block.lean makes a block out of blocks: liftPart,
inside,
andThen. General in the block, its record and its type of claims. The law for the fourth way,
Block.lift, is not stated here.
  step_iff        Block.step's yes, both ways: the rounds fit; the view's next columns are, in key,
                  position and width, those that are read; decide says yes at just the groups cut of
                  these; as many columns are taken. ALL THE OTHER LAWS STAND ON THIS ONE AND ON THE
                  MAKER's decide: if Block.step gains a test, Fits gains a clause and step_iff's
                  proof
                  a line.
  liftPart_step   a block that is typed at a part which is there only at times: its yes at t says:
  the
                  part is there, the block says yes at it, and the record behind is set t of the
                  block's. Both ways.
  inside_step     the like for a record that is born and dies inside. Both ways.
  andThen_step    two blocks as one: the first's yes at its rounds and the view's next columns, then
                  the second's at the rounds and columns behind; the columns taken add up. Both
                  ways.
  andThen_step_noRound   where the second block has no round: the first's yes at all the rounds,
  then
                  the second's decide at the record between, on no round and no column.
On the way: roundsFit_append, groupsOf_app, regroup_append, regroup_take, cols_cut, want_andThen,
shown_andThen, length_shown. roundsFit's clauses are used round by round alone (roundsFit_append is
by
simp over its own equations).
No Mathlib. Nothing on soundness.
-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S T Cl : Type}

/-! ## Except -/

theorem Except.map_eq_ok {ε α β : Type} (f : α → β) (x : Except ε α) (y : β) : x.map f = .ok y ↔ ∃
    a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => simp [Except.map]
  | ok a => simp [Except.map]

theorem Except.bind_eq_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (y : β) : x.bind f =
    .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Except.bind]
  | ok a => simp [Except.bind]

theorem named_eq_ok {α : Type} (n : String) (x : Option α) (a : α) : named n x = .ok a ↔ x = some a
    := by
  cases x with
  | none => simp [named]
  | some b => simp [named]

/-! ## Block.step's yes -/

/-- Key, position and width of the columns that a block reads at these rounds, in a row. -/
def Block.want (firstTree : Nat) (b : Block S Cl) (rs : List Fmt.RoundView) : List (Nat × Nat × Nat) :=
  (groupsOf firstTree b.rounds (rs.map (·.drawn))).flatMap id

/-- The groups of columns that Block.step shows decide. -/
def Block.shown (firstTree : Nat) (b : Block S Cl) (rs : List Fmt.RoundView) (cols : List OpenedColumn) : List (List
                    (Nat × List UInt64)) :=
  regroup ((groupsOf firstTree b.rounds (rs.map (·.drawn))).map (·.length)) (cols.take (b.want
      firstTree rs).length)

/-- Block.step's own tests. -/
def Block.Fits (firstTree : Nat) (b : Block S Cl) (rs : List Fmt.RoundView) (cols : List OpenedColumn) : Prop :=
  roundsFit b.rounds rs = true ∧
    ((cols.take (b.want firstTree rs).length).map (fun c => (c.1, c.2.1, c.2.2.length)) == b.want
        firstTree rs) = true

theorem step_iff (firstTree : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : Nat) :
    b.step firstTree s rs cols = .ok (s', k) ↔
      b.Fits firstTree rs cols ∧ b.decide s (rs.map noDigest) (b.shown firstTree rs cols) = .ok s' ∧
          k = (b.want firstTree rs).length := by
  constructor
  · intro h
    unfold Block.step at h
    dsimp only [bind, Except.bind, need, pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    rename_i u1 hu1
    split at h
    · exact absurd h (by simp)
    rename_i u2 hu2
    split at h
    · exact absurd h (by simp)
    rename_i v hv
    have hp := Except.ok.inj h
    have hvs : v = s' := (Prod.mk.inj hp).1
    have hk := (Prod.mk.inj hp).2
    subst hvs
    refine ⟨⟨?_, ?_⟩, hv, hk.symm⟩
    · split at hu1
      · assumption
      · exact absurd hu1 (by simp)
    · split at hu2
      · assumption
      · exact absurd hu2 (by simp)
  · rintro ⟨⟨h1, h2⟩, h3, rfl⟩
    unfold Block.want at h2
    unfold Block.shown Block.want at h3
    unfold Block.step Block.want
    dsimp only [bind, Except.bind, need, pure, Except.pure]
    rw [if_pos h1]
    dsimp only
    rw [if_pos h2]
    dsimp only
    rw [h3]

/-! ## liftPart · inside -/

theorem liftPart_step (get? : T → Option S) (set : T → S → T) (b : Block S Cl) (firstTree : Nat) (t
    t' : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    (b.liftPart get? set).step firstTree t rs cols = .ok (t', k) ↔
      ∃ p p', get? t = some p ∧ b.step firstTree p rs cols = .ok (p', k) ∧ t' = set t p' := by
  constructor
  · intro h
    obtain ⟨hf, hd, hk⟩ := (step_iff _ _ _ _ _ _ _).1 h
    obtain ⟨p, hp, hd2⟩ := (Except.bind_eq_ok _ _ _).1 hd
    obtain ⟨p', hp', he⟩ := (Except.map_eq_ok _ _ _).1 hd2
    exact ⟨p, p', (named_eq_ok _ _ _).1 hp, (step_iff _ _ _ _ _ _ _).2 ⟨hf, hp', hk⟩, he.symm⟩
  · rintro ⟨p, p', hg, h, rfl⟩
    obtain ⟨hf, hd, hk⟩ := (step_iff _ _ _ _ _ _ _).1 h
    exact (step_iff _ _ _ _ _ _ _).2 ⟨hf, (Except.bind_eq_ok _ _ _).2 ⟨p, (named_eq_ok _ _ _).2 hg,
        (Except.map_eq_ok _ _ _).2 ⟨p', hd, rfl⟩⟩, hk⟩

theorem inside_step (enter : S → Except String T) (b : Block T Cl) (leave : S → T → Except String S)
    (firstTree : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    (Block.inside enter b leave).step firstTree s rs cols = .ok (s', k) ↔
      ∃ t t', enter s = .ok t ∧ b.step firstTree t rs cols = .ok (t', k) ∧ leave s t' = .ok s' := by
  constructor
  · intro h
    obtain ⟨hf, hd, hk⟩ := (step_iff _ _ _ _ _ _ _).1 h
    obtain ⟨t, ht, hd2⟩ := (Except.bind_eq_ok _ _ _).1 hd
    obtain ⟨t', ht', hl⟩ := (Except.bind_eq_ok _ _ _).1 hd2
    exact ⟨t, t', ht, (step_iff _ _ _ _ _ _ _).2 ⟨hf, ht', hk⟩, hl⟩
  · rintro ⟨t, t', he, h, hl⟩
    obtain ⟨hf, hd, hk⟩ := (step_iff _ _ _ _ _ _ _).1 h
    exact (step_iff _ _ _ _ _ _ _).2 ⟨hf, (Except.bind_eq_ok _ _ _).2 ⟨t, he, (Except.bind_eq_ok _ _
        _).2 ⟨t', hd, hl⟩⟩, hk⟩

/-! ## andThen: how rounds, groups and columns are cut -/

theorem roundsFit_length : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
    rs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [roundsFit] at h
  | _ :: _, [], h => by simp [roundsFit] at h
  | d :: ds, r :: rs, h => by
    simp only [roundsFit, Bool.and_eq_true] at h
    simp only [List.length_cons, roundsFit_length ds rs h.2]

theorem roundsFit_append : ∀ (A B : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit (A ++ B) rs = true ↔ roundsFit A (rs.take A.length) = true ∧ roundsFit B (rs.drop
        A.length) = true
  | [], B, rs => by simp [roundsFit]
  | d :: A, B, [] => by simp [roundsFit]
  | d :: A, B, r :: rs => by
    simp only [List.cons_append, roundsFit, List.length_cons, List.take_succ_cons,
        List.drop_succ_cons, Bool.and_eq_true,
      roundsFit_append A B rs, and_assoc]

theorem groupsOf_nil_right (firstTree : Nat) : ∀ ds : List Fmt.DeclaredRound, groupsOf firstTree ds [] =
    []
  | [] => rfl
  | _ :: _ => rfl

theorem groupsOf_app (firstTree : Nat) : ∀ (A B : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    groupsOf firstTree (A ++ B) Rs = groupsOf firstTree A (Rs.take A.length) ++ groupsOf firstTree B
        (Rs.drop A.length)
  | [], B, Rs => by simp [groupsOf]
  | d :: A, B, [] => by simp [groupsOf_nil_right]
  | d :: A, B, R :: Rs => by
    simp only [List.cons_append, groupsOf, List.length_cons, List.take_succ_cons,
        List.drop_succ_cons, groupsOf_app firstTree A B Rs,
      List.append_assoc]

theorem foldl_openings : ∀ (A : List Fmt.DeclaredRound) (n : Nat),
    A.foldl (fun n r => n + r.stored.length + r.opens.length) n = n + A.foldl (fun n r => n +
        r.stored.length + r.opens.length) 0
  | [], n => by simp
  | d :: A, n => by
    simp only [List.foldl_cons]
    rw [foldl_openings A (n + d.stored.length + d.opens.length), foldl_openings A (0 +
        d.stored.length + d.opens.length)]
    omega

theorem length_groupsOf (firstTree : Nat) : ∀ (A : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    Rs.length = A.length →
    (groupsOf firstTree A Rs).length = A.foldl (fun n r => n + r.stored.length + r.opens.length) 0
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | d :: A, R :: Rs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [groupsOf, List.length_append, List.length_map, List.foldl_cons, length_groupsOf
        firstTree A Rs h]
    rw [foldl_openings A (0 + d.stored.length + d.opens.length)]
    omega

theorem length_regroup : ∀ (L : List Nat) (cols : List OpenedColumn), (regroup L cols).length = L.length
  | [], _ => rfl
  | n :: L, cols => by simp only [regroup, List.length_cons, length_regroup L]

theorem regroup_append : ∀ (L M : List Nat) (cols : List OpenedColumn), regroup (L ++ M) cols = regroup L
    cols ++ regroup M (cols.drop L.sum)
  | [], M, cols => by simp [regroup]
  | n :: L, M, cols => by
    simp only [List.cons_append, regroup, regroup_append L M (cols.drop n), List.sum_cons,
        List.drop_drop]

theorem regroup_take : ∀ (L : List Nat) (cols : List OpenedColumn) (m : Nat), L.sum ≤ m → regroup L
    (cols.take m) = regroup L cols
  | [], _, _, _ => rfl
  | n :: L, cols, m, h => by
    simp only [List.sum_cons] at h
    simp only [regroup, List.take_take, List.drop_take]
    rw [regroup_take L (cols.drop n) (m - n) (by omega), Nat.min_eq_left (by omega)]

theorem length_flatMap_id (G : List (List (Nat × Nat × Nat))) : (G.flatMap id).length = (G.map
    (·.length)).sum := by
  induction G with
  | nil => rfl
  | cons g G ih => simp only [List.flatMap_cons, id, List.length_append, List.map_cons,
      List.sum_cons, ih]

theorem cols_cut (W1 W2 : List (Nat × Nat × Nat)) (cols : List OpenedColumn) :
    ((cols.take (W1 ++ W2).length).map (fun c => (c.1, c.2.1, c.2.2.length)) == W1 ++ W2) = true ↔
      ((cols.take W1.length).map (fun c => (c.1, c.2.1, c.2.2.length)) == W1) = true ∧
        (((cols.drop W1.length).take W2.length).map (fun c => (c.1, c.2.1, c.2.2.length)) == W2) =
            true := by
  simp only [beq_iff_eq, List.length_append, List.take_add, List.map_append]
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop] at hl
    exact List.append_inj h (by simp only [List.length_map, List.length_take]; omega)
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem groups_andThen (name : String) (p q : Block S Cl) (firstTree : Nat) (rs : List Fmt.RoundView) :
    groupsOf firstTree (p.andThen name q).rounds (rs.map (·.drawn)) =
      groupsOf firstTree p.rounds ((rs.take p.rounds.length).map (·.drawn)) ++ groupsOf firstTree
          q.rounds ((rs.drop p.rounds.length).map (·.drawn)) := by
  show groupsOf firstTree (p.rounds ++ q.rounds) (rs.map (·.drawn)) = _
  rw [groupsOf_app, List.map_take, List.map_drop]

theorem want_andThen (name : String) (p q : Block S Cl) (firstTree : Nat) (rs : List Fmt.RoundView) :
    (p.andThen name q).want firstTree rs = p.want firstTree (rs.take p.rounds.length) ++ q.want
        firstTree (rs.drop p.rounds.length) := by
  unfold Block.want
  rw [groups_andThen, List.flatMap_append]

theorem shown_andThen (name : String) (p q : Block S Cl) (firstTree : Nat) (rs : List Fmt.RoundView) (cols
           : List OpenedColumn) :
    (p.andThen name q).shown firstTree rs cols =
      p.shown firstTree (rs.take p.rounds.length) cols ++
        q.shown firstTree (rs.drop p.rounds.length) (cols.drop (p.want firstTree (rs.take
            p.rounds.length)).length) := by
  have hs : ((groupsOf firstTree p.rounds ((rs.take p.rounds.length).map (·.drawn))).map
      (·.length)).sum =
      (p.want firstTree (rs.take p.rounds.length)).length := (length_flatMap_id _).symm
  unfold Block.shown
  rw [want_andThen, groups_andThen, List.map_append, regroup_append, List.length_append, hs,
    regroup_take _ cols _ (by rw [hs]; omega), regroup_take _ cols _ (by rw [hs]; omega),
        List.drop_take, Nat.add_sub_cancel_left]

theorem length_shown (p : Block S Cl) (firstTree : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h :
                    roundsFit p.rounds rs = true) :
    (p.shown firstTree rs cols).length = p.openings := by
  unfold Block.shown Block.openings
  rw [length_regroup, List.length_map, length_groupsOf firstTree p.rounds _ (by rw [List.length_map,
      roundsFit_length _ _ h])]

/-- **Two blocks as one.** -/
theorem andThen_step (name : String) (p q : Block S Cl) (firstTree : Nat) (s s'' : S) (rs : List
    Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    (p.andThen name q).step firstTree s rs cols = .ok (s'', k) ↔
      ∃ s' k1 k2, p.step firstTree s (rs.take p.rounds.length) cols = .ok (s', k1) ∧
        q.step firstTree s' (rs.drop p.rounds.length) (cols.drop k1) = .ok (s'', k2) ∧ k = k1 + k2
            := by
  constructor
  · intro h
    obtain ⟨⟨hf, hc⟩, hd, hk⟩ := (step_iff _ _ _ _ _ _ _).1 h
    have hf' := (roundsFit_append p.rounds q.rounds rs).1 hf
    rw [want_andThen] at hc hk
    have hc' := (cols_cut _ _ cols).1 hc
    obtain ⟨s', hp, hq⟩ := (Except.bind_eq_ok _ _ _).1 hd
    rw [shown_andThen, List.take_left' (length_shown p firstTree _ cols hf'.1),
      ← List.map_take] at hp
    rw [shown_andThen, List.drop_left' (length_shown p firstTree _ cols hf'.1),
      ← List.map_drop] at hq
    exact ⟨s', _, _, (step_iff _ _ _ _ _ _ _).2 ⟨⟨hf'.1, hc'.1⟩, hp, rfl⟩, (step_iff _ _ _ _ _ _
        _).2 ⟨⟨hf'.2, hc'.2⟩, hq, rfl⟩,
      by rw [hk, List.length_append]⟩
  · rintro ⟨s', k1, k2, h1, h2, rfl⟩
    obtain ⟨⟨hf1, hc1⟩, hd1, rfl⟩ := (step_iff _ _ _ _ _ _ _).1 h1
    obtain ⟨⟨hf2, hc2⟩, hd2, rfl⟩ := (step_iff _ _ _ _ _ _ _).1 h2
    refine (step_iff _ _ _ _ _ _ _).2 ⟨⟨(roundsFit_append p.rounds q.rounds rs).2 ⟨hf1, hf2⟩, ?_⟩,
        ?_, ?_⟩
    · rw [want_andThen]
      exact (cols_cut _ _ cols).2 ⟨hc1, hc2⟩
    · refine (Except.bind_eq_ok _ _ _).2 ⟨s', ?_, ?_⟩
      · rw [shown_andThen, List.take_left' (length_shown p firstTree _ cols hf1), ← List.map_take]
        exact hd1
      · rw [shown_andThen, List.drop_left' (length_shown p firstTree _ cols hf1), ← List.map_drop]
        exact hd2
    · rw [want_andThen, List.length_append]

/-- The case that a kind's whole place wants: the second block has no round: it reads nothing and
takes no column: its decide is asked at the record between, on no round. -/
theorem andThen_step_noRound (name : String) (p q : Block S Cl) (hq : q.rounds = []) (firstTree :
    Nat) (s s'' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    (p.andThen name q).step firstTree s rs cols = .ok (s'', k) ↔
      ∃ s', p.step firstTree s rs cols = .ok (s', k) ∧ q.decide s' [] [] = .ok s'' := by
  rw [andThen_step]
  constructor
  · rintro ⟨s', k1, k2, h1, h2, rfl⟩
    obtain ⟨⟨hf1, _⟩, _, _⟩ := (step_iff _ _ _ _ _ _ _).1 h1
    obtain ⟨⟨hf2, _⟩, hd2, hk2⟩ := (step_iff _ _ _ _ _ _ _).1 h2
    rw [hq] at hf2
    have hnil : rs.drop p.rounds.length = [] := List.eq_nil_of_length_eq_zero (roundsFit_length _ _
        hf2)
    have htake : rs.take p.rounds.length = rs := by
      have := List.take_append_drop p.rounds.length rs
      rw [hnil, List.append_nil] at this
      exact this
    rw [htake] at h1
    have hk0 : k2 = 0 := by rw [hk2]; simp [Block.want, hq, hnil, groupsOf]
    have hsh : q.shown firstTree (rs.drop p.rounds.length) (cols.drop k1) = [] := by simp
        [Block.shown, hq, hnil, groupsOf, regroup]
    rw [hsh, hnil] at hd2
    subst hk0
    exact ⟨s', h1, hd2⟩
  · rintro ⟨s', h1, h2⟩
    obtain ⟨⟨hf1, _⟩, _, _⟩ := (step_iff _ _ _ _ _ _ _).1 h1
    have hlen := roundsFit_length _ _ hf1
    have htake : rs.take p.rounds.length = rs := by rw [← hlen]; exact List.take_length
    have hnil : rs.drop p.rounds.length = [] := by rw [← hlen]; exact List.drop_length
    refine ⟨s', k, 0, by rw [htake]; exact h1, (step_iff _ _ _ _ _ _ _).2 ⟨⟨by rw [hq, hnil]; rfl,
        by simp [Block.want, hq, hnil, groupsOf]⟩, ?_, by simp [Block.want, hq, hnil, groupsOf]⟩,
        rfl⟩
    have hsh : q.shown firstTree (rs.drop p.rounds.length) (cols.drop k) = [] := by simp
        [Block.shown, hq, hnil, groupsOf, regroup]
    rw [hsh, hnil]
    exact h2

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.step_iff
#print axioms VerifiableInference.Desc.liftPart_step
#print axioms VerifiableInference.Desc.inside_step
#print axioms VerifiableInference.Desc.andThen_step
#print axioms VerifiableInference.Desc.andThen_step_noRound
