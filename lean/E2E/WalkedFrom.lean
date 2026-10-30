-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WalkedFrom.lean: a letter for a thread (the parameter `Said` of Thread/Said.lean): the state is one that the
thread's own steps reach from a state that begins the chain.

Why. `PlayedTo` speaks of the frame's `play`, which lays no columns, so it stands only where the field `opened` is
none. A guarded half errs there. This letter follows `Thread.Moved` and `Mid.took` instead, so it holds of the
walk's states, with the field as the walk lays it, and it is the same term on each of the three chains: only the
predicate `Begun` on the first state differs.

Main names.
  `WalkedFrom`: the letter: a state that begins, and what one sub-protocol's `Moved` makes of a state that has the
    letter and at which the thread stands.
  `saidNext_walked`: `SaidNext` for it, at every sub-protocol, with no premise.
  `walked_begun`: at border 0 the letter says `Begun`.
  `walked_unique`, `oneStand_walked`: two states with the letter at one border, input and challenges heard are one,
    where `Begun` is one-valued and a sub-protocol's columns do not hang on the set of tables: the premise `OneColumns`.
  `oneColumns_of`: that premise, where every source that a round opens is at hand behind it, with the depth that the
    round declares, and no tree taken over bears an own tree's name.
  `walked_least`: it is the least letter that begins at `Begun` and is carried: whatever any such letter says of a
    state, this one gives. So it loses nothing, and by itself it pays nothing.

What stays open. `oneColumns_of` takes its three premises at a thread; they are shown of no thread here. That a state has the letter says nothing on whether a run reaches it: that is the caller's, by the
thread's statements at each border. Nothing here reads the field. What the letter gives at a border of the thread's
own sentences, the field among them, is for laws to be stated on it.

The letter names a run's coins as a letter: `Begun` and the carried `Thr` may read them. No law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.OneState
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The state is one that the thread's steps reach from a state that begins the chain.** -/
inductive WalkedFrom (T : Thread Bk S Cl V W X Pb) (Begun : Coins Bk → Mid W X → Prop) :
    Nat → Coins Bk → Mid W X → Prop
  | begun {k : Coins Bk} {m : Mid W X} (h : Begun k m) : WalkedFrom T Begun 0 k m
  | next {b : Nat} {blk : VerifiableInference.Desc.Block S Cl} {k : Coins Bk} {s : S}
      {m : Mid W X} {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X}
      {cols : List VerifiableInference.Desc.OpenedColumn}
      (h : WalkedFrom T Begun b k m) (hblk : T.bs[b]? = some blk) (hT : Thr T b k s m E)
      (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols) :
      WalkedFrom T Begun (b + 1) k (y.2.took cols)

variable (T : Thread Bk S Cl V W X Pb) (Begun : Coins Bk → Mid W X → Prop)

/-- **The letter is carried over every sub-protocol**: by its second constructor. -/
theorem saidNext_walked (b : Nat) : SaidNext T (WalkedFrom T Begun) b :=
  fun _ hblk _ _ _ _ _ _ _ hT hS hd hM => .next hS hblk hT hd hM

variable {T Begun}

/-- **At border 0 the letter says that the state begins the chain.** -/
theorem walked_begun {k : Coins Bk} {m : Mid W X} (h : WalkedFrom T Begun 0 k m) : Begun k m := by
  cases h with
  | begun h => exact h

/-- **The least letter that begins at `Begun` and is carried.** -/
theorem walked_least {Said : Nat → Coins Bk → Mid W X → Prop} (h0 : ∀ k m, Begun k m → Said 0 k m)
    (hN : ∀ b, SaidNext T Said b) {b : Nat} {k : Coins Bk} {m : Mid W X}
    (h : WalkedFrom T Begun b k m) : Said b k m := by
  induction h with
  | begun h => exact h0 _ _ h
  | next _ hblk hT hd hM ih => exact hN _ _ hblk _ _ _ _ _ _ _ hT ih hd hM

/-- **One sub-protocol's columns do not hang on the set of tables** at one state of the run. A definition, meant as a
hypothesis. -/
def OneColumns (T : Thread Bk S Cl V W X Pb) (n : Nat) : Prop :=
  ∀ b, b < n → ∀ blk, T.bs[b]? = some blk → ∀ k s s' m E E' ds y cols cols',
    Thr T b k s m E → Thr T b k s' m E' → T.Moved blk k m E ds y cols →
    T.Moved blk k m E' ds y cols' → cols = cols'

/-- **Two states with the letter at one border, one input and one list of challenges heard are one.** -/
theorem walked_unique {n : Nat} (hB : ∀ k m m', Begun k m → Begun k m' →
      m.st.input = m'.st.input → m.st.heard = m'.st.heard → m = m')
    (hC : OneColumns T n) {b : Nat} {k : Coins Bk} {m m' : Mid W X} (hb : b ≤ n)
    (h : WalkedFrom T Begun b k m) (h' : WalkedFrom T Begun b k m')
    (hi : m.st.input = m'.st.input) (hh : m.st.heard = m'.st.heard) : m = m' := by
  induction h generalizing m' with
  | begun h₀ =>
    cases h' with
    | begun h₁ => exact hB _ _ _ h₀ h₁ hi hh
  | @next b blk k s m E ds y cols _ hblk hT hd hM ih =>
    cases h' with
    | @next _ blk' _ s' m' E' ds' y' cols' h₂ hblk' hT' hd' hM' =>
      have eb : blk = blk' := Option.some.inj (hblk.symm.trans hblk')
      subst eb
      obtain ⟨⟨l, hl, hp⟩, hf⟩ := hM
      obtain ⟨⟨l', hl', hp'⟩, hf'⟩ := hM'
      have ei : m.st.input = m'.st.input := by
        have a := (play_mid _ _ _ _ _ hp).1
        have a' := (play_mid _ _ _ _ _ hp').1
        exact a.symm.trans (hi.trans a')
      have eh : m.st.heard ++ ds = m'.st.heard ++ ds' := by
        have a := play_heard _ _ _ _ _ hp
        have a' := play_heard _ _ _ _ _ hp'
        exact a.symm.trans (hh.trans a')
      have el : ds.length = ds'.length :=
        (drawsFit_length _ _ hd).trans (drawsFit_length _ _ hd').symm
      obtain ⟨e₁, e₂⟩ := List.append_inj' eh el
      have em : m = m' := ih (by omega) h₂ ei e₁
      subst em
      subst e₂
      have e₃ : l = l' := by
        rw [hl] at hl'
        exact Except.ok.inj hl'
      subst e₃
      have e₄ : y = y' := by
        rw [hp] at hp'
        exact Except.ok.inj hp'
      subst e₄
      have e₅ : cols = cols' :=
        hC _ (by omega) _ hblk _ _ _ _ _ _ _ _ _ _ hT hT' ⟨⟨l, hl, hp⟩, hf⟩ ⟨⟨l, hl', hp'⟩, hf'⟩
      rw [e₅]

section Columns
variable {T : Thread Bk S Cl V W X Pb}

/-- What stood at hand before the rounds stands as it stood. -/
theorem tree_add_old {b : Nat} {E : Env} {σ : Fmt.TreeSource} (hTaken : ∀ n, Fmt.TreeSource.own n ∉ T.taken)
    (hm : σ ∈ T.hand b) (hs : E.sent = treesTo T.bs b) (ps : List Played) :
    (E.add ps).tree σ = E.tree σ := by
  cases σ with
  | own n =>
    have hn : n < E.sent := by
      rcases List.mem_append.1 hm with h | h
      · exact absurd h (hTaken n)
      · obtain ⟨j, hj, e⟩ := List.mem_map.1 h
        cases e
        rw [hs]
        exact List.mem_range.1 hj
    show (if n < E.sent then E.tree (.own n) else _) = _
    rw [if_pos hn]
  | taken ch j => rfl

/-- What the rounds brought is the same at two sets of tables that have sent as many. -/
theorem tree_add_new {b : Nat} {E E' : Env} {σ : Fmt.TreeSource} (hnot : σ ∉ T.hand b)
    (hin : σ ∈ T.hand (b + 1)) (hs : E.sent = treesTo T.bs b) (hs' : E'.sent = treesTo T.bs b)
    (ps : List Played) : (E.add ps).tree σ = (E'.add ps).tree σ := by
  cases σ with
  | own n =>
    have hn : ¬ n < treesTo T.bs b := fun h =>
      hnot (List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 h, rfl⟩))
    show (if n < E.sent then E.tree (.own n) else ((tablesOf ps)[n - E.sent]?).bind id) =
      (if n < E'.sent then E'.tree (.own n) else ((tablesOf ps)[n - E'.sent]?).bind id)
    rw [hs, hs', if_neg hn, if_neg hn]
  | taken ch j =>
    rcases List.mem_append.1 hin with h | h
    · exact absurd (List.mem_append_left _ h) hnot
    · obtain ⟨_, _, e⟩ := List.mem_map.1 h
      cases e

/-- **A sub-protocol's columns do not hang on the set of tables**, where every source that a round opens is at hand
behind it with the depth that the round declares, and no tree taken over bears an own tree's name. -/
theorem oneColumns_of {n : Nat} (hTaken : ∀ j, Fmt.TreeSource.own j ∉ T.taken)
    (hO : ∀ b, b < n → T.opensAvailable (b + 1) = true)
    (hD : ∀ b, b < n → ∀ k m, DepthsAt T (b + 1) k m) : OneColumns T n := by
  intro b hb blk hblk k s s' m E E' ds y cols cols' hT hT' hM hM'
  obtain ⟨hH, -, -, -, hMd, -, -⟩ := hT
  obtain ⟨hH', -, -, -, hMd', -, -⟩ := hT'
  have hs : E.sent = treesTo T.bs b := hMd.2.2.1
  have hs' : E'.sent = treesTo T.bs b := hMd'.2.2.1
  have hst : (E.add y.1).stored = (E'.add y.1).stored :=
    funext fun i => funext fun x => (hH.1 i x).trans (hH'.1 i x).symm
  have hdecl : ∀ d ∈ blk.rounds, d ∈ declsTo T.bs (b + 1) := by
    intro d hd
    rw [declsTo_succ hblk]
    exact List.mem_append_right _ hd
  have ht : ∀ d ∈ blk.rounds, ∀ o ∈ d.opens,
      ((E.add y.1).tree o.2).map (·.1) = ((E'.add y.1).tree o.2).map (·.1) ∧
        ∀ x, x < 2 ^ o.1.a →
          ((E.add y.1).tree o.2).map (·.2.col x) = ((E'.add y.1).tree o.2).map (·.2.col x) := by
    intro d hdm o hom
    have hσ : o.2 ∈ T.hand (b + 1) :=
      of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 (hO b hb) d (hdecl d hdm)) o hom)
    by_cases hold : o.2 ∈ T.hand b
    · rw [tree_add_old hTaken hold hs, tree_add_old hTaken hold hs']
      obtain ⟨pt, e, p, -⟩ := T.handAt_elim (hH.2 o.2 hold)
      obtain ⟨pt', e', p', -⟩ := T.handAt_elim (hH'.2 o.2 hold)
      obtain ⟨qt, f, c⟩ := T.col_of_handAt (hH.2 o.2 hold)
      obtain ⟨qt', f', c'⟩ := T.col_of_handAt (hH'.2 o.2 hold)
      obtain rfl : pt = qt := Option.some.inj (e.symm.trans f)
      obtain rfl : pt' = qt' := Option.some.inj (e'.symm.trans f')
      refine ⟨?_, fun x hx => ?_⟩
      · rw [e, e']
        show some pt.1 = some pt'.1
        rw [p, p']
      · have hx' : x < 2 ^ (T.tableAt o.2 k m).2.logLength := by
          rw [hD b hb k m d (hdecl d hdm) o hom]
          exact hx
        rw [e, e']
        show some (pt.2.col x) = some (pt'.2.col x)
        rw [c x hx', c' x hx']
    · rw [tree_add_new hold hσ hs hs']
      exact ⟨rfl, fun _ _ => rfl⟩
  have hr := readsOf_congr T.chain T.ft (E'.add y.1).stored blk.rounds ds ht
  have a := hM.2
  have a' := hM'.2
  rw [hst, hr, a'] at a
  exact (Except.ok.inj a).symm

end Columns

/-- **`OneStand` for the letter.** Then `oneState_at` gives `OneState`. -/
theorem oneStand_walked {n : Nat} (hB : ∀ k m m', Begun k m → Begun k m' →
      m.st.input = m'.st.input → m.st.heard = m'.st.heard → m = m')
    (hC : OneColumns T n) : OneStand (WalkedFrom T Begun) n :=
  fun _ _ _ h h' hi hh => walked_unique hB hC (Nat.le_refl n) h h' hi hh

end ProofFile.Honest

#print axioms ProofFile.Honest.oneColumns_of
#print axioms ProofFile.Honest.walked_unique
#print axioms ProofFile.Honest.oneStand_walked
#print axioms ProofFile.Honest.walked_least
#print axioms ProofFile.Honest.saidNext_walked
#print axioms ProofFile.Honest.walked_begun
