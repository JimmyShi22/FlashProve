-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean: FROM THE THREAD TO THE LIBRARY's "REACHED" OVER
THE SUB-PROTOCOLS UNDER `below`. The library pays facts "at reached states" at `Reach`
(Johnson/Top/H0/Walk/Reach.lean) over the blocks `below b` (Johnson/Desc/Sound/ChainRule.lean): b's
decision behind the test that every word which it is shown is below the field's prime.
`reach_of_made` (Honest/Thread/MadeLaw.lean) gives `Reach` over the bare members. No clause of the
thread speaks of the values that the rounds seen show: so the step from bare to `below` wants a
sentence more. It is the first use of the second family (Honest/Thread/Said.lean): the letter
`SaidOk`: every word that the rounds seen show is below the prime. Its debt `SaidNext` is paid here
ONCE, AT EVERY MEMBER, general in the kind: no kind's authors owe it. Conditional lemmas on our own
definitions and the library's.

  1  `okRounds_append`, `okRounds_sub`, `okRounds_noDigest`, `regroup_mem`   small ones
  2  `SaidOk`, `saidNext_ok`, `saidOk_nil`, `saidOk_append`   THE LETTER; its debt, paid; the seams
  3  `step_below`, `fold_left`, `reach_below_of_fold`   a step; what a fold leaves; the fold
  4  `reach_below`   THE LAW

The one premise on a letter: the words of the thread's stored columns are below the prime
(`T.stored`): true of `Prover.storedWords` by make. A table's columns are so by make (`col_lt`,
Honest/Law/Play.lean).

Credit. The gap, and that the rounds' half follows from the frame's own `play` for every kind, were
found in the work on the lookups' lemmas. The rounds'
half is had here from row 12's `okViewW_of_yields` (Honest/Law/Play.lean).

Limits. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below step_ok_iff groupsAt)
open Johnson.Desc.First.Walk.Tied (Reach StepYes step_less fold_split)

/-! ## 1 Small ones -/

theorem okRounds_append (a b : List Fmt.RoundView) :
    viewWordsBelowPrime ⟨a ++ b, []⟩ = true ↔ viewWordsBelowPrime ⟨a, []⟩ = true ∧ viewWordsBelowPrime ⟨b, []⟩ = true := by
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true, List.all_append, Bool.and_eq_true]

theorem okRounds_sub {R R' : List Fmt.RoundView} (h : viewWordsBelowPrime ⟨R, []⟩ = true) (hs : ∀ r ∈ R', r ∈ R) :
    viewWordsBelowPrime ⟨R', []⟩ = true := by
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true, List.all_eq_true] at h ⊢
  exact fun r hr => h r (hs r hr)

theorem okRounds_noDigest {R : List Fmt.RoundView} (h : viewWordsBelowPrime ⟨R, []⟩ = true) :
    viewWordsBelowPrime ⟨R.map noDigest, []⟩ = true := by
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true, List.all_eq_true] at h ⊢
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
  exact h r' hr'

theorem regroup_mem : ∀ (ns : List Nat) (cols : List OpenedColumn) (x : Nat × List UInt64),
    x ∈ (regroup ns cols).flatMap id → ∃ c ∈ cols, x = (c.2.1, c.2.2)
  | [], _, x, h => by simp [regroup] at h
  | n :: ns, cols, x, h => by
    simp only [regroup, List.flatMap_cons, id, List.mem_append, List.mem_map] at h
    rcases h with ⟨c, hc, rfl⟩ | h
    · exact ⟨c, List.mem_of_mem_take hc, rfl⟩
    · obtain ⟨c, hc, e⟩ := regroup_mem ns _ x h
      exact ⟨c, List.mem_of_mem_drop hc, e⟩

/-! ## 2 The letter -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **EVERY WORD THAT THE ROUNDS SEEN SHOW IS BELOW THE PRIME**: the library's own test on a view's
rounds, at all that the prover's run has seen. The same at every border and all coins. It is a
definition: a filling of the letter `Said`. -/
def SaidOk (_ : Nat) (_ : Coins Bk) (m : Mid W X) : Prop := viewWordsBelowPrime ⟨m.seen, []⟩ = true

/-- **ITS DEBT IS PAID, AT EVERY MEMBER, WHATEVER THE KIND**: what the frame's own `play` lays is
below the prime by make. -/
theorem saidNext_ok (T : Thread Bk S Cl V W X Pb) (b : Nat) : SaidNext T SaidOk b := by
  intro blk _ k s m E ds y cols _ hS hd hM
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  have hdl : l.map (·.decl) = blk.rounds := by
    rw [steps_decl hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h1 := okViewW_of_yields _ _ _ _ (play_yields _ _ _ _ _ hy)
    (by rw [hdl]; exact drawsFit_bare _ _ hd) okViewW_nil
  show viewWordsBelowPrime ⟨y.2.seen, []⟩ = true
  rw [(play_mid _ _ _ _ _ hy).2.2]
  exact (okRounds_append _ _).2 ⟨hS, h1⟩

/-- For the seams: a stand that has seen nothing. -/
theorem saidOk_nil {b : Nat} {k : Coins Bk} {m : Mid W X} (h : m.seen = []) :
    SaidOk b k m := by
  show viewWordsBelowPrime ⟨m.seen, []⟩ = true
  rw [h]
  rfl

/-- For the door: a stand that has seen what two stands have seen. -/
theorem saidOk_append {W' X' W'' X'' : Type} {b b' b'' : Nat} {k : Coins Bk} {m : Mid W X}
    {m' : Mid W' X'} {m'' : Mid W'' X''} (h : m.seen = m'.seen ++ m''.seen)
    (h' : SaidOk b' k m') (h'' : SaidOk b'' k m'') : SaidOk b k m := by
  show viewWordsBelowPrime ⟨m.seen, []⟩ = true
  rw [h]
  exact (okRounds_append _ _).2 ⟨h', h''⟩

end

/-! ## 3 A step; what a fold leaves; the fold -/

section
variable {S Cl P : Type}

/-- A step's yes on words below the prime is a yes of the same step under `below`. -/
theorem step_below {ft : Nat} {b : Block S Cl} {s s' : S} {R : List Fmt.RoundView} {c : List OpenedColumn}
    {n : Nat} (h : b.step ft s R c = .ok (s', n)) (hR : viewWordsBelowPrime ⟨R, []⟩ = true)
    (hc : ∀ x ∈ c, ∀ a ∈ x.2.2, a < fieldPrimeWord) : (below b).step ft s R c = .ok (s', n) := by
  obtain ⟨h1, h2, h3, h4⟩ := (step_ok_iff ft b s s' R c n).1 h
  refine (step_ok_iff ft (below b) s s' R c n).2 ⟨h1, h2, h3, ?_⟩
  have hok : viewWordsBelowPrime ⟨R.map noDigest,
                  ((groupsAt ft b R (c.take n)).flatMap id).map fun x => (0, x.1, x.2)⟩ = true := by
    refine (okViewW_split _ _).2 ⟨okRounds_noDigest hR, ?_⟩
    intro x hx a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨z, hz, rfl⟩ := regroup_mem _ _ y hy
    exact hc z (List.mem_of_mem_take hz) a ha
  show (if viewWordsBelowPrime ⟨R.map noDigest,
                  ((groupsAt ft b R (c.take n)).flatMap id).map fun x => (0, x.1, x.2)⟩ then
    b.decide s (R.map noDigest) (groupsAt ft b R (c.take n))
    else .error "a word is not below the prime") = .ok s'
  rw [if_pos hok]
  exact h4

/-- What a fold leaves over is of what it was handed. -/
theorem fold_left (ft : Nat) : ∀ (l : List (Block S Cl)) (s t : S) (rs r : List Fmt.RoundView)
    (cols c : List OpenedColumn), foldBlocks ft l s rs cols = .ok (t, r, c) →
    (∀ x ∈ r, x ∈ rs) ∧ ∀ x ∈ c, x ∈ cols
  | [], s, t, rs, r, cols, c, h => by
    unfold foldBlocks at h
    injection h with h
    obtain ⟨-, h2⟩ := Prod.mk.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  | b :: l, s, t, rs, r, cols, c, h => by
    obtain ⟨s', k, -, -, h'⟩ := foldBlocks_cons ft b l s rs cols _ h
    obtain ⟨a1, a2⟩ := fold_left ft l s' t _ r _ c h'
    exact ⟨fun x hx => List.mem_of_mem_drop (a1 x hx), fun x hx => List.mem_of_mem_drop (a2 x hx)⟩

/-- **A fold's yes on words below the prime reaches its state by the steps under `below`.** After
the library's `reach_of_fold`. -/
theorem reach_below_of_fold {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (hR : viewWordsBelowPrime ⟨rs, []⟩ = true)
    (hc : ∀ x ∈ cols, ∀ a ∈ x.2.2, a < fieldPrimeWord) :
    ∀ (k : Nat), k ≤ bs.length → ∀ (s : S) (r : List Fmt.RoundView) (c : List OpenedColumn),
    foldBlocks ft (bs.take k) (start z) rs cols = .ok (s, r, c) →
    Reach ft (bs.map below) start k (z, s)
  | 0, _, s, r, c, h => by
    rw [List.take_zero] at h
    unfold foldBlocks at h
    injection h with h
    obtain ⟨rfl, _⟩ := Prod.mk.inj h
    exact Reach.zero z
  | k + 1, hk, s, r, c, h => by
    have hb : bs[k]? = some bs[k] := List.getElem?_eq_getElem hk
    rw [List.take_add_one, hb] at h
    obtain ⟨t, r₁, c₁, h1, h2⟩ := fold_split ft _ _ _ _ _ _ h
    obtain ⟨s', n, hl, hs, h3⟩ := foldBlocks_cons ft bs[k] [] t r₁ c₁ _ h2
    unfold foldBlocks at h3
    injection h3 with h3
    obtain ⟨rfl, _⟩ := Prod.mk.inj h3
    obtain ⟨a1, a2⟩ := fold_left ft _ _ _ _ _ _ _ h1
    have hb' : (bs.map below)[k]? = some (below bs[k]) := by
      rw [List.getElem?_map, hb]
      rfl
    exact Reach.succ (reach_below_of_fold hR hc k (Nat.le_of_lt hk) t r₁ c₁ h1) hb'
      ⟨_, _, hl, step_below (step_less hs)
        (okRounds_sub hR fun x hx => a1 x (List.mem_of_mem_take hx))
        fun x hx => hc x (a2 x (List.mem_of_mem_take hx))⟩

end

/-! ## 4 The law -/

/-- **FROM THE THREAD AND `SaidOk` TO THE LIBRARY's "REACHED" OVER THE BLOCKS UNDER `below`.** hb,
h0: as in `reach_of_made`. hst: the one premise on a letter. A conditional lemma. It is none of the
library's goals. -/
theorem reach_below {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {P : Type}
    (start : P → S) (z : P) {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (hb : b ≤ T.bs.length)
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = start z)
    (hst : ∀ w i x u, T.stored w i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (h : ThrS T SaidOk b k s m E) : Reach T.ft (T.bs.map below) start b (z, s) := by
  obtain ⟨hT, hS⟩ := h
  unfold Thr Thread.Hand Thread.Made at hT
  obtain ⟨⟨hsto, -⟩, -, -, -, ⟨-, -, -, -, s₀, c₀, hbeg, hcols, hf⟩, -, -⟩ := hT
  rw [h0 s₀ hbeg] at hf
  have hE : ∀ i x u, E.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord := fun i x u hu => by
    rw [hsto i x] at hu
    exact hst _ i x u hu
  unfold Thread.colsTo at hcols
  have hc := fillCols_words _ _ _ (readsOf_words T.chain T.ft E.stored E.tree hE _ _)
    (fun x hx => by cases hx) hcols
  exact reach_below_of_fold (okRounds_sub hS fun x hx => List.mem_of_mem_drop hx) hc b hb s _ _ hf

end ProofFile.Honest

#print axioms ProofFile.Honest.okRounds_append
#print axioms ProofFile.Honest.okRounds_sub
#print axioms ProofFile.Honest.okRounds_noDigest
#print axioms ProofFile.Honest.regroup_mem
#print axioms ProofFile.Honest.saidNext_ok
#print axioms ProofFile.Honest.saidOk_nil
#print axioms ProofFile.Honest.saidOk_append
#print axioms ProofFile.Honest.step_below
#print axioms ProofFile.Honest.fold_left
#print axioms ProofFile.Honest.reach_below_of_fold
#print axioms ProofFile.Honest.reach_below
