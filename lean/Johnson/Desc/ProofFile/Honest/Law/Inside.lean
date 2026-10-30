-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Inside.lean: the invariant's condition at a state inside a
sub-protocol, for one chain, from its start. A list of several parts has no state of the verifier
between two parts: so what can be said before a later part is the state of the run: it is reached,
by `play` over the sub-protocol's first i rounds, from a state at which the invariant before the
sub-protocol holds (`InsideOf`). Where the walk (Honest/Walk.lean) has produced, at or after that
round, a round that a prover's side made, the walk over the rounds before returns, and its own state
of the prover's run is such a state.

What this is. A conditional lemma on this folder's own functions, pointwise. It is none of the
library's goals.

  1  `InsideOf`   the condition
  2  `drawsFit_take`   a list's initial segment
  3  `thread_in_chain`   the lemma

Limits.
  * `InsideOf` is a definition, meant as a hypothesis for whoever uses it. It names a state of the
    verifier, and says nothing of it but the invariant.
  * `thread_in_chain` asks i < the number of b's rounds: after b's last round b is asked, and the
    walk's state is no longer one inside b.
  * `play` is named inside b alone, from the walk's own state before b: there nothing is asked, and
    the state's field `opened` stands still (`walk_in`, Honest/Law/WalkMid.lean).
  * Among the hypotheses that the prose above does not name: `PlaysOn` (Honest/Law/ThreadC.lean) at
    every sub-protocol of pre; `chainStopAt … = none`; `drawsFit`; that `chainSteps` returns; hL.
  * `PlaysOn` is asked at every state that the invariant allows, at every value of the field
    `opened` too: where a sub-protocol of pre has a part that reads the columns and errs at `none`
    (its duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant before it that lets
    `none` through is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ThreadAtChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb : Type}

/-! ## 1 The condition -/

/-- **The state of a run after the first n rounds of the sub-protocol b**: reached by `play` over
the sub-protocol's first n `Step`s from a state at which A holds before b. On a whole run's coins,
the state of the prover's run, and the available tables. A definition, meant as a hypothesis. -/
def InsideOf (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (A : Coins Bk → S → Mid W Y → Env → Prop) (n : Nat) (k : Coins Bk)
    (m : Mid W Y) (E : Env) : Prop :=
  ∃ (s : S) (m₀ : Mid W Y) (E₀ : Env) (l : List (Step W Y)) (ds : List Fmt.Drawn)
    (y : List Played × Mid W Y), A k s m₀ E₀ ∧
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m₀.st.input) [b] hs = .ok l ∧
    drawsFit (b.rounds.take n) ds = true ∧ play (l.take n) ds [] m₀ = .ok y ∧ m = y.2 ∧
    E = E₀.add y.1

/-! ## 2 A list's initial segment -/

theorem drawsFit_take (A : List Fmt.DeclaredRound) (D : List Fmt.Drawn) (i : Nat) (hi : i ≤ A.length)
    (h : drawsFit A D = true) : drawsFit (A.take i) (D.take i) = true := by
  have e : drawsFit (A.take i ++ A.drop i) D = true := by
    rw [List.take_append_drop]
    exact h
  rw [drawsFit_append, Bool.and_eq_true, List.length_take, Nat.min_eq_left hi] at e
  exact e.1

/-! ## 3 The lemma -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **The invariant's condition at a state inside a sub-protocol.** `pre`: the sub-protocols before;
`b`: the sub-protocol, which has a round; `t`: those after it; `i`: how many of b's rounds come
before the state. `y`: the walk after the rounds before the state. The first invariant is asked at
the state as `ChainProgress.start` lays it: m₀ with `some front` in the field `opened`. -/
theorem thread_in_chain (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V)
    (pre : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length)
    (I : Nat → Coins Bk → S → Mid W Y → Env → Prop)
    (hP : ∀ j c, pre[j]? = some c → PlaysOn φ Bk L.chain L.firstTree hs c (I j) (I (j + 1)))
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} (m₀ : Mid W Y) (s₀ : S)
    {front : List OpenedColumn} (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some s₀) front = .ok a)
    (hz : walk L ss ds a = .ok z)
    (hss : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v (pre ++ b :: t) hs = .ok ss)
    (hsee : φ.sees m₀.st.input = v)
    (h0 : I 0 k s₀ { m₀ with opened := some front } (envOf L.stored taken []))
    (hd : drawsFit ((pre ++ b :: t).flatMap (·.rounds)) ds = true)
    (hst : chainStopAt v (pre ++ b :: t) hs m₀.loc ds = none) (i : Nat)
    (hi : i < b.rounds.length)
    (ht : ∃ p ∈ z.laid.drop ((pre.flatMap (·.rounds)).length + i), p.told = true) :
    ∃ y m, walk L (ss.take ((pre.flatMap (·.rounds)).length + i))
        (ds.take ((pre.flatMap (·.rounds)).length + i)) a = .ok y ∧ y.mid = some m ∧
      InsideOf φ Bk L.chain hs b (I pre.length) i k m
        (envOf L.stored taken (z.laid.take ((pre.flatMap (·.rounds)).length + i))) ∧
      m.seen = m₀.seen ++ roundsOf (z.laid.take ((pre.flatMap (·.rounds)).length + i)) := by
  have hp0 := steps_part0 _ _ hss
  have ht' : ∃ p ∈ z.laid.drop (pre.flatMap (·.rounds)).length, p.told = true := by
    obtain ⟨p, hp, e⟩ := ht
    rw [← List.drop_drop] at hp
    exact ⟨p, List.mem_of_mem_drop hp, e⟩
  obtain ⟨y₀, s, mN, w0, l0, q0, -, o0, t0, iN⟩ := thread_chain (φ := φ) (hs := hs) L taken hL k v
    pre b t hb I hP m₀ s₀ ha hz hss hsee h0 hd hst ht'
  have hin := (walk_mid ha w0 q0).1
  have hss' : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v (pre ++ ([b] ++ t)) hs =
      .ok ss := hss
  rw [chainSteps_append] at hss'
  obtain ⟨l₁, hl₁, hss'⟩ := exBind_ok hss'
  obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hss'
  rw [chainSteps_append] at hl₂
  obtain ⟨lb, hlb, hl₂⟩ := exBind_ok hl₂
  obtain ⟨lt, hlt, rfl⟩ := exMap_ok hl₂
  have hn : l₁.length = (pre.flatMap (·.rounds)).length := by
    rw [← steps_decl hl₁, List.length_map]
  have hdeclb : lb.map (·.decl) = b.rounds := by
    have e := steps_decl hlb
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    exact e
  have hnb : lb.length = b.rounds.length := by rw [← hdeclb, List.length_map]
  rw [List.flatMap_append, drawsFit_append, Bool.and_eq_true, List.flatMap_cons, drawsFit_append,
    Bool.and_eq_true] at hd
  obtain ⟨hd₁, hdb, -⟩ := hd
  generalize hN : (pre.flatMap (·.rounds)).length = N at *
  have hdN : (ds.take N).length = l₁.length := by rw [drawsFit_length _ _ hd₁, hn, hN]
  -- the rounds before, cut at the sub-protocol's border
  have eS : (l₁ ++ (lb ++ lt)).take (N + i) = l₁ ++ lb.take i := by
    rw [← hn, List.take_append, Nat.add_sub_cancel_left,
      List.take_of_length_le (Nat.le_add_right _ _),
      List.take_append_of_le_length (by rw [hnb]; exact Nat.le_of_lt hi)]
  have eS0 : (l₁ ++ (lb ++ lt)).take N = l₁ := by
    rw [← hn]
    exact List.take_left' rfl
  have eD : ds.take (N + i) = ds.take N ++ (ds.drop N).take i := List.take_add
  have hle : N + i ≤ (l₁ ++ (lb ++ lt)).length := by
    rw [List.length_append, List.length_append, hn, hnb]
    omega
  obtain ⟨y, w1, -, l1, -⟩ := walk_cut (start_laid ha) hz (N + i) hle
  have w1' := w1
  rw [eS, eD] at w1'
  obtain ⟨y₁, u1, u2⟩ := walk_append_ok (lb.take i) ((ds.drop N).take i) l₁ (ds.take N) a y hdN w1'
  rw [eS0] at w0
  obtain rfl : y₁ = y₀ := Except.ok.inj (u1.symm.trans w0)
  obtain ⟨w, g1, g2⟩ := walk_in (lb.take i) _ y₁ y t0 (by
    rw [o0, List.length_nil, Nat.zero_add, List.length_take, hnb]
    omega) u2
  rw [q0] at g1
  obtain ⟨m, e1, e2⟩ := lays_live _ _ mN w (fun u hu => hp0 u
    (List.mem_append_right _ (List.mem_append_left _ (List.mem_of_mem_take hu)))) g1
  have hym : y.mid = some m := by
    rw [g2]
    exact e1
  have hyl : z.laid.take N ++ w.1 = z.laid.take (N + i) := by
    rw [← l1, ← l0, g2]
    rfl
  refine ⟨y, m, w1, hym, ⟨s, mN, _, lb, (ds.drop N).take i, (w.1, m), iN, ?_, ?_, e2, rfl, ?_⟩, ?_⟩
  · rw [hin, hsee]
    exact hlb
  · have g := drawsFit_take _ _ i (Nat.le_of_lt hi) hdb
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hi)] at g
    exact g
  · show _ = (envOf L.stored taken (z.laid.take N)).add w.1
    rw [envOf_add, hyl]
  · rw [← l1]
    exact (walk_mid ha w1 hym).2.2

end

end ProofFile.Honest

#print axioms ProofFile.Honest.drawsFit_take
#print axioms ProofFile.Honest.thread_in_chain
#print axioms ProofFile.Honest.InsideOf
