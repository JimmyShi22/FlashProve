-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OnTools.lean: small tools for reading `Owed.owed`
(Honest/Owed.lean) at a part whose keys form one contiguous stretch of its chain's keys (`SegAt`,
Honest/Law/Rule/RowHere.lean), by the lemmas on a run at an address (Honest/Law/RunAt.lean). It is
the twelfth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `SegAt.steps`   a chain's `Step`s whose keys are these: how many are before the address, how
     many at it; they form one contiguous stretch
  2  `tell_told`, `part_moves`, `head_told`   a part's first round is real (`told`)
  3  `steps_sh`   each `Step` declares as many oracle messages as its entry counts roots, if each
     round of the chain's sub-protocols does
  4  `mid_ext`   two states of a run with the same four fields

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {S Cl V W Y : Type}

/-! ## 1 The `Step`s at an address -/

theorem SegAt.steps {keys kp ku kq : List (Addr × Option (State W Y → Y))} {a : Addr}
    (h : SegAt keys a kp ku kq) {ss : List (Step W Y)} (hk : ss.map Step.key = keys) :
    InStretch ss a kp.length ku.length ∧
      (ss.takeWhile fun s => s.addr != a).length = kp.length ∧
      (ss.filter fun s => s.addr == a).length = ku.length ∧
      ss.any (·.addr == a) = true := by
  obtain ⟨he, hf, ho, hb, hpos⟩ := h
  have hkey : ss.map Step.key = kp ++ (ku ++ kq) := by rw [hk, he, List.append_assoc]
  have h1 : (ss.take kp.length).map Step.key = kp := by
    rw [List.map_take, hkey]
    exact List.take_left' rfl
  have h2 : (ss.drop kp.length).map Step.key = ku ++ kq := by
    rw [List.map_drop, hkey]
    exact List.drop_left' rfl
  have h3 : ((ss.drop kp.length).take ku.length).map Step.key = ku := by
    rw [List.map_take, h2]
    exact List.take_left' rfl
  have h4 : ((ss.drop kp.length).drop ku.length).map Step.key = kq := by
    rw [List.map_drop, h2]
    exact List.drop_left' rfl
  have mem : ∀ (l : List (Step W Y)) (s : Step W Y), s ∈ l → s.key ∈ l.map Step.key :=
    fun l s hs => List.mem_map.2 ⟨s, hs, rfl⟩
  have f1 : ∀ s ∈ ss.take kp.length, (s.addr == a) = false := fun s hs => by
    have := mem _ s hs
    rw [h1] at this
    exact beq_eq_false_iff_ne.2 (hf _ this)
  have f2 : ∀ s ∈ (ss.drop kp.length).take ku.length, (s.addr == a) = true := fun s hs => by
    have := mem _ s hs
    rw [h3] at this
    exact beq_iff_eq.2 (ho _ this)
  have f3 : ∀ s ∈ (ss.drop kp.length).drop ku.length, (s.addr == a) = false := fun s hs => by
    have := mem _ s hs
    rw [h4] at this
    exact beq_eq_false_iff_ne.2 (hb _ this)
  have hlen3 : ((ss.drop kp.length).take ku.length).length = ku.length := by
    have := congrArg List.length h3
    rw [List.length_map] at this
    exact this
  have hlen1 : (ss.take kp.length).length = kp.length := by
    have := congrArg List.length h1
    rw [List.length_map] at this
    exact this
  have hfil := filter_stretch (fun s : Step W Y => s.addr == a) ss kp.length ku.length f1 f2 f3
  have hku : ku.length ≠ 0 := fun e => hpos (List.eq_nil_of_length_eq_zero e)
  -- the first `Step` at the address
  obtain ⟨s₀, rest, hs₀⟩ : ∃ s₀ rest, (ss.drop kp.length).take ku.length = s₀ :: rest := by
    cases hc : (ss.drop kp.length).take ku.length with
    | nil =>
      rw [hc] at hlen3
      exact absurd hlen3.symm hku
    | cons s₀ rest => exact ⟨s₀, rest, rfl⟩
  have hs₀a : (s₀.addr == a) = true := f2 s₀ (by rw [hs₀]; exact List.mem_cons.2 (Or.inl rfl))
  have hsplit : ss = ss.take kp.length ++ (s₀ :: (rest ++ (ss.drop kp.length).drop ku.length)) := by
    conv_lhs => rw [← List.take_append_drop kp.length ss,
      ← List.take_append_drop ku.length (ss.drop kp.length), hs₀]
    rfl
  refine ⟨⟨f1, f2, f3⟩, ?_, by rw [hfil, hlen3], ?_⟩
  · rw [hsplit, List.takeWhile_append_of_pos (fun s hs => by
      show (s.addr != a) = true
      rw [bne, f1 s hs]
      rfl), List.takeWhile_cons_of_neg (by
      show ¬ ((s₀.addr != a) = true)
      rw [bne, hs₀a]
      exact Bool.false_ne_true), List.append_nil]
    exact hlen1
  · refine List.any_eq_true.2 ⟨s₀, ?_, hs₀a⟩
    rw [hsplit]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))

/-! ## 2 A part's first round is real (`told`) -/

theorem tell_told {s : Step W Y} {back : Option Fmt.RoundView} {m : Mid W Y} {x : Told}
    (h : s.tell back m = .ok x) (hm : s.move.isSome = true) : x.told = true := by
  unfold Step.tell at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl
  · rename_i hn
    rw [hn] at hm
    cases hm

theorem part_moves (p : Part V W Y) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    ∀ s ∈ p.steps name a rs v c, s.move.isSome = true := by
  intro s hs
  unfold Part.steps at hs
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hs
  rfl

/-- Rounds that are played by moves: the first is real (`told`). -/
theorem head_told {ss : List (Step W Y)} {ds : List Fmt.Drawn} {back : List Fmt.RoundView} {m : Mid W Y}
    {y : List Played × Mid W Y} (h : play ss ds back m = .ok y)
    (hm : ∀ s ∈ ss, s.move.isSome = true) (hne : y.1 ≠ []) (l : List Played) :
    ((y.1 ++ l).head?.map (·.told)) = some true := by
  cases ss with
  | nil =>
    cases ds with
    | nil =>
      simp only [play] at h
      cases h
      exact absurd rfl hne
    | cons _ _ => simp [play] at h
  | cons s ss =>
    cases ds with
    | nil => simp [play] at h
    | cons d ds =>
      obtain ⟨x, m', z, hx, -, -, rfl⟩ := play_cons_ok h
      show some x.told = some true
      rw [tell_told hx (hm s (List.mem_cons.2 (Or.inl rfl)))]

/-! ## 3 The `Step`s' shape -/

theorem steps_sh {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss →
    (∀ b ∈ bs, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots) →
    ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots
  | [], ss, h, _, s, hs' => by
    simp only [chainSteps] at h
    cases h
    cases hs'
  | b :: bs, ss, h, hsh, s, hs' => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok h
    have ih := steps_sh bs l hl fun b' hb' => hsh b' (List.mem_cons_of_mem _ hb')
    have hb := hsh b (List.mem_cons.2 (Or.inl rfl))
    have key : ∀ sb : List (Step W Y),
        (sb.map fun s => (s.decl, s.oracles)) = b.rounds.zip b.oracles → s ∈ sb →
        s.oracles.length = s.decl.entry.roots := by
      intro sb e hm
      have h1 : (s.decl, s.oracles) ∈ sb.map fun s => (s.decl, s.oracles) :=
        List.mem_map.2 ⟨s, hm, rfl⟩
      rw [e] at h1
      exact hb _ h1
    rcases hcase with ⟨-, rfl⟩ | ⟨g, c, -, hr, -, -, rfl⟩
    · rcases List.mem_append.1 hs' with hm | hm
      · exact key _ (bare_states b) hm
      · exact ih s hm
    · rcases List.mem_append.1 hs' with hm | hm
      · exact key _ (row_states g b v c hr ho) hm
      · exact ih s hm

/-! ## 4 Two states of a run -/

theorem mid_ext {m m' : Mid W Y} (h1 : m.st = m'.st) (h2 : m.loc = m'.loc)
    (h3 : m.seen = m'.seen) (h4 : m.opened = m'.opened) : m = m' := by
  cases m
  cases m'
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

end ProofFile.Honest

#print axioms ProofFile.Honest.SegAt.steps
#print axioms ProofFile.Honest.tell_told
#print axioms ProofFile.Honest.part_moves
#print axioms ProofFile.Honest.head_told
#print axioms ProofFile.Honest.steps_sh
#print axioms ProofFile.Honest.mid_ext
