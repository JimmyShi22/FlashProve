-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ThreadAt.lean: the invariant's condition at the run's own state.
Where a chain's walk (Honest/Walk.lean) is before a sub-protocol with the prover's run still
available, no sub-protocol before has rejected, and the invariant before that sub-protocol holds
there: at the run's coins, the verifier's own state, the state of the prover's run, and the tables
produced so far. Of the two conditions of Honest/Law/ThreadC.lean it takes `PlaysOn` alone
(whose end is at the state that has taken the sub-protocol's columns, `Mid.took`, as the walk's own
state has), at the sub-protocols before.

What this is. A conditional lemma on this folder's own functions, pointwise. It is none of the
library's goals.

  1  `dead_settle`, `dead_walk`   once the prover's run is taken away it stays away
  2  `chain_live`   one chain, up to a sub-protocol that has a round

Limits.
  * The sub-protocol before which the walk is has a round: a sub-protocol without one is asked at
    once, after the sub-protocol before it.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `chain_live`.
  * `PlaysOn` is asked at every state that the invariant allows, at every value of the field
    `opened` too: where a sub-protocol of pre has a part that reads the columns and errs at `none`
    (its duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant before it that lets
    `none` through is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunsC
import Johnson.Desc.ProofFile.Honest.Law.RunMid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb : Type}

/-! ## 1 Once away, away -/

theorem dead_settle (L : Lay) (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y)
    (h : ChainProgress.settle L todo z = .ok z') (hm : z.mid = none) : z'.mid = none := by
  cases hz : z'.mid with
  | none => rfl
  | some m =>
    obtain ⟨_, _, g, -⟩ := settle_mid L todo z z' h (by rw [hz]; rfl)
    rw [hm] at g
    cases g

theorem dead_walk (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L l d z = .ok z' → z.mid = none → z'.mid = none
  | [], [], z, z', h, hm => by
    rw [walk_nil_ok h]
    exact hm
  | [], _ :: _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, h, _ => by simp [walk] at h
  | s :: l, d₀ :: d, z, z', h, hm => by
    obtain ⟨x, z₁, -, hz, hw⟩ := walk_cons_ok h
    obtain ⟨m', h1, hs⟩ := heard_ok hz
    rw [hm] at h1
    cases h1
    have key := fun (u : ChainProgress S Cl W Y) (g1 : ChainProgress.settle L z.todo u = .ok z₁)
        (g2 : u.mid = none) => dead_settle L z.todo u z₁ g1 g2
    exact dead_walk L l d z₁ z' hw (key _ hs rfl)

/-! ## 2 One chain, up to a sub-protocol that has a round -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **The invariant's condition at the run's own state.** `pre`: the sub-protocols before; `b`: the
sub-protocol before which the walk is, which has a round; `t`: those after it. `l`, `ds`: the rounds
and the challenges of `pre`. Among its other hypotheses: the `Lay`'s look-up of a tree is that of
`envOf`; a round without a move is under the part 0; the first invariant at the walk's state; no
stop (`chainStopAt … = none`); `chainSteps` returns at k; and at the end the prover's run is still
available. -/
theorem chain_live (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V)
    (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length) :
    ∀ (pre : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop),
    (∀ j c, pre[j]? = some c → PlaysOn φ Bk L.chain L.firstTree hs c (I j) (I (j + 1))) →
    ∀ (l : List (Step W Y)) (z z' : ChainProgress S Cl W Y) (ds : List Fmt.Drawn) (s : S) (m : Mid W Y),
    (∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) → z.own = [] → z.mid = some m →
    z.ver = some s → φ.sees m.st.input = v → I 0 k s m (envOf L.stored taken z.laid) →
    chainStopAt v pre hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v pre hs = .ok l →
    drawsFit (pre.flatMap (·.rounds)) ds = true →
    (ChainProgress.settle L (pre ++ b :: t) z).bind (walk L l ds) = .ok z' → z'.mid.isSome = true →
    ∃ s' m', z'.ver = some s' ∧ z'.mid = some m' ∧
      I pre.length k s' m' (envOf L.stored taken z'.laid)
  | [], I, _, l, z, z', ds, s, m, _, ho, hm, hv, _, h0, _, hl, hd, hz, _ => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    have hz' : (ChainProgress.settle L (b :: t) z).bind (walk L [] []) = .ok z' := hz
    rw [settle_wait L b t z (by rw [ho]; exact hb)] at hz'
    have hz'' : (Except.ok { z with todo := b :: t } : Except Refusal (ChainProgress S Cl W Y)) =
        .ok z' := hz'
    cases hz''
    exact ⟨s, m, hv, hm, h0⟩
  | c :: pre, I, h, l, z, z', ds, s, m, hp0, ho, hm, hv, hsee, h0, hst, hl, hd, hz, hlive => by
    have hl' : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v ([c] ++ pre) hs = .ok l := hl
    rw [chainSteps_append] at hl'
    obtain ⟨l₁, hl₁, hl'⟩ := exBind_ok hl'
    obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hl'
    rw [List.flatMap_cons, drawsFit_append, Bool.and_eq_true] at hd
    obtain ⟨hd₁, hd₂⟩ := hd
    have hdecl : l₁.map (·.decl) = c.rounds := by
      have e := steps_decl hl₁
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
      exact e
    have hn : l₁.length = c.rounds.length := by rw [← hdecl, List.length_map]
    have hlen₁ : (ds.take c.rounds.length).length = l₁.length := by
      rw [drawsFit_length _ _ hd₁, hn]
    have hW : walk L (l₁ ++ l₂) ds = fun a : ChainProgress S Cl W Y =>
        (walk L l₁ (ds.take c.rounds.length) a).bind (walk L l₂ (ds.drop c.rounds.length)) := by
      funext a
      have e' := walk_append L l₂ (ds.drop c.rounds.length) l₁ (ds.take c.rounds.length) a hlen₁
      rw [List.take_append_drop] at e'
      exact e'
    have hz₀ : (ChainProgress.settle L (c :: (pre ++ b :: t)) z).bind (walk L (l₁ ++ l₂) ds) = .ok z' := hz
    rw [hW] at hz₀
    have hst' : ((hs.find? fun g => g.place == c.place).bind fun g =>
        rowStopAt v g.parts m.loc (ds.take c.rounds.length)).or
          (chainStopAt v pre hs (m.loc ++ ds.take c.rounds.length)
            (ds.drop c.rounds.length)) = none := hst
    obtain ⟨hs₁, hs₂⟩ := or_none hst'
    have hs₁' : chainStopAt v [c] hs m.loc (ds.take c.rounds.length) = none := by
      show ((hs.find? fun g => g.place == c.place).bind fun g =>
        rowStopAt v g.parts m.loc
          ((ds.take c.rounds.length).take c.rounds.length)).or (none : Option Why) = none
      rw [List.take_take, Nat.min_self, hs₁]
      rfl
    obtain ⟨y, cols, p₁, f₁, hB⟩ := h 0 c (by simp) k s m _ (ds.take c.rounds.length) l₁ h0 hd₁
      (by rw [hsee]; exact hs₁') (by rw [hsee]; exact hl₁)
    obtain ⟨e1, e2, -⟩ := play_mid _ _ _ _ _ p₁
    have Y₁ := play_yields _ _ _ _ _ p₁
    have hdr : y.1.map (·.drawn) = ds.take c.rounds.length := by
      have e := yields_drawn _ _ _ _ Y₁
      unfold roundsOf at e
      rw [List.map_map] at e
      exact e
    have hE : (envOf L.stored taken z.laid).add y.1 = envOf L.stored taken (z.laid ++ y.1) :=
      envOf_add _ _ _ _
    have f₁' : fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) c.rounds
        (y.1.map (·.drawn))) [] = .ok cols := by
      rw [hdr, hL]
      rw [hE] at f₁
      exact f₁
    have hlay : lays l₁ (ds.take c.rounds.length) z.mid = .ok (y.1, some y.2) := by
      rw [hm]
      exact lays_of_play _ _ _ _ (fun u hu => hp0 u (List.mem_append_left _ hu)) p₁
    rw [member_laid L c (pre ++ b :: t) z l₁ _ (y.1, some y.2) cols ho hn hlay f₁'] at hz₀
    cases hj : judge L.firstTree c s (roundsOf y.1) cols with
    | none =>
      have hdead : (z.askedO L c (y.1, some y.2) cols).mid = none := by
        show (if (z.ver.bind fun s => judge L.firstTree c s (roundsOf y.1) cols).isSome
          then some (y.2.took cols) else none) = none
        rw [hv]
        show (if (judge L.firstTree c s (roundsOf y.1) cols).isSome then some (y.2.took cols)
          else none) = _
        rw [hj]
        rfl
      obtain ⟨a, g1, g2⟩ := exBind_ok hz₀
      have d1 := dead_settle L _ _ a g1 hdead
      have d2 := dead_walk L _ _ a z' g2 d1
      rw [d2] at hlive
      cases hlive
    | some s' =>
      have hstep : ∃ n, c.step L.firstTree s (roundsOf y.1) cols = .ok (s', n) := by
        unfold judge at hj
        cases hs' : c.step L.firstTree s (roundsOf y.1) cols with
        | error e =>
          rw [hs'] at hj
          cases hj
        | ok w =>
          rw [hs'] at hj
          cases hj
          exact ⟨w.2, rfl⟩
      obtain ⟨n, hstep⟩ := hstep
      have hB' := hB s' n hstep
      rw [hE] at hB'
      have hver : (z.askedO L c (y.1, some y.2) cols).ver = some s' := by
        show (z.ver.bind fun s => judge L.firstTree c s (roundsOf y.1) cols) = some s'
        rw [hv]
        exact hj
      have hmid : (z.askedO L c (y.1, some y.2) cols).mid = some (y.2.took cols) := by
        show (if (z.ver.bind fun s => judge L.firstTree c s (roundsOf y.1) cols).isSome
          then some (y.2.took cols) else none) = some (y.2.took cols)
        rw [hv]
        show (if (judge L.firstTree c s (roundsOf y.1) cols).isSome then some (y.2.took cols)
          else none) = _
        rw [hj]
        rfl
      exact chain_live L taken hL k v b t hb pre (fun j => I (j + 1))
        (fun j c' hj' => h (j + 1) c' (by rw [List.getElem?_cons_succ]; exact hj')) l₂
        (z.askedO L c (y.1, some y.2) cols) z' (ds.drop c.rounds.length) s' (y.2.took cols)
        (fun u hu => hp0 u (List.mem_append_right _ hu)) rfl hmid hver
        (by
          show φ.sees y.2.st.input = v
          rw [e1]
          exact hsee)
        hB'
        (by
          show chainStopAt v pre hs y.2.loc _ = none
          rw [e2]
          exact hs₂)
        hl₂ hd₂ hz₀ hlive

end

end ProofFile.Honest

#print axioms ProofFile.Honest.dead_settle
#print axioms ProofFile.Honest.dead_walk
#print axioms ProofFile.Honest.chain_live
