-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/BudAt.lean: `bud`, from one list's clause of `Owed.owed`
(Honest/Owed.lean), for one chain (`bud_chain`). At every part of a list, called or not, the
parameter `bud` of the list holds at the part's own stretch of the chain's challenges and at the
positions that the run's reads have of its tables (`hq`, a hypothesis). The proof uses the lemmas on
a run at an address (Honest/Law/RunAtFile.lean: `drawnAt_of`, `askedAt_of`). `mid_stretch` is a
small lemma on lists. It is the nineteenth piece of the proof of `rowOk_of`
(Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

theorem mid_stretch {α : Type} {l a b c : List α} (h : l = a ++ b ++ c) {n len : Nat}
    (hn : a.length = n) (hl : b.length = len) : (l.drop n).take len = b ∧ l.take n = a := by
  subst hn
  subst hl
  rw [h, List.append_assoc]
  refine ⟨?_, List.take_left' rfl⟩
  rw [List.drop_left' rfl]
  exact List.take_left' rfl

/- **`bud` at every part of a list, for one chain.** `howed`: the list's own clause of `Owed.owed`
(`Lettered.owedAt`), at a `k`, `mid`, `r` and `st` that nothing here ties to one another or to a run
of `runC`. `hA`: `At` (Honest/Law/RunAtFile.lean) at every address that has a round among `ss`: what
the run has produced there is this chain's, from these `Step`s at these challenges. `hq`: `tree j`
lists the positions that the reads of `r` have of tree j of chain `ch`. `hk`, `hst`: `keys` and
`rsAll` are the `Step`s' own. -/
theorem bud_chain {F : FileDescription Xi} {Bk : ProverCoinCounts} (ch : Nat) (bs : List (Block S Cl))
    (L : Lettered Bk S Cl V W Y Pb) (σ : Side S Cl V W Y Pb) (hσ : L.side bs = some σ)
    (k : Coins Bk) (mid : Addr → Except Refusal (Mid W Y)) (r : RunC F)
    (st : List (Nat × Nat × List UInt64)) (howed : L.owedAt bs k ch mid r.run st r.called)
    (ss : List (Step W Y)) (dsAll : List Fmt.Drawn)
    (keys : List (Addr × Option (State W Y → Y))) (hk : ss.map Step.key = keys)
    (rsAll : List (Fmt.DeclaredRound × List Oracle))
    (hst : (ss.map fun s => (s.decl, s.oracles)) = rsAll) (pl : List Played)
    (hA : ∀ a, ss.any (·.addr == a) = true → At r.run a ch pl ss dsAll) (tree : Nat → List Nat)
    (hq : ∀ j, (((r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2).filter fun q =>
      q.src == some (ch, j)).map (·.pos)) = tree j) :
    ∀ u ∈ σ.members, ∀ (dsu : List Fmt.Drawn)
      (kp ku kq : List (Addr × Option (State W Y → Y))) (dp dq : List Fmt.Drawn)
      (rp rq : List (Fmt.DeclaredRound × List Oracle)),
      SegAt keys ⟨σ.block.place, u.number⟩ kp ku kq → ku.length = u.rounds.length →
      dsAll = dp ++ dsu ++ dq → rsAll = rp ++ u.rounds ++ rq → dp.length = kp.length →
      rp.length = kp.length → dsu.length = u.rounds.length →
      L.bud u.number dsu
        (asksFrom tree (u.rounds.map (·.2.length)) (rp.map (·.2.length)).sum) := by
  intro u hu dsu kp ku kq dp dq rp rq hseg hkul hd hr l1 l2 l3
  obtain ⟨hin, -, -, hany⟩ := hseg.steps hk
  obtain ⟨-, h2, -⟩ := side_ok hσ
  have b := (howed σ hσ u hu).1
  rw [← h2, drawnAt_of (hA _ hany) hin, askedAt_of (hA _ hany) hin tree hq] at b
  obtain ⟨d1, -⟩ := mid_stretch hd l1 (l3.trans hkul.symm)
  have hst' : (ss.map fun s => (s.decl, s.oracles)) = rp ++ u.rounds ++ rq := hst.trans hr
  obtain ⟨r1, r2⟩ := mid_stretch hst' l2 hkul.symm
  have o1 : ((ss.drop kp.length).take ku.length).map (·.oracles.length) =
      u.rounds.map (·.2.length) := by
    rw [← r1, ← List.map_drop, ← List.map_take, List.map_map]
    rfl
  have o2 : (ss.take kp.length).map (·.oracles.length) = rp.map (·.2.length) := by
    rw [← r2, ← List.map_take, List.map_map]
    rfl
  rw [d1, o1, o2] at b
  exact b

end ProofFile.Honest

#print axioms ProofFile.Honest.mid_stretch
#print axioms ProofFile.Honest.bud_chain
