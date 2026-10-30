-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Lends.lean: where a chain's `Step`s are prepared at a run's
coins and `SeatOk` holds at every sub-protocol of the chain, every part of every list that is at a
place is given its coins there; and the blocks that it carries are what `carriedAt`
(Honest/Frame.lean) returns. The proof goes as that of `row_fit` and `chain_fit`
(Honest/Law/Rule/ItemsForm.lean), with the coins kept.

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ItemsForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

theorem row_lent {Bk : ProverCoinCounts} {ch : Nat} {a : Place} {k : Coins Bk} :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins (row.map (·.1))),
    lendRow Bk (Bk.rowsOf ch) (k.look ch) a (row.map (·.1)) j = .ok c →
    ∀ u ∈ membersOf row j rs, ∃ c' : u.part.Coins,
      lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨a, u.number⟩ u.part = .ok c'
  | [], _, _, _, _, u, hu => by cases hu
  | q :: row, j, rs, c, hl, u, hu => by
    obtain ⟨l1, l2⟩ := lendRow_cons_ok (p := q.1) (ps := row.map (·.1)) hl
    rcases List.mem_cons.1 hu with e | e
    · rw [e]
      exact ⟨c.1, l1⟩
    · exact row_lent row (j + 1) _ c.2 l2 u e

/-- **Every part of every list that is at a place is given its coins.** -/
theorem chain_lent {Bk : ProverCoinCounts} (R : RealAt Bk) (ch ft : Nat) (tl : Addr → Option Teller)
    (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
    (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
    (seat : Block S Cl → Option (Side S Cl V W Y Pb × OnT V W Y Pb))
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (bsAll : List (Block S Cl)) {k : Coins Bk}
    {v : Option V} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps Bk (Bk.rowsOf ch) (k.look ch) v bs hs = .ok ss →
    (∀ b ∈ bs, SeatOk (Bk := Bk) R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll b) →
    ∀ b ∈ bs, ∀ p, seat b = some p → ∀ u ∈ p.1.members, ∃ c : u.part.Coins,
      lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.1.block.place, u.number⟩ u.part = .ok c ∧
        carriedAt Bk k ch ⟨p.1.block.place, u.number⟩ u.part = .ok c.2.2
  | [], _, _, _, b, hb', _, _, _, _ => by cases hb'
  | b₀ :: bs, ss, h, hok, b, hb', p, hseat, u, hu => by
    obtain ⟨-, l, hl, hcase⟩ := chainSteps_cons_ok h
    rcases List.mem_cons.1 hb' with e | e
    · subst e
      obtain ⟨hpb, ⟨g, hg, hparts⟩, -⟩ := (hok b hb').some p hseat
      rcases hcase with ⟨h1, -⟩ | ⟨g', c, h1, -, -, h4, -⟩
      · rw [hg] at h1
        cases h1
      · have eg : g' = g := Option.some.inj (h1.symm.trans hg)
        subst eg
        obtain ⟨gp, gparts⟩ := g'
        have hparts' : gparts = p.1.row.map (·.1) := hparts
        subst hparts'
        subst hpb
        obtain ⟨c', hc'⟩ := row_lent p.1.row 0 _ c h4 u hu
        refine ⟨c', hc', ?_⟩
        unfold carriedAt
        rw [hc']
        rfl
    · exact chain_lent R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll bs l hl
        (fun b' h' => hok b' (List.mem_cons_of_mem _ h')) b e p hseat u hu

end ProofFile.Honest

#print axioms ProofFile.Honest.row_lent
#print axioms ProofFile.Honest.chain_lent
