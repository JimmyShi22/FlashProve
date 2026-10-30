-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Has.lean: every part of a list has a cell at its address
among its chain's items (Honest/Law/Rule/ChainHere.lean), where each part fits the book. It is the
twentieth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `row_has`, `chain_has`   a list of parts; a chain. `earlier`, `bsAll`: as `memberItems` takes
     them; nothing here ties `bsAll` to the sub-protocols over which `chain_has` runs
  2  `seat_of_row`, `addr_row`   what `seatOf` gives at a list's own sub-protocol; an address among
     the lists' addresses

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ItemsForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (ch ft : Nat) (tree : Nat → List Nat) (φ : Face V W Pb) (pb : Pb)
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
  (Ve : VerAt F S Cl x st ch ft)
  (seat : Block S Cl → Option (Side S Cl V W Y Pb × OnT V W Y Pb))
  (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (bsAll : List (Block S Cl))

theorem row_has (pr : List (Nat × Nat × List Fmt.DeclaredRound)) (σ : Side S Cl V W Y Pb)
    (On : OnT V W Y Pb) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (n : Nat) (ds : List Fmt.Drawn),
    (∀ u ∈ membersOf row j rs, Fit Bk ch ⟨σ.block.place, u.number⟩ u.part) →
    ∀ i, i < row.length → ∃ C, Item.cell C ∈ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀
        pb On pr row j rs n ds ∧
      C.addr = ⟨σ.block.place, j + i⟩
  | [], _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | q :: row, j, rs, n, ds, hfit, 0, _ => by
    have hf := hfit ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (List.mem_cons.2 (Or.inl rfl))
    refine ⟨cellAt φ σ ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ pb ch ft pr
      (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩) st (ds.take q.1.moves.length)
      (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n)
      (On ⟨j, rs.take q.1.moves.length, q.1, q.2⟩) hf, ?_, rfl⟩
    refine List.mem_cons.2 (Or.inl ?_)
    unfold partItem
    rw [dif_pos hf]
  | q :: row, j, rs, n, ds, hfit, i + 1, hi => by
    obtain ⟨C, h1, h2⟩ := row_has pr σ On row (j + 1) (rs.drop q.1.moves.length)
      (n + ((rs.take q.1.moves.length).map (·.2.length)).sum) (ds.drop q.1.moves.length)
      (fun u hu => hfit u (List.mem_cons_of_mem _ hu)) i (Nat.lt_of_succ_lt_succ hi)
    refine ⟨C, List.mem_cons_of_mem _ h1, ?_⟩
    rw [h2, Nat.add_assoc, Nat.add_comm 1 i]

theorem chain_has : ∀ (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn),
    (∀ b ∈ bs, ∀ p, seat b = some p → p.1.block = b ∧ ∀ u ∈ p.1.members,
      Fit Bk ch ⟨p.1.block.place, u.number⟩ u.part) →
    ∀ b ∈ bs, ∀ p, seat b = some p → ∀ i, i < p.1.row.length →
    ∃ C, Item.cell C ∈ chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier
        bsAll bs n ds ∧
        C.addr = ⟨b.place, i⟩
  | [], _, _, _, b, hb, _, _, _, _ => by cases hb
  | b₀ :: bs, n, ds, hfit, b, hb, p, hseat, i, hi => by
    show ∃ C, Item.cell C ∈ memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier
        bsAll b₀ n
        (ds.take b₀.rounds.length) ++
        Item.det (Act.stage x st R (Ve.J b₀ (ds.take b₀.rounds.length))) (fun _ => []) ::
          chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll bs
            (n + ((b₀.rounds.zip b₀.oracles).map (·.2.length)).sum) (ds.drop b₀.rounds.length) ∧
      C.addr = ⟨b.place, i⟩
    rcases List.mem_cons.1 hb with e | e
    · subst e
      obtain ⟨hpb, hf⟩ := hfit b hb p hseat
      have hrow : p.1.row.isEmpty = false := by
        cases hr : p.1.row with
        | nil =>
          rw [hr] at hi
          exact absurd hi (Nat.not_lt_zero i)
        | cons _ _ => rfl
      rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat hrow]
      subst hpb
      obtain ⟨C, h1, h2⟩ := row_has x st R ch ft tree φ pb keys dsAll m₀ _ p.1 p.2 p.1.row 0
        (p.1.block.rounds.zip p.1.block.oracles) n (ds.take p.1.block.rounds.length) hf i hi
      refine ⟨C, List.mem_append.2 (Or.inl h1), ?_⟩
      rw [h2, Nat.zero_add]
    · obtain ⟨C, h1, h2⟩ := chain_has bs _ _ (fun b' h' => hfit b' (List.mem_cons_of_mem _ h')) b e
        p hseat i hi
      exact ⟨C, List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ h1)), h2⟩

end

/-- **What `seatOf` gives at a list's own sub-protocol**: the list's side, with its parameter `On`.
-/
theorem seat_of_row {Bk : ProverCoinCounts} {bs : List (Block S Cl)} {Ls : List (Lettered Bk S Cl V W Y Pb)}
    (hLs : (Ls.map (·.place)).Nodup) {L : Lettered Bk S Cl V W Y Pb} (hL : L ∈ Ls)
    {σ : Side S Cl V W Y Pb} (hσ : L.side bs = some σ) :
    σ.block ∈ bs ∧ σ.block.place = L.place ∧ σ.row = L.row ∧
      seatOf bs Ls σ.block = some (σ, L.On) := by
  obtain ⟨h1, h2, h3⟩ := side_ok hσ
  refine ⟨h1, h2, h3, ?_⟩
  unfold seatOf
  cases hf : Ls.find? fun L' => L'.place == σ.block.place with
  | none =>
    have := List.find?_eq_none.1 hf L hL
    rw [h2] at this
    exact absurd (beq_self_eq_true _) this
  | some L' =>
    have hq₀ := List.find?_some hf
    have hq : (L'.place == σ.block.place) = true := hq₀
    have e : L' = L := List.inj_on_of_nodup_map hLs (List.mem_of_find?_eq_some hf) hL
      ((beq_iff_eq.1 hq).trans h2)
    subst e
    show ((L'.side bs).map fun σ => (σ, L'.On)) = _
    rw [hσ]
    rfl

theorem addr_row {Bk : ProverCoinCounts} {Ls : List (Lettered Bk S Cl V W Y Pb)} {a : Addr}
    (h : a ∈ addrsOf Ls) : ∃ L ∈ Ls, a.place = L.place ∧ a.part < L.row.length := by
  unfold addrsOf at h
  obtain ⟨L, hL, h'⟩ := List.mem_flatMap.1 h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h'
  exact ⟨L, hL, rfl, List.mem_range.1 hj⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.row_has
#print axioms ProofFile.Honest.chain_has
#print axioms ProofFile.Honest.seat_of_row
#print axioms ProofFile.Honest.addr_row
