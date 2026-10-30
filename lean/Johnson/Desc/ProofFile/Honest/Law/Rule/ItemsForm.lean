-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ItemsForm.lean: what a chain's items are
(Honest/Law/Rule/ChainHere.lean): the conclusions name no coin. It is the seventeenth piece of the
proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `row_fit`, `chain_fit`   each part of a list fits the book (`Fit`,
     Honest/Law/Rule/PartCell.lean), where the chain's `Step`s are prepared at one run's coins, the
     book passes its tests, the description its test on the places, and the places are the chain's,
     and `ch` is 0, 1 or 2; for `chain_fit` also: `SeatOk` at each sub-protocol
  2  `row_det`, `chain_det`   where each part fits the book (`Fit`): a list of parts has no item
     that is no cell, and an item of a chain that is no cell is a sub-protocol's stretch without a
     part (`bareItem`) or a step `judge`. (A part that does not fit has a placeholder for its item:
     `partItem`, Honest/Law/Rule/RowHere.lean.)
  3  `rowItems_addr`, `CellsInOrder`, `rowItems_order`, `chainItems_place`, `chainItems_order`   the
     cells are at their sub-protocols' places, in the order of their addresses

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Seat
import Johnson.Desc.ProofFile.Honest.Law.Rule.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 Each part fits the book -/

theorem row_fit {F : FileDescription Xi} {Bk : ProverCoinCounts} (hb : Bk.word F = none) (hp : F.placesOk = true)
    {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {a : Place} (ha : a ∈ placesAt F ch)
    {k : Coins Bk} : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
      (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins (row.map (·.1))),
    lendRow Bk (Bk.rowsOf ch) (k.look ch) a (row.map (·.1)) j = .ok c →
    ∀ u ∈ membersOf row j rs, Fit Bk ch ⟨a, u.number⟩ u.part
  | [], _, _, _, _, u, hu => by cases hu
  | q :: row, j, rs, c, hl, u, hu => by
    obtain ⟨l1, l2⟩ := lendRow_cons_ok (p := q.1) (ps := row.map (·.1)) hl
    rcases List.mem_cons.1 hu with e | e
    · rw [e]
      exact fit_of_lent hb hp hch ha l1
    · exact row_fit hb hp hch ha row (j + 1) _ c.2 l2 u e

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (ch ft : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller)
  (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
  (Ve : VerAt F S Cl x st ch ft)
  (seat : Block S Cl → Option (Side S Cl V W Y Pb × OnT V W Y Pb))
  (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (bsAll : List (Block S Cl))

/-- **Each part of each list that `seat` gives fits the book.** -/
theorem chain_fit (hb : Bk.word F = none) (hp : F.placesOk = true)
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {k : Coins Bk} {v : Option V} :
    ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps Bk (Bk.rowsOf ch) (k.look ch) v bs hs = .ok ss →
    (∀ b ∈ bs, b.place ∈ placesAt F ch) →
    (∀ b ∈ bs, SeatOk (Bk := Bk) R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll b) →
    ∀ b ∈ bs, ∀ p, seat b = some p → ∀ u ∈ p.1.members,
      Fit Bk ch ⟨p.1.block.place, u.number⟩ u.part
  | [], _, _, _, _, b, hb', _, _, _, _ => by cases hb'
  | b₀ :: bs, ss, h, hpl, hok, b, hb', p, hseat, u, hu => by
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
        exact row_fit hb hp hch (hpl _ hb') p.1.row 0 _ c h4 u hu
    · exact chain_fit hb hp hch bs l hl (fun b' h' => hpl b' (List.mem_cons_of_mem _ h'))
        (fun b' h' => hok b' (List.mem_cons_of_mem _ h')) b e p hseat u hu

/-! ## 2 The items that are no cells -/

/- Where each part fits the book, every item of a list of parts is a cell. -/
theorem row_det (pr : List (Nat × Nat × List Fmt.DeclaredRound)) (σ : Side S Cl V W Y Pb)
    (On : OnT V W Y Pb) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (n : Nat) (ds : List Fmt.Drawn),
    (∀ u ∈ membersOf row j rs, Fit Bk ch ⟨σ.block.place, u.number⟩ u.part) →
    ∀ s f, Item.det s f ∉ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row j rs n
        ds
  | [], _, _, _, _, _, s, f, h => by cases h
  | q :: row, j, rs, n, ds, hfit, s, f, h => by
    have h' : Item.det s f = partItem (F := F) x st R ch ft φ σ keys dsAll m₀ pb On pr
        ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (ds.take q.1.moves.length)
        (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n) ∨
        Item.det s f ∈ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row (j + 1)
          (rs.drop q.1.moves.length) (n + ((rs.take q.1.moves.length).map (·.2.length)).sum)
          (ds.drop q.1.moves.length) := List.mem_cons.1 h
    rcases h' with e | e
    · unfold partItem at e
      rw [dif_pos (hfit _ (List.mem_cons.2 (Or.inl rfl)))] at e
      cases e
    · exact row_det pr σ On row (j + 1) _ _ _
        (fun u hu => hfit u (List.mem_cons_of_mem _ hu)) s f e

/-- **An item of a chain that is no cell**, where each part fits the book. -/
theorem chain_det : ∀ (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn),
    (∀ b ∈ bs, ∀ p, seat b = some p → p.1.block = b ∧ ∀ u ∈ p.1.members,
      Fit Bk ch ⟨p.1.block.place, u.number⟩ u.part) →
    ∀ s f, Item.det s f ∈ chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier
        bsAll bs n ds →
    (∃ (b : Block S Cl) (n' : Nat) (own : List Fmt.Drawn),
      Item.det s f = bareItem (F := F) x st R ch tree b n' own) ∨
      ∃ b own, Item.det s f = .det (Act.stage x st R (Ve.J b own)) fun _ => []
  | [], _, _, _, s, f, h => by cases h
  | b :: bs, n, ds, hfit, s, f, h => by
    have hb : b ∈ b :: bs := List.mem_cons.2 (Or.inl rfl)
    have h' : Item.det s f ∈ memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier
        bsAll b n
        (ds.take b.rounds.length) ++
        Item.det (Act.stage x st R (Ve.J b (ds.take b.rounds.length))) (fun _ => []) ::
          chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll bs
            (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (ds.drop b.rounds.length) := h
    rcases List.mem_append.1 h' with e | e
    · cases hseat : seat b with
      | none =>
        rw [memberItems_none x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _
          hseat] at e
        exact Or.inl ⟨b, n, _, List.mem_singleton.1 e⟩
      | some p =>
        cases hrow : p.1.row.isEmpty with
        | true =>
          rw [memberItems_bare x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow] at e
          exact Or.inl ⟨b, n, _, List.mem_singleton.1 e⟩
        | false =>
          rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow] at e
          obtain ⟨hpb, hf⟩ := hfit b hb p hseat
          subst hpb
          exact absurd e (row_det x st R ch ft tree φ pb keys dsAll m₀ _ p.1 p.2 p.1.row 0 _ n _ hf
              s
            f)
    · rcases List.mem_cons.1 e with e | e
      · exact Or.inr ⟨b, _, e⟩
      · exact chain_det bs _ _ (fun b' h' => hfit b' (List.mem_cons_of_mem _ h')) s f e

/-! ## 3 The order of the cells -/

theorem rowItems_addr (pr : List (Nat × Nat × List Fmt.DeclaredRound)) (σ : Side S Cl V W Y Pb)
    (On : OnT V W Y Pb) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (n : Nat) (ds : List Fmt.Drawn),
    ∀ C, Item.cell C ∈ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row j rs n ds
        →
    C.addr.place = σ.block.place ∧ j ≤ C.addr.part ∧ C.chain = ch
  | [], _, _, _, _, C, h => by cases h
  | q :: row, j, rs, n, ds, C, h => by
    have h' : Item.cell C = partItem (F := F) x st R ch ft φ σ keys dsAll m₀ pb On pr
        ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (ds.take q.1.moves.length)
        (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n) ∨
        Item.cell C ∈ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row (j + 1)
          (rs.drop q.1.moves.length) (n + ((rs.take q.1.moves.length).map (·.2.length)).sum)
          (ds.drop q.1.moves.length) := List.mem_cons.1 h
    rcases h' with e | e
    · unfold partItem at e
      split at e
      · rw [Item.cell.inj e]
        exact ⟨rfl, Nat.le_refl j, rfl⟩
      · cases e
    · obtain ⟨h1, h2, h3⟩ := rowItems_addr pr σ On row (j + 1) _ _ _ C e
      exact ⟨h1, by omega, h3⟩

/-- Items whose cells are in the order of their addresses. -/
def CellsInOrder (ord : List Place) (I : List (Item Bk (Stand F) (List (Shown × Fmt.Drawn)))) :
    Prop :=
  I.Pairwise fun i j => ∀ C C', i = .cell C → j = .cell C' → C.addr.before ord C'.addr = true

theorem rowItems_order (ord : List Place) (pr : List (Nat × Nat × List Fmt.DeclaredRound))
    (σ : Side S Cl V W Y Pb) (On : OnT V W Y Pb) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (n : Nat) (ds : List Fmt.Drawn),
    CellsInOrder ord (rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row j rs n ds)
  | [], _, _, _, _ => List.Pairwise.nil
  | q :: row, j, rs, n, ds => by
    refine List.pairwise_cons.2 ⟨fun i hi C C' e e' => ?_,
      rowItems_order ord pr σ On row (j + 1) _ _ _⟩
    subst e'
    obtain ⟨h1, h2, -⟩ := rowItems_addr x st R ch ft tree φ pb keys dsAll m₀ pr σ On row (j + 1) _ _
        _
      C' hi
    unfold partItem at e
    split at e
    · rw [← Item.cell.inj e]
      have e2 : C'.addr = ⟨σ.block.place, C'.addr.part⟩ := by rw [← h1]
      rw [e2]
      show (⟨σ.block.place, j⟩ : Addr).before ord ⟨σ.block.place, C'.addr.part⟩ = true
      exact Addr.before_same ord σ.block.place (by omega)
    · cases e

theorem chainItems_place : ∀ (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn),
    (∀ b ∈ bs, ∀ p, seat b = some p → p.1.block = b) →
    ∀ C, Item.cell C ∈ chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier
        bsAll bs n ds →
    C.addr.place ∈ bs.map (·.place) ∧ C.chain = ch
  | [], _, _, _, C, h => by cases h
  | b :: bs, n, ds, hblk, C, h => by
    have hb : b ∈ b :: bs := List.mem_cons.2 (Or.inl rfl)
    have h' : Item.cell C ∈ memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier
        bsAll b n
        (ds.take b.rounds.length) ++
        Item.det (Act.stage x st R (Ve.J b (ds.take b.rounds.length))) (fun _ => []) ::
          chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll bs
            (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (ds.drop b.rounds.length) := h
    rcases List.mem_append.1 h' with e | e
    · cases hseat : seat b with
      | none =>
        rw [memberItems_none x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _
          hseat] at e
        have e' := List.mem_singleton.1 e
        cases e'
      | some p =>
        cases hrow : p.1.row.isEmpty with
        | true =>
          rw [memberItems_bare x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow] at e
          have e' := List.mem_singleton.1 e
          cases e'
        | false =>
          rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow] at e
          obtain ⟨h1, -, h3⟩ := rowItems_addr x st R ch ft tree φ pb keys dsAll m₀ _ p.1 p.2 _ 0 _ _
            _ C e
          refine ⟨List.mem_cons.2 (Or.inl ?_), h3⟩
          rw [h1, hblk b hb p hseat]
    · rcases List.mem_cons.1 e with e | e
      · cases e
      · obtain ⟨h1, h2⟩ := chainItems_place bs _ _
          (fun b' h' => hblk b' (List.mem_cons_of_mem _ h')) C e
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- **A chain's cells are in order.** `pre`, `post`: the places before and after these
sub-protocols, in an order that has no place twice. -/
theorem chainItems_order {ord : List Place} (hn : ord.Nodup) :
    ∀ (bs : List (Block S Cl)) (pre post : List Place) (n : Nat) (ds : List Fmt.Drawn),
    ord = pre ++ bs.map (·.place) ++ post →
    (∀ b ∈ bs, ∀ p, seat b = some p → p.1.block = b) →
    CellsInOrder ord (chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll
        bs n ds)
  | [], _, _, _, _, _, _ => List.Pairwise.nil
  | b :: bs, pre, post, n, ds, ho, hblk => by
    have hb : b ∈ b :: bs := List.mem_cons.2 (Or.inl rfl)
    have hblk' : ∀ b' ∈ bs, ∀ p, seat b' = some p → p.1.block = b' :=
      fun b' h' => hblk b' (List.mem_cons_of_mem _ h')
    have ho' : ord = (pre ++ [b.place]) ++ bs.map (·.place) ++ post := by
      rw [ho]
      simp
    have ih := chainItems_order hn bs (pre ++ [b.place]) post
      (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (ds.drop b.rounds.length) ho' hblk'
    have hsplit : ord = (pre ++ [b.place]) ++ (bs.map (·.place) ++ post) := by
      rw [ho', List.append_assoc]
    have hown : ∀ C, Item.cell C ∈ memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat
        earlier bsAll b
        n (ds.take b.rounds.length) → C.addr.place = b.place := by
      intro C e
      have := (chainItems_place x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll [b] n ds
        (fun b' h' p hp => by
          rw [List.mem_singleton.1 h'] at hp ⊢
          exact hblk b hb p hp) C (List.mem_append.2 (Or.inl e))).1
      simpa using this
    show List.Pairwise _ (memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier
        bsAll b n
        (ds.take b.rounds.length) ++ _ :: _)
    refine List.pairwise_append.2 ⟨?_, List.pairwise_cons.2 ⟨(fun i _ C C' e _ => by cases e),
      ih⟩, ?_⟩
    · cases hseat : seat b with
      | none =>
        rw [memberItems_none x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat]
        exact List.pairwise_singleton _ _
      | some p =>
        cases hrow : p.1.row.isEmpty with
        | true =>
          rw [memberItems_bare x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow]
          exact List.pairwise_singleton _ _
        | false =>
          rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow]
          exact rowItems_order x st R ch ft tree φ pb keys dsAll m₀ ord _ p.1 p.2 _ 0 _ _ _
    · intro i hi i' hi' C C' e e'
      subst e
      subst e'
      rcases List.mem_cons.1 hi' with e | e
      · cases e
      · have hq := (chainItems_place x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll bs _
          _ hblk' C'
          e).1
        exact before_places hn hsplit
          (List.mem_append.2 (Or.inr (by rw [hown C hi]; exact List.mem_singleton.2 rfl)))
          (List.mem_append.2 (Or.inl hq))

end

end ProofFile.Honest

#print axioms ProofFile.Honest.row_fit
#print axioms ProofFile.Honest.chain_fit
#print axioms ProofFile.Honest.row_det
#print axioms ProofFile.Honest.chain_det
#print axioms ProofFile.Honest.rowItems_addr
#print axioms ProofFile.Honest.rowItems_order
#print axioms ProofFile.Honest.chainItems_place
#print axioms ProofFile.Honest.chainItems_order
#print axioms ProofFile.Honest.CellsInOrder
