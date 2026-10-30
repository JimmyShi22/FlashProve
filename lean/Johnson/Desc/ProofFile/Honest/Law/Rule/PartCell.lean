-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/PartCell.lean: when a part has a cell
(Honest/Law/Rule/CellOf.lean), and what of `RowOk.here` (Honest/Law/Rule/Items.lean) follows where
the part is given its coins and plays its rounds. It is the second piece of the proof of `rowOk_of`
(Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `lend_names`, `lendPart_ok`   where `lendPart` returns: the part is typed at the entries' own
     names and counts, and takes what the book has for it
  2  `Fit`, `fit_of_lent`   a definition: the part's own row is a lens, and three agreements with
     the book: its count; the names and counts of the blocks that it spends; those of the blocks
     that it carries; a part that is given its coins at one run's coins meets it
  3  `cellAt`, `cellAt_row`, `cellAt_stage`   the cell of a part that fits
  4  `cell_here`   at given coins: the blocks are available, and the cell says something

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.CellOf
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 Where `lendPart` returns -/

theorem lend_names (look : Addr → (d : Due) × Cs d) :
    ∀ (ds : List (String × Due)) (E : List Ahead) (x : CsAll ds), lend look ds E = .ok x →
    E.map Ahead.named = ds
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [lend] at h
  | _ :: _, [], _, h => by simp [lend] at h
  | d :: ds, a :: l, x, h => by
    simp only [lend] at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    obtain ⟨y, hy, -⟩ := exMap_ok h
    have ih := lend_names look ds l y hy
    have e1 : a.name = d.1 := by simpa using h1
    have e2 : a.count = d.2 := by simpa using h2
    show (a.name, a.count) :: l.map Ahead.named = d :: ds
    rw [ih, e1, e2]

theorem lendPart_ok {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Addr} {p : Part V W Y} {c : p.Coins} (h : lendPart Bk rows look a p = .ok c) :
    p.takes = dueAt rows a ∧ lend look p.spends (spentE Bk a) = .ok c.2.1 ∧
      lend look p.carries (carryE Bk a) = .ok c.2.2 := by
  unfold lendPart at h
  simp only at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  obtain ⟨sp, hsp, h⟩ := exBind_ok h
  obtain ⟨ca, hca, e⟩ := exMap_ok h
  subst e
  exact ⟨by simpa using h1, hsp, hca⟩

/-! ## 2 A part that fits the book -/

/-- **The part at an address fits the book.** `ch`: its chain's number, from 0. -/
structure Fit (Bk : ProverCoinCounts) (ch : Nat) (a : Addr) (p : Part V W Y) : Prop where
  row : ∃ gp : (Coins Bk → Cs p.takes) × (Cs p.takes → Coins Bk → Coins Bk),
    RowAt Bk a ch p.takes gp.1 gp.2
  due : p.takes = dueAt (Bk.rowsOf ch) a
  sp : (spentE Bk a).map Ahead.named = p.spends
  ca : (carryE Bk a).map Ahead.named = p.carries

/-- **A part that is given its coins, at one run's coins, fits**, where the book passes its tests,
the description its test on the places, `ch` is 0, 1 or 2, and the address's place is one of that
chain's. -/
theorem fit_of_lent {F : FileDescription Xi} {Bk : ProverCoinCounts} (hb : Bk.word F = none)
    (hp : F.placesOk = true) {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {a : Addr}
    (ha : a.place ∈ placesAt F ch) {p : Part V W Y} {k : Coins Bk} {c : p.Coins}
    (h : lendPart Bk (Bk.rowsOf ch) (k.look ch) a p = .ok c) : Fit Bk ch a p := by
  obtain ⟨h1, h2, h3⟩ := lendPart_ok h
  have hrows : (ch ≠ 0 → Bk.first.any (fun r => r.1 == a) = false) ∧
      (ch ≠ 1 → Bk.shared.any (fun r => r.1 == a) = false) ∧
      (ch ≠ 2 → Bk.second.any (fun r => r.1 == a) = false) := by
    rcases hch with rfl | rfl | rfl
    · have := ProverCoinCounts.noRow₁ hb hp ha
      exact ⟨fun e => absurd rfl e, fun _ => this.1, fun _ => this.2⟩
    · have := ProverCoinCounts.noRow₂ hb hp ha
      exact ⟨fun _ => this.1, fun e => absurd rfl e, fun _ => this.2⟩
    · have := ProverCoinCounts.noRow₃ hb hp ha
      exact ⟨fun _ => this.1, fun _ => this.2, fun e => absurd rfl e⟩
  obtain ⟨get, put, l1, l2, l3⟩ := Coins.lens a p.takes ch hch h1.symm hrows.1 hrows.2.1 hrows.2.2
  exact ⟨⟨(get, put), ⟨l1, l2, l3⟩⟩, h1, lend_names _ _ _ _ h2, lend_names _ _ _ _ h3⟩

/-! ## 3 The cell of a part that fits -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (φ : Face V W Pb) (σ : Side S Cl V W Y Pb)
  (u : Member V W Y Pb) (pb : Pb) (ch ft : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
  (dry : Mid W Y) (st : List (Nat × Nat × List UInt64)) (ds : List Fmt.Drawn)
  (asks : List (List (List Nat)))
  (On : CsAll u.part.carries → Mid W Y → Before → Prop)
  (hf : Fit Bk ch ⟨σ.block.place, u.number⟩ u.part)

/- The part's cell (`cellOf`) at a lens that `Fit.row` gives, taken by choice (`Classical.choose`).
`cellAt_row`: it is a lens on the part's row. `cellAt_stage`: the cell's stage is the stretch's,
whichever lens is taken. -/
noncomputable def cellAt : Cell Bk (Stand F) (List (Shown × Fmt.Drawn)) :=
  cellOf φ σ u pb ch ft pre dry st ds asks (Classical.choose hf.row).1
    (Classical.choose hf.row).2 hf.sp hf.ca On

theorem cellAt_row : RowAt Bk ⟨σ.block.place, u.number⟩ ch u.part.takes
    (Classical.choose hf.row).1 (Classical.choose hf.row).2 := Classical.choose_spec hf.row

theorem cellAt_stage (x : Xi) (R : RealAt Bk)
    (hR : R ch ⟨σ.block.place, u.number⟩ = partShows φ σ u Bk ch pre dry) :
    (cellAt (F := F) φ σ u pb ch ft pre dry st ds asks On hf).stage =
      Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
        some ⟨u.sim.takes, u.sim.tell pb⟩⟩ : Act F) :=
  cell_stage φ σ u pb ch ft pre dry st ds asks _ _ hf.sp hf.ca On x R (cellAt_row σ u ch hf) hf.due
    hR

/-! ## 4 At given coins -/

/-- **Where the part is given its coins and plays its rounds**, from the state and the challenges at
which the cell is built and from what has been produced before (the rounds shown, and the opened
columns that it holds for the reads of `pre`): the blocks are available; those that
it carries are the ones that `lendPart` gives; and the cell says something. -/
theorem cell_here (k : Coins Bk) (Z : Stand F) (c : u.part.Coins) (y : List Played × Mid W Y)
    (hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, u.number⟩ u.part = .ok c)
    (hplay : play (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
      (φ.sees dry.st.input) c) ds [] ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
        (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ =
      .ok y)
    (hd : y.1.map (·.drawn) = ds) :
    ∃ sp ca v, (cellAt (F := F) φ σ u pb ch ft pre dry st ds asks On hf).spent k = some sp ∧
      (cellAt (F := F) φ σ u pb ch ft pre dry st ds asks On hf).carried k = some ca ∧
      castAll hf.ca ca = c.2.2 ∧
      (cellAt (F := F) φ σ u pb ch ft pre dry st ds asks On hf).speaks
        ((cellAt (F := F) φ σ u pb ch ft pre dry st ds asks On hf).get k) sp ca Z = some v := by
  have ho := lendPart_opt u.part (cellAt_row σ u ch hf) hf.due hf.sp hf.ca k
  rw [hl] at ho
  cases h1 : runs (k.look ch) (spentE Bk ⟨σ.block.place, u.number⟩) with
  | none =>
    rw [h1] at ho
    cases ho
  | some sp =>
    cases h2 : runs (k.look ch) (carryE Bk ⟨σ.block.place, u.number⟩) with
    | none =>
      rw [h1, h2] at ho
      cases ho
    | some ca =>
      rw [h1, h2] at ho
      have ec : c = ((Classical.choose hf.row).1 k, castAll hf.sp sp, castAll hf.ca ca) :=
        Option.some.inj ho
      have hlen : (shownOf y.1 asks).length = ds.length := by
        rw [← hd]
        unfold shownOf
        simp
      refine ⟨sp, ca, (shownOf y.1 asks).zip ds, h1, h2, by rw [ec], ?_⟩
      show (σ.shows φ u ((Classical.choose hf.row).1 k, castAll hf.sp sp, castAll hf.ca ca)
        ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
          (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ ds asks).bind
        (zipLen ds) = _
      rw [← ec]
      unfold Side.shows
      rw [hplay]
      show zipLen ds (shownOf y.1 asks) = _
      unfold zipLen
      rw [if_pos (by rw [hlen]; exact beq_self_eq_true _)]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.lend_names
#print axioms ProofFile.Honest.lendPart_ok
#print axioms ProofFile.Honest.fit_of_lent
#print axioms ProofFile.Honest.cellAt_row
#print axioms ProofFile.Honest.cellAt_stage
#print axioms ProofFile.Honest.cell_here
#print axioms ProofFile.Honest.Fit
#print axioms ProofFile.Honest.cellAt
