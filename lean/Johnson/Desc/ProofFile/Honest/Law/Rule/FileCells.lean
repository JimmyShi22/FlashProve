-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/FileCells.lean: the cells of a file's items
(Honest/Law/Rule/FileHere.lean) satisfy `CellOk` (Honest/Law/Rule/CellLaws.lean): three of the
things that `RowOk` asks of a cell (`row`, `exact`, `fresh`), the book's count and the chain's
number. From `Owed` (Honest/Owed.lean) and `FileOk` (Honest/Law/Rule/Model.lean), at an input in
`Rel` with its trace, at challenges that the rounds can draw, outside the one silent set
(`silentAt`, Honest/Rule.lean). `RowOk.here` is not among them (Honest/Law/Rule/FileHere.lean).
Each lemma also says that the cell's place is one of its chain's. It is the twenty-first piece of
the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `stops_none`, `fits_of`, `row_sum`   three small lemmas
  2  `cells₁`, `cells₂`, `cells₃`   chain by chain

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OnFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.BudAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.CellLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 Three small lemmas -/

/-- Outside the one silent set no chain's prover's sides stop. -/
theorem stops_none {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws}
    (htr : H.trace w₀ x = some tr) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none) :
    chainStopAt (see₁ w₀ rc x tr) F.first.blocksInOrder (G.prover H).first [] ρ.first = none ∧
      chainStopAt (see₂ H w₀ rc x) F.shared.blocksInOrder (G.prover H).shared [] ρ.shared = none ∧
      chainStopAt (see₁ w₀ rc x tr) F.second.blocksInOrder (G.prover H).second ρ.first ρ.second = none := by
  unfold silentAt at hsil
  have htr' : (G.prover H).trace w₀ x = some tr := htr
  rw [htr'] at hsil
  obtain ⟨h1, h23⟩ := none_of_or (show (chainStopAt (see₁ w₀ rc x tr) F.first.blocksInOrder
    (G.prover H).first [] ρ.first).or ((chainStopAt (see₂ H w₀ rc x) F.shared.blocksInOrder
      (G.prover H).shared [] ρ.shared).or (chainStopAt (see₁ w₀ rc x tr) F.second.blocksInOrder
        (G.prover H).second ρ.first ρ.second)) = none from hsil)
  obtain ⟨h2, h3⟩ := none_of_or h23
  exact ⟨h1, h2, h3⟩

theorem fits_of {F : FileDescription Xi} {ρ : Draws} (hρ : ρ.due F = true) :
    drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true ∧
      drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true ∧
      drawsFit (F.second.blocksInOrder.flatMap (·.rounds)) ρ.second = true := by
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  exact ⟨hρ.1.1.1, hρ.1.1.2, hρ.1.2⟩

/-- A list of parts whose side fits has one move for each round of its sub-protocol. -/
theorem row_sum {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts} {bs : List (Block S Cl)}
    {Ls : List (Lettered Bk S Cl V W Y Pb)}
    (hseat : ∀ L ∈ Ls, ∃ σ, L.side bs = some σ ∧ σ.fits = true) {b : Block S Cl}
    {p : Side S Cl V W Y Pb × OnT V W Y Pb} (hp : seatOf bs Ls b = some p) (hb : p.1.block = b) :
    (p.1.row.map (·.1.moves.length)).sum = (b.rounds.zip b.oracles).length := by
  obtain ⟨L, hL, hσ, -⟩ := seat_inv hp
  obtain ⟨σ, hσ', hf⟩ := hseat L hL
  have e : σ = p.1 := Option.some.inj (hσ'.symm.trans hσ)
  subst e
  subst hb
  unfold Side.fits at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have h0 := hf.1.2
  unfold Side.half Placed.rounds at h0
  rw [foldl_moves, Nat.zero_add, List.map_map] at h0
  rw [List.length_zip, hf.2, Nat.min_self]
  exact h0

/-! ## 2 Chain by chain -/

/-- **The cells of the first chain.** -/
theorem cells₁ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (htr : H.trace w₀ x = some tr) :
    ∀ C, Item.cell C ∈ items₁ F H G w₀ rc x tr ρ →
      CellOk (orderOf F) 0 C ∧ C.addr.place ∈ placesAt F 0 := by
  intro C hC
  obtain ⟨r, hrun⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  obtain ⟨R, hR, o₁, o₂, o₃, k₁, k₂, k₃, -, -, -, -, -⟩ := run_setup hO hF htr hrun
  obtain ⟨-, tr', -, -, -, hs₁, hs₂, hs₃⟩ := ready_ok hR
  obtain ⟨st₁, st₂, st₃⟩ := stops_none htr hsil
  obtain ⟨ft₁, ft₂, ft₃⟩ := fits_of hρ
  have hok := (seats_ok (tr := tr) (ρ := ρ) hF hR).1
  obtain ⟨b, hb, p, hseat, hP⟩ := chain_where x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 0 0
    (treeAsks F ρ 0) (tellerOf G.sims.first x) (fun a => G.sims.first.any (·.addr.place == a))
        Face.own x (G.prover H).first (keys₁ F H G) ρ.first
    (mid₁ H w₀ rc x tr) (ver₁ F x _) (see₁ w₀ rc x tr) (seatOf F.first.blocksInOrder G.first)
    (F.first.blocksInOrder.flatMap fun b => b.rounds.zip b.oracles) (earlierOf F 0) F.first.blocksInOrder F.first.blocksInOrder
    ρ.first 0 [] [] []
    { keys := rfl
      all := rfl
      rounds := rfl
      len := rfl
      lenr := rfl
      fresh := fun q hq => by cases hq
      stop := by
        rw [List.append_nil]
        exact st₁
      fit := ft₁
      num := rfl }
    hF.nd₁ (fun b hb => (chain_facts _ _ hs₁ b hb).1) (fun b hb => (chain_facts _ _ hs₁ b hb).2.1)
    (fun b _ cs => hF.cuts b.place cs) hok
    (fun b hb p hp => row_sum hF.seat₁ hp ((hok b hb).some p hp).1) C hC
  obtain ⟨L, hL, hσ, hOnE⟩ := seat_inv hseat
  rw [hOnE, (side_ok hσ).2.1] at hP
  have hblk := ((hok b hb).some p hseat).1
  refine ⟨part_laws (stF F H w₀ rc ρ) 0 0 (treeAsks F ρ 0) Face.own x (keys₁ F H G) ρ.first
    (mid₁ H w₀ rc x tr) (see₁ w₀ rc x tr) _ (orderOf F) F.first.blocksInOrder G.falls₁
    (L.withField 0 0 F.first.blocksInOrder [] 0) (earlierOf F 0) p.1 (hO.good.1 L hL) hσ rfl rfl
    (bud_chain 0 F.first.blocksInOrder L p.1 hσ _ _ r _ ((hO.owed w₀ rc x hrel _ ρ r hρ hsil hrun).1 L hL)
      R.first ρ.first (keys₁ F H G) k₁ _ (chain_states _ _ hs₁) _
      (fun a ha => at_first hrun hR o₁ o₂ o₃ hO.places ha) (treeAsks F ρ 0)
      (runC_asks hrun hR o₁ o₂ o₃ 0)) C hP, ?_⟩
  obtain ⟨u, dsu, kp, kq, dp, dq, rp, rq, hf, hu, rfl, -⟩ := hP
  show p.1.block.place ∈ placesAt F 0
  rw [hblk]
  exact List.mem_map.2 ⟨b, hb, rfl⟩


/-- **The cells of the shared chain.** -/
theorem cells₂ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (htr : H.trace w₀ x = some tr) :
    ∀ C, Item.cell C ∈ items₂ F H G w₀ rc x tr ρ →
      CellOk (orderOf F) 1 C ∧ C.addr.place ∈ placesAt F 1 := by
  intro C hC
  obtain ⟨r, hrun⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  obtain ⟨R, hR, o₁, o₂, o₃, k₁, k₂, k₃, -, -, -, -, -⟩ := run_setup hO hF htr hrun
  obtain ⟨-, tr', -, -, -, hs₁, hs₂, hs₃⟩ := ready_ok hR
  obtain ⟨st₁, st₂, st₃⟩ := stops_none htr hsil
  obtain ⟨ft₁, ft₂, ft₃⟩ := fits_of hρ
  have hok := (seats_ok (tr := tr) (ρ := ρ) hF hR).2.1
  obtain ⟨b, hb, p, hseat, hP⟩ := chain_where x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 1 0
    (treeAsks F ρ 1) (tellerOf G.sims.shared (H.key x)) (fun a => G.sims.shared.any (·.addr.place ==
        a)) Face.shared (H.key x) (G.prover H).shared (keys₂ F H G) ρ.shared
    (startShared H ⟨w₀, rc, H.key x⟩) (ver₂ F x _) (see₂ H w₀ rc x) (seatOf F.shared.blocksInOrder G.shared)
    (F.shared.blocksInOrder.flatMap fun b => b.rounds.zip b.oracles) (earlierOf F 1) F.shared.blocksInOrder
        F.shared.blocksInOrder
    ρ.shared 0 [] [] []
    { keys := rfl
      all := rfl
      rounds := rfl
      len := rfl
      lenr := rfl
      fresh := fun q hq => by cases hq
      stop := by
        rw [List.append_nil]
        exact st₂
      fit := ft₂
      num := rfl }
    hF.nd₂ (fun b hb => (chain_facts _ _ hs₂ b hb).1) (fun b hb => (chain_facts _ _ hs₂ b hb).2.1)
    (fun b _ cs => hF.cuts b.place cs) hok
    (fun b hb p hp => row_sum hF.seat₂ hp ((hok b hb).some p hp).1) C hC
  obtain ⟨L, hL, hσ, hOnE⟩ := seat_inv hseat
  rw [hOnE, (side_ok hσ).2.1] at hP
  have hblk := ((hok b hb).some p hseat).1
  refine ⟨part_laws (stF F H w₀ rc ρ) 1 0 (treeAsks F ρ 1) Face.shared (H.key x) (keys₂ F H G)
      ρ.shared
    (startShared H ⟨w₀, rc, H.key x⟩) (see₂ H w₀ rc x) _ (orderOf F) F.shared.blocksInOrder G.falls₂
    (L.withField 1 0 F.shared.blocksInOrder [] 0) (earlierOf F 1) p.1 (hO.good.2.1 L hL) hσ rfl rfl
    (bud_chain 1 F.shared.blocksInOrder L p.1 hσ _ _ r _ ((hO.owed w₀ rc x hrel _ ρ r hρ hsil hrun).2.1 L hL)
      R.shared ρ.shared (keys₂ F H G) k₂ _ (chain_states _ _ hs₂) _
      (fun a ha => at_shared hrun hR o₁ o₂ o₃ hO.places ha) (treeAsks F ρ 1)
      (runC_asks hrun hR o₁ o₂ o₃ 1)) C hP, ?_⟩
  obtain ⟨u, dsu, kp, kq, dp, dq, rp, rq, hf, hu, rfl, -⟩ := hP
  show p.1.block.place ∈ placesAt F 1
  rw [hblk]
  exact List.mem_map.2 ⟨b, hb, rfl⟩


/-- **The cells of the second chain.** -/
theorem cells₃ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (htr : H.trace w₀ x = some tr) :
    ∀ C, Item.cell C ∈ items₃ F H G w₀ rc x tr ρ →
      CellOk (orderOf F) 2 C ∧ C.addr.place ∈ placesAt F 2 := by
  intro C hC
  obtain ⟨r, hrun⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  obtain ⟨R, hR, o₁, o₂, o₃, k₁, k₂, k₃, -, -, -, -, -⟩ := run_setup hO hF htr hrun
  obtain ⟨-, tr', -, -, -, hs₁, hs₂, hs₃⟩ := ready_ok hR
  obtain ⟨st₁, st₂, st₃⟩ := stops_none htr hsil
  obtain ⟨ft₁, ft₂, ft₃⟩ := fits_of hρ
  have hok := (seats_ok (tr := tr) (ρ := ρ) hF hR).2.2
  obtain ⟨b, hb, p, hseat, hP⟩ := chain_where x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 2
      F.lastChainFirstTreeNumber
    (treeAsks F ρ 2) (tellerOf G.sims.second x) (fun a => G.sims.second.any (·.addr.place == a))
        Face.own x (G.prover H).second (keys₃ F H G) ρ.second
    (mid₃ F H G w₀ rc x tr ρ) (ver₃ F x _) (see₁ w₀ rc x tr) (seatOf F.second.blocksInOrder G.second)
    (F.second.blocksInOrder.flatMap fun b => b.rounds.zip b.oracles) (earlierOf F 2) F.second.blocksInOrder
        F.second.blocksInOrder
    ρ.second 0 [] [] []
    { keys := rfl
      all := rfl
      rounds := rfl
      len := rfl
      lenr := rfl
      fresh := fun q hq => by cases hq
      stop := by
        rw [List.append_nil]
        exact st₃
      fit := ft₃
      num := rfl }
    hF.nd₃ (fun b hb => (chain_facts _ _ hs₃ b hb).1) (fun b hb => (chain_facts _ _ hs₃ b hb).2.1)
    (fun b _ cs => hF.cuts b.place cs) hok
    (fun b hb p hp => row_sum hF.seat₃ hp ((hok b hb).some p hp).1) C hC
  obtain ⟨L, hL, hσ, hOnE⟩ := seat_inv hseat
  rw [hOnE, (side_ok hσ).2.1] at hP
  have hblk := ((hok b hb).some p hseat).1
  refine ⟨part_laws (stF F H w₀ rc ρ) 2 F.lastChainFirstTreeNumber (treeAsks F ρ 2) Face.own x (keys₃ F H G)
      ρ.second
    (mid₃ F H G w₀ rc x tr ρ) (see₁ w₀ rc x tr) _ (orderOf F) F.second.blocksInOrder G.falls₃
    (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder [] 0) (earlierOf F 2) p.1 (hO.good.2.2 L hL [] 0) hσ
    rfl rfl
    (bud_chain 2 F.second.blocksInOrder L p.1 hσ _ _ r _ ((hO.owed w₀ rc x hrel _ ρ r hρ hsil hrun).2.2 L hL)
      R.second ρ.second (keys₃ F H G) k₃ _ (chain_states _ _ hs₃) _
      (fun a ha => at_second hrun hR o₁ o₂ o₃ hO.places ha) (treeAsks F ρ 2)
      (runC_asks hrun hR o₁ o₂ o₃ 2)) C hP, ?_⟩
  obtain ⟨u, dsu, kp, kq, dp, dq, rp, rq, hf, hu, rfl, -⟩ := hP
  show p.1.block.place ∈ placesAt F 2
  rw [hblk]
  exact List.mem_map.2 ⟨b, hb, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.stops_none
#print axioms ProofFile.Honest.fits_of
#print axioms ProofFile.Honest.row_sum
#print axioms ProofFile.Honest.cells₁
#print axioms ProofFile.Honest.cells₂
#print axioms ProofFile.Honest.cells₃
