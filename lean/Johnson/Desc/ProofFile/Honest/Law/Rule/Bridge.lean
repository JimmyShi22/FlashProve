-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`. Where a description, a
book and its lists of parts meet `Owed` (Honest/Owed.lean), at an input in `Rel` with its trace, at
challenges that the rounds can draw, outside the one silent set (`silentAt`, Honest/Rule.lean), the
session's steps as items (Honest/Law/Rule/FileHere.lean: `fileItems`) meet `RowOk`
(Honest/Law/Rule/Items.lean). This is `rowOk_of`. Most of its proof is in nineteen other files of
this folder; the head of each says which piece of the proof it is (the second, and the fourth to the
twenty-first). What ties the opened columns that a part is handed to what has been produced is in
seven more of this folder, over tools of Honest/: OpenedAt, OpenedStep, OpenedStart, OpenedFile,
OpenedWalk, OpenedRun and FaithOwnFile.

  1  `bare_det`, `file_mem`, `file_cell`, `due_all`   small lemmas
  2  `fits_all`   each part of each list that `seatOf` gives fits the book
  3  `file_order`   the cells are in the order of their addresses
  4  `file_has`   an entry's owner has a cell
  5  `rowOk_of`   the main lemma

Hypotheses beside `Owed`: `FileOk` (Honest/Law/Rule/Model.lean: facts on the description, the book
and the lists of parts, without a coin) and `Sides.owns` (Honest/Law/Rule/Session.lean: an
executable test).

Limits.
  * `Owed` is a hypothesis here. In scope, where `protocolDataWellFormed` accepts, it is proved at
    the key file's muted rows (`OfflineRows.offline_rows_at_the_files`), in no lemma of this file.
  * `Rel` is a free parameter. At a relation that holds of nothing, and where the silent set holds
    every list of challenges, the lemmas behind the line `include` say nothing.
  * Hypotheses that the prose above does not name: `FileDescription.placesOk` (the library's executable
    test): `due_all`; `ProverCoinCounts.word … = none` (every test on the book passes): `due_all`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileCells
import Johnson.Desc.ProofFile.Honest.Law.Rule.Has

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 Small lemmas -/

/-- A sub-protocol's stretch without a part (`bareItem`) draws nothing. -/
theorem bare_det {S Cl : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi)
    (st : List (Nat × Nat × List UInt64)) (R : RealAt Bk) (ch : Nat) (tree : Nat → List Nat)
    (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) {s : Kit.Stage (Coins Bk) (Stand F) _}
    {f : Stand F → List (Shown × Fmt.Drawn)}
    (e : Item.det s f = bareItem (F := F) x st R ch tree b n own) :
    (∀ k φ, s.shows k φ = f φ) ∧ ∀ φ, s.tells φ = PMF.pure (some (f φ)) := by
  unfold bareItem at e
  obtain ⟨rfl, rfl⟩ := Item.det.inj e
  refine ⟨fun k Z => ?_, fun Z => ?_⟩
  · show Stretch.real (bareStretch ch tree b n own) R (Z.live ch) k _ =
      if Z.live ch = true then (bareStretch ch tree b n own).bare
      else (bareStretch ch tree b n own).sub
    unfold Stretch.real
    cases Z.live ch <;> rfl
  · show Stretch.lay (bareStretch ch tree b n own) (Z.live ch) (Z.laid.front ch st) =
      PMF.pure (some (if Z.live ch = true then (bareStretch ch tree b n own).bare
        else (bareStretch ch tree b n own).sub))
    unfold Stretch.lay
    cases Z.live ch <;> rfl

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws}

/- An item of the file is an item of one of the three chains, or the step `door`. -/
theorem file_mem {i : Item Bk (Stand F) (List (Shown × Fmt.Drawn))}
    (h : i ∈ fileItems F H G w₀ rc x tr ρ) :
    i ∈ items₁ F H G w₀ rc x tr ρ ∨ i ∈ items₂ F H G w₀ rc x tr ρ ∨
      i = .det (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) (.door : Act F)) (fun _ =>
          []) ∨
      i ∈ items₃ F H G w₀ rc x tr ρ := by
  unfold fileItems at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- An address of one chain: its count in that chain's table is its count in the three tables
concatenated. -/
theorem due_all (hb : Bk.word F = none) (hp : F.placesOk = true) {ch : Nat}
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {a : Addr} (ha : a.place ∈ placesAt F ch) :
    dueAt (Bk.first ++ Bk.shared ++ Bk.second) a = dueAt (Bk.rowsOf ch) a := by
  rcases hch with rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := ProverCoinCounts.noRow₁ hb hp ha
    rw [dueAt_right _ _ _ h2, dueAt_right _ _ _ h1]
    rfl
  · obtain ⟨h1, h2⟩ := ProverCoinCounts.noRow₂ hb hp ha
    rw [dueAt_right _ _ _ h2, dueAt_left _ _ _ h1]
    rfl
  · obtain ⟨h1, h2⟩ := ProverCoinCounts.noRow₃ hb hp ha
    rw [List.append_assoc, dueAt_left _ _ _ h1, dueAt_left _ _ _ h2]
    rfl

variable {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel) (hF : FileOk F Bk G)
  (hrel : Rel w₀ rc x) (hρ : ρ.due F = true)
  (hsil : silentAt F (G.prover H) w₀ rc x ρ = none) (htr : H.trace w₀ x = some tr)
include hO hF hrel hρ hsil htr

/-- **A cell of the file's items** is `CellOk` at one of the three chains' numbers, and its place is
a place of that chain. -/
theorem file_cell {C : Cell Bk (Stand F) (List (Shown × Fmt.Drawn))}
    (h : Item.cell C ∈ fileItems F H G w₀ rc x tr ρ) :
    ∃ ch, (ch = 0 ∨ ch = 1 ∨ ch = 2) ∧ CellOk (orderOf F) ch C ∧ C.addr.place ∈ placesAt F ch := by
  rcases file_mem h with h | h | h | h
  · exact ⟨0, Or.inl rfl, cells₁ hO hF hrel hρ hsil htr C h⟩
  · exact ⟨1, Or.inr (Or.inl rfl), cells₂ hO hF hrel hρ hsil htr C h⟩
  · cases h
  · exact ⟨2, Or.inr (Or.inr rfl), cells₃ hO hF hrel hρ hsil htr C h⟩

/-! ## 2 Each part fits the book -/

/- Each part of each list that `seatOf` gives fits the book, chain by chain. What it asserts names
no input and no challenge; it is proved only where there is a point as in the line `include` above.
-/
theorem fits_all :
    (∀ b ∈ F.first.blocksInOrder, ∀ p, seatOf F.first.blocksInOrder G.first b = some p → p.1.block = b ∧
      ∀ u ∈ p.1.members, Fit Bk 0 ⟨p.1.block.place, u.number⟩ u.part) ∧
    (∀ b ∈ F.shared.blocksInOrder, ∀ p, seatOf F.shared.blocksInOrder G.shared b = some p → p.1.block = b ∧
      ∀ u ∈ p.1.members, Fit Bk 1 ⟨p.1.block.place, u.number⟩ u.part) ∧
    ∀ b ∈ F.second.blocksInOrder, ∀ p, seatOf F.second.blocksInOrder G.second b = some p → p.1.block = b ∧
      ∀ u ∈ p.1.members, Fit Bk 2 ⟨p.1.block.place, u.number⟩ u.part := by
  obtain ⟨r, hrun⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  obtain ⟨R, hR, -⟩ := run_setup hO hF htr hrun
  obtain ⟨-, tr', -, -, -, hs₁, hs₂, hs₃⟩ := ready_ok hR
  obtain ⟨ok₁, ok₂, ok₃⟩ := seats_ok (tr := tr) (ρ := ρ) hF hR
  exact ⟨(fun b hb p hp => ⟨((ok₁ b hb).some p hp).1,
      chain_fit (realF F H G w₀ rc x tr ρ) 0 _ _ _ _ _ (G.prover H).first _ _ _
        (seatOf F.first.blocksInOrder G.first) _ _ hO.book
        hO.places (by decide) F.first.blocksInOrder _ hs₁ (fun b' hb' => List.mem_map.2 ⟨b', hb', rfl⟩) ok₁ b
            hb
        p hp⟩),
    (fun b hb p hp => ⟨((ok₂ b hb).some p hp).1,
      chain_fit (realF F H G w₀ rc x tr ρ) 1 _ _ _ _ _ (G.prover H).shared _ _ _
        (seatOf F.shared.blocksInOrder G.shared) _ _ hO.book
        hO.places (by decide) F.shared.blocksInOrder _ hs₂ (fun b' hb' => List.mem_map.2 ⟨b', hb', rfl⟩) ok₂
            b hb
        p hp⟩),
    (fun b hb p hp => ⟨((ok₃ b hb).some p hp).1,
      chain_fit (realF F H G w₀ rc x tr ρ) 2 _ _ _ _ _ (G.prover H).second _ _ _
        (seatOf F.second.blocksInOrder G.second) _ _ hO.book
        hO.places (by decide) F.second.blocksInOrder _ hs₃ (fun b' hb' => List.mem_map.2 ⟨b', hb', rfl⟩) ok₃
            b hb
        p hp⟩)⟩

/-! ## 3 The order -/

theorem file_order : CellsInOrder (orderOf F) (fileItems F H G w₀ rc x tr ρ) := by
  have hn := orderOf_nodup hO.places
  obtain ⟨f₁, f₂, f₃⟩ := fits_all hO hF hrel hρ hsil htr
  have b₁ := fun b hb p hp => (f₁ b hb p hp).1
  have b₂ := fun b hb p hp => (f₂ b hb p hp).1
  have b₃ := fun b hb p hp => (f₃ b hb p hp).1
  have p₁ : ∀ C, Item.cell C ∈ items₁ F H G w₀ rc x tr ρ → C.addr.place ∈ F.first.blocksInOrder.map (·.place)
      :=
    fun C h => (chainItems_place _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b₁ C h).1
  have p₂ : ∀ C, Item.cell C ∈ items₂ F H G w₀ rc x tr ρ → C.addr.place ∈ F.shared.blocksInOrder.map
      (·.place) :=
    fun C h => (chainItems_place _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b₂ C h).1
  have p₃ : ∀ C, Item.cell C ∈ items₃ F H G w₀ rc x tr ρ → C.addr.place ∈ F.second.blocksInOrder.map
      (·.place) :=
    fun C h => (chainItems_place _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b₃ C h).1
  unfold CellsInOrder fileItems
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩,
    List.pairwise_cons.2 ⟨(fun i _ C C' e _ => by cases e), ?_⟩, ?_⟩
  · exact chainItems_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn F.first.blocksInOrder []
      (F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place)) 0 ρ.first (by
                          unfold orderOf
                          rw [List.nil_append, List.append_assoc]) b₁
  · exact chainItems_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn F.shared.blocksInOrder (F.first.blocksInOrder.map
               (·.place))
      (F.second.blocksInOrder.map (·.place)) 0 ρ.shared rfl b₂
  · intro i hi i' hi' C C' e e'
    subst e
    subst e'
    exact before_places hn (l₁ := F.first.blocksInOrder.map (·.place))
      (l₂ := F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place))
      (by unfold orderOf; rw [List.append_assoc]) (p₁ C hi)
      (List.mem_append.2 (Or.inl (p₂ C' hi')))
  · exact chainItems_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn F.second.blocksInOrder
      (F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place)) [] 0 ρ.second (by
                          unfold orderOf
                          rw [List.append_nil]) b₃
  · intro i hi i' hi' C C' e e'
    subst e
    subst e'
    rcases List.mem_cons.1 hi' with e | e
    · cases e
    · refine before_places hn (l₁ := F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place))
        (l₂ := F.second.blocksInOrder.map (·.place)) rfl ?_ (p₃ C' e)
      rcases List.mem_append.1 hi with h | h
      · exact List.mem_append.2 (Or.inl (p₁ C h))
      · exact List.mem_append.2 (Or.inr (p₂ C h))

/-! ## 4 An entry's owner has a cell -/

theorem file_has (hE : G.owns = true) : ∀ e ∈ Bk.ahead,
    ∃ Co, Item.cell Co ∈ fileItems F H G w₀ rc x tr ρ ∧ Co.addr = e.owner := by
  intro e he
  obtain ⟨f₁, f₂, f₃⟩ := fits_all hO hF hrel hρ hsil htr
  unfold Sides.owns at hE
  have h := List.all_eq_true.1 hE e he
  have hm : e.owner ∈ addrsOf G.first ++ addrsOf G.shared ++ addrsOf G.second := by
    simpa using h
  have ea : ∀ (pl : Place), e.owner.place = pl → (⟨pl, e.owner.part⟩ : Addr) = e.owner := by
    intro pl hpl
    rw [← hpl]
  unfold fileItems
  rcases List.mem_append.1 hm with hm | hm
  · rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨L, hL, a1, a2⟩ := addr_row hm
      obtain ⟨σ, hσ, -⟩ := hF.seat₁ L hL
      obtain ⟨s1, s2, s3, s4⟩ := seat_of_row hF.rows₁ hL hσ
      obtain ⟨C, c1, c2⟩ := chain_has x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 0 0 (treeAsks F
          ρ 0)
        Face.own x (keys₁ F H G) ρ.first (mid₁ H w₀ rc x tr) (ver₁ F x _)
        (seatOf F.first.blocksInOrder G.first) (earlierOf F 0) F.first.blocksInOrder F.first.blocksInOrder 0 ρ.first f₁ σ.block
            s1 _ s4 e.owner.part
        (by rw [s3]; exact a2)
      exact ⟨C, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl c1))),
        c2.trans (ea _ (a1.trans s2.symm))⟩
    · obtain ⟨L, hL, a1, a2⟩ := addr_row hm
      obtain ⟨σ, hσ, -⟩ := hF.seat₂ L hL
      obtain ⟨s1, s2, s3, s4⟩ := seat_of_row hF.rows₂ hL hσ
      obtain ⟨C, c1, c2⟩ := chain_has x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 1 0 (treeAsks F
          ρ 1)
        Face.shared (H.key x) (keys₂ F H G) ρ.shared (startShared H ⟨w₀, rc, H.key x⟩) (ver₂ F x _)
        (seatOf F.shared.blocksInOrder G.shared) (earlierOf F 1) F.shared.blocksInOrder F.shared.blocksInOrder 0 ρ.shared f₂
            σ.block s1 _ s4 e.owner.part
        (by rw [s3]; exact a2)
      exact ⟨C, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr c1))),
        c2.trans (ea _ (a1.trans s2.symm))⟩
  · obtain ⟨L, hL, a1, a2⟩ := addr_row hm
    obtain ⟨σ, hσ, -⟩ := hF.seat₃ L hL
    obtain ⟨s1, s2, s3, s4⟩ := seat_of_row hF.rows₃ hL hσ
    obtain ⟨C, c1, c2⟩ := chain_has x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 2 F.lastChainFirstTreeNumber
      (treeAsks F ρ 2) Face.own x (keys₃ F H G) ρ.second (mid₃ F H G w₀ rc x tr ρ) (ver₃ F x _)
      (seatOf F.second.blocksInOrder G.second) (earlierOf F 2) F.second.blocksInOrder F.second.blocksInOrder 0 ρ.second f₃
          σ.block s1 _ s4 e.owner.part
      (by rw [s3]; exact a2)
    exact ⟨C, List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ c1)),
      c2.trans (ea _ (a1.trans s2.symm))⟩

/-! ## 5 The main lemma -/

/-- **From `Owed` to `RowOk`**, from `Stand.start F x`: nothing produced; the description's own
first states. -/
theorem rowOk_of (hE : G.owns = true) :
    RowOk (orderOf F) (fileItems F H G w₀ rc x tr ρ) (Stand.start F x) := by
  obtain ⟨f₁, f₂, f₃⟩ := fits_all hO hF hrel hρ hsil htr
  have hI : ∀ k, ∃ z₁ z₂ z₃, FileInv F Bk H G w₀ rc x tr ρ k z₁ z₂ z₃ := fun k => by
    obtain ⟨r, hrun⟩ := hO.runs w₀ rc x hrel k ρ hρ hsil
    exact file_inv hF htr hrun
  choose z₁ z₂ z₃ hI using hI
  obtain ⟨r₀, hrun₀⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  obtain ⟨R₀, hR₀, -⟩ := run_setup hO hF htr hrun₀
  have hhere := file_here hF z₁ z₂ z₃ hI hR₀
    (fun b hb p hp k => on₁ hO hF hrel hρ hsil htr (hI k) b hb p hp)
    (fun b hb p hp k => on₂ hO hF hrel hρ hsil htr (hI k) b hb p hp)
    (fun b hb p hp k => on₃ hO hF hrel hρ hsil htr (hI k) b hb p hp)
  exact
    { det := fun s f h => by
        rcases file_mem h with h | h | h | h
        · rcases chain_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f₁ s f h with ⟨b, n, own, e⟩ | ⟨b,
            own,
            e⟩
          · exact bare_det _ _ _ _ _ _ _ _ e
          · obtain ⟨rfl, rfl⟩ := Item.det.inj e
            exact ⟨fun _ _ => rfl, fun _ => rfl⟩
        · rcases chain_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f₂ s f h with ⟨b, n, own, e⟩ | ⟨b,
            own,
            e⟩
          · exact bare_det _ _ _ _ _ _ _ _ e
          · obtain ⟨rfl, rfl⟩ := Item.det.inj e
            exact ⟨fun _ _ => rfl, fun _ => rfl⟩
        · obtain ⟨rfl, rfl⟩ := Item.det.inj h
          exact ⟨fun _ _ => rfl, fun _ => rfl⟩
        · rcases chain_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f₃ s f h with ⟨b, n, own, e⟩ | ⟨b,
            own,
            e⟩
          · exact bare_det _ _ _ _ _ _ _ _ e
          · obtain ⟨rfl, rfl⟩ := Item.det.inj e
            exact ⟨fun _ _ => rfl, fun _ => rfl⟩
      row := fun C h => by
        obtain ⟨ch, -, hC, -⟩ := file_cell hO hF hrel hρ hsil htr h
        exact hC.row
      exact := fun C h => by
        obtain ⟨ch, -, hC, -⟩ := file_cell hO hF hrel hρ hsil htr h
        exact hC.exact
      fresh := fun C h => by
        obtain ⟨ch, -, hC, -⟩ := file_cell hO hF hrel hρ hsil htr h
        exact hC.fresh
      order := file_order hO hF hrel hρ hsil htr
      behind := ProverCoinCounts.behind hO.book
      vis := fun e he Co Cb ho hb eo eb => by
        obtain ⟨t, ht, hCo, po⟩ := file_cell hO hF hrel hρ hsil htr ho
        obtain ⟨c, hc, hCb, pb⟩ := file_cell hO hF hrel hρ hsil htr hb
        rw [hCo.chain, hCb.chain]
        rw [eo] at po
        rw [eb] at pb
        exact ProverCoinCounts.visible hO.book hO.places he ht hc po pb
      within := fun e he Co ho eo => by
        obtain ⟨t, ht, hCo, po⟩ := file_cell hO hF hrel hρ hsil htr ho
        have hw := ProverCoinCounts.within hO.book e he
        rw [← eo, due_all hO.book hO.places ht po, ← hCo.due] at hw
        exact hw
      owns := fun e he _ _ _ _ => file_has hO hF hrel hρ hsil htr hE e he
      here := fun I₁ C I₂ e => by
        have := HereAll.cut _ _ hhere I₁ C I₂ e
        rw [List.nil_append] at this
        exact this }

end

end ProofFile.Honest

#print axioms ProofFile.Honest.bare_det
#print axioms ProofFile.Honest.file_mem
#print axioms ProofFile.Honest.due_all
#print axioms ProofFile.Honest.file_cell
#print axioms ProofFile.Honest.fits_all
#print axioms ProofFile.Honest.file_order
#print axioms ProofFile.Honest.file_has
#print axioms ProofFile.Honest.rowOk_of
