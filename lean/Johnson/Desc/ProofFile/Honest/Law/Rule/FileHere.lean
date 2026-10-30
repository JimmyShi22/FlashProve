-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/FileHere.lean: a file: a session's steps as items
(`fileItems`; for `Item` see Honest/Law/Rule/Items.lean); under `FileOk`
(Honest/Law/Rule/Model.lean), where `ready` returns at some coins, their stages are the steps'
(`file_stage`); and, where moreover the prover of Honest/Walk.lean goes through at all coins
(`FileInv`, Honest/Law/Rule/FileInv.lean), `HereAll` (Honest/Law/Rule/Here.lean) of them
(`file_here`). The condition on `On` remains a hypothesis, chain by chain (`hOn₁`, `hOn₂`, `hOn₃`);
it may use `OpenedAt` (Honest/Law/Rule/OpenedAt.lean) at the part's state. It is the eleventh piece
of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `stF`, `keys₁`, `keys₂`, `keys₃`, `see₁`, `see₂`, `realF`   abbreviations
  2  `items₁`, `items₂`, `items₃`, `fileItems`   the items
  3  `seats_ok`, `stage₁`, `stage₂`, `stage₃`, `file_stage`   their stages
  4  `file_here`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileInv
import Johnson.Desc.ProofFile.Honest.Law.Rule.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

section
variable (F : FileDescription Xi) {Bk : ProverCoinCounts} (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) (tr : Tr) (ρ : Draws)

/-- The stored tables' columns at the positions that the declared rounds read. -/
abbrev stF : List (Nat × Nat × List UInt64) := storedShown (H.storedWords w₀ rc) (storedAsks F ρ)

/-- For each round of the first chain: its part's address and what its move passes on (`chainKeys`,
Honest/Law/Rule/Dry.lean). These are not `Prover.key`. -/
abbrev keys₁ := chainKeys F.first.blocksInOrder (G.prover H).first
/- The same for the shared chain. -/
abbrev keys₂ := chainKeys F.shared.blocksInOrder (G.prover H).shared
/- The same for the second chain. -/
abbrev keys₃ := chainKeys F.second.blocksInOrder (G.prover H).second

/-- `Face.sees` (Honest/Frame.lean) at the input of the first and the second chain's parts: what a
second stop there may read: the input. -/
abbrev see₁ := Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)
/- `Face.sees` at the shared chain's input: `none`: in the shared chain that stop is not asked. -/
abbrev see₂ := Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)

/-- The honest side beside a session's steps. -/
abbrev realF : RealAt Bk := realAt F Bk H G ⟨w₀, rc, x, tr⟩ ⟨w₀, rc, H.key x⟩ ρ

/- The first chain's items: `chainItems` at the public value x, at `earlierOf F 0` and the chain's
whole list (likewise below). -/
noncomputable def items₁ : List (Item Bk (Stand F) (List (Shown × Fmt.Drawn))) :=
  chainItems x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 0 0 (treeAsks F ρ 0) Face.own x
    (keys₁ F H G) ρ.first (mid₁ H w₀ rc x tr) (ver₁ F x _) (seatOf F.first.blocksInOrder G.first)
    (earlierOf F 0) F.first.blocksInOrder F.first.blocksInOrder 0 ρ.first

/- The shared chain's items: at the public value `H.key x`. -/
noncomputable def items₂ : List (Item Bk (Stand F) (List (Shown × Fmt.Drawn))) :=
  chainItems x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 1 0 (treeAsks F ρ 1) Face.shared
    (H.key x) (keys₂ F H G) ρ.shared (startShared H ⟨w₀, rc, H.key x⟩) (ver₂ F x _)
    (seatOf F.shared.blocksInOrder G.shared) (earlierOf F 1) F.shared.blocksInOrder F.shared.blocksInOrder 0 ρ.shared

/- The second chain's items: at the public value x, from `mid₃`. -/
noncomputable def items₃ : List (Item Bk (Stand F) (List (Shown × Fmt.Drawn))) :=
  chainItems x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) 2 F.lastChainFirstTreeNumber (treeAsks F ρ 2)
    Face.own x (keys₃ F H G) ρ.second (mid₃ F H G w₀ rc x tr ρ) (ver₃ F x _)
    (seatOf F.second.blocksInOrder G.second) (earlierOf F 2) F.second.blocksInOrder F.second.blocksInOrder 0 ρ.second

/-- **A session's steps as items.** -/
noncomputable def fileItems : List (Item Bk (Stand F) (List (Shown × Fmt.Drawn))) :=
  items₁ F H G w₀ rc x tr ρ ++ items₂ F H G w₀ rc x tr ρ ++
    .det (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) (.door : Act F))
      (fun _ => []) ::
      items₃ F H G w₀ rc x tr ρ

end

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws}

/-- `SeatOk` for the three chains, where the `Step`s are prepared at given coins. -/
theorem seats_ok (hF : FileOk F Bk G) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    (∀ b ∈ F.first.blocksInOrder, SeatOk (realF F H G w₀ rc x tr ρ) 0 0 (tellerOf G.sims.first x)
      (fun a => G.sims.first.any (·.addr.place == a)) Face.own x (G.prover H).first (keys₁ F H G)
      ρ.first (mid₁ H w₀ rc x tr) (seatOf F.first.blocksInOrder G.first) (earlierOf F 0) F.first.blocksInOrder b) ∧
    (∀ b ∈ F.shared.blocksInOrder, SeatOk (realF F H G w₀ rc x tr ρ) 1 0 (tellerOf G.sims.shared (H.key x))
      (fun a => G.sims.shared.any (·.addr.place == a)) Face.shared (H.key x) (G.prover H).shared
      (keys₂ F H G) ρ.shared (startShared H ⟨w₀, rc, H.key x⟩) (seatOf F.shared.blocksInOrder G.shared)
          (earlierOf F 1) F.shared.blocksInOrder b) ∧
    ∀ b ∈ F.second.blocksInOrder, SeatOk (realF F H G w₀ rc x tr ρ) 2 F.lastChainFirstTreeNumber (tellerOf G.sims.second x)
      (fun a => G.sims.second.any (·.addr.place == a)) Face.own x (G.prover H).second (keys₃ F H G)
      ρ.second (mid₃ F H G w₀ rc x tr ρ) (seatOf F.second.blocksInOrder G.second) (earlierOf F 2)
          F.second.blocksInOrder b := by
  obtain ⟨-, tr', -, -, -, hs₁, hs₂, hs₃⟩ := ready_ok hR
  exact ⟨seat_ok _ 0 Face.own x F.first.blocksInOrder G.first _ ρ.first _ (by funext a; rfl) hF.seat₁
      hF.rows₁ hF.nd₁ fun b hb g hg => (chain_facts _ _ hs₁ b hb).2.2 g hg,
    seat_ok _ 1 Face.shared (H.key x) F.shared.blocksInOrder G.shared _ ρ.shared _ (by funext a; rfl)
      hF.seat₂ hF.rows₂ hF.nd₂ fun b hb g hg => (chain_facts _ _ hs₂ b hb).2.2 g hg,
    seat_ok _ 2 Face.own x F.second.blocksInOrder G.second _ ρ.second _ (by funext a; rfl) hF.seat₃
      hF.rows₃ hF.nd₃ fun b hb g hg => (chain_facts _ _ hs₃ b hb).2.2 g hg⟩

theorem stage₁ (hF : FileOk F Bk G) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    (items₁ F H G w₀ rc x tr ρ).map Item.stage =
      (chainActs F Bk 0 (treeAsks F ρ 0) (tellerOf G.sims.first x)
        (fun a => G.sims.first.any (·.addr.place == a)) Act.judge₁ F.first.blocksInOrder 0 ρ.first).map
        (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ)) :=
  chainItems_stage x _ _ 0 0 _ _ _ Face.own x (G.prover H).first _ ρ.first _ (ver₁ F x _) _ _ _
    F.first.blocksInOrder 0 ρ.first (seats_ok hF hR).1

theorem stage₂ (hF : FileOk F Bk G) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    (items₂ F H G w₀ rc x tr ρ).map Item.stage =
      (chainActs F Bk 1 (treeAsks F ρ 1) (tellerOf G.sims.shared (H.key x))
        (fun a => G.sims.shared.any (·.addr.place == a)) Act.judge₂ F.shared.blocksInOrder 0 ρ.shared).map
        (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ)) :=
  chainItems_stage x _ _ 1 0 _ _ _ Face.shared (H.key x) (G.prover H).shared _ ρ.shared _
    (ver₂ F x _) _ _ _ F.shared.blocksInOrder 0 ρ.shared (seats_ok hF hR).2.1

theorem stage₃ (hF : FileOk F Bk G) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    (items₃ F H G w₀ rc x tr ρ).map Item.stage =
      (chainActs F Bk 2 (treeAsks F ρ 2) (tellerOf G.sims.second x)
        (fun a => G.sims.second.any (·.addr.place == a)) Act.judge₃ F.second.blocksInOrder 0 ρ.second).map
        (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ)) :=
  chainItems_stage x _ _ 2 F.lastChainFirstTreeNumber _ _ _ Face.own x (G.prover H).second _ ρ.second _
    (ver₃ F x _) _ _ _ F.second.blocksInOrder 0 ρ.second (seats_ok hF hR).2.2

/-- **The items' stages are those of the session's steps.** -/
theorem file_stage (hF : FileOk F Bk G) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    (fileItems F H G w₀ rc x tr ρ).map Item.stage =
      (theActs F Bk G.sims H.key x ρ).map
        (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ)) := by
  unfold fileItems theActs
  rw [List.map_append, List.map_append, List.map_cons, List.map_append, List.map_append,
    List.map_cons, stage₁ hF hR, stage₂ hF hR, stage₃ hF hR]
  rfl

/-- **A file.** `z₁`, `z₂`, `z₃`: at all coins, the ends of the three walks. `hOn₁`, `hOn₂`, `hOn₃`
may use `OpenedAt` at the part's state, at `preOf` (Honest/Rule.lean) of `earlierOf`
(Honest/Owed.lean) and the chain's list at the part's place. It is paid out of `hI`: `ChainInv.tie`
(Honest/Law/Rule/ChainStep.lean) in `i₁`, `i₂`, `i₃`, which `file_inv` proves. -/
theorem file_here (hF : FileOk F Bk G)
    (z₁ : Coins Bk → ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (z₂ : Coins Bk → ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀)
    (z₃ : Coins Bk → ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X)
    (hI : ∀ k, FileInv F Bk H G w₀ rc x tr ρ k (z₁ k) (z₂ k) (z₃ k))
    {k₀ : Coins Bk} {R₀ : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR₀ : ready F Bk (G.prover H) w₀ rc x k₀ = .ok R₀)
    (hOn₁ : (∀ b ∈ F.first.blocksInOrder, ∀ p, seatOf F.first.blocksInOrder G.first b = some p →
      ∀ (k : Coins Bk) (u : Member _ _ _ _) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins)
        (m : Mid _ _) (y₁ : List Played × Mid _ _) (lp la : List Played) (kp ku kq : List _),
      u ∈ p.1.members → Z.live 0 = true →
      Z.laid = ((Stand.start F x).laid).add 0 (pairsBy (treeAsks F ρ 0) lp 0) →
      ((z₁ k).core).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] →
      SegAt (keys₁ F H G) ⟨p.1.block.place, u.number⟩ kp ku kq → lp.length = kp.length →
      (∀ q ∈ readsOf 0 0 (fun _ _ => none) (fun _ => none) (u.rounds.map (·.1)) ds,
        q ∈ (bareReads F ρ).1) →
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p.1.block.place, u.number⟩ u.part = .ok c →
      play (u.part.steps p.1.block.name ⟨p.1.block.place, u.number⟩ u.rounds
        (see₁ w₀ rc x tr) c) ds [] m = .ok y₁ →
      (dryAt (keys₁ F H G) ρ.first
        (mid₁ H w₀ rc x tr) ⟨p.1.block.place, u.number⟩).st = m.st →
      (dryAt (keys₁ F H G) ρ.first
        (mid₁ H w₀ rc x tr) ⟨p.1.block.place, u.number⟩).loc = m.loc →
      m.seen = (Z.laid.front 0 (stF F H w₀ rc ρ)).seen →
      OpenedAt (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder p.1.block.place) m
        (Z.laid.front 0 (stF F H w₀ rc ρ)) →
      p.2 u c.2.2 m (Z.laid.front 0 (stF F H w₀ rc ρ)) ∧
        (Z.laid.front 0 (stF F H w₀ rc ρ)).holds 0 0 (u.rounds.map (·.1)) ds = true))
    (hOn₂ : (∀ b ∈ F.shared.blocksInOrder, ∀ p, seatOf F.shared.blocksInOrder G.shared b = some p →
      ∀ (k : Coins Bk) (u : Member _ _ _ _) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins)
        (m : Mid _ _) (y₁ : List Played × Mid _ _) (lp la : List Played) (kp ku kq : List _),
      u ∈ p.1.members → Z.live 1 = true →
      Z.laid = (laidOf F ρ (z₁ k).laid [] []).add 1 (pairsBy (treeAsks F ρ 1) lp 0) →
      ((z₂ k).core).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] →
      SegAt (keys₂ F H G) ⟨p.1.block.place, u.number⟩ kp ku kq → lp.length = kp.length →
      (∀ q ∈ readsOf 1 0 (fun _ _ => none) (fun _ => none) (u.rounds.map (·.1)) ds,
        q ∈ (bareReads F ρ).2.1) →
      lendPart Bk (Bk.rowsOf 1) (k.look 1) ⟨p.1.block.place, u.number⟩ u.part = .ok c →
      play (u.part.steps p.1.block.name ⟨p.1.block.place, u.number⟩ u.rounds
        (see₂ H w₀ rc x) c) ds [] m = .ok y₁ →
      (dryAt (keys₂ F H G) ρ.shared
        (startShared H ⟨w₀, rc, H.key x⟩) ⟨p.1.block.place, u.number⟩).st = m.st →
      (dryAt (keys₂ F H G) ρ.shared
        (startShared H ⟨w₀, rc, H.key x⟩) ⟨p.1.block.place, u.number⟩).loc = m.loc →
      m.seen = (Z.laid.front 1 (stF F H w₀ rc ρ)).seen →
      OpenedAt (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder p.1.block.place) m
        (Z.laid.front 1 (stF F H w₀ rc ρ)) →
      p.2 u c.2.2 m (Z.laid.front 1 (stF F H w₀ rc ρ)) ∧
        (Z.laid.front 1 (stF F H w₀ rc ρ)).holds 1 0 (u.rounds.map (·.1)) ds = true))
    (hOn₃ : (∀ b ∈ F.second.blocksInOrder, ∀ p, seatOf F.second.blocksInOrder G.second b = some p →
      ∀ (k : Coins Bk) (u : Member _ _ _ _) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins)
        (m : Mid _ _) (y₁ : List Played × Mid _ _) (lp la : List Played) (kp ku kq : List _),
      u ∈ p.1.members → Z.live 2 = true →
      Z.laid = (laidOf F ρ (z₁ k).laid (z₂ k).laid []).add 2 (pairsBy (treeAsks F ρ 2) lp 0) →
      ((z₃ k).core).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] →
      SegAt (keys₃ F H G) ⟨p.1.block.place, u.number⟩ kp ku kq → lp.length = kp.length →
      (∀ q ∈ readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none) (u.rounds.map (·.1)) ds,
        q ∈ (bareReads F ρ).2.2) →
      lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨p.1.block.place, u.number⟩ u.part = .ok c →
      play (u.part.steps p.1.block.name ⟨p.1.block.place, u.number⟩ u.rounds
        (see₁ w₀ rc x tr) c) ds [] m = .ok y₁ →
      (dryAt (keys₃ F H G) ρ.second
        (mid₃ F H G w₀ rc x tr ρ) ⟨p.1.block.place, u.number⟩).st = m.st →
      (dryAt (keys₃ F H G) ρ.second
        (mid₃ F H G w₀ rc x tr ρ) ⟨p.1.block.place, u.number⟩).loc = m.loc →
      m.seen = (Z.laid.front 2 (stF F H w₀ rc ρ)).seen →
      OpenedAt (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder p.1.block.place) m
        (Z.laid.front 2 (stF F H w₀ rc ρ)) →
      p.2 u c.2.2 m (Z.laid.front 2 (stF F H w₀ rc ρ)) ∧
        (Z.laid.front 2 (stF F H w₀ rc ρ)).holds 2 F.lastChainFirstTreeNumber (u.rounds.map (·.1)) ds = true)) :
    HereAll (Stand.start F x) [] (fileItems F H G w₀ rc x tr ρ) := by
  obtain ⟨ok₁, ok₂, ok₃⟩ := seats_ok (tr := tr) (ρ := ρ) hF hR₀
  have H1 : HereAll (Stand.start F x) [] (items₁ F H G w₀ rc x tr ρ) :=
    chain_here x _ _ 0 0 _ (tellerOf G.sims.first x)
      (fun a => G.sims.first.any (·.addr.place == a)) Face.own x (G.prover H).first _ ρ.first _
      (ver₁ F x _) (see₁ w₀ rc x tr) _ (bareReads F ρ).1 (earlierOf F 0) F.first.blocksInOrder (Stand.start F
                   x)
      (fun _ => ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩) (fun _ => (Stand.start F x).laid)
      (fun k => (z₁ k).core) F.first.blocksInOrder 0 ρ.first [] [] hF.nd₁ hF.sh₁
      (fun b _ cs => hF.cuts b.place cs)
      (look_ok _ 0 Face.own x F.first.blocksInOrder G.first _ ρ.first _ (by funext a; rfl) hF.seat₁ hF.rows₁
        hF.nd₁) ok₁ hOn₁ fun k => by
        obtain ⟨ss, c, h⟩ := (hI k).i₁
        exact ⟨ss, c, [], [], h⟩
  have H2 : HereAll (Stand.start F x) ([] ++ (items₁ F H G w₀ rc x tr ρ).map Item.stage)
      (items₂ F H G w₀ rc x tr ρ) :=
    chain_here x _ _ 1 0 _ (tellerOf G.sims.shared (H.key x))
      (fun a => G.sims.shared.any (·.addr.place == a)) Face.shared (H.key x) (G.prover H).shared _
      ρ.shared _ (ver₂ F x _) (see₂ H w₀ rc x) _ (bareReads F ρ).2.1 (earlierOf F 1) F.shared.blocksInOrder
      (Stand.start F x)
      (fun _ => ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩)
      (fun k => laidOf F ρ (z₁ k).laid [] []) (fun k => (z₂ k).core) F.shared.blocksInOrder 0 ρ.shared _
      [] hF.nd₂ hF.sh₂ (fun b _ cs => hF.cuts b.place cs)
      (look_ok _ 1 Face.shared (H.key x) F.shared.blocksInOrder G.shared _ ρ.shared _ (by funext a; rfl)
        hF.seat₂ hF.rows₂ hF.nd₂) ok₂ hOn₂ fun k => by
        obtain ⟨ss, c, h⟩ := (hI k).i₂
        refine ⟨ss, c, [], [], ?_⟩
        rw [List.nil_append, stage₁ hF hR₀, (hI k).r₁]
        exact h
  have H3 : HereAll (Stand.start F x)
      (([] ++ (items₁ F H G w₀ rc x tr ρ ++ items₂ F H G w₀ rc x tr ρ).map Item.stage) ++
        [Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ) (.door : Act F)])
      (items₃ F H G w₀ rc x tr ρ) :=
    chain_here x _ _ 2 F.lastChainFirstTreeNumber _ (tellerOf G.sims.second x)
      (fun a => G.sims.second.any (·.addr.place == a)) Face.own x (G.prover H).second _ ρ.second _
      (ver₃ F x _) (see₁ w₀ rc x tr) _ (bareReads F ρ).2.2 (earlierOf F 2) F.second.blocksInOrder
      (Stand.start F x)
      (fun k => ⟨2, F.lastChainFirstTreeNumber, (G.prover H).storedWords w₀ rc,
        treeThird (z₁ k).laid (z₂ k).laid⟩)
      (fun k => laidOf F ρ (z₁ k).laid (z₂ k).laid []) (fun k => (z₃ k).core) F.second.blocksInOrder 0
      ρ.second _ [] hF.nd₃ hF.sh₃ (fun b _ cs => hF.cuts b.place cs)
      (look_ok _ 2 Face.own x F.second.blocksInOrder G.second _ ρ.second _ (by funext a; rfl) hF.seat₃
        hF.rows₃ hF.nd₃) ok₃ hOn₃ fun k => by
        obtain ⟨ss, c, h⟩ := (hI k).i₃
        refine ⟨ss, c, [], [], ?_⟩
        rw [List.nil_append, List.map_append, stage₁ hF hR₀, stage₂ hF hR₀, Kit.real_append,
          Kit.real_append, (hI k).r₁, (hI k).r₂]
        exact h
  unfold fileItems
  exact HereAll.append _ _ _ (HereAll.append _ _ _ H1 H2) (HereAll.cons (fun C e => by cases e) H3)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.seats_ok
#print axioms ProofFile.Honest.stage₁
#print axioms ProofFile.Honest.stage₂
#print axioms ProofFile.Honest.stage₃
#print axioms ProofFile.Honest.file_stage
#print axioms ProofFile.Honest.file_here
#print axioms ProofFile.Honest.stF
#print axioms ProofFile.Honest.keys₁
#print axioms ProofFile.Honest.keys₂
#print axioms ProofFile.Honest.keys₃
#print axioms ProofFile.Honest.see₁
#print axioms ProofFile.Honest.see₂
#print axioms ProofFile.Honest.realF
#print axioms ProofFile.Honest.items₁
#print axioms ProofFile.Honest.items₂
#print axioms ProofFile.Honest.items₃
#print axioms ProofFile.Honest.fileItems
