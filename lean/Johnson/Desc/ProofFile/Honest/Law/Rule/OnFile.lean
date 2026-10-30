-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OnFile.lean: `On` and `Before.holds`, at a file: the three
hypotheses `hOn₁`, `hOn₂`, `hOn₃` of `file_here` (Honest/Law/Rule/FileHere.lean), at given coins
(`on₁`, `on₂`, `on₃`), from `Owed` (Honest/Owed.lean), `FileOk` and `FileInv`, at an input in `Rel`,
at challenges that the rounds can draw, outside the one silent set (`silentAt`, Honest/Rule.lean).
The proofs use `on_chain` (Honest/Law/Rule/OnAt.lean), the lemmas on a run at an address
(Honest/Law/RunAtFile.lean, Honest/Law/RunMidFile.lean, Honest/Law/RunBefore.lean), `midDry_first`,
`midDry_shared` and `midDry_second` (Honest/Law/Rule/MidDry.lean), and `holds_run`
(Honest/Law/Rule/HoldsRun.lean). It is the sixteenth piece of the proof of `rowOk_of`
(Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `of_orRefused`, `run_setup`   a small one; what a run that goes through says of its `Step`s
  2  `on₁`, `on₂`, `on₃`   the three hypotheses, chain by chain

Limits.
  * `Owed.owed` speaks at the walk's own state (`midAtW`, `midSharedAtW`, Honest/MidW.lean); the
    rule's state m comes with `OpenedAt` (Honest/Law/Rule/OpenedAt.lean); `tie_first`, `tie_shared`
    and `tie_second_at` (Honest/Law/Rule/OpenedRun.lean) join the two fields. That `OpenedAt` is a
    hypothesis inside each of the three ends, in `file_here`'s own form; `row_here`
    (Honest/Law/Rule/RowHere.lean) pays it.
  * Of `FileInv` the field `run` alone is used.
  * Hypotheses that the prose above does not name: `Prover.trace … = some` (the request has a
    trace): `run_setup`, `on₁`, `on₂`, `on₃`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Owed
import Johnson.Desc.ProofFile.Honest.Law.RunMidFile
import Johnson.Desc.ProofFile.Honest.Law.RunBefore
import Johnson.Desc.ProofFile.Honest.Law.Rule.OnAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.MidDry
import Johnson.Desc.ProofFile.Honest.Law.Rule.HoldsRun
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileHere
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- Where `orRefused` (Honest/Owed.lean) returns a state, its argument has returned that state. -/
theorem of_orRefused {W Y : Type} {e : Except Refusal (Option (Mid W Y))} {m : Mid W Y}
    (h : orRefused e = .ok m) : e = .ok (some m) := by
  unfold orRefused at h
  obtain ⟨o, ho, h⟩ := of_bind_ok h
  cases o with
  | none => cases h
  | some m' =>
    have e' : m' = m := Except.ok.inj h
    rw [ho, e']

/-- What a run that goes through says of its `Step`s. -/
theorem run_setup {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws}
    (htr : H.trace w₀ x = some tr) {k : Coins Bk} {r : RunC F}
    (hrun : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r) :
    ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R ∧
      (∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots) ∧
      (∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots) ∧
      (∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) ∧
      R.first.map Step.key = keys₁ F H G ∧ R.shared.map Step.key = keys₂ F H G ∧
      R.second.map Step.key = keys₃ F H G ∧ R.start₁ (G.prover H) = mid₁ H w₀ rc x tr ∧
      R.start₂ (G.prover H) = startShared H ⟨w₀, rc, H.key x⟩ ∧ R.own = ⟨w₀, rc, x, tr⟩ ∧
      (∀ s ∈ R.first, s.addr.place.chain = 1) ∧ ∀ s ∈ R.second, s.addr.place.chain = 3 := by
  obtain ⟨R, a₁, w₁, a₂, w₂, a₃, w₃, hR, -, -, -, -, -, -, -, -⟩ := runC_parts hrun
  obtain ⟨-, tr', htr', hown, hcom, hs₁, hs₂, hs₃⟩ := ready_ok hR
  have etr : tr' = tr := Option.some.inj (htr'.symm.trans htr)
  subst etr
  obtain ⟨p1, -, p3⟩ := places_chain hO.places
  refine ⟨R, hR, steps_sh _ _ hs₁ hF.sh₁, steps_sh _ _ hs₂ hF.sh₂, steps_sh _ _ hs₃ hF.sh₃,
    chainSteps_keys _ _ _ hs₁, chainSteps_keys _ _ _ hs₂, chainSteps_keys _ _ _ hs₃, ?_, ?_, hown,
    steps_chain hs₁ p1, steps_chain hs₃ p3⟩
  · unfold Ready.start₁
    rw [hown]
    rfl
  · unfold Ready.start₂
    rw [hcom]
    rfl

/-- **The first chain.** -/
theorem on₁ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (htr : H.trace w₀ x = some tr) {k : Coins Bk} {z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    {z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀} {z₃ : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X}
    (hI : FileInv F Bk H G w₀ rc x tr ρ k z₁ z₂ z₃) :
    ∀ b ∈ F.first.blocksInOrder, ∀ p, seatOf F.first.blocksInOrder G.first b = some p →
      ∀ (u : Member _ _ _ _) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins)
        (m : Mid _ _) (y₁ : List Played × Mid _ _) (lp la : List Played) (kp ku kq : List _),
      u ∈ p.1.members → Z.live 0 = true →
      Z.laid = ((Stand.start F x).laid).add 0 (pairsBy (treeAsks F ρ 0) lp 0) →
      (z₁.core).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] →
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
        (Z.laid.front 0 (stF F H w₀ rc ρ)).holds 0 0 (u.rounds.map (·.1)) ds = true := by
  intro b _ p hseat u ds Z c m y₁ lp la kp ku kq hu _ hZ hfin hne hseg hlp hbq hl hplay e1 e2 hseen
    hopen
  obtain ⟨L, hL, hσ, hOnE⟩ := seat_inv hseat
  obtain ⟨r, hrun, hpl, -⟩ := hI.run
  obtain ⟨R, hR, o₁, o₂, o₃, k₁, k₂, k₃, s₁, s₂, ow, c₁, c₃⟩ := run_setup hO hF htr hrun
  obtain ⟨hRO, -, -, -⟩ := runOk_of hrun
  have hp1 : r.run.played.1 = z₁.laid := by rw [hpl]
  have hp2 : r.run.played.2.1 = z₂.laid := by rw [hpl]
  have hp3 : r.run.played.2.2 = z₃.laid := by rw [hpl]
  have hZl : Z.laid = laidOf F ρ lp [] [] := by
    rw [hZ]
    exact add_first _ lp [] []
  have hP : r.run.played.1 = lp ++ y₁.1 ++ la := hp1.trans hfin
  refine ⟨?_, ?_⟩
  · rw [hOnE]
    exact on_chain ρ (H.storedWords w₀ rc) 0 F.first.blocksInOrder L p.1 hσ u hu k _ r
      ((hO.owed w₀ rc x hrel k ρ r hρ hsil hrun).1 L hL) hRO R.first ρ.first (keys₁ F H G) k₁
      (mid₁ H w₀ rc x tr) r.run.played.1 (fun ha => at_first hrun hR o₁ o₂ o₃ hO.places ha) []
      (treeAsks F ρ 0)
      (fun ha hs hc m' hm' => by
        have hm'' := of_orRefused hm'
        obtain ⟨m'', g1, g2⟩ := mid_first hrun hR o₁ o₂ o₃ hO.places ha hs hc
        have e : m'' = m' := Option.some.inj (Except.ok.inj (g1.symm.trans hm''))
        subst e
        obtain ⟨d1, d2⟩ := midDry_first hR ha hm''
        rw [k₁, s₁] at d1 d2
        have t : OpenedAt (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder p.1.block.place) m''
            (r.run.beforeAt (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
              ⟨p.1.block.place, u.number⟩) := by
          rw [before_first hrun hR o₁ o₂ o₃ hO.places ha hs (treeAsks F ρ 0)
            (shown_is hRO 0 (by decide))]
          exact tie_first hrun hR ha hm''
        exact ⟨g2, d1, d2, t⟩)
      (fun ha hs st => before_first hrun hR o₁ o₂ o₃ hO.places ha hs (treeAsks F ρ 0)
        (shown_is hRO 0 (by decide)) st)
      (see₁ w₀ rc x tr) ds Z c m y₁ lp la kp ku kq (by rw [hZl]; rfl) hP hne hseg hlp hl hplay e1
      e2 hseen hopen
  · rw [hZl]
    have h := hRO
    rw [hP, List.append_assoc] at h
    exact holds_run (l₀ := lp) (t₀ := y₁.1 ++ la) (l₁ := []) (t₁ := r.run.played.2.1) (l₂ := [])
      (t₂ := r.run.played.2.2) h 0 0 (by decide) (fun _ => (run_src hrun).1)
      (fun e => by cases e) _ _ fun q hq => by
        show q ∈ r.run.reads.1.map Read.bare
        rw [hRO.bare₀]
        exact hbq q hq

/-- **The shared chain.** -/
theorem on₂ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (htr : H.trace w₀ x = some tr) {k : Coins Bk} {z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    {z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀} {z₃ : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X}
    (hI : FileInv F Bk H G w₀ rc x tr ρ k z₁ z₂ z₃) :
    ∀ b ∈ F.shared.blocksInOrder, ∀ p, seatOf F.shared.blocksInOrder G.shared b = some p →
      ∀ (u : Member _ _ _ _) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins)
        (m : Mid _ _) (y₁ : List Played × Mid _ _) (lp la : List Played) (kp ku kq : List _),
      u ∈ p.1.members → Z.live 1 = true →
      Z.laid = (laidOf F ρ z₁.laid [] []).add 1 (pairsBy (treeAsks F ρ 1) lp 0) →
      (z₂.core).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] →
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
        (Z.laid.front 1 (stF F H w₀ rc ρ)).holds 1 0 (u.rounds.map (·.1)) ds = true := by
  intro b _ p hseat u ds Z c m y₁ lp la kp ku kq hu _ hZ hfin hne hseg hlp hbq hl hplay e1 e2 hseen
    hopen
  obtain ⟨L, hL, hσ, hOnE⟩ := seat_inv hseat
  obtain ⟨r, hrun, hpl, -⟩ := hI.run
  obtain ⟨R, hR, o₁, o₂, o₃, k₁, k₂, k₃, s₁, s₂, ow, c₁, c₃⟩ := run_setup hO hF htr hrun
  obtain ⟨hRO, -, -, -⟩ := runOk_of hrun
  have hp1 : r.run.played.1 = z₁.laid := by rw [hpl]
  have hp2 : r.run.played.2.1 = z₂.laid := by rw [hpl]
  have hp3 : r.run.played.2.2 = z₃.laid := by rw [hpl]
  have hZl : Z.laid = laidOf F ρ z₁.laid lp [] := by
    rw [hZ]
    exact add_shared _ lp _ []
  have hP : r.run.played.2.1 = lp ++ y₁.1 ++ la := hp2.trans hfin
  refine ⟨?_, ?_⟩
  · rw [hOnE]
    exact on_chain ρ (H.storedWords w₀ rc) 1 F.shared.blocksInOrder L p.1 hσ u hu k _ r
      ((hO.owed w₀ rc x hrel k ρ r hρ hsil hrun).2.1 L hL) hRO R.shared ρ.shared (keys₂ F H G) k₂
      (startShared H ⟨w₀, rc, H.key x⟩) r.run.played.2.1
      (fun ha => at_shared hrun hR o₁ o₂ o₃ hO.places ha) [] (treeAsks F ρ 1)
      (fun ha hs hc m' hm' => by
        have hm'' := of_orRefused hm'
        obtain ⟨m'', g1, g2⟩ := mid_shared hrun hR o₁ o₂ o₃ hO.places ha hs hc
        have e : m'' = m' := Option.some.inj (Except.ok.inj (g1.symm.trans hm''))
        subst e
        obtain ⟨d1, d2⟩ := midDry_shared hR hm''
        rw [k₂, s₂] at d1 d2
        have t : OpenedAt (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder p.1.block.place) m''
            (r.run.beforeAt (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
              ⟨p.1.block.place, u.number⟩) := by
          rw [before_shared hrun hR o₁ o₂ o₃ hO.places ha hs (treeAsks F ρ 1)
            (shown_is hRO 1 (by decide))]
          exact tie_shared hrun hR hm''
        exact ⟨g2, d1, d2, t⟩)
      (fun ha hs st => before_shared hrun hR o₁ o₂ o₃ hO.places ha hs (treeAsks F ρ 1)
        (shown_is hRO 1 (by decide)) st)
      (see₂ H w₀ rc x) ds Z c m y₁ lp la kp ku kq (by rw [hZl]; rfl) hP hne hseg hlp hl hplay e1
      e2 hseen hopen
  · rw [hZl]
    have h := hRO
    rw [hp1, hP, List.append_assoc, ← List.append_nil z₁.laid] at h
    exact holds_run (l₀ := z₁.laid) (t₀ := []) (l₁ := lp) (t₁ := y₁.1 ++ la) (l₂ := [])
      (t₂ := r.run.played.2.2) h 1 0 (by decide) (fun _ => (run_src hrun).2)
      (fun e => by cases e) _ _ fun q hq => by
        show q ∈ r.run.reads.2.1.map Read.bare
        rw [hRO.bare₁]
        exact hbq q hq

/-- **The second chain.** -/
theorem on₃ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x)
    (hρ : ρ.due F = true) (hsil : silentAt F (G.prover H) w₀ rc x ρ = none)
    (htr : H.trace w₀ x = some tr) {k : Coins Bk} {z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    {z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀} {z₃ : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X}
    (hI : FileInv F Bk H G w₀ rc x tr ρ k z₁ z₂ z₃) :
    ∀ b ∈ F.second.blocksInOrder, ∀ p, seatOf F.second.blocksInOrder G.second b = some p →
      ∀ (u : Member _ _ _ _) (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins)
        (m : Mid _ _) (y₁ : List Played × Mid _ _) (lp la : List Played) (kp ku kq : List _),
      u ∈ p.1.members → Z.live 2 = true →
      Z.laid = (laidOf F ρ z₁.laid z₂.laid []).add 2 (pairsBy (treeAsks F ρ 2) lp 0) →
      (z₃.core).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] →
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
        (Z.laid.front 2 (stF F H w₀ rc ρ)).holds 2 F.lastChainFirstTreeNumber (u.rounds.map (·.1)) ds = true := by
  intro b _ p hseat u ds Z c m y₁ lp la kp ku kq hu _ hZ hfin hne hseg hlp hbq hl hplay e1 e2 hseen
    hopen
  obtain ⟨L, hL, hσ, hOnE⟩ := seat_inv hseat
  obtain ⟨r, hrun, hpl, -⟩ := hI.run
  obtain ⟨R, hR, o₁, o₂, o₃, k₁, k₂, k₃, s₁, s₂, ow, c₁, c₃⟩ := run_setup hO hF htr hrun
  obtain ⟨hRO, -, -, -⟩ := runOk_of hrun
  have hp1 : r.run.played.1 = z₁.laid := by rw [hpl]
  have hp2 : r.run.played.2.1 = z₂.laid := by rw [hpl]
  have hp3 : r.run.played.2.2 = z₃.laid := by rw [hpl]
  have hZl : Z.laid = laidOf F ρ z₁.laid z₂.laid lp := by
    rw [hZ]
    exact add_second _ lp _ _
  have hP : r.run.played.2.2 = lp ++ y₁.1 ++ la := hp3.trans hfin
  refine ⟨?_, ?_⟩
  · rw [hOnE]
    exact on_chain ρ (H.storedWords w₀ rc) 2 F.second.blocksInOrder L p.1 hσ u hu k _ r
      ((hO.owed w₀ rc x hrel k ρ r hρ hsil hrun).2.2 L hL) hRO R.second ρ.second (keys₃ F H G) k₃
      (mid₃ F H G w₀ rc x tr ρ) r.run.played.2.2
      (fun ha => at_second hrun hR o₁ o₂ o₃ hO.places ha)
      (shownBy 0 (treeAsks F ρ 0) z₁.laid 0 ++ shownBy 1 (treeAsks F ρ 1) z₂.laid 0)
      (treeAsks F ρ 2)
      (fun ha hs hc m' hm' => by
        have hm'' := of_orRefused hm'
        obtain ⟨m'', g1, g2⟩ := mid_second hrun hR o₁ o₂ o₃ hO.places ha hs hc
        have e : m'' = m' := Option.some.inj (Except.ok.inj (g1.symm.trans hm''))
        subst e
        have hoff := off_chain (show (3 : Nat) ≠ 1 by decide) c₃ c₁ ha
        have hn : R.first.any (·.addr == ⟨p.1.block.place, u.number⟩) = false :=
          List.any_eq_false.2 fun s hs' => by
            rw [hoff s hs']
            exact Bool.false_ne_true
        obtain ⟨d1, d2⟩ := midDry_second hR hn hm''
        rw [k₁, k₂, k₃, s₁, s₂, ow] at d1 d2
        have t : OpenedAt (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder p.1.block.place) m''
            (r.run.beforeAt (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
              ⟨p.1.block.place, u.number⟩) := by
          rw [before_second hrun hR o₁ o₂ o₃ hO.places ha hs (treeAsks F ρ 0) (treeAsks F ρ 1)
            (treeAsks F ρ 2) (shown_is hRO 0 (by decide)) (shown_is hRO 1 (by decide))
            (shown_is hRO 2 (by decide))]
          exact tie_second_at hrun hR hn hm''
        refine ⟨?_, d1, d2, t⟩
        rw [g2, hp1, hp2]
        unfold roundsOff
        rw [List.map_append]
        show _ = roundsOff (shownBy 0 (treeAsks F ρ 0) z₁.laid 0) ++
          roundsOff (shownBy 1 (treeAsks F ρ 1) z₂.laid 0) ++ _
        rw [roundsOff_by, roundsOff_by])
      (fun ha hs st => by
        have hb := before_second hrun hR o₁ o₂ o₃ hO.places ha hs (treeAsks F ρ 0) (treeAsks F ρ 1)
          (treeAsks F ρ 2) (shown_is hRO 0 (by decide)) (shown_is hRO 1 (by decide))
          (shown_is hRO 2 (by decide)) st
        rw [hp1, hp2] at hb
        exact hb)
      (see₁ w₀ rc x tr) ds Z c m y₁ lp la kp ku kq (by rw [hZl]; rfl) hP hne hseg hlp hl hplay e1
      e2 hseen hopen
  · rw [hZl]
    have h := hRO
    rw [hp1, hp2, hP, List.append_assoc, ← List.append_nil z₁.laid,
      ← List.append_nil z₂.laid] at h
    exact holds_run (l₀ := z₁.laid) (t₀ := []) (l₁ := z₂.laid) (t₁ := []) (l₂ := lp)
      (t₂ := y₁.1 ++ la) h 2 F.lastChainFirstTreeNumber (by decide) (fun e => absurd rfl e)
      (fun _ c hc hne' => by
        have h01 : c = 0 ∨ c = 1 := by omega
        rcases h01 with rfl | rfl <;> rfl) _ _ fun q hq => by
        show q ∈ r.run.reads.2.2.map Read.bare
        rw [hRO.bare₂]
        exact hbq q hq

end ProofFile.Honest

#print axioms ProofFile.Honest.of_orRefused
#print axioms ProofFile.Honest.run_setup
#print axioms ProofFile.Honest.on₁
#print axioms ProofFile.Honest.on₂
#print axioms ProofFile.Honest.on₃
