-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Model.lean: the model. A run of the prover of
Honest/Walk.lean that goes through is the fold at coins (Honest/Law/Rule/Stages.lean: `Kit.real`)
over a session's steps (Honest/Law/Rule/Session.lean: `theActs`), with the honest side of the
description's lists of parts beside each step (Honest/Law/Rule/Real.lean: `realAt`). What is
produced is what the run's rounds show, and the verifier's three states are the run's (`model`).

  1  `FileOk`   a definition: what the model uses of a description, a book and its lists of parts:
     tests and conditions without a coin
  2  `add_first`, `add_shared`, `add_second`   what is produced, chain by chain
  3  `end_mid`   the state of the prover's run at the end of a chain in which the verifier has not
     rejected
  4  `model`   the main lemma

Limits.
  * Hypotheses that the prose above does not name: `Prover.trace … = some` (the request has a
    trace): `model`.
  * The states that `dryAt` and `dryEnd` (Honest/Law/Rule/Real.lean) are given hand no columns
    (`none`): of what these return the state and the challenges alone are read. What the field
    `opened` holds at the three chains' starts is paid inside `model` (`TieAt.start`,
    Honest/Law/Rule/OpenedStart.lean; `tie_second`, Honest/Law/Rule/OpenedFile.lean), and so is
    `hsrc`.
  * `realAt` hands each part the columns that what has been produced holds for the reads before its
    place (`partShows`, Honest/Law/Rule/Real.lean); so `model` speaks also of parts that read them.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainEnd
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 What the model uses -/

/-- **What the model uses of a description, a book and its lists of parts.** `fileOk_of`
(Honest/Law/Rule/FileOkOf.lean) proves it from `Owed`, where one run goes through. -/
structure FileOk (F : FileDescription Xi) (Bk : ProverCoinCounts) (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Prop where
  /- no two sub-protocols of a chain's flat list are at one place (likewise `nd₂`, `nd₃`) -/
  nd₁ : (F.first.blocksInOrder.map (·.place)).Nodup
  nd₂ : (F.shared.blocksInOrder.map (·.place)).Nodup
  nd₃ : (F.second.blocksInOrder.map (·.place)).Nodup
  /- each round has as many oracle messages as its entry has roots; asked over `rounds.zip oracles`,
  so not of a round beyond the shorter list (likewise `sh₂`, `sh₃`) -/
  sh₁ : ∀ b ∈ F.first.blocksInOrder, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots
  sh₂ : ∀ b ∈ F.shared.blocksInOrder, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots
  sh₃ : ∀ b ∈ F.second.blocksInOrder, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots
  /- each list of parts has a side at its chain's flat list, and the side passes `Side.fits`
  (likewise `seat₂`, `seat₃`) -/
  seat₁ : ∀ L ∈ G.first, ∃ σ, L.side F.first.blocksInOrder = some σ ∧ σ.fits = true
  seat₂ : ∀ L ∈ G.shared, ∃ σ, L.side F.shared.blocksInOrder = some σ ∧ σ.fits = true
  seat₃ : ∀ L ∈ G.second, ∃ σ, L.side F.second.blocksInOrder = some σ ∧ σ.fits = true
  /- no two lists of parts of a chain are at one place (likewise `rows₂`, `rows₃`) -/
  rows₁ : (G.first.map (·.place)).Nodup
  rows₂ : (G.shared.map (·.place)).Nodup
  rows₃ : (G.second.map (·.place)).Nodup
  /- no part of a cut of the book has 0 rounds -/
  cuts : ∀ a cs, Bk.cuts.lookup a = some cs → ∀ n ∈ cs, n ≠ 0

/-! ## 2 What is produced, chain by chain -/

theorem add_first (t : Nat → List Nat) (l : List Played) (B C : List (Nat × Shown × Fmt.Drawn)) :
    (⟨[], B, C⟩ : Laid).add 0 (pairsBy t l 0) = ⟨shownBy 0 t l 0, B, C⟩ := by
  rw [shownBy_pairs]
  rfl

theorem add_shared (t : Nat → List Nat) (l : List Played) (A C : List (Nat × Shown × Fmt.Drawn)) :
    (⟨A, [], C⟩ : Laid).add 1 (pairsBy t l 0) = ⟨A, shownBy 1 t l 0, C⟩ := by
  rw [shownBy_pairs]
  rfl

theorem add_second (t : Nat → List Nat) (l : List Played) (A B : List (Nat × Shown × Fmt.Drawn)) :
    (⟨A, B, []⟩ : Laid).add 2 (pairsBy t l 0) = ⟨A, B, shownBy 2 t l 0⟩ := by
  rw [shownBy_pairs]
  rfl

/-! ## 3 At the end of a chain in which the verifier has not rejected -/

/-- The prover's run has a state just where the verifier has not rejected. The state of the prover's
run at the end of a chain: state and challenges are those of the dry fold
(Honest/Law/Rule/Real.lean: `dryEnd`); what it has been shown are the start's rounds and the
chain's. At whatever columns the start is handed; nothing is said on the state's field `opened`. -/
theorem end_mid {S Cl V W Y : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {hs : List (Placed V W Y)} {L : Lay}
    {bs : List (Block S Cl)} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {m₀ : Mid W Y} {s₀ : S}
    {a z : ChainProgress S Cl W Y} (hss : chainSteps B rows look v bs hs = .ok ss)
    {front : List OpenedColumn} (ha : ChainProgress.start L bs (some m₀) (some s₀) front = .ok a)
    (hw : walk L ss ds a = .ok z) :
    z.mid.isSome = z.ver.isSome ∧ ∀ m, z.mid = some m →
      m.st = (dryEnd (chainKeys bs hs) ds m₀).st ∧ m.loc = (dryEnd (chainKeys bs hs) ds m₀).loc ∧
        m.seen = m₀.seen ++ roundsOf z.laid := by
  have hC := chained_of_start ha hw (chainSteps_length bs ss hss)
  obtain ⟨h1, suf, h2, h3⟩ := chained_mid bs ss ds _ _ hss hC rfl
  refine ⟨h1, fun m hm => ?_⟩
  obtain ⟨m', hm', d1, d2, i3⟩ := h3 m hm
  have e : m' = { m₀ with opened := some front } := (Option.some.inj hm').symm
  subst e
  have hk : ss.map Step.hand = (chainKeys bs hs).map (·.2) := by
    rw [← chainSteps_keys _ _ _ hss, List.map_map]
    rfl
  have hl : z.laid = suf := h2
  refine ⟨?_, d2, by rw [hl]; exact i3⟩
  show m.st = dryFold ((chainKeys bs hs).map (·.2)) ds m₀.st
  rw [← hk]
  exact d1

/-! ## 4 The model -/

/-- **The model.** -/
theorem model {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr}
    {k : Coins Bk} {ρ : Draws} {r : RunC F} (htr : H.trace w₀ x = some tr)
    (hrun : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r) :
    Kit.real ((theActs F Bk G.sims H.key x ρ).map
        (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
          (realAt F Bk H G ⟨w₀, rc, x, tr⟩ ⟨w₀, rc, H.key x⟩ ρ))) k (Stand.start F x) =
      ⟨laidOf F ρ r.run.played.1 r.run.played.2.1 r.run.played.2.2, r.ends.1, r.ends.2.1,
        r.ends.2.2⟩ := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, -, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hrun
  obtain ⟨-, tr', htr', hown, hcom, hs₁, hs₂, hs₃⟩ := ready_ok hR
  have etr : tr' = tr := Option.some.inj (htr'.symm.trans htr)
  subst etr
  have e₁ : R.start₁ (G.prover H) = ⟨⟨⟨w₀, rc, x, tr'⟩, [], H.own₀⟩, [], [], none⟩ := by
    unfold Ready.start₁
    rw [hown]
    rfl
  have e₂ : R.start₂ (G.prover H) = startShared H ⟨w₀, rc, H.key x⟩ := by
    unfold Ready.start₂
    rw [hcom]
    rfl
  rw [e₁] at ha₁
  rw [e₂] at ha₂
  rw [hown] at hs₁ hs₃
  rw [hcom] at hs₂
  obtain ⟨b₁, n₁⟩ := end_mid hs₁ ha₁ hz₁
  obtain ⟨b₂, n₂⟩ := end_mid hs₂ ha₂ hz₂
  -- the first chain
  have c1 : Kit.real ((chainActs F Bk 0 (treeAsks F ρ 0) (tellerOf G.sims.first x)
      (fun a => G.sims.first.any (·.addr.place == a)) Act.judge₁ F.first.blocksInOrder 0 ρ.first).map
      (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
        (realAt F Bk H G ⟨w₀, rc, x, tr'⟩ ⟨w₀, rc, H.key x⟩ ρ))) k (Stand.start F x) =
      (⟨laidOf F ρ z₁.laid [] [], z₁.ver, some (F.start₂ (F.pub x)), none⟩ : Stand F) :=
    chain_file (earlier := earlierOf F 0) x ρ _ k 0 0 Face.own x F.first.blocksInOrder G.first ρ.first
      ⟨⟨⟨w₀, rc, x, tr'⟩, [], H.own₀⟩, [], [], none⟩
      ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ rfl rfl (ver₁ F x _) (Stand.start F x)
      (fun l => (l, [], [])) rfl
      (fun l => add_first _ l [] [])
      (fun l o pT h => by
        obtain ⟨n, rfl, hn⟩ := own_tab l o pT h
        exact ⟨(show (0 : Nat) ≤ 2 by decide), hn⟩)
      (fun l o pT h => by
        obtain ⟨n, rfl, -⟩ := own_tab l o pT h
        exact Or.inl rfl)
      (by funext a; rfl) hF.seat₁ hF.rows₁ hF.nd₁ hF.sh₁ hF.cuts R.first hs₁ _ _
      (fun m hm => by cases hm; exact ⟨rfl, rfl, rfl⟩) (fun _ => rfl) rfl a₁ z₁ ha₁ hz₁
      (TieAt.start laid_field rfl)
      (fun q hq => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hq))))
  -- the shared chain
  have c2 : Kit.real ((chainActs F Bk 1 (treeAsks F ρ 1) (tellerOf G.sims.shared (H.key x))
      (fun a => G.sims.shared.any (·.addr.place == a)) Act.judge₂ F.shared.blocksInOrder 0 ρ.shared).map
      (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
        (realAt F Bk H G ⟨w₀, rc, x, tr'⟩ ⟨w₀, rc, H.key x⟩ ρ))) k
      (⟨laidOf F ρ z₁.laid [] [], z₁.ver, some (F.start₂ (F.pub x)), none⟩ : Stand F) =
      (⟨laidOf F ρ z₁.laid z₂.laid [], z₁.ver, z₂.ver, none⟩ : Stand F) :=
    chain_file (earlier := earlierOf F 1) x ρ _ k 1 0 Face.shared (H.key x) F.shared.blocksInOrder G.shared
      ρ.shared
      (startShared H ⟨w₀, rc, H.key x⟩) ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ rfl rfl
      (ver₂ F x _) _ (fun l => (z₁.laid, l, [])) rfl (fun l => add_shared _ l _ [])
      (fun l o pT h => by
        obtain ⟨n, rfl, hn⟩ := own_tab l o pT h
        exact ⟨(show (1 : Nat) ≤ 2 by decide), hn⟩)
      (fun l o pT h => by
        obtain ⟨n, rfl, -⟩ := own_tab l o pT h
        exact Or.inl rfl)
      (by funext a; rfl) hF.seat₂ hF.rows₂ hF.nd₂ hF.sh₂ hF.cuts R.shared hs₂ _ _
      (fun m hm => by cases hm; exact ⟨rfl, rfl, rfl⟩) (fun _ => rfl) rfl a₂ z₂ ha₂ hz₂
      (TieAt.start laid_field rfl)
      (fun q hq => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hq))))
  -- the second chain
  have c3 : Kit.real ((chainActs F Bk 2 (treeAsks F ρ 2) (tellerOf G.sims.second x)
      (fun a => G.sims.second.any (·.addr.place == a)) Act.judge₃ F.second.blocksInOrder 0 ρ.second).map
      (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
        (realAt F Bk H G ⟨w₀, rc, x, tr'⟩ ⟨w₀, rc, H.key x⟩ ρ))) k
      (⟨laidOf F ρ z₁.laid z₂.laid [], z₁.ver, z₂.ver, door₃ F x z₁.ver z₂.ver⟩ : Stand F) =
      (⟨laidOf F ρ z₁.laid z₂.laid z₃.laid, z₁.ver, z₂.ver, z₃.ver⟩ : Stand F) :=
    chain_file (earlier := earlierOf F 2) x ρ _ k 2 F.lastChainFirstTreeNumber Face.own x F.second.blocksInOrder G.second
      ρ.second
      ⟨⟨⟨w₀, rc, x, tr'⟩,
          (dryEnd (chainKeys F.first.blocksInOrder (G.prover H).first) ρ.first
            ⟨⟨⟨w₀, rc, x, tr'⟩, [], H.own₀⟩, [], [], none⟩).st.heard ++
          (dryEnd (chainKeys F.shared.blocksInOrder (G.prover H).shared) ρ.shared
            (startShared H ⟨w₀, rc, H.key x⟩)).st.heard,
          H.meet (dryEnd (chainKeys F.first.blocksInOrder (G.prover H).first) ρ.first
            ⟨⟨⟨w₀, rc, x, tr'⟩, [], H.own₀⟩, [], [], none⟩).st.own
          (dryEnd (chainKeys F.shared.blocksInOrder (G.prover H).shared) ρ.shared
            (startShared H ⟨w₀, rc, H.key x⟩)).st⟩,
        (dryEnd (chainKeys F.first.blocksInOrder (G.prover H).first) ρ.first
          ⟨⟨⟨w₀, rc, x, tr'⟩, [], H.own₀⟩, [], [], none⟩).loc, [], none⟩
      ⟨2, F.lastChainFirstTreeNumber, (G.prover H).storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ rfl rfl
      (ver₃ F x _) _ (fun l => (z₁.laid, z₂.laid, l)) rfl (fun l => add_second _ l _ _)
      (fun l o pT h => third_tab z₁.laid z₂.laid l o pT h)
      (fun _ _ _ _ => Or.inr (Nat.le_refl 2)) (by funext a; rfl) hF.seat₃ hF.rows₃
      hF.nd₃ hF.sh₃ hF.cuts R.second hs₃ _ _
      (fun m hm => by
        cases h1 : z₁.mid with
        | none =>
          rw [h1] at hm
          cases hm
        | some m₁ =>
          cases h2 : z₂.mid with
          | none =>
            rw [h1, h2] at hm
            cases hm
          | some m₂ =>
            rw [h1, h2] at hm
            cases hm
            obtain ⟨p1, p2, p3⟩ := n₁ m₁ h1
            obtain ⟨q1, -, q3⟩ := n₂ m₂ h2
            refine ⟨?_, p2, ?_⟩
            · show (⟨R.own, m₁.st.heard ++ m₂.st.heard, H.meet m₁.st.own m₂.st⟩ :
                State (Local W₀ Rc Xi Tr) X) = _
              rw [hown, p1, q1]
            · show m₁.seen ++ m₂.seen = roundsOff (shownBy 0 (treeAsks F ρ 0) z₁.laid 0 ++
                shownBy 1 (treeAsks F ρ 1) z₂.laid 0 ++ shownBy 2 (treeAsks F ρ 2) [] 0)
              rw [p3, q3]
              unfold roundsOff
              rw [List.map_append, List.map_append]
              show _ = roundsOff (shownBy 0 (treeAsks F ρ 0) z₁.laid 0) ++
                roundsOff (shownBy 1 (treeAsks F ρ 1) z₂.laid 0) ++ []
              rw [roundsOff_by, roundsOff_by, List.append_nil]
              rfl)
      (fun hv => by
        cases h1 : z₁.ver with
        | none =>
          rw [h1] at hv
          cases hv
        | some s₁ =>
          cases h2 : z₂.ver with
          | none =>
            rw [h1, h2] at hv
            cases hv
          | some s₂ =>
            rw [h1] at b₁
            rw [h2] at b₂
            obtain ⟨m₁, g1⟩ := Option.isSome_iff_exists.1 b₁
            obtain ⟨m₂, g2⟩ := Option.isSome_iff_exists.1 b₂
            rw [g1, g2]
            rfl)
      rfl a₃ z₃ ha₃ hz₃ (tie_second hR ha₁ hz₁ ha₂ hz₂ laid_field)
      (fun q hq => List.mem_append.2 (Or.inr hq))
  unfold theActs
  rw [List.map_append, List.map_append, Kit.real_append, Kit.real_append, c1, c2]
  show Kit.real ((chainActs F Bk 2 (treeAsks F ρ 2) (tellerOf G.sims.second x)
      (fun a => G.sims.second.any (·.addr.place == a)) Act.judge₃ F.second.blocksInOrder 0 ρ.second).map
      (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
        (realAt F Bk H G ⟨w₀, rc, x, tr'⟩ ⟨w₀, rc, H.key x⟩ ρ))) k
      (⟨laidOf F ρ z₁.laid z₂.laid [], z₁.ver, z₂.ver, door₃ F x z₁.ver z₂.ver⟩ : Stand F) = _
  rw [c3]

end ProofFile.Honest

#print axioms ProofFile.Honest.add_first
#print axioms ProofFile.Honest.add_shared
#print axioms ProofFile.Honest.add_second
#print axioms ProofFile.Honest.end_mid
#print axioms ProofFile.Honest.model
#print axioms ProofFile.Honest.FileOk
