-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/FileInv.lean: a file, at given coins. Under `FileOk`
(Honest/Law/Rule/Model.lean), at the request's trace, where a run of the prover of Honest/Walk.lean
goes through: what holds before each of the three chains (`ChainInv`,
Honest/Law/Rule/ChainStep.lean), and what a session's steps have produced there
(Honest/Law/Rule/ChainFile.lean: `chain_file`). These are the steps of the proof of `model`
(Honest/Law/Rule/Model.lean), kept apart. It is the tenth piece of the proof of `rowOk_of`
(Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `chain_start`   `ChainInv` before a chain's first sub-protocol. Its letters are those of
     `chain_file` (Honest/Law/Rule/ChainFile.lean)
  2  `mid₁`, `mid₃`, `FileInv`, `file_inv`   the file

Limits.
  * What the field `opened` holds at a chain's start (`htie`: `TieAt`,
    Honest/Law/Rule/OpenedStep.lean) is a hypothesis of `chain_start`, and so is `hsrc` (each tree
    that the chain's look-up returns is one of the chain's own, or `2 ≤ ch`: at a file the second
    chain, whose number is 2); `file_inv` pays both.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Model
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainStep
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

/-! ## 1 Before a chain's first sub-protocol -/

section
variable {Xi S Cl V W Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}

theorem chain_start {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {front : List OpenedColumn} (x : Xi)
    (ρ : Draws) (k : Coins Bk) (ch ft : Nat) (φ : Face V W Pb)
    (bs : List (Block S Cl)) (Ls : List (Lettered Bk S Cl V W Y Pb)) (dsAll : List Fmt.Drawn)
    (m₀ : Mid W Y) (L : Lay) (hLc : L.chain = ch) (hLf : L.firstTree = ft)
    (Ve : VerAt F S Cl x (storedShown L.stored (storedAsks F ρ)) ch ft) (Z : Stand F)
    (trip : List Played → List Played × List Played × List Played) (hZ0 : Z.laid.of ch = [])
    (hZ : ∀ l, Z.laid.add ch (pairsBy (treeAsks F ρ ch) l 0) =
      laidOf F ρ (trip l).1 (trip l).2.1 (trip l).2.2)
    (htr : ∀ l o pT, L.tree l o = some pT → (srcOf ch o).1 ≤ 2 ∧
      ((allTabs (pick3 (trip l).1 (trip l).2.1 (trip l).2.2
        (srcOf ch o).1))[(srcOf ch o).2]?).join = some pT.2)
    (hsrc : ∀ l o pT, L.tree l o = some pT → ch = (srcOf ch o).1 ∨ 2 ≤ ch)
    (ss : List (Step W Y))
    (hss : chainSteps Bk (Bk.rowsOf ch) (k.look ch) (φ.sees m₀.st.input) bs
      (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) = .ok ss)
    (mid : Option (Mid W Y)) (ver : Option S)
    (hmid : ∀ m, mid = some m → m.st = m₀.st ∧ m.loc = m₀.loc ∧
      m.seen = (Z.laid.front ch (storedShown L.stored (storedAsks F ρ))).seen)
    (hvm : ver.isSome = true → mid.isSome = true) (hget : Ve.get Z = ver) (a z' : ChainProgress S Cl W Y)
    (ha : ChainProgress.start L bs mid ver front = .ok a) (hw : walk L ss dsAll a = .ok z')
    (htie : TieAt earlier ch ft []
      (if ver.isSome then mid.map ({ · with opened := some front }) else none)
      (Z.laid.front ch (storedShown L.stored (storedAsks F ρ))))
    (hmem : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) dsAll,
      q ∈ allBare F ρ) :
    ChainInv x (storedShown L.stored (storedAsks F ρ)) ch ft (treeAsks F ρ ch) φ
      (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y))
      (chainKeys bs (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y))) dsAll m₀ Ve
      (φ.sees m₀.st.input) (readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds))
          dsAll) earlier bs k L
      Z.laid bs ss dsAll 0
      ⟨if ver.isSome then mid.map ({ · with opened := some front }) else none,
        if mid.isSome then ver else none, [], [], []⟩ z'.core Z [] [] [] := by
  have hlen := chainSteps_length bs ss hss
  have hdl := walk_length ss dsAll a z' hw
  have hver : (if mid.isSome then ver else none) = ver := by
    cases hv : ver with
    | none => cases mid <;> rfl
    | some s =>
      rw [hvm (by rw [hv]; rfl)]
      rfl
  exact
    { lc := hLc
      lf := hLf
      zb := hZ0
      steps := hss
      chained := chained_of_start ha hw hlen
      laid := (Laid.add_nil _ _).symm
      ver := hget.trans hver.symm
      both := by cases mid <;> cases ver <;> rfl
      mid := by
        intro m hm
        have hm' : ∃ m₁, mid = some m₁ ∧ m = { m₁ with opened := some front } := by
          cases hv : ver with
          | none =>
            rw [hv] at hm
            cases hm
          | some s =>
            rw [hv] at hm
            cases hq : mid with
            | none =>
              rw [hq] at hm
              cases hm
            | some m₁ =>
              rw [hq] at hm
              have hm2 : some ({ m₁ with opened := some front } : Mid W Y) = some m := hm
              exact ⟨m₁, rfl, (Option.some.inj hm2).symm⟩
        obtain ⟨m₁, hm₁, rfl⟩ := hm'
        obtain ⟨e1, e2, e3⟩ := hmid m₁ hm₁
        refine ⟨?_, e3, e1, ?_⟩
        · show φ.sees m₀.st.input = φ.sees m₁.st.input
          rw [e1]
        · show m₁.loc = m₀.loc ++ []
          rw [e2]
          exact (List.append_nil _).symm
      tie := htie
      keys := rfl
      all := rfl
      len := rfl
      fresh := fun q hq => by cases hq
      whole := rfl
      apart := fun q hq => by cases hq
      faith := faithAll_of F ρ ch ft L Z.laid trip hZ htr bs dsAll (hdl.trans hlen) hmem
      faithC := faithOwn_of F ρ ch ft L Z.laid trip hZ htr hsrc bs dsAll (hdl.trans hlen) hmem
      num := rfl
      lenp := rfl
      bare := fun _ hq => hq }

end

/-! ## 2 The file -/

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- The state at which the first chain's run starts, before `ChainProgress.start` lays the field `opened`: no
columns are handed. -/
abbrev mid₁ (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) (tr : Tr) :
    Mid (Local W₀ Rc Xi Tr) X := ⟨⟨⟨w₀, rc, x, tr⟩, [], H.own₀⟩, [], [], none⟩

/-- The state and the challenges at which the second chain's run starts, computed from the input,
the prover's own functions, and the two earlier chains' keys and challenges: no coin and nothing
that was sent goes in. Nothing shown is put in, and no columns are handed. -/
abbrev mid₃ (F : FileDescription Xi) {Bk : ProverCoinCounts} (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) (tr : Tr) (ρ : Draws) :
    Mid (Local W₀ Rc Xi Tr) X :=
  ⟨⟨⟨w₀, rc, x, tr⟩,
      (dryEnd (chainKeys F.first.blocksInOrder (G.prover H).first) ρ.first
        ⟨⟨⟨w₀, rc, x, tr⟩, [], H.own₀⟩, [], [], none⟩).st.heard ++
      (dryEnd (chainKeys F.shared.blocksInOrder (G.prover H).shared) ρ.shared
        (startShared H ⟨w₀, rc, H.key x⟩)).st.heard,
      H.meet (dryEnd (chainKeys F.first.blocksInOrder (G.prover H).first) ρ.first
        ⟨⟨⟨w₀, rc, x, tr⟩, [], H.own₀⟩, [], [], none⟩).st.own
      (dryEnd (chainKeys F.shared.blocksInOrder (G.prover H).shared) ρ.shared
        (startShared H ⟨w₀, rc, H.key x⟩)).st⟩,
    (dryEnd (chainKeys F.first.blocksInOrder (G.prover H).first) ρ.first
      ⟨⟨⟨w₀, rc, x, tr⟩, [], H.own₀⟩, [], [], none⟩).loc, [], none⟩

section
variable (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi) (tr : Tr) (ρ : Draws)

/-- **What holds of a run that goes through, at given coins**, chain by chain. `z₁`, `z₂`, `z₃`: the
ends of the three walks. `i₁`, `i₂`, `i₃`: `ChainInv` before each chain; `r₁`, `r₂`: what the
session's steps have produced after the first and after the shared chain (there is no `r₃`). The
`Stand` in `i₃` is the one after the step `door`. Each `ChainInv` stands at the chain's whole list,
with no sub-protocol passed, and at the earlier chains' declared rounds (`earlierOf`,
Honest/Owed.lean). -/
structure FileInv (k : Coins Bk) (z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (z₃ : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X) :
    Prop where
  run : ∃ r, runC F Bk (G.prover H) w₀ rc x k ρ = .ok r ∧
    r.run.played = (z₁.laid, z₂.laid, z₃.laid) ∧ r.run.reads = (z₁.reads, z₂.reads, z₃.reads)
  i₁ : ∃ ss c, ChainInv x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) 0 0
    (treeAsks F ρ 0) Face.own (G.prover H).first (chainKeys F.first.blocksInOrder (G.prover H).first)
    ρ.first (mid₁ H w₀ rc x tr) (ver₁ F x _) (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr))
    (bareReads F ρ).1 (earlierOf F 0) F.first.blocksInOrder k
    ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ (Stand.start F x).laid
        F.first.blocksInOrder ss ρ.first
    0 c z₁.core (Stand.start F x) [] [] []
  r₁ : Kit.real ((chainActs F Bk 0 (treeAsks F ρ 0) (tellerOf G.sims.first x)
      (fun a => G.sims.first.any (·.addr.place == a)) Act.judge₁ F.first.blocksInOrder 0 ρ.first).map
      (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
        (realAt F Bk H G ⟨w₀, rc, x, tr⟩ ⟨w₀, rc, H.key x⟩ ρ))) k (Stand.start F x) =
      (⟨laidOf F ρ z₁.laid [] [], z₁.ver, some (F.start₂ (F.pub x)), none⟩ : Stand F)
  i₂ : ∃ ss c, ChainInv x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) 1 0
    (treeAsks F ρ 1) Face.shared (G.prover H).shared
    (chainKeys F.shared.blocksInOrder (G.prover H).shared) ρ.shared (startShared H ⟨w₀, rc, H.key x⟩)
    (ver₂ F x _) (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky))
    (bareReads F ρ).2.1 (earlierOf F 1) F.shared.blocksInOrder k
    ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ (laidOf F ρ z₁.laid [] []) F.shared.blocksInOrder ss
    ρ.shared 0 c z₂.core
    (⟨laidOf F ρ z₁.laid [] [], z₁.ver, some (F.start₂ (F.pub x)), none⟩ : Stand F) [] [] []
  r₂ : Kit.real ((chainActs F Bk 1 (treeAsks F ρ 1) (tellerOf G.sims.shared (H.key x))
      (fun a => G.sims.shared.any (·.addr.place == a)) Act.judge₂ F.shared.blocksInOrder 0 ρ.shared).map
      (Act.stage x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
        (realAt F Bk H G ⟨w₀, rc, x, tr⟩ ⟨w₀, rc, H.key x⟩ ρ))) k
      (⟨laidOf F ρ z₁.laid [] [], z₁.ver, some (F.start₂ (F.pub x)), none⟩ : Stand F) =
      (⟨laidOf F ρ z₁.laid z₂.laid [], z₁.ver, z₂.ver, none⟩ : Stand F)
  i₃ : ∃ ss c, ChainInv x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) 2 F.lastChainFirstTreeNumber
    (treeAsks F ρ 2) Face.own (G.prover H).second (chainKeys F.second.blocksInOrder (G.prover H).second)
    ρ.second (mid₃ F H G w₀ rc x tr ρ) (ver₃ F x _)
    (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) (bareReads F ρ).2.2 (earlierOf F 2)
    F.second.blocksInOrder k
    ⟨2, F.lastChainFirstTreeNumber, (G.prover H).storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
    (laidOf F ρ z₁.laid z₂.laid []) F.second.blocksInOrder ss ρ.second 0 c z₃.core
    (⟨laidOf F ρ z₁.laid z₂.laid [], z₁.ver, z₂.ver, door₃ F x z₁.ver z₂.ver⟩ : Stand F) [] [] []

end

/-- **A run that goes through satisfies `FileInv`**, under `FileOk`, at the request's trace. -/
theorem file_inv {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} (hF : FileOk F Bk G) {w₀ : W₀} {rc : Rc} {x : Xi} {tr : Tr}
    {k : Coins Bk} {ρ : Draws} {r : RunC F} (htr : H.trace w₀ x = some tr)
    (hrun : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r) :
    ∃ z₁ z₂ z₃, FileInv F Bk H G w₀ rc x tr ρ k z₁ z₂ z₃ := by
  have hrun₀ := hrun
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
  have j1 :=
    chain_start (earlier := earlierOf F 0) x ρ k 0 0 Face.own F.first.blocksInOrder G.first ρ.first
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
      R.first hs₁ _ _
      (fun m hm => by cases hm; exact ⟨rfl, rfl, rfl⟩) (fun _ => rfl) rfl a₁ z₁ ha₁ hz₁
      (TieAt.start laid_field rfl)
      (fun q hq => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hq))))
  have j2 :=
    chain_start (earlier := earlierOf F 1) x ρ k 1 0 Face.shared F.shared.blocksInOrder G.shared ρ.shared
      (startShared H ⟨w₀, rc, H.key x⟩) ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ rfl rfl
      (ver₂ F x _)
      (⟨laidOf F ρ z₁.laid [] [], z₁.ver, some (F.start₂ (F.pub x)), none⟩ : Stand F)
      (fun l => (z₁.laid, l, [])) rfl (fun l => add_shared _ l _ [])
      (fun l o pT h => by
        obtain ⟨n, rfl, hn⟩ := own_tab l o pT h
        exact ⟨(show (1 : Nat) ≤ 2 by decide), hn⟩)
      (fun l o pT h => by
        obtain ⟨n, rfl, -⟩ := own_tab l o pT h
        exact Or.inl rfl)
      R.shared hs₂ (some (startShared H ⟨w₀, rc, H.key x⟩)) (some (F.start₂ (F.pub x)))
      (fun m hm => by cases hm; exact ⟨rfl, rfl, rfl⟩) (fun _ => rfl) rfl a₂ z₂ ha₂ hz₂
      (TieAt.start laid_field rfl)
      (fun q hq => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hq))))
  have j3 :=
    chain_start (earlier := earlierOf F 2) x ρ k 2 F.lastChainFirstTreeNumber Face.own F.second.blocksInOrder G.second
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
      (ver₃ F x _)
      (⟨laidOf F ρ z₁.laid z₂.laid [], z₁.ver, z₂.ver, door₃ F x z₁.ver z₂.ver⟩ : Stand F)
      (fun l => (z₁.laid, z₂.laid, l)) rfl (fun l => add_second _ l _ _)
      (fun l o pT h => third_tab z₁.laid z₂.laid l o pT h)
      (fun _ _ _ _ => Or.inr (Nat.le_refl 2)) R.second hs₃
      (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ (G.prover H) m₁ m₂)
      (door₃ F x z₁.ver z₂.ver)
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
  exact ⟨z₁, z₂, z₃, ⟨_, hrun₀, rfl, rfl⟩, ⟨_, _, j1⟩, c1, ⟨_, _, j2⟩, c2, ⟨_, _, j3⟩⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.chain_start
#print axioms ProofFile.Honest.file_inv
#print axioms ProofFile.Honest.mid₁
#print axioms ProofFile.Honest.mid₃
#print axioms ProofFile.Honest.FileInv
