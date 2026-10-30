-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenedRun.lean: `OpenedAt` (Honest/Law/Rule/OpenedAt.lean) at
a run of `runC` (Honest/Walk.lean): at the state that `midAtW` or `midSharedAtW` (Honest/MidW.lean)
returns in front of a part, the field is what the rounds produced before the part, as shown, hold
for the reads of the sub-protocols in front of the part's place, and in the second chain of the two
earlier chains (`earlierOf`, Honest/Owed.lean); chain by chain (`tie_first`, `tie_shared`,
`tie_second_at`). The `Before` is written as `before_first`, `before_shared` and `before_second`
(Honest/Law/RunBefore.lean) compute `Run.beforeAt`: so, where these apply and `asked_is`
(Honest/Law/Rule/OnAt.lean) turns `storedAsks F ρ` into `Run.storedAsked`, the three are the three
clauses of `Tie1` (Honest/Ties.lean) at the address (no
statement of this library says so, and none concludes
`Tie1`).

  1  `faith_front`   each read's words are found in what a simulator of the chain is given: for the
     reads of a stretch of declared rounds from the chain's start
  2  `take_len`, `tie_first`, `tie_shared`, `tie_second_at`   a length; the three chains

By what. `opened_at_chain` (Honest/Law/Rule/OpenedWalk.lean); `TieAt.start`
(Honest/Law/Rule/OpenedStart.lean), `tie_second` (Honest/Law/Rule/OpenedFile.lean); `faith_one`
(Honest/Law/Rule/Words.lean), `wordsAt_own` (Honest/Law/Rule/FaithOwnFile.lean). The unpacking of a
run goes as in `tie2` (Honest/Tie2File.lean).

Limits.
  * CONDITIONAL in each clause: `midAtW` or `midSharedAtW` returns a state. It is not shown here
    that it does; at a called part of the chain whose rounds are one stretch, where the roots'
    counts fit (`o₁`, `o₂`, `o₃` there): `mid_first`, `mid_shared`, `mid_second`
    (Honest/Law/RunMidFile.lean).
  * Hypotheses beside that, in all three: the run of `runC` returns (`hr`); `ready`
    (Honest/Frame.lean) returns R at the same input and coins (`hR`): the `Before` is written at R's
    `Step`s. In `tie_first`: a `Step` of R's first chain stands at the address (`hany`); in
    `tie_second_at`: none does (`h1`).
  * `Tie1` itself is not stated of `Run.beforeAt` here. Neither the ends of its three clauses under
    the hypotheses of `before_first`, `before_shared` and `before_second`, nor `Tie1` as
    Honest/Ties.lean states it, under its own guards alone, is concluded by a statement of this
    library.
  * The theorems are about the frame's own bookkeeping. They prove no property of a prover or a
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedWalk
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.FaithOwnFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.Model
import Johnson.Desc.ProofFile.Honest.Tie2File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

/-! ## 1 The reads of a stretch from the chain's start -/

/-- The letters and the first hypotheses are those of `faithOwn_of`
(Honest/Law/Rule/FaithOwnFile.lean). `D`: a stretch of the chain's declared rounds, from the start.
-/
theorem faith_front {Xi S Cl : Type} (F : FileDescription Xi) (ρ : Draws) (ch ft : Nat) (L : Lay)
    (Z₀ : Laid) (trip : List Played → List Played × List Played × List Played)
    (hZ : ∀ l, Z₀.add ch (pairsBy (treeAsks F ρ ch) l 0) =
      laidOf F ρ (trip l).1 (trip l).2.1 (trip l).2.2)
    (htr : ∀ l o pT, L.tree l o = some pT → (srcOf ch o).1 ≤ 2 ∧
      ((allTabs (pick3 (trip l).1 (trip l).2.1 (trip l).2.2
        (srcOf ch o).1))[(srcOf ch o).2]?).join = some pT.2)
    (hsrc : ∀ l o pT, L.tree l o = some pT → ch = (srcOf ch o).1 ∨ 2 ≤ ch)
    (bs : List (Block S Cl)) (ds : List Fmt.Drawn)
    (hmem : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) ds,
      q ∈ allBare F ρ) :
    ∀ (l : List Played) (D rest : List Fmt.DeclaredRound), bs.flatMap (·.rounds) = D ++ rest →
      D.length ≤ ds.length →
      ∀ q ∈ readsOf ch ft L.stored (L.tree l) D (ds.take D.length), ∀ w, q.words = some w →
        ((Z₀.add ch (pairsBy (treeAsks F ρ ch) l 0)).front ch
          (storedShown L.stored (storedAsks F ρ))).wordsAt q.bare = some w := by
  intro l D rest hD hlen q hq w hw
  have e : readsOf ch ft (fun _ _ => none) (fun _ => none) (D ++ rest) ds =
      readsOf ch ft (fun _ _ => none) (fun _ => none) D (ds.take D.length) ++
        readsOf ch ft (fun _ _ => none) (fun _ => none) rest (ds.drop D.length) := by
    conv_lhs => rw [← List.take_append_drop D.length ds]
    exact readsOf_append _ _ _ _ _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hlen])
  have hb : q.bare ∈ allBare F ρ := by
    refine hmem _ ?_
    rw [hD, e]
    refine List.mem_append.2 (Or.inl ?_)
    rw [← readsOf_bare ch ft L.stored (L.tree l)]
    exact List.mem_map.2 ⟨q, hq, rfl⟩
  have hside : ∀ c j, q.bare.item = none → q.bare.src = some (c, j) →
      c ≤ 2 ∧ (ch = c ∨ 2 ≤ ch) := by
    intro c j hi hs
    rcases readsOf_form ch ft L.stored (L.tree l) D _ q hq with ⟨i, h1, -, -⟩ | ⟨o, -, g2, g3⟩
    · have hi' : q.item = none := hi
      rw [h1] at hi'
      cases hi'
    · have hs' : q.src = some (c, j) := hs
      rw [g2] at hs'
      have ec : (srcOf ch o).1 = c := congrArg Prod.fst (Option.some.inj hs')
      rw [hw] at g3
      cases hto : L.tree l o with
      | none =>
        rw [hto] at g3
        cases g3
      | some pT =>
        rw [← ec]
        exact ⟨(htr l o pT hto).1, hsrc l o pT hto⟩
  rw [hZ l, wordsAt_own F ρ _ _ _ _ ch q.bare hside]
  exact faith_one F ρ _ _ _ L.stored ch ft (L.tree l) D _ (htr l) q hq hb w hw

/-! ## 2 The three chains -/

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {B : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws}
  {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- A walk's rounds, cut at the number of the `Step`s in front of an address, are just as many as
these `Step`s. -/
theorem take_len {S Cl W Y : Type} {L : Lay} {bs : List (Block S Cl)} {mo : Option (Mid W Y)}
    {vo : Option S} {front : List OpenedColumn} {a₀ z : ChainProgress S Cl W Y} {steps : List (Step W Y)}
    {ds : List Fmt.Drawn} (ha : ChainProgress.start L bs mo vo front = .ok a₀)
    (hw : walk L steps ds a₀ = .ok z) (a : Addr) :
    (z.laid.take (steps.takeWhile fun s => s.addr != a).length).length =
      (steps.takeWhile fun s => s.addr != a).length := by
  rw [List.length_take, walk_laid_length L steps ds a₀ z hw, start_laid ha]
  exact Nat.min_eq_left (Nat.le_trans (List.takeWhile_prefix _).length_le (Nat.le_add_left _ _))

/-- **The first chain.** -/
theorem tie_first (hr : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    {a : Addr} (hany : R.first.any (·.addr == a) = true) {m : Mid (Local W₀ Rc Xi Tr) X}
    (hm : midAtW F B H w₀ rc x c ρ a = .ok (some m)) :
    OpenedAt (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder a.place) m
      ⟨shownBy 0 (treeAsks F ρ 0)
        (r.run.played.1.take (R.first.takeWhile fun s => s.addr != a).length) 0,
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))⟩ := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hr
  have eR : R' = R := Except.ok.inj (hR'.symm.trans hR)
  subst eR
  obtain ⟨hT, tr, -, -, -, hc₁, -, -⟩ := ready_ok hR
  have hn := orderOf_nodup (placesOk_of_tests hT)
  unfold orderOf at hn
  have n₁ := hn.of_append_left.of_append_left
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => (envOf_tree (H.storedWords w₀ rc) ps [] []).1.symm
  unfold midAtW at hm
  simp only [hR, ha₁, Except.bind] at hm
  rw [if_pos hany] at hm
  have h : OpenedAt (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder a.place) m
      (((⟨[], [], []⟩ : Laid).add 0 (pairsBy (treeAsks F ρ 0)
        (z₁.laid.take (R'.first.takeWhile fun s => s.addr != a).length) 0)).front 0
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))) :=
    opened_at_chain ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ hLo F.first.blocksInOrder n₁ _ _ [] hc₁ ha₁ hz₁ hm
      (earlierOf F 0) ⟨[], [], []⟩ _ (treeAsks F ρ 0)
      (fun m₀ _ => TieAt.start (fun m' e => by cases e; rfl) rfl)
      (faith_front F ρ 0 0 ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ ⟨[], [], []⟩
        (fun l => (l, [], [])) (fun l => add_first _ l [] [])
        (fun l o pT h => by
          obtain ⟨n, rfl, hn⟩ := own_tab l o pT h
          exact ⟨(show (0 : Nat) ≤ 2 by decide), hn⟩)
        (fun l o pT h => by
          obtain ⟨n, rfl, -⟩ := own_tab l o pT h
          exact Or.inl rfl)
        F.first.blocksInOrder ρ.first
        (fun q hq => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hq)))))
      _ (List.take_prefix _ _) (take_len ha₁ hz₁ a)
  rw [add_first] at h
  exact h

/-- **The shared chain.** -/
theorem tie_shared (hr : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    {a : Addr} {m : Mid (Common W₀ Rc Ky) X₀}
    (hm : midSharedAtW F B H w₀ rc x c ρ a = .ok (some m)) :
    OpenedAt (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder a.place) m
      ⟨shownBy 1 (treeAsks F ρ 1)
        (r.run.played.2.1.take (R.shared.takeWhile fun s => s.addr != a).length) 0,
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))⟩ := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hr
  have eR : R' = R := Except.ok.inj (hR'.symm.trans hR)
  subst eR
  obtain ⟨hT, tr, -, -, -, -, hc₂, -⟩ := ready_ok hR
  have hn := orderOf_nodup (placesOk_of_tests hT)
  unfold orderOf at hn
  have n₂ := hn.of_append_left.of_append_right
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => (envOf_tree (H.storedWords w₀ rc) ps [] []).1.symm
  unfold midSharedAtW at hm
  simp only [hR, ha₂, Except.bind] at hm
  have h : OpenedAt (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder a.place) m
      (((⟨shownBy 0 (treeAsks F ρ 0) z₁.laid 0, [], []⟩ : Laid).add 1 (pairsBy (treeAsks F ρ 1)
        (z₂.laid.take (R'.shared.takeWhile fun s => s.addr != a).length) 0)).front 1
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))) :=
    opened_at_chain ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ hLo F.shared.blocksInOrder n₂ _ _ [] hc₂ ha₂ hz₂ hm
      (earlierOf F 1) ⟨shownBy 0 (treeAsks F ρ 0) z₁.laid 0, [], []⟩ _ (treeAsks F ρ 1)
      (fun m₀ _ => TieAt.start (fun m' e => by cases e; rfl) rfl)
      (faith_front F ρ 1 0 ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩
        ⟨shownBy 0 (treeAsks F ρ 0) z₁.laid 0, [], []⟩
        (fun l => (z₁.laid, l, [])) (fun l => add_shared _ l _ [])
        (fun l o pT h => by
          obtain ⟨n, rfl, hn⟩ := own_tab l o pT h
          exact ⟨(show (1 : Nat) ≤ 2 by decide), hn⟩)
        (fun l o pT h => by
          obtain ⟨n, rfl, -⟩ := own_tab l o pT h
          exact Or.inl rfl)
        F.shared.blocksInOrder ρ.shared
        (fun q hq => List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hq)))))
      _ (List.take_prefix _ _) (take_len ha₂ hz₂ a)
  rw [add_shared] at h
  exact h

/-- **The second chain.** `h1`: no round of the first chain stands at the address. -/
theorem tie_second_at (hr : runC F B H w₀ rc x c ρ = .ok r)
    (hR : ready F B H w₀ rc x c = .ok R) {a : Addr} (h1 : R.first.any (·.addr == a) = false)
    {m : Mid (Local W₀ Rc Xi Tr) X} (hm : midAtW F B H w₀ rc x c ρ a = .ok (some m)) :
    OpenedAt (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder a.place) m
      ⟨shownBy 0 (treeAsks F ρ 0) r.run.played.1 0 ++ shownBy 1 (treeAsks F ρ 1) r.run.played.2.1 0
          ++
        shownBy 2 (treeAsks F ρ 2)
          (r.run.played.2.2.take (R.second.takeWhile fun s => s.addr != a).length) 0,
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))⟩ := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, hq, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hr
  have eR : R' = R := Except.ok.inj (hR'.symm.trans hR)
  subst eR
  obtain ⟨hT, tr, -, -, -, -, -, hc₃⟩ := ready_ok hR
  have hn := orderOf_nodup (placesOk_of_tests hT)
  unfold orderOf at hn
  have n₃ := hn.of_append_right
  have hL₃ : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (H.storedWords w₀ rc) (takenOf z₁.laid z₂.laid) ps).tree :=
    fun ps => (envOf_tree (H.storedWords w₀ rc) z₁.laid z₂.laid ps).2.symm
  have hno : ¬ (R'.first.any (·.addr == a) = true) := by
    rw [h1]
    exact Bool.false_ne_true
  unfold midAtW at hm
  simp only [hR, ha₁, Except.bind] at hm
  rw [if_neg hno] at hm
  simp only [hz₁, hq, ha₂, hz₂, ha₃, Bool.not_true, Bool.false_eq_true, if_false] at hm
  have h : OpenedAt (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder a.place) m
      (((⟨shownBy 0 (treeAsks F ρ 0) z₁.laid 0, shownBy 1 (treeAsks F ρ 1) z₂.laid 0, []⟩ :
        Laid).add 2 (pairsBy (treeAsks F ρ 2)
        (z₃.laid.take (R'.second.takeWhile fun s => s.addr != a).length) 0)).front 2
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))) :=
    opened_at_chain ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ hL₃
      F.second.blocksInOrder n₃ _ _ (z₁.cols ++ z₂.cols) hc₃ ha₃ hz₃ hm (earlierOf F 2)
      ⟨shownBy 0 (treeAsks F ρ 0) z₁.laid 0, shownBy 1 (treeAsks F ρ 1) z₂.laid 0, []⟩ _
      (treeAsks F ρ 2)
      (fun m₀ _ => tie_second hR ha₁ hz₁ ha₂ hz₂ (fun m' e => by cases e; rfl))
      (faith_front F ρ 2 F.lastChainFirstTreeNumber
        ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
        ⟨shownBy 0 (treeAsks F ρ 0) z₁.laid 0, shownBy 1 (treeAsks F ρ 1) z₂.laid 0, []⟩
        (fun l => (z₁.laid, z₂.laid, l)) (fun l => add_second _ l _ _)
        (fun l o pT h => third_tab z₁.laid z₂.laid l o pT h)
        (fun _ _ _ _ => Or.inr (Nat.le_refl 2))
        F.second.blocksInOrder ρ.second (fun q hq => List.mem_append.2 (Or.inr hq)))
      _ (List.take_prefix _ _) (take_len ha₃ hz₃ a)
  rw [add_second] at h
  exact h

end ProofFile.Honest

#print axioms ProofFile.Honest.faith_front
#print axioms ProofFile.Honest.take_len
#print axioms ProofFile.Honest.tie_first
#print axioms ProofFile.Honest.tie_shared
#print axioms ProofFile.Honest.tie_second_at
