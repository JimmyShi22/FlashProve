-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/BackParts.lean: the six parts of the transcript that the two
strategies write, at a run of `runC` that has returned (`laid_at_stratC`), if both `KeyAndJoiningRoundMessages`s' `keyOf`
at the input is the prover's key at the instance (`hk₀`, `hk`) and `sh` at that key is the
description's first state of the shared chain (`hsh`). The three rounds without a challenge send
`front` and `seam` of the slot's `KeyAndJoiningRoundMessages` (J) and `join` of the shared part's (J₀). Each chain's part
is, message by message, the typed message of that chain's rounds as the run has produced them
(`trLaid`, Honest/Law/BackChain.lean). The lemma also gives the counts that the lemmas of
Honest/Law/BackChain.lean take as hypotheses: each chain's data are no longer than its rounds as
produced, each round produces as many tables as its data declare trees, and the description's counts
of trees are the data's.

What this is. A conditional lemma about this folder's own strategies, pointwise: at one input, one
run's coins and one typed verifier's message. Equations between typed transcripts. It is none of the
library's goals.

  1  `lens_fits`, `zip_lens`, `trLaid_more`, `endOfC_laid`   small lemmas
  2  `laid_at_stratC`   the main lemma

Limits.
  * Where `runC` does not return nothing is said.
  * The first part of the proof is that of `views_of_stratC` (Honest/Law/StratRunC.lean), copied by
    a program.
  * Hypotheses that the prose above does not name: `FileDescription.planOk` (the library's executable
    test): `laid_at_stratC`; `DataFits` (Honest/Law/StratWords.lean): `laid_at_stratC`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratRunC
import Johnson.Desc.ProofFile.Honest.Law.BackChain
import Johnson.Desc.ProofFile.Honest.Law.RunAtFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD Want uLT roundT chainsOf drawnT rhoT rvT colAtST colOf viewOf wantsOf
  view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 S Cl V W Y : Type}

/-! ## 1 Small lemmas -/

theorem lens_fits : ∀ (ds : List RDT) (zs : List (Fmt.DeclaredRound × List Oracle)),
    List.Forall₂ RoundFits ds zs → ds.map (·.trees.length) = zs.map (·.2.length) := by
  intro ds zs h
  induction h with
  | nil => rfl
  | @cons d z ds zs h1 _ ih =>
    have h2 := congrArg List.length h1.2
    rw [List.length_map, List.length_map] at h2
    rw [List.map_cons, List.map_cons, ih, h2]

theorem zip_lens {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (ds : List α) (ps : List β)
    (e : List Nat), ds.map f ++ e = ps.map g → ∀ z ∈ ds.zip ps, g z.2 = f z.1
  | [], _, _, _, _, hz => by simp at hz
  | _ :: _, [], _, h, _, _ => by simp at h
  | d :: ds, p :: ps, e, h, z, hz => by
    rw [List.map_cons, List.map_cons, List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [List.zip_cons_cons] at hz
    rcases List.mem_cons.1 hz with rfl | hz'
    · exact h1.symm
    · exact zip_lens f g ds ps e h2 z hz'

/-- Rounds beyond the data's are not read. -/
theorem trLaid_more (C : CK) : ∀ (ds : List RDT) (ps more : List Played) (ρ : Iop.Rho (uLT C ds)),
    ps.length = ds.length → trLaid C ds (ps ++ more) ρ = trLaid C ds ps ρ
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, h => by simp at h
  | d :: ds, p :: ps, more, (c, ρ), h => by
    show ((msgOf C d (some ⟨p.vals, p.tables, p.told⟩), c, trLaid C ds (ps ++ more) ρ) :
      Iop.Tr (uLT C (d :: ds))) = (msgOf C d (some ⟨p.vals, p.tables, p.told⟩), c, trLaid C ds ps ρ)
    rw [trLaid_more C ds ps more ρ (Nat.succ.inj h)]

/-- **The state of the strategies' chain after the walk's rounds**: the `Step`s that are left, and
the walk's own end. -/
theorem endOfC_laid (C : CK) (L : Lay) (left : List (Step W Y)) :
    ∀ (ds : List RDT) (ss : List (Step W Y)) (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds))
    (z' : ChainProgress S Cl W Y), walk L ss (drawnT C ds ρ) z = .ok z' →
    endOfC C L ds (ss ++ left) z ρ = (left, z')
  | [], [], z, ρ, z', hw => by
    have hw' : walk L ([] : List (Step W Y)) [] z = .ok z' := hw
    rw [walk_nil_ok hw']
    rfl
  | [], _ :: _, _, _, _, hw => by
    have hw' : walk L (_ :: _) [] _ = .ok _ := hw
    simp [walk] at hw'
  | d :: ds, [], _, (c, ρ), _, hw => by
    have hw' : walk L ([] : List (Step W Y)) (drOf C d c :: drawnT C ds ρ) _ = .ok _ := hw
    simp [walk] at hw'
  | d :: ds, s :: ss, z, (c, ρ), z', hw => by
    have hw' : walk L (s :: ss) (drOf C d c :: drawnT C ds ρ) z = .ok z' := hw
    obtain ⟨x, z₁, hx, hz₁, hw₁⟩ := walk_cons_ok hw'
    show endOfC C L ds (ss ++ left) (progressAfterChallenge L z (some s) (drOf C d c)) ρ = _
    rw [hearC_ok hx hz₁]
    exact endOfC_laid C L left ds ss z₁ ρ z' hw₁

/-! ## 2 The main lemma -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- **The six parts of the strategies' transcript, from the run's rounds as produced.** -/
theorem laid_at_stratC (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) {r : RunC F}
    (hr : runC F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩ (drawsAt C D tF tJ t3 ρ) = .ok r)
    (hp : F.planOk = true) (hD : DataFits F D)
    (hk₀ : J₀.keyOf w.1 w.2.1 w.2.2 = H.key x) (hk : J.keyOf w.1 w.2.1 w.2.2 = H.key x)
    (hsh : sh (H.key x) = F.start₂ (F.pub x)) :
    (chainsOf C D tF tJ t3).msgF (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      ((), J.front w.1 w.2.1 w.2.2 x) ∧
    (chainsOf C D tF tJ t3).msgJ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      ((), J₀.join w.1 w.2.1 w.2.2) ∧
    (chainsOf C D tF tJ t3).msg3 (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      ((), J.seam w.1 w.2.1 w.2.2 x) ∧
    (chainsOf C D tF tJ t3).tr₁ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      trLaid C D.ds₁ r.run.played.1 ((chainsOf C D tF tJ t3).rho₁ ρ) ∧
    (chainsOf C D tF tJ t3).tr₂ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      trLaid C D.ds₂ r.run.played.2.1 ((chainsOf C D tF tJ t3).rho₂ ρ) ∧
    (chainsOf C D tF tJ t3).tr₃ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      trLaid C D.ds₃ r.run.played.2.2 ((chainsOf C D tF tJ t3).rho₃ ρ) ∧
    (D.ds₁.length ≤ r.run.played.1.length ∧ D.ds₂.length ≤ r.run.played.2.1.length ∧
      D.ds₃.length ≤ r.run.played.2.2.length) ∧
    ((∀ z ∈ D.ds₁.zip r.run.played.1, z.2.tables.length = z.1.trees.length) ∧
      (∀ z ∈ D.ds₂.zip r.run.played.2.1, z.2.tables.length = z.1.trees.length) ∧
      ∀ z ∈ D.ds₃.zip r.run.played.2.2, z.2.tables.length = z.1.trees.length) ∧
    F.t₁ = D.t₁ ∧ F.t₂ = D.t₂ ∧ (r.run.played.1.map (·.tables.length)).sum = D.t₁ ∧
    (r.run.played.2.1.map (·.tables.length)).sum = D.t₂ := by
  have hr0 := hr
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hw₁, hq, ha₂, hw₂, ha₃, hw₃, rfl⟩ := runC_parts hr
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨hS, hst⟩ := readyShared_ok hR
  have hS' : readyShared F B H w.1 w.2.1 (H.key x) c₀ = .ok R.shared := hS
  have P := (F.planOk_ok).1 hp
  have o1 := steps_shaped s1 P.blocks₁
  have o2 := steps_shaped s2 P.blocks₂
  have o3 := steps_shaped s3 P.blocks₃
  obtain ⟨ρ₁, hρ₁⟩ : ∃ u, (chainsOf C D tF tJ t3).rho₁ ρ = u := ⟨_, rfl⟩
  obtain ⟨ρ₂, hρ₂⟩ : ∃ u, (chainsOf C D tF tJ t3).rho₂ ρ = u := ⟨_, rfl⟩
  obtain ⟨ρ₃, hρ₃⟩ : ∃ u, (chainsOf C D tF tJ t3).rho₃ ρ = u := ⟨_, rfl⟩
  obtain ⟨L₁, hL₁⟩ : ∃ u : Lay, u = ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩ := ⟨_, rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ u : Lay, u = ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩ := ⟨_, rfl⟩
  obtain ⟨L₃, hL₃⟩ : ∃ u : Lay, u =
      ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩ := ⟨_, rfl⟩
  have p1' : walk L₁ R.first (drawnT C D.ds₁ ρ₁ ++ [⟨[], [], [], none⟩]) a₁ = .ok z₁ := by
    rw [← hρ₁, hL₁]
    exact hw₁
  have p2' : walk L₂ R.shared (drawnT C D.ds₂ ρ₂) a₂ = .ok z₂ := by
    rw [← hρ₂, hL₂]
    exact hw₂
  have p3' : walk L₃ R.second (drawnT C D.ds₃ ρ₃) a₃ = .ok z₃ := by
    rw [← hρ₃, hL₃]
    exact hw₃
  have hLo : ∀ ps, treeOwn ps =
      (envOf (H.storedWords w.1 w.2.1) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w.1 w.2.1) ps [] []).1).symm
  have f1' : fillCols (readsOf 0 0 (H.storedWords w.1 w.2.1) (treeOwn z₁.laid) F.roundsDeclaredByBlocks.1
      (drawnT C D.ds₁ ρ₁ ++ [⟨[], [], [], none⟩])) [] = .ok z₁.cols := by
    rw [← hρ₁]
    exact walk_cols (L := ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩) hLo F.first.blocksInOrder _ _ ha₁ hw₁
      (steps_decl s1) o1
  have f2' : fillCols (readsOf 1 0 (H.storedWords w.1 w.2.1) (treeOwn z₂.laid) F.roundsDeclaredByBlocks.2.1
      (drawnT C D.ds₂ ρ₂)) [] = .ok z₂.cols := by
    rw [← hρ₂]
    exact walk_cols (L := ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩) hLo F.shared.blocksInOrder _ _ ha₂ hw₂
      (steps_decl s2) o2
  have f3' : fillCols (readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w.1 w.2.1)
      (treeThird z₁.laid z₂.laid z₃.laid) F.roundsDeclaredByBlocks.2.2 (drawnT C D.ds₃ ρ₃)) [] = .ok z₃.cols := by
    rw [← hρ₃]
    exact walk_cols
      (L := ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩)
      (fun ps => ((envOf_tree (H.storedWords w.1 w.2.1) z₁.laid z₂.laid ps).2).symm)
      F.second.blocksInOrder _ _ ha₃ hw₃ (steps_decl s3) o3
  have hal₁ : a₁.laid = [] := by
    have e := ha₁
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ a₁ e
    exact g
  have hal₂ : a₂.laid = [] := by
    have e := ha₂
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ a₂ e
    exact g
  have hal₃ : a₃.laid = [] := by
    have e := ha₃
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ a₃ e
    exact g
  have Tb1 := (tables_sentC L₁ _ _ a₁ z₁ z₁.laid p1' (by rw [hal₁, List.nil_append]) o1).2
  have Tb2 := (tables_sentC L₂ _ _ a₂ z₂ z₂.laid p2' (by rw [hal₂, List.nil_append]) o2).2
  have Tb3 := (tables_sentC L₃ _ _ a₃ z₃ z₃.laid p3' (by rw [hal₃, List.nil_append]) o3).2
  -- the first chain: the sealing round's `Step` is handled separately
  have hne : R.first ≠ [] := by
    intro h0
    have e := walk_len L₁ _ _ a₁ z₁ p1'
    rw [h0] at e
    simp at e
  obtain ⟨A, sL, hA⟩ := exists_snoc R.first hne
  have hF1 : List.Forall₂ RoundFits D.ds₁ (A.map fun s => (s.decl, s.oracles)) := by
    have h0 := hD.first
    rw [← steps_pairs s1, hA, List.map_append, List.map_cons, List.map_nil,
      List.dropLast_concat] at h0
    exact h0
  have hAl : D.ds₁.length = A.length := by
    have h0 := hF1.length_eq
    rw [List.length_map] at h0
    exact h0
  have p1'' := p1'
  rw [hA] at p1''
  obtain ⟨y₁, q1, qz⟩ := walk_append_ok [sL] [⟨[], [], [], none⟩] A (drawnT C D.ds₁ ρ₁) a₁ z₁
    (by rw [drawnT_length, hAl]) p1''
  obtain ⟨xL, u, -, hzL, hwL⟩ := walk_cons_ok qz
  have huz : z₁ = u := walk_nil_ok hwL
  obtain ⟨pL, hr1⟩ : ∃ pL, z₁.laid = y₁.laid ++ [pL] := ⟨_, by rw [huz]; exact heard_laid hzL⟩
  have hqL : sealQuiet [pL] = true := by
    rw [hr1, sealQuiet_snoc] at hq
    exact hq
  have htz : tablesOf z₁.laid = tablesOf y₁.laid := by
    rw [hr1, tablesOf_append]
    have h1 : tablesOf [pL] = [] := by
      unfold tablesOf
      simp [sealQuiet_one hqL]
    rw [h1, List.append_nil]
  have hrd : (roundsOf z₁.laid).dropLast = roundsOf y₁.laid := by
    rw [hr1]
    simp [roundsOf]
  have oA : ∀ s ∈ A, s.oracles.length = s.decl.entry.roots := fun s hs =>
    o1 s (by rw [hA]; exact List.mem_append_left _ hs)
  have t1b := endOfC_laid C L₁ [sL] D.ds₁ A a₁ ρ₁ y₁ q1
  -- how many trees
  have n1 : (tablesOf y₁.laid).length = D.t₁ := by
    rw [tables_lenC L₁ q1 hal₁ oA]
    have h1 := sum_fits _ _ hF1
    rw [List.map_map] at h1
    exact h1.symm
  have n2 : (tablesOf z₂.laid).length = D.t₂ := by
    rw [tables_lenC L₂ p2' hal₂ o2]
    have h1 := sum_fits _ _ hD.shared
    rw [← steps_pairs s2, List.map_map] at h1
    exact h1.symm
  have e1 : F.t₁ = D.t₁ := by
    rw [← n1, ← htz, tables_lenC L₁ p1' hal₁ o1]
    show Johnson.G.OfPlan.rootsOf F.roundsDeclaredByBlocks.1 = _
    unfold Johnson.G.OfPlan.rootsOf
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s hs => (o1 s hs).symm)
  have e2 : F.t₂ = D.t₂ := by
    rw [← n2, tables_lenC L₂ p2' hal₂ o2]
    show Johnson.G.OfPlan.rootsOf F.roundsDeclaredByBlocks.2.1 = _
    unfold Johnson.G.OfPlan.rootsOf
    rw [show F.roundsDeclaredByBlocks.2.1 = R.shared.map (·.decl) from (steps_decl s2).symm, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s hs => (o2 s hs).symm)
  -- the transcript's six parts
  have hSC : sharedChainStart F B H sh w.1 w.2.1 (H.key x) c₀ = (R.shared, a₂) :=
    sharedC_ok hS' hsh (by rw [hst]; exact ha₂)
  have hs1 : chainStartOrHalted ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩ F.first.blocksInOrder
      ((Except.ok R : Except Refusal (Ready W₀ Rc Xi Ky Tr X₀ X)).toOption.map
        fun R => R.start₁ H) (some (F.start₁ (F.pub x))) [] = a₁ := startC_ok ha₁
  have hτ : trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ =
      ((Iop.SStrat.zip (sharedOfC C D tF tJ t3 (J₀.join w.1 w.2.1 w.2.2) L₂ R.shared a₂)
        (slotOfC C D tF tJ t3 (J.front w.1 w.2.1 w.2.2 x) L₁ R.first a₁
          (seamAtC F B H J sh w c₀ x c))).run ρ).1 := by
    unfold trAtC
    rw [sharedPartStrategyTrackingVerifier_form, requestStrategyTrackingVerifier_form, hk₀, hSC, hR, hs1, hL₁, hL₂]
    rfl
  have hz₃ : (J.seam w.1 w.2.1 w.2.2 x, L₃, R.second, a₃) =
      seamAtC F B H J sh w c₀ x c
        (endOfC C L₁ D.ds₁ R.first a₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).1
        (endOfC C L₁ D.ds₁ R.first a₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).2
        (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) := by
    rw [hρ₁, hρ₂, hA, t1b, hL₃]
    refine (seamAtC_ok hR (by rw [hk]; exact hSC) ?_ hq ?_ ha₃).symm
    · rw [← hL₁]
      exact qz
    · rw [← hL₂]
      exact p2'
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := parts_of_zipC C D tF tJ t3 _ _ _ _ _ _ _ _ _ ρ _ hτ _ hz₃
  rw [hρ₁, hA] at m2
  rw [hρ₂] at m4
  rw [hρ₃] at m6
  have m6' : (chainsOf C D tF tJ t3).tr₃ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      trOfC C L₃ D.ds₃ R.second a₃ ρ₃ := m6
  obtain ⟨g₁, v1, w1, x1⟩ := trOfC_laid C L₁ [sL] D.ds₁ A a₁ ρ₁ y₁ q1
  rw [hal₁, List.nil_append] at v1
  subst v1
  obtain ⟨g₂, v2, w2, x2⟩ := trOfC_laid C L₂ [] D.ds₂ R.shared a₂ ρ₂ z₂ p2'
  rw [hal₂, List.nil_append] at v2
  subst v2
  rw [List.append_nil] at x2
  obtain ⟨g₃, v3, w3, x3⟩ := trOfC_laid C L₃ [] D.ds₃ R.second a₃ ρ₃ z₃ p3'
  rw [hal₃, List.nil_append] at v3
  subst v3
  rw [List.append_nil] at x3
  obtain ⟨l1, l2, l3⟩ := runC_laidAs hr0 hR o1 o2 o3
  have t1 : z₁.laid.map (·.tables.length) = R.first.map (·.oracles.length) := laidAs_tables l1
  have t2 : z₂.laid.map (·.tables.length) = R.shared.map (·.oracles.length) := laidAs_tables l2
  have t3' : z₃.laid.map (·.tables.length) = R.second.map (·.oracles.length) := laidAs_tables l3
  refine ⟨m1, m3, m5, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, e1, e2, ?_, ?_⟩
  · rw [m2, x1, hρ₁]
    show _ = trLaid C D.ds₁ z₁.laid ρ₁
    rw [hr1, trLaid_more C D.ds₁ y₁.laid [pL] ρ₁ w1]
  · rw [m4, x2, hρ₂]
  · rw [m6', x3, hρ₃]
  · show D.ds₁.length ≤ z₁.laid.length
    rw [hr1, List.length_append, w1]
    exact Nat.le_add_right _ _
  · exact Nat.le_of_eq w2.symm
  · exact Nat.le_of_eq w3.symm
  · refine zip_lens (·.trees.length) (·.tables.length) D.ds₁ z₁.laid [sL.oracles.length] ?_
    rw [t1, hA, List.map_append, lens_fits _ _ hF1, List.map_map]
    rfl
  · refine zip_lens (·.trees.length) (·.tables.length) D.ds₂ z₂.laid [] ?_
    rw [t2, List.append_nil, lens_fits _ _ hD.shared, ← steps_pairs s2, List.map_map]
    rfl
  · refine zip_lens (·.trees.length) (·.tables.length) D.ds₃ z₃.laid [] ?_
    rw [t3', List.append_nil, lens_fits _ _ hD.second, ← steps_pairs s3, List.map_map]
    rfl
  · show (z₁.laid.map (·.tables.length)).sum = D.t₁
    rw [t1, ← tables_lenC L₁ p1' hal₁ o1, htz]
    exact n1
  · show (z₂.laid.map (·.tables.length)).sum = D.t₂
    rw [t2, ← tables_lenC L₂ p2' hal₂ o2]
    exact n2

end

end ProofFile.Honest

#print axioms ProofFile.Honest.lens_fits
#print axioms ProofFile.Honest.zip_lens
#print axioms ProofFile.Honest.trLaid_more
#print axioms ProofFile.Honest.endOfC_laid
#print axioms ProofFile.Honest.laid_at_stratC
