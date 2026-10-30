-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/ColsTermOwn.lean

THE TERM's GROUPS AT THE TABLES AFTER THE PLAYED ROUNDS, WHERE THE FIRST FOLD SENDS ITS OWN FRESH
TABLE. The fellow of `cols_term` (ColsTerm.lean in the folder above), whose hypothesis `OldAt` cannot
be met there: the tree that the fold sends is one of the job's trees, and it is not among those sent
before the test.

  `col_new`      a tree sent in the test's round r shows what `treeAt` lists at r
  `treeAt_own`   at round 1 that is `freshCol`
  `OldAtO`       `OldAt` at every tree of the job but number n; tree n is the next to be sent
  `cols_term_own`   the groups, from `OldAtO` and the tree's column (hF)
  `treeOf_fresh`, `fresh_tree_atOmega`   tree number 2 of the job at the test on G_omega is `freshCol`

HOW EACH PREMISE OF `cols_term_own` WOULD BE PAID AT jobKO (E2E/KeyHalves.lean), n := 2.
- hdep: by the job's text; depths [22, 13, 13] at `piKOFull`: a closed line, not typed.
- hO: `opensFit_of_B` at `opens_O` (E2E/KeyOmegaClosedKernel.lean, a trial), with sources own 1, own
  2, own 7 and E.sent = 7.
- hE.fresh: src₀ 2 = own 7 is own E.sent where E.sent = 7: `Made` gives E.sent = treesTo bs 10; that
  this is 7 at the thread is `chain_counts`, by its letter. OPEN HERE.
- hE.inFront at k = 0, 1: own 1, own 2 below 7. By the same count.
- hE.cols at k = 0, 1: OPEN: from `Hand` at border 10 through `tree0_lent_Omega`, `tree1_lent_Omega`,
  `tree0_atOmega`, `tree1_atOmega`, `col_sent`, and `sendTable` to `sentTables`.
- h1, hr1: depthAt J 1 is some by `J.fresh = none` and two stages or more; 1 below the rounds' count.
- hF: `fresh_tree_atOmega` and `treeAt_own`, here, at every x.
- hT: the second conclusion of `played_term`, under `Agree`: `agree_of_tiesO`, `ties_O` (a trial).

Limits. As in ColsTerm.lean: `OldAtO.cols` compares through `colAt`, which is the empty list where
there is no table, so it does not say that a table is there; `colGroups` is not the frame's own text
(`regroup_cols`, not called here). `OldAtO` does not ask n < T₀.length: at an n beyond the list it is
`OldAt` with an idle equation. a₁ and tree n's depth are tied by nothing, harmlessly (`col_treeAt`
holds at every depth). h1 wants two stages or more. No thread and no run here: l is a free parameter. The job's trees are numbered as the job
has them; that number n is the fold's own is hF's. Nothing on completeness, on soundness or on what
is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ColsTerm
import Johnson.Desc.ProofFile.Honest.K12.FitsAll
import Johnson.Desc.ProofFile.Honest.K12.JobShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (colGroups add_new add_old add_taken)

variable {W X : Type}

/-- **A tree that the test's round r sends shows, at the tables after the played rounds, what
`treeAt` lists at r.** The `sent` case of `cols_term`'s proof, by itself. -/
theorem col_new (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (ds : List Fmt.Drawn)
    (decls : List Fmt.DeclaredRound) (E : Env) (l : List Played)
    (hT : l.map (·.tables) = (List.range decls.length).map fun i =>
      (msgAt J w fr C (byNo ds) i).tables.map some)
    (r a : ℕ) (hr : r < decls.length) (ha : depthAt J r = some a) (pos : ℕ) :
    colAt (E.add l).tree (.own (E.sent + sentBefore J r)) pos =
      treeAt J w fr C (byNo ds) r pos := by
  have e1 : l.flatMap (·.tables) = (List.range decls.length).flatMap fun i =>
      (msgAt J w fr C (byNo ds) i).tables.map some := by
    rw [List.flatMap_def, hT, ← List.flatMap_def]
  have e2 := add_new E l (sentBefore J r)
  rw [e1, sent_table J w fr C (byNo ds) decls.length r a hr ha] at e2
  unfold colAt
  cases ht : (E.add l).tree (.own (E.sent + sentBefore J r)) with
  | none =>
    rw [ht] at e2
    cases e2
  | some u =>
    rw [ht] at e2
    have e3 : u.2 = tableOf a (treeAt J w fr C (byNo ds) r) := Option.some.inj e2
    show u.2.col pos = _
    rw [e3, col_treeAt]

/-- No round stands in front of round 1 but "BAT", which sends no tree. -/
theorem sentBefore_one (J : TestJob W X) : sentBefore J 1 = 0 := rfl

theorem getD_set_one {α : Type} (d f : α) (L : List α) (hL : L ≠ []) :
    (d :: L.set 0 f).getD 1 d = f := by
  cases L with
  | nil => exact absurd rfl hL
  | cons c L => rfl

/-- **Where the first fold sends its own table, what `treeAt` lists at round 1 is `freshCol`.** -/
theorem treeAt_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest)
    (hown : J.fresh.isNone = true) :
    treeAt J w fr C D 1 = freshCol (sgOf s) (J.first w fr C) := by
  obtain ⟨-, e2⟩ := test_parts J w fr C D s rest hst
  unfold treeAt
  rw [e2, if_pos hown]
  refine getD_set_one _ _ _ fun h => ?_
  have hw := stages_widths J.p (coinsOf J.p.nums.stages C.hide C.rest) D rest 0 s (J.laid.drop 1) 1
    (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C))
  rw [h] at hw
  cases rest <;> simp [widthsFrom] at hw

/-- `OldAt` at every tree of the job but number n, and tree number n is the next that the chain
sends. -/
structure OldAtO (E : Env) (T₀ : List Tree) (src₀ : ℕ → Fmt.TreeSource) (n : ℕ) : Prop where
  inFront : ∀ k, k < T₀.length → k ≠ n → ∀ m, src₀ k = .own m → m < E.sent
  cols : ∀ k, k < T₀.length → k ≠ n → ∀ x, x < 2 ^ (T₀.getD k (0, fun _ => [])).1 →
    colAt E.tree (src₀ k) x = (T₀.getD k (0, fun _ => [])).2 x
  fresh : src₀ n = .own E.sent

/-- **`colGroups` at the tables available after the played rounds is the term's list of groups,
where the job's tree number n is the one that round 1 sends.** h1, hr1: round 1 sends a tree. hF:
tree number n shows, below its length, what `treeAt` lists at round 1. -/
theorem cols_term_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: rest)
    (decls : List Fmt.DeclaredRound) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (E : Env)
    (l : List Played) (n a₁ : ℕ) (hdep : (J.trees₀ w fr C.mem (J.first w fr C)).map (·.1) = depths)
    (hO : OpensFit J decls depths src₀ E.sent)
    (hE : OldAtO E (J.trees₀ w fr C.mem (J.first w fr C)) src₀ n)
    (h1 : depthAt J 1 = some a₁) (hr1 : 1 < decls.length)
    (hF : ∀ x, x < 2 ^ ((J.trees₀ w fr C.mem (J.first w fr C)).getD n (0, fun _ => [])).1 →
      ((J.trees₀ w fr C.mem (J.first w fr C)).getD n (0, fun _ => [])).2 x =
        treeAt J w fr C (byNo ds) 1 x)
    (hT : l.map (·.tables) = (List.range decls.length).map fun i =>
      (msgAt J w fr C (byNo ds) i).tables.map some)
    (hl : ds.length = decls.length) :
    colGroups (E.add l).stored (E.add l).tree decls ds = (testAll J w fr C (byNo ds)).gs := by
  subst hdep
  rw [colGroups_opens _ _ (byNo ds) decls ds 0 hO.stored hl (fun n h => by
      rw [Nat.zero_add]
      unfold byNo
      rw [List.getD_eq_getElem _ _ h]), hO.opens, gs_test J w fr C (byNo ds) s rest hst,
    List.map_map]
  refine List.map_congr_left fun x hx => ?_
  show groupAt x.2.1 (byNo ds x.1).poss (colAt (E.add l).tree (srcBy J src₀ E.sent x.2.2)) = _
  refine groupAt_congr _ _ _ _ fun pos hpos => ?_
  cases hs : x.2.2 with
  | old k =>
    obtain ⟨hk', hdk⟩ := hO.olds x hx k hs
    have hk : k < (J.trees₀ w fr C.mem (J.first w fr C)).length := by
      rwa [List.length_map] at hk'
    have hdep' : x.2.1 = ((J.trees₀ w fr C.mem (J.first w fr C)).getD k (0, fun _ => [])).1 := by
      rw [hdk, List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk, List.getElem_map]
    rw [hdep'] at hpos
    show colAt (E.add l).tree (src₀ k) pos =
      ((J.trees₀ w fr C.mem (J.first w fr C)).getD k (0, fun _ => [])).2 pos
    by_cases hn : k = n
    · subst hn
      rw [hF pos hpos, hE.fresh]
      have e := col_new J w fr C ds decls E l hT 1 a₁ hr1 h1 pos
      rw [sentBefore_one, Nat.add_zero] at e
      exact e
    · rw [← hE.cols k hk hn pos hpos]
      unfold colAt
      cases hσ : src₀ k with
      | own m => rw [add_old E l (hE.inFront k hk hn m hσ)]
      | taken c q => rw [add_taken]
  | sent r =>
    obtain ⟨hr, hd⟩ := hO.senders x hx r hs
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hd
    exact col_new J w fr C ds decls E l hT r a hr ha pos

/-- The rows of a fresh table, as a tree: it is `freshCol`. -/
theorem treeOf_fresh (s : Fmt.M1.Stage) (a : ℕ) (P : PS) (x : ℕ) :
    (Light.treeOf s (a, (List.range (2 ^ s.h)).map fun r => (⟨.fresh, r, false⟩ : Light.Sel)) P).2 x =
      freshCol (sgOf s) P x := by
  show Light.wordsAt (Light.symOf s P x)
      ((List.range (2 ^ s.h)).map fun r => (⟨.fresh, r, false⟩ : Light.Sel)) =
    Johnson.Prover.Link.wordsOf (wr (2 ^ s.h) (freshSym (sgOf s) P.fM P.fT x))
  unfold Light.wordsAt Johnson.Prover.Link.wordsOf wr
  rw [List.flatMap_def, List.flatMap_def, List.map_map, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hlt : r < 2 ^ s.h := List.mem_range.1 hr
  have e : Light.symOf s P x ⟨.fresh, r, false⟩ = ofE (freshSym (sgOf s) P.fM P.fT x r) := by
    show (if r < 2 ^ s.h then ofE (freshSym (sgOf s) P.fM P.fT x r) else Fmt.Fld.zeroE) = _
    rw [if_pos hlt]
  show Fmt.M1.Own.words (Light.symOf s P x ⟨.fresh, r, false⟩) = _
  rw [e]
  rfl

/-- **Tree number 2 of the job at the test on G_omega is the fold's own table.** -/
theorem fresh_tree_atOmega (A : ProofFile.Honest.K14.SendPub) (p : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) (m : ℕ → Stretch) (P : PS) (x : ℕ) :
    (((Light.jobAtOmega A p door weights rand omega?).toRun.toTest.trees₀ w fr m P).getD 2
      (0, fun _ => [])).2 x =
      freshCol (sgOf (Light.jobAtOmega A p door weights rand omega?).s₀) P x := by
  have e := treeOf_fresh (Light.jobAtOmega A p door weights rand omega?).s₀
    (p.nums.stages.headD default).Z.a P x
  rw [← e]
  show Light.wordsAt _ (((List.range (2 ^ _)).map fun r => (⟨.fresh, r, false⟩ : Light.Sel)) ++ []) = _
  rw [List.append_nil]
  rfl

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.col_new
#print axioms ProofFile.Honest.K12.Own.sentBefore_one
#print axioms ProofFile.Honest.K12.Own.getD_set_one
#print axioms ProofFile.Honest.K12.Own.treeAt_own
#print axioms ProofFile.Honest.K12.Own.OldAtO
#print axioms ProofFile.Honest.K12.Own.cols_term_own
#print axioms ProofFile.Honest.K12.Own.treeOf_fresh
#print axioms ProofFile.Honest.K12.Own.fresh_tree_atOmega
