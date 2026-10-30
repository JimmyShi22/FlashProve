-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/WantsAtStretch.lean: WHAT A STRETCH OF A CHAIN's DATA READS IS WHAT ITS DECLARED
ROUNDS READ, EACH TREE BY ITS NUMBER OVER THE FILE: the statement `WantsAre`
(Johnson/Desc/BlockSlot.lean), which speaks of a whole chain, CUT TO A STRETCH, at the stretch's own
stage.

Why. The law of a kind of block is stated at the block's own stretch: its base, its rounds' data,
and the depth function of the stage made of these (`stg Fr base ds`). It asks, as a public fact on
the place, that at all draws the stretch's wants are the declared rounds' wants.
  `forall₂_map_self`, `forall₂_cut`   two facts on lists
  `rel_of`       round by round: what `wantsOf_eq_decl` asks, from `Matches` and the openings by
                 number
  `wants_piece`  **one stretch**: from `Matches`, the openings by number, `InTime`, `own`, `listed`
  `wants_cut`    **the stretch behind pre, as long as mid**, of a chain's data, in closed form:
                 base₀ + nTrees (ds.take pre.length) and (ds.drop pre.length).take mid.length
  `blk`, `chainFits_of_data`   what the tiling rests on, at every description's data, chain by chain
  `wants_first` | `wants_shared` | `wants_last`   **at every description**: from
                 `F.data file = .ok D` alone, at every way to write the chain's declared rounds as
                 pre ++ (mid ++ post)
  `wants_form`   the same with the stage written out and the stretch as dB :: dt
Limits. On reading alone: which positions are asked for. That a block's rounds are such a mid, and
that its piece's base and data are the closed form, are the caller's. At the first chain the stretch
must end in front of the sealing round. Nothing on soundness.

-/
import Johnson.Desc.Sound.TilesDataProofs
import Johnson.Desc.BlockSlotOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open VerifiableInference.Desc

theorem forall₂_map_self {α β : Type} {P : α → β → Prop} (f : α → β) :
    ∀ l : List α, List.Forall₂ P l (l.map f) → ∀ x ∈ l, P x (f x)
  | [], _, _, h => nomatch h
  | a :: l, h, x, hx => by
    cases h with
    | cons h1 ht =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h1
      · exact forall₂_map_self f l ht x hx

theorem forall₂_cut {α β : Type} {P : α → β → Prop} {ds : List α} (pre mid post : List β)
    (h : List.Forall₂ P ds (pre ++ (mid ++ post))) :
    List.Forall₂ P ((ds.drop pre.length).take mid.length) mid := by
  have h1 := List.forall₂_drop pre.length h
  rw [List.drop_left] at h1
  have h2 := List.forall₂_take mid.length h1
  rwa [List.take_left] at h2

/-- Round by round, what `wantsOf_eq_decl` asks. dep: the file's depths; dep': another function that
agrees with it at the trees that these rounds open. -/
theorem rel_of (a : ℕ) (dep dep' : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ) :
    ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT), Matches a dep rs ds →
      List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) => d.opens = r.opens.map fun o => num o.2)
        ds rs →
      (∀ d ∈ ds, ∀ j ∈ d.opens, dep' j = dep j) →
      List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
        d.stored = r.stored ∧ d.opens = r.opens.map (fun o => num o.2) ∧
          (∀ s ∈ r.stored, s.sh.a = a) ∧ ∀ o ∈ r.opens, dep' (num o.2) = some o.1.a) ds rs
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, hN, _ => nomatch hN
  | _ :: _, [], _, hN, _ => nomatch hN
  | r :: rs, d :: ds, hM, hN, hd => by
    have hM' : RoundMatch a dep r d ∧ Matches a dep rs ds := hM
    cases hN with
    | cons h1 ht =>
      refine .cons ⟨hM'.1.1, h1, hM'.1.2.1, fun o ho => ?_⟩
        (rel_of a dep dep' num rs ds hM'.2 ht fun e he => hd e (List.mem_cons_of_mem _ he))
      have hj : num o.2 ∈ d.opens := by
        rw [h1]
        exact List.mem_map.2 ⟨o, ho, rfl⟩
      rw [hd d List.mem_cons_self _ hj]
      have h3 := hM'.1.2.2
      rw [h1] at h3
      exact forall₂_map_self (fun o => num o.2) r.opens h3 o ho

/-- **One stretch.** -/
theorem wants_piece (Fr : Frame) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ)
    (rs : List Fmt.DeclaredRound) (base : ℕ) (ds : List RDT) (hM : Matches Fr.a dep rs ds)
    (hN : List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.opens = r.opens.map fun o => num o.2) ds rs)
    (hT : InTime base ds)
    (own : ∀ n sh, treeShT ds n = some sh → dep (base + n) = some sh.a)
    (listed : ∀ j a', dep j = some a' → (Fr.all.filter (·.no == j)).map (·.a) = [a']) :
    ∀ Rs, wantsOf Fr.a (stg Fr base ds).depth ds Rs = wantsDecl num rs Rs :=
  wantsOf_eq_decl Fr.a _ num (rel_of Fr.a dep _ num rs ds hM hN
    (depth_agrees Fr dep base ds (inTime_below ds base hT) own listed
      (matches_dep Fr.a dep rs ds hM)))

/-- **The stretch behind pre, as long as mid.** -/
theorem wants_cut (Fr : Frame) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ)
    (pre mid post : List Fmt.DeclaredRound) (base₀ : ℕ) (ds : List RDT)
    (hM : Matches Fr.a dep (pre ++ (mid ++ post)) ds)
    (hN : List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.opens = r.opens.map fun o => num o.2) ((ds.drop pre.length).take mid.length) mid)
    (hT : InTime base₀ ds)
    (own : ∀ n sh, treeShT ds n = some sh → dep (base₀ + n) = some sh.a)
    (listed : ∀ j a', dep j = some a' → (Fr.all.filter (·.no == j)).map (·.a) = [a']) :
    ∀ Rs, wantsOf Fr.a (stg Fr (base₀ + nTrees (ds.take pre.length))
        ((ds.drop pre.length).take mid.length)).depth ((ds.drop pre.length).take mid.length) Rs =
      wantsDecl num mid Rs := by
  have hM2 := (matches_split Fr.a dep pre (mid ++ post) ds hM).2
  have hM3 := (matches_split Fr.a dep mid post _ hM2).1
  have t1 := (inTime_append (ds.take pre.length) (ds.drop pre.length) base₀
    (by rw [List.take_append_drop]; exact hT)).2
  have t2 := (inTime_append ((ds.drop pre.length).take mid.length)
    ((ds.drop pre.length).drop mid.length) _ (by rw [List.take_append_drop]; exact t1)).1
  refine wants_piece Fr dep num mid _ _ hM3 hN t2 (fun n sh h => ?_) listed
  have lt := treeShT_lt _ n sh h
  have e1 : treeShT (ds.drop pre.length) n = some sh := by
    rw [← List.take_append_drop mid.length (ds.drop pre.length), treeShT_append, if_pos lt]
    exact h
  have e2 : treeShT ds (nTrees (ds.take pre.length) + n) = some sh := by
    rw [← List.take_append_drop pre.length ds, treeShT_append, if_neg (by
      rw [List.take_append_drop]; omega)]
    rw [List.take_append_drop, Nat.add_sub_cancel_left]
    exact e1
  rw [Nat.add_assoc]
  exact own _ sh e2

/-! ## At every description's data -/

/-- One block that declares the rounds d: so that what the tiling rests on can be asked of a chain's
declared rounds as one list. -/
def blk (d : List Fmt.DeclaredRound) : Block Unit Unit :=
  { (roundlessBlock "" 0 none 0 fun s => .ok s : Block Unit Unit) with rounds := d }

theorem flat_blk (d : List Fmt.DeclaredRound) : (blk d :: []).flatMap (·.rounds) = d := by
  simp [blk]

/-- **What the tiling rests on, at every description's data**, each chain's declared rounds as one
list. -/
theorem chainFits_of_data {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (r : Fmt.RoundView) (k₁ k₂ k₃ : ℕ → ℕ) (ft₁ ft₂ ft₃ : ℕ) :
    ChainFit (frameAt D (allOf D) k₁ ft₁) D.depth 0 (blk F.roundsDeclaredByBlocks.1) [] D.ds₁ [r] ∧
      ChainFit (frameAt D (allOf D) k₂ ft₂) D.depth D.t₁ (blk F.roundsDeclaredByBlocks.2.1) [] D.ds₂ [] ∧
      ChainFit (frameAt D (allOf D) k₃ ft₃) D.depth (D.t₁ + D.t₂) (blk F.roundsDeclaredByBlocks.2.2) [] D.ds₃ [] := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := VerifiableInference.Desc.Sound.data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  refine fitOfOk _ R₁ R₂ R₃ _ _ _ _ _ _ w₁ w₂ w₃ hok Unit Unit Unit Unit (blk F.roundsDeclaredByBlocks.1) []
    (blk F.roundsDeclaredByBlocks.2.1) [] (blk F.roundsDeclaredByBlocks.2.2) [] r k₁ k₂ k₃ ft₁ ft₂ ft₃ (flat_blk _) (flat_blk _)
    (flat_blk _) ?_
  show 1 ≤ F.roundsDeclaredByBlocks.1.length
  have hsome : someFit (R₁, R₂, R₃) = true := (okAt_parts hok).rounds
  unfold someFit at hsome
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsome
  have l₁ := List.Forall₂.length_eq w₁
  have h2 : 2 ≤ R₁.length := hsome.1
  exact Nat.le_trans (Nat.le_trans (by decide) h2) (Nat.le_of_eq l₁.symm)

section
variable {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}

/-- **A stretch of the last chain.** -/
theorem wants_last (h : F.data file = .ok D) (pre mid post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.2 = pre ++ (mid ++ post)) (k : ℕ → ℕ) (ft : ℕ) :
    ∀ Rs, wantsOf (frameAt D (allOf D) k ft).a
        (stg (frameAt D (allOf D) k ft) (D.t₁ + D.t₂ + nTrees (D.ds₃.take pre.length))
          ((D.ds₃.drop pre.length).take mid.length)).depth
        ((D.ds₃.drop pre.length).take mid.length) Rs =
      wantsDecl (numAt F.t₁ F.t₂ 2) mid Rs := by
  obtain ⟨-, -, f⟩ := chainFits_of_data F file D h ⟨[], ⟨[], [], [], none⟩⟩ k k k ft ft ft
  have hM := f.rounds
  rw [flat_blk, e] at hM
  have hN := forall₂_cut pre mid post (by rw [← e]; exact (opensOfData Xi F file D h).2.2)
  exact wants_cut _ D.depth _ pre mid post _ D.ds₃ hM (hN.imp fun _ _ x => x.2) f.inTime f.own
    f.listed

/-- **A stretch of the shared chain.** -/
theorem wants_shared (h : F.data file = .ok D) (pre mid post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.1 = pre ++ (mid ++ post)) (k : ℕ → ℕ) (ft : ℕ) :
    ∀ Rs, wantsOf (frameAt D (allOf D) k ft).a
        (stg (frameAt D (allOf D) k ft) (D.t₁ + nTrees (D.ds₂.take pre.length))
          ((D.ds₂.drop pre.length).take mid.length)).depth
        ((D.ds₂.drop pre.length).take mid.length) Rs =
      wantsDecl (numAt F.t₁ F.t₂ 1) mid Rs := by
  obtain ⟨-, f, -⟩ := chainFits_of_data F file D h ⟨[], ⟨[], [], [], none⟩⟩ k k k ft ft ft
  have hM := f.rounds
  rw [flat_blk, e] at hM
  have hN := forall₂_cut pre mid post (by rw [← e]; exact (opensOfData Xi F file D h).2.1)
  exact wants_cut _ D.depth _ pre mid post _ D.ds₂ hM (hN.imp fun _ _ x => x.2) f.inTime f.own
    f.listed

/-- **A stretch of the first chain**, in front of its last declared round (the seal). -/
theorem wants_first (h : F.data file = .ok D) (pre mid post : List Fmt.DeclaredRound)
    (r₀ : Fmt.DeclaredRound) (e : F.roundsDeclaredByBlocks.1 = pre ++ (mid ++ (post ++ [r₀]))) (k : ℕ → ℕ) (ft : ℕ) :
    ∀ Rs, wantsOf (frameAt D (allOf D) k ft).a
        (stg (frameAt D (allOf D) k ft) (0 + nTrees (D.ds₁.take pre.length))
          ((D.ds₁.drop pre.length).take mid.length)).depth
        ((D.ds₁.drop pre.length).take mid.length) Rs =
      wantsDecl (numAt F.t₁ F.t₂ 0) mid Rs := by
  obtain ⟨f, -, -⟩ := chainFits_of_data F file D h ⟨[], ⟨[], [], [], none⟩⟩ k k k ft ft ft
  have hM := f.rounds
  rw [flat_blk, e] at hM
  have ed : F.roundsDeclaredByBlocks.1.dropLast = pre ++ (mid ++ post) := by
    rw [e]
    simp only [← List.append_assoc, List.dropLast_concat]
  have hN := forall₂_cut pre mid post (by rw [← ed]; exact (opensOfData Xi F file D h).1)
  exact wants_cut _ D.depth _ pre mid (post ++ [r₀]) _ D.ds₁ hM (hN.imp fun _ _ x => x.2) f.inTime
    f.own f.listed

/-- The same in the form in which a kind's law asks it: the stage written out, the stretch as
dB :: dt. -/
theorem wants_form (Fr : Frame) (num : Fmt.TreeSource → ℕ) (rs : List Fmt.DeclaredRound) (b : ℕ)
    (ds : List RDT) (hw : ∀ Rs, wantsOf Fr.a (stg Fr b ds).depth ds Rs = wantsDecl num rs Rs)
    (base : ℕ) (dB : RDT) (dt : List RDT) (hb : base = b) (hd : dB :: dt = ds) :
    ∀ Rs,
      wantsOf Fr.a (⟨Fr.a, base, Fr.all, dB :: dt, Fr.key, Fr.all⟩ : StageD).depth (dB :: dt) Rs =
        wantsDecl num rs Rs := by
  subst hb
  rw [hd]
  exact hw

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.chainFits_of_data
#print axioms VerifiableInference.Desc.Sound.wants_last
#print axioms VerifiableInference.Desc.Sound.wants_shared
#print axioms VerifiableInference.Desc.Sound.wants_first
#print axioms VerifiableInference.Desc.Sound.wants_form
#print axioms VerifiableInference.Desc.Sound.rel_of
#print axioms VerifiableInference.Desc.Sound.wants_piece
#print axioms VerifiableInference.Desc.Sound.wants_cut
