-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WireLaws.lean: the wire record of a whole file (OnBytes/Maker/Wire.lean) obeys the
laws of a wire record (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean, `ProtocolQueryLayout.OKG`). The pattern is
Run/PlanQSLaws.lean's `wireS_okg`, `wire0S_okg`, `wiresS_okg` and `wqS_okg`, whose rounds (`RD`,
Run/PlanQTypes.lean) have at most one tree. The four laws on tree and leaf, `wireLo_okg` and
`wireSh_okg` are OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean's, OnBytes/TypedOracleCompiler/Run/PlanQSLaws.lean's `wireS_okg`
and OnBytes/TypedOracleCompiler/Slice/Batch3Wire.lean's `wireSh_okg` under this folder's names; what is shown here
is the rows, the depths, the count of what is opened, and the whole.

The hypotheses, each on the three chains' lists of rounds.
  `ChalUnifT`: in every round uniform hash blocks give a uniform verifier's message.
  `DrawnFitsT`: what was drawn holds at most the entry's number of positions.
  Every entry's work is at most 64 bits.

Main theorems.
  `placeT_lt`, `posAtT_place`, `place_posAtT`, `posAtT_none`: tree and leaf number a round's
    positions.
  `wireLo_okg`, `wireSh_okg`, `wireSilent_okg`, `wiresLo_okg`, `wiresSh_okg`, `wiresOf_okg`: the
    rounds' records.
  `wiresLo_depthLe`, `wiresSh_depthLe`, `wiresOf_depthLe`: no tree is deeper than `maxDepthW`.
  `weOne_ok`: the stored table's record.
  `wantsOf_len`, `two_filterMaps`, `whole_opens`: the verifier opens at most `nOpenW` positions.
  `wqWhole_okg`: the whole.
  `chalUnifT_ckP`, `drawnFitsT_ckP`, `wqWhole_okg_ckP`: at verifier's messages as hash blocks
    (`ckP f`, `chalP f K`, Run/PlanPull.lean) the hypotheses come down to two on numbers: no round
    has more than K blocks, none more than 64 bits of work.

What is not claimed. That these two hold of any data. Nothing on soundness. `ChalUnifT` is an
equation of laws: with verifier's messages as sampled values it is false in every round that draws a
field element, and `wqWhole_okg` cannot be applied there. No law here knows `maxRt`, or that a round
has as many trees as its items have roots: the laws hold at a round of three trees, where the
compiled verifier refuses every string (OnBytes/Maker/FitsFew.lean has that
bound).


-/
import OnBytes.Maker.Wire
import Run.PlanQSLaws
import Run.PlanQXLawsProofs
import Run.PlanPull

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-! ## Tree and leaf number the positions of a round -/

theorem placeT_lt : ∀ (ts : List Fmt.Shape) (p : PosT ts),
    ∃ d, (ts.map (·.a))[treeT ts p]? = some d ∧ placeT ts p < 2 ^ d := TypedOracleCompiler.Run.PQ.placeT_lt

theorem posAtT_place : ∀ (ts : List Fmt.Shape) (p : PosT ts),
    posAtT ts (treeT ts p) (placeT ts p) = some p := TypedOracleCompiler.Run.PQ.posAtT_place

theorem place_posAtT : ∀ (ts : List Fmt.Shape) (k j : ℕ) (p : PosT ts),
    posAtT ts k j = some p → treeT ts p = k ∧ placeT ts p = j := TypedOracleCompiler.Run.PQ.place_posAtT

theorem posAtT_none : ∀ (ts : List Fmt.Shape) (k : ℕ), ts.length ≤ k → ∀ j, posAtT ts k j = none :=
  TypedOracleCompiler.Run.PQ.posAtT_none

/-! ## The rounds' records -/

/-- Uniform blocks give a uniform verifier's message, in every round. -/
def ChalUnifT (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RDT) :
    Prop :=
  ∀ d ∈ ds, (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind)

/-- What was drawn holds at most the entry's number of positions. -/
def DrawnFitsT (C : CK) (ds : List RDT) : Prop :=
  ∀ d ∈ ds, ∀ c, (C.dr d.entry d.kind c).poss.length ≤ d.entry.poss

/-- A round's data without its trees, as the library's: entry, kind and items are kept. -/
def bareRD (d : RDT) : RD := ⟨d.entry, d.kind, d.items, none, []⟩

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem wireLo_okg (d : RDT)
    (hc : (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind))
    (hw : d.entry.work ≤ 64) : (wireLo C K chal d).OKG :=
  TypedOracleCompiler.Run.PQ.wireS_okg C K chal d.toRD hc hw

theorem wireSh_okg (d : RDT)
    (hc : (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind))
    (hw : d.entry.work ≤ 64) : (wireSh C K chal d).OKG :=
  TypedOracleCompiler.Slice.wireSh_okg C K chal d.toRD hc hw

theorem wiresLo_okg : ∀ ds : List RDT, ChalUnifT C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
    RoundsQueryLayout.OKG (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [], _, _ => trivial
  | d :: ds, hc, hw =>
    ⟨wireLo_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wiresLo_okg ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wiresSh_okg : ∀ ds : List RDT, ChalUnifT C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
    RoundsQueryLayout.OKG (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [], _, _ => trivial
  | d :: ds, hc, hw =>
    ⟨wireSh_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wiresSh_okg ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

end

theorem wireSilent_okg (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    (wireSilent K T t a).OKG :=
  { place_lt0 := fun p => p.elim, place_ltJ := fun p => p.elim,
    posAt0_place := fun p => p.elim, posAtJ_place := fun p => p.elim
    place_posAt0 := fun _ _ _ h => by cases h
    place_posAtJ := fun _ _ _ h => by cases h
    no0 := fun _ _ _ => rfl, noJ := fun _ _ _ => rfl
    chal_unif := @unif_unique _ Unit _ _ _ _ _ _
    gr0_ok := fun _ e => by cases e
    grJ_ok := fun _ e => by cases e }

/-! ## Depths -/

theorem foldl_max_le' {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (a : ℕ),
      a ≤ l.foldl (fun a d => max a (f d)) a ∧ ∀ d ∈ l, f d ≤ l.foldl (fun a d => max a (f d)) a
  | [], a => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | e :: l, a => by
      obtain ⟨h1, h2⟩ := foldl_max_le' f l (max a (f e))
      refine ⟨le_trans (le_max_left _ _) h1, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact le_trans (le_max_right _ _) h1
      · exact h2 d hd

/-- Every tree that a list of rounds sends is at most as deep as the deepest. -/
theorem le_maxDepthT (ds : List RDT) : ∀ d ∈ ds, ∀ e ∈ d.trees.map (·.a), e ≤ maxDepthT ds := by
  intro d hd e he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
  exact le_trans ((foldl_max_le' (fun s : Fmt.Shape => s.a) d.trees 0).2 s hs)
    ((foldl_max_le' (fun d : RDT => d.trees.foldl (fun n s => max n s.a) 0) ds 0).2 d hd)

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (n : ℕ)

theorem wiresLo_depthLe : ∀ ds : List RDT, (∀ d ∈ ds, ∀ e ∈ d.trees.map (·.a), e ≤ n) →
    RoundsQueryLayout.DepthLe n (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨fun _ he => (by cases he), h d List.mem_cons_self⟩,
      wiresLo_depthLe ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wiresSh_depthLe : ∀ ds : List RDT, (∀ d ∈ ds, ∀ e ∈ d.trees.map (·.a), e ≤ n) →
    RoundsQueryLayout.DepthLe n (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨h d List.mem_cons_self, fun _ he => (by cases he)⟩,
      wiresSh_depthLe ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

end

theorem weOne_ok (a : ℕ) : (weOne a).OK :=
  ⟨(WireE.one_ok (2 ^ a) SgX (0, [])).nodup, (WireE.one_ok (2 ^ a) SgX (0, [])).complete,
    (WireE.one_ok (2 ^ a) SgX (0, [])).build_rd⟩

/-! ## The count of what is opened -/

/-- One round's stored parts. -/
theorem stored_len (a : ℕ) (R : Fmt.Drawn) (l : List Fmt.Stored) :
    (l.flatMap fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ a))).map fun x =>
        Want.table s.item x).length ≤ (l.map (·.count)).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons s l ih =>
      rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      refine Nat.add_le_add ?_ ih
      rw [List.length_map]
      refine le_trans (Fmt.listOf_len _) ?_
      rw [List.length_map]
      unfold Fmt.partOf
      exact List.length_take_le _ _

/-- One round's trees. -/
theorem trees_len (dep : ℕ → Option ℕ) (R : Fmt.Drawn) (n : ℕ) (h : R.poss.length ≤ n)
    (l : List ℕ) :
    (l.flatMap fun j =>
      match dep j with
      | none => []
      | some b => (Fmt.listOf (R.poss.map (· % 2 ^ b))).map fun x => Want.tree j x).length ≤
      n * l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons j l ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ, Nat.add_comm]
      refine Nat.add_le_add ih ?_
      cases dep j with
      | none => exact Nat.zero_le _
      | some b =>
          show ((Fmt.listOf (R.poss.map (· % 2 ^ b))).map fun x => Want.tree j x).length ≤ n
          rw [List.length_map]
          exact le_trans (Fmt.listOf_len _) (by rw [List.length_map]; exact h)

theorem wantsOf_len (C : CK) (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (ds : List RDT), DrawnFitsT C ds → ∀ ρ : Rho (uLT C ds),
      (wantsOf a dep ds (drawnT C ds ρ)).length ≤ nOpenT ds
  | [], _, _ => Nat.le_refl _
  | d :: ds, h, (c, ρ) => by
      show (_ ++ _ ++ wantsOf a dep ds (drawnT C ds ρ)).length ≤
        (((d.stored.map (·.count)).sum + d.entry.poss * d.opens.length) ::
          ds.map fun d => (d.stored.map (·.count)).sum + d.entry.poss * d.opens.length).sum
      rw [List.length_append, List.length_append, List.sum_cons]
      exact Nat.add_le_add
        (Nat.add_le_add (stored_len a _ d.stored)
          (trees_len dep _ _ (h d List.mem_cons_self _) d.opens))
        (wantsOf_len C a dep ds (fun e he => h e (List.mem_cons_of_mem _ he)) ρ)

/-- Two choices from one list, of which no member passes both, are together no longer than it. -/
theorem two_filterMaps {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (h : ∀ x, f x = none ∨ g x = none) :
    ∀ l : List α, (l.filterMap f).length + (l.filterMap g).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: l => by
      have ih := two_filterMaps f g h l
      rcases h x with e | e
      · rw [List.filterMap_cons_none e, List.length_cons]
        cases hg : g x with
        | none => rw [List.filterMap_cons_none hg]; omega
        | some b => rw [List.filterMap_cons_some hg, List.length_cons]; omega
      · rw [List.filterMap_cons_none e, List.length_cons]
        cases hf : f x with
        | none => rw [List.filterMap_cons_none hf]; omega
        | some b => rw [List.filterMap_cons_some hf, List.length_cons]; omega

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

theorem wiresOf_okg (h₁ : ChalUnifT C K chal D.ds₁) (h₂ : ChalUnifT C K chal D.ds₂)
    (h₃ : ChalUnifT C K chal D.ds₃) (w₁ : ∀ d ∈ D.ds₁, d.entry.work ≤ 64)
    (w₂ : ∀ d ∈ D.ds₂, d.entry.work ≤ 64) (w₃ : ∀ d ∈ D.ds₃, d.entry.work ≤ 64) :
    (wiresOf C K chal D tF tJ t3).OKG where
  wF := wireSilent_okg _ _ _ _
  W₁ := wiresLo_okg C K chal D.ds₁ h₁ w₁
  wJ := wireSilent_okg _ _ _ _
  W₂ := wiresSh_okg C K chal D.ds₂ h₂ w₂
  w3 := wireSilent_okg _ _ _ _
  W₃ := wiresLo_okg C K chal D.ds₃ h₃ w₃

theorem wiresOf_depthLe : (wiresOf C K chal D tF tJ t3).DepthLe (maxDepthW D) where
  wF := ⟨fun _ he => (by cases he), fun _ he => (by cases he)⟩
  W₁ := wiresLo_depthLe C K chal _ D.ds₁ fun d hd e he =>
    le_trans (le_maxDepthT D.ds₁ d hd e he) (le_trans (le_max_left _ _) (le_max_right _ _))
  wJ := ⟨fun _ he => (by cases he), fun _ he => (by cases he)⟩
  W₂ := wiresSh_depthLe C K chal _ D.ds₂ fun d hd e he =>
    le_trans (le_maxDepthT D.ds₂ d hd e he)
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  w3 := ⟨fun _ he => (by cases he), fun _ he => (by cases he)⟩
  W₃ := wiresLo_depthLe C K chal _ D.ds₃ fun d hd e he =>
    le_trans (le_maxDepthT D.ds₃ d hd e he)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The verifier opens at most `nOpenW` positions.** -/
theorem whole_opens (f₁ : DrawnFitsT C D.ds₁) (f₂ : DrawnFitsT C D.ds₂) (f₃ : DrawnFitsT C D.ds₃)
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    ((reductionOfWholeFile C D tF tJ t3 silent run).reads ρ).card +
      ((reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ).card ≤ nOpenW D := by
  have hl : (wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)).length ≤
      nOpenW D := by
    rw [List.length_append, List.length_append]
    exact Nat.add_le_add (wantsOf_len C D.a D.depth D.ds₁ f₁ _)
      (Nat.add_le_add (wantsOf_len C D.a D.depth D.ds₂ f₂ _) (wantsOf_len C D.a D.depth D.ds₃ f₃ _))
  refine le_trans (Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)) ?_
  refine le_trans (two_filterMaps _ _ (fun w => ?_) _) hl
  cases w with
  | table _ _ => exact Or.inl rfl
  | tree _ _ => exact Or.inr rfl

/-- **The wire record of a whole file obeys the laws.** -/
theorem wqWhole_okg (h₁ : ChalUnifT C K chal D.ds₁) (h₂ : ChalUnifT C K chal D.ds₂)
    (h₃ : ChalUnifT C K chal D.ds₃) (w₁ : ∀ d ∈ D.ds₁, d.entry.work ≤ 64)
    (w₂ : ∀ d ∈ D.ds₂, d.entry.work ≤ 64) (w₃ : ∀ d ∈ D.ds₃, d.entry.work ≤ 64)
    (f₁ : DrawnFitsT C D.ds₁) (f₂ : DrawnFitsT C D.ds₂) (f₃ : DrawnFitsT C D.ds₃) :
    (wqWhole C K chal D tF tJ t3 silent run).OKG :=
  (wiresOf C K chal D tF tJ t3).qb_okg (wholeDesc C D tF tJ t3 silent run) (weOne D.a)
    (decWhole C D tF tJ t3) (nOpenW D) (maxDepthW D)
    (wiresOf_okg C K chal D tF tJ t3 h₁ h₂ h₃ w₁ w₂ w₃) (weOne_ok D.a)
    (fun _ ρ _ => whole_opens C D tF tJ t3 silent run f₁ f₂ f₃ ρ)
    (wiresOf_depthLe C K chal D tF tJ t3)

end

/-! ## At verifier's messages as hash blocks -/

/-- At hash blocks the first hypothesis is a matter of numbers: no round has more blocks than K. -/
theorem chalUnifT_ckP (f : Fmt.Fld) (K : ℕ) (ds : List RDT)
    (h : ∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) : ChalUnifT (ckP f) K (chalP f K) ds :=
  fun d hd =>
    map_firstBlocks_unif (Dig 256) (fun _ => false) (bsRound f d.entry d.kind).b K (h d hd)

/-- At hash blocks the second hypothesis holds. -/
theorem drawnFitsT_ckP (f : Fmt.Fld) (ds : List RDT) : DrawnFitsT (ckP f) ds :=
  fun d _ c => le_of_eq ((planPull_fits f d.entry d.kind).2 c)

/-- **At hash blocks the wire record of a whole file obeys the laws**, if no round has more than K
blocks or more than 64 bits of work. -/
theorem wqWhole_okg_ckP (f : Fmt.Fld) (K : ℕ) (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ)
    (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (hK : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.entry.work ≤ 64) :
    (wqWhole (ckP f) K (chalP f K) D tF tJ t3 silent run).OKG :=
  wqWhole_okg (ckP f) K (chalP f K) D tF tJ t3 silent run
    (chalUnifT_ckP f K _ fun d hd => hK d (List.mem_append_left _ hd))
    (chalUnifT_ckP f K _ fun d hd => hK d (List.mem_append_right _ (List.mem_append_left _ hd)))
    (chalUnifT_ckP f K _ fun d hd => hK d (List.mem_append_right _ (List.mem_append_right _ hd)))
    (fun d hd => hw d (List.mem_append_left _ hd))
    (fun d hd => hw d (List.mem_append_right _ (List.mem_append_left _ hd)))
    (fun d hd => hw d (List.mem_append_right _ (List.mem_append_right _ hd)))
    (drawnFitsT_ckP f _) (drawnFitsT_ckP f _) (drawnFitsT_ckP f _)

end OnBytes.Maker
