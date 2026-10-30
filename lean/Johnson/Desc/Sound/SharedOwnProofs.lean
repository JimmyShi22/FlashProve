-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedOwnProofs.lean: the proofs of `LiftHands` and `ChainLinkOwn`
(Johnson/Desc/Sound/SharedRule.lean).

Limits: those of Johnson/Desc/Sound/SharedRule.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedRuleClosed
import Johnson.Desc.Sound.FoldLiftProof
import OnBytes.Maker.RowWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- To hand an acting part on is to treat statements with one acting part alike. -/
theorem handsAct_of_congr (p : Piece C F S Cl W) (act act' : BKey F S)
    (h : ∀ a a' τ, act.2 a = act.2 a' →
      (p.ior.red.out a τ).map act'.2 = (p.ior.red.out a' τ).map act'.2) : p.HandsAct act act' := by
  classical
  refine ⟨fun k τ => if hk : ∃ a, act.2 a = k then (p.ior.red.out hk.choose τ).map act'.2 else none,
    fun a τ => ?_⟩
  have hk : ∃ a', act.2 a' = act.2 a := ⟨a, rfl⟩
  beta_reduce
  rw [dif_pos hk]
  exact h a hk.choose τ hk.choose_spec.symm

/-- Two strings of oracles with one table, alike at the trees from lo to below the stretch's first:
the column at a wanted leaf of a tree from lo on is the same. -/
theorem sCol_alike (p : Piece C F S Cl W) (lo : ℕ) (t : (oneExternalString (2 ^ F.a) SgX).Str)
    (u u' : (EjOf F.all).Str)
    (hT : ∀ j x, lo ≤ j → j < p.base → (posL F.all j x).map u = (posL F.all j x).map u')
    (τ : Iop.Tr (uLT C p.ds)) :
    ∀ w : Want, (∀ j x, w = .tree j x → lo ≤ j) →
      sCol C p.stage (t, u) τ w = sCol C p.stage (t, u') τ w
  | .table _ _, _ => rfl
  | .tree j x, h => by
    by_cases hj : j < p.base
    · show (if j < p.base then (posL F.all j x).map u else _) =
        (if j < p.base then (posL F.all j x).map u' else _)
      rw [if_pos hj, if_pos hj]
      exact hT j x (h j x rfl) hj
    · show (if j < p.base then (posL F.all j x).map u else _) =
        (if j < p.base then (posL F.all j x).map u' else _)
      rw [if_neg hj, if_neg hj]

theorem liftHands : LiftHands := by
  intro S S₀ Cl W C F get set b₀ p lo hb h1 h2 ho
  refine handsAct_of_congr p _ _ ?_
  rintro ⟨s, t, u⟩ ⟨s', t', u'⟩ τ e
  have es : get s = get s' := congrArg Prod.fst e
  obtain rfl : t = t' := congrArg (fun z => z.2.1) e
  have e3 : (fun j x => if lo ≤ j ∧ j < p.base then (posL F.all j x).map u else none) =
      fun j x => if lo ≤ j ∧ j < p.base then (posL F.all j x).map u' else none :=
    congrArg (fun z => z.2.2) e
  have hT : ∀ j x, lo ≤ j → j < p.base → (posL F.all j x).map u = (posL F.all j x).map u' := by
    intro j x h1 h2
    have := congrFun (congrFun e3 j) x
    rwa [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h2⟩] at this
  have hc := sCol_alike p lo t u u' hT τ
  have hv : sView C p.stage (t, u) τ = sView C p.stage (t, u') τ := by
    unfold sView
    congr 1
    refine List.filterMap_congr fun w hw => ?_
    rw [hc w fun j x hjx => ?_]
    subst hjx
    obtain ⟨⟨d, hd, hj⟩, _⟩ := mem_wantsOf_tree _ _ j x _ _ hw
    exact ho d hd j hj
  have hl : ∀ j x, lo ≤ j → (posL F.all j x).map (sLeft C p.stage (t, u) τ) =
      (posL F.all j x).map (sLeft C p.stage (t, u') τ) := by
    intro j x h1
    cases hp : posL F.all j x with
    | none => rfl
    | some q =>
      have hq := posL_spec F.all j x q hp
      refine congrArg some ?_
      show (sCol C p.stage (t, u) τ (.tree (F.all.get q.1).no q.2.val)).getD [] =
        (sCol C p.stage (t, u') τ (.tree (F.all.get q.1).no q.2.val)).getD []
      rw [hc _ fun j' x' hjx => ?_]
      cases hjx
      rw [hq.1]
      exact h1
  have ht : sTests C p.stage (t, u) τ = sTests C p.stage (t, u') τ := rfl
  have hr : ∀ (x : S) (v : Fmt.View),
      p.run x v = (foldRun F p.b.name [b₀] p.back (get x) v).map (set x) := by
    intro x v
    show foldRun F p.b.name [p.b] p.back x v = _
    rw [hb]
    exact foldLift S S₀ Cl F _ [b₀] p.back get set h1 h2 x v
  have key : ∀ (x : S) (w : (EjOf F.all).Str),
      ((p.ior.out x (t, w) τ).map fun xo => (xo, p.ior.imp (t, w) τ)).map
          (actAt F get lo (p.base + p.trees)).2 =
        (if sTests C p.stage (t, w) τ then
          foldRun F p.b.name [b₀] p.back (get x) (sView C p.stage (t, w) τ) else none).map
          fun z => (z, t, fun j y => if lo ≤ j ∧ j < p.base + p.trees then
            (posL F.all j y).map (sLeft C p.stage (t, w) τ) else none) := by
    intro x w
    show ((if sTests C p.stage (t, w) τ then p.run x (sView C p.stage (t, w) τ)
      else none).map _).map _ = _
    rw [hr]
    by_cases hs : sTests C p.stage (t, w) τ = true
    · rw [if_pos hs, if_pos hs]
      cases foldRun F p.b.name [b₀] p.back (get x) (sView C p.stage (t, w) τ) with
      | none => rfl
      | some z =>
        show some (get (set x z), t, _) = some (z, t, _)
        rw [h1]
    · rw [if_neg hs, if_neg hs]
      rfl
  have hf : (fun j y => if lo ≤ j ∧ j < p.base + p.trees then
      (posL F.all j y).map (sLeft C p.stage (t, u) τ) else none) =
      fun j y => if lo ≤ j ∧ j < p.base + p.trees then
        (posL F.all j y).map (sLeft C p.stage (t, u') τ) else none := by
    funext j y
    by_cases h : lo ≤ j ∧ j < p.base + p.trees
    · rw [if_pos h, if_pos h]
      exact hl j y h.1
    · rw [if_neg h, if_neg h]
  show ((p.ior.out s (t, u) τ).map fun xo => (xo, p.ior.imp (t, u) τ)).map _ =
    ((p.ior.out s' (t, u') τ).map fun xo => (xo, p.ior.imp (t, u') τ)).map _
  rw [key s u, key s' u', es, hv, ht, hf]

theorem each_own {S₀ : Type} (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (Rc : S × F.E.Str → W → Prop) (get : S → S₀) (set : S → S₀ → S)
    (g1 : ∀ t s, get (set t s) = s) (g2 : ∀ t s s', set (set t s) s' = set t s') (lo : ℕ) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ) (act : ℕ → BKey F S),
      (∀ k, act (i + k) = actAt F get lo (hiAt k p l)) → Tiled p l →
      EachGoodIn on R i (p :: l) → EachRels on R act i (p :: l) → EachKeeps on Rc i (p :: l) →
      (∀ q ∈ p :: l, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
      (∀ q ∈ p :: l, ∀ d ∈ q.ds, ∀ j ∈ d.opens, lo ≤ j) →
      EachLost on (fun i a w => R i a w ∧ Rc a w) act i (p :: l) ∧ EachHands act i (p :: l)
  | [], p, i, act, ha, _, hg, hr, hk, hb, ho => by
    have h0 : act i = actAt F get lo p.base := ha 0
    have h1 : act (i + 1) = actAt F get lo (p.base + p.trees) := ha 1
    obtain ⟨b₀, hb₀⟩ := hb p (List.mem_cons_self ..)
    have hh : p.HandsAct (act i) (act (i + 1)) := by
      rw [h0, h1]
      exact liftHands S S₀ Cl W C F get set b₀ p lo hb₀ g1 g2 (ho p (List.mem_cons_self ..))
    exact ⟨⟨lostBeside S Cl W C F p _ _ _ _ Rc _
      (lostOfGoodIn S Cl W C F p _ _ _ _ _ _ hg.1 ⟨hh, hr.1⟩) hk.1, trivial⟩, ⟨hh, trivial⟩⟩
  | q :: l, p, i, act, ha, ht, hg, hr, hk, hb, ho => by
    have h0 : act i = actAt F get lo p.base := ha 0
    have h1 : act (i + 1) = actAt F get lo (p.base + p.trees) := by
      rw [ha 1]
      show actAt F get lo q.base = _
      rw [ht.2.2.2.1]
    obtain ⟨b₀, hb₀⟩ := hb p (List.mem_cons_self ..)
    have hh : p.HandsAct (act i) (act (i + 1)) := by
      rw [h0, h1]
      exact liftHands S S₀ Cl W C F get set b₀ p lo hb₀ g1 g2 (ho p (List.mem_cons_self ..))
    have ih := each_own on R Rc get set g1 g2 lo l q (i + 1) act
      (fun k => by
        rw [show i + 1 + k = i + (k + 1) by omega]
        exact ha (k + 1))
      ht.2.2.2.2 hg.2 hr.2 hk.2 (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq'))
      (fun q' hq' => ho q' (List.mem_cons_of_mem _ hq'))
    exact ⟨⟨lostBeside S Cl W C F p _ _ _ _ Rc _
      (lostOfGoodIn S Cl W C F p _ _ _ _ _ _ hg.1 ⟨hh, hr.1⟩) hk.1, ih.1⟩, ⟨hh, ih.2⟩⟩

theorem chainLinkOwn : ChainLinkOwn := by
  intro S S₀ Cl W C F name N on R Rc d p l h get set lo ht hg hr hk g1 g2 hb ho
  obtain ⟨h1, h2⟩ := each_own on R Rc get set g1 g2 lo l p 0 (actsOf get lo p l)
    (fun k => by rw [Nat.zero_add]; rfl) ht hg hr hk hb ho
  exact chainLinkActs S Cl W C F name N on (fun i a w => R i a w ∧ Rc a w) d p l h
    (actsOf get lo p l) ht h1 h2

end VerifiableInference.Desc.Sound
