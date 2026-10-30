-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRelParts.lean: TWO RUNS OF ONE TEXT (FlRel,
Johnson/Desc/First/K4/Returns/FlRel.lean): FOLDS AND LISTS; A LAYER OF A PRODUCT TREE; A TOKEN
SUMCHECK. General laws: nothing is evaluated.

  FlRel.foldlM, mapM_list, fmap   the frame through a fold, a list and a map.
  FlRel.shownAll  the values shown under n slots: two arrays of one size.
  FlRel.levelRounds, **FlRel.levelIn**   one shape of the layer (levelSh,
                  Johnson/Desc/First/Shape/Own.lean).
  TscAlike, FlRel.tscLoop, **FlRel.tscIn**   one shape of the token sumcheck (tscSh).

Limits. The weak form of the frame. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelPsc
import Johnson.Desc.First.K4.Returns.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc Tsc Level)
open VerifiableInference.Desc.First.Shape

/-! ## Folds and lists in the frame -/

theorem FlRel.foldlM {α σ σ' : Type} {R : σ → σ' → Prop} {f : σ → α → Fl σ} {f' : σ' → α → Fl σ'}
    (hf : ∀ x s s', R s s' → FlRel R (f s x) (f' s' x)) :
    ∀ (l : List α) (s : σ) (s' : σ'), R s s' → FlRel R (l.foldlM f s) (l.foldlM f' s')
  | [], _, _, h => by
    rw [List.foldlM_nil, List.foldlM_nil]
    exact FlRel.pure h
  | x :: l, s, s', h => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact FlRel.bind (hf x s s' h) fun a b hab => FlRel.foldlM hf l a b hab

/-- Two lists of one length. -/
theorem FlRel.mapM_list {α β β' : Type} {f : α → Fl β} {f' : α → Fl β'}
    (hf : ∀ a, FlRel (fun _ _ => True) (f a) (f' a)) :
    ∀ l : List α, FlRel (fun x y => x.length = y.length) (l.mapM f) (l.mapM f')
  | [] => by
    rw [List.mapM_nil, List.mapM_nil]
    exact FlRel.pure rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    refine FlRel.bind (hf a) fun _ _ _ => FlRel.bind (FlRel.mapM_list hf l) fun x y h => ?_
    exact FlRel.pure (by rw [List.length_cons, List.length_cons, h])

theorem FlRel.fmap {α β γ δ : Type} {S : α → β → Prop} {R : γ → δ → Prop} {x : Fl α} {x' : Fl β}
    {g : α → γ} {g' : β → δ} (hx : FlRel S x x') (hg : ∀ a b, S a b → R (g a) (g' b)) :
    FlRel R (g <$> x) (g' <$> x') := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact FlRel.bind hx fun a b h => FlRel.pure (hg a b h)

/-- The values shown under n slots: two arrays of one size. -/
theorem FlRel.shownAll (first first' n : Nat) :
    FlRel SameSize (OnBytes.Desc.First.K4.shownRun engFl first n)
      (OnBytes.Desc.First.K4.shownRun engFl first' n) := by
  unfold OnBytes.Desc.First.K4.shownRun
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  refine FlRel.fmap (FlRel.mapM_list (f := fun i => engFl.shown (first + i))
    (f' := fun i => engFl.shown (first' + i)) (fun i => FlRel.shown _ _) _) fun a b h => ?_
  show a.toArray.size = b.toArray.size
  simpa using h

/-! ## A layer of a product tree -/

theorem FlRel.levelRounds (mu : Nat) (rho rho' : Array E) :
    ∀ (order : List Nat) (r r' : Array E) (p p' : Psc), SameSize r r' → PscAlike p p' →
      FlRel (fun x x' : Array E × Psc => SameSize x.1 x'.1 ∧ PscAlike x.2 x'.2)
        (Fl.levelRounds mu rho order r p) (Fl.levelRounds mu rho' order r' p')
  | [], r, r', p, p', hr, hp => by
    unfold Fl.levelRounds
    exact FlRel.pure ⟨hr, hp⟩
  | v :: order, r, r', p, p', hr, hp => by
    unfold Fl.levelRounds
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (FlRel.roundIn .eq2 hp _ _ 0) fun x x' hx => ?_
    obtain ⟨a, q⟩ := x
    obtain ⟨a', q'⟩ := x'
    exact FlRel.levelRounds mu rho rho' order _ _ q q' (by
      show (r.set! _ _).size = (r'.set! _ _).size
      simpa using hr) hx

theorem FlRel.levelIn (mu : Nat) (rho rho' : Array E) {C C' : Aff} (h : SameSh C C')
    (order : List Nat) :
    FlRel LevelAlike (Fl.levelIn mu rho C order) (Fl.levelIn mu rho' C' order) := by
  unfold Fl.levelIn
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.pscBegin h) fun p p' hp => ?_
  refine FlRel.bind (FlRel.levelRounds mu rho rho' order _ _ p p' rfl hp) fun x x' hx => ?_
  obtain ⟨r, q⟩ := x
  obtain ⟨r', q'⟩ := x'
  refine FlRel.bind (FlRel.pscEnds hx.2 2 2) fun y y' hy => ?_
  obtain ⟨sL, q2⟩ := y
  obtain ⟨sL', q2'⟩ := y'
  obtain ⟨rfl, hq2⟩ : sL = sL' ∧ PscAlike q2 q2' := hy
  refine FlRel.bind (FlRel.answer _) fun tau tau' _ => ?_
  refine FlRel.bind (FlRel.shown _ _) fun a a' _ => ?_
  refine FlRel.bind (FlRel.shown _ _) fun b b' _ => ?_
  refine FlRel.bind (FlRel.pscRow hq2 _ _ (SameSh.refl _)) fun z z' hz => ?_
  obtain ⟨row, q3⟩ := z
  obtain ⟨row', q3'⟩ := z'
  refine FlRel.pure ?_
  show LevelSh.mk r.size sL (sL + 1) (affSh row) = LevelSh.mk r'.size sL (sL + 1) (affSh row')
  rw [hx.1, hz.1]

/-! ## A token sumcheck -/

/-- Two token sumchecks of one shape. -/
def TscAlike (o o' : Tsc) : Prop := tscSh o = tscSh o'

theorem FlRel.tscLoop : ∀ (zs zs' : List E) (r r' : Array E) (p p' : Psc),
    zs.length = zs'.length → SameSize r r' → PscAlike p p' →
      FlRel (fun x x' : Array E × Psc => SameSize x.1 x'.1 ∧ PscAlike x.2 x'.2)
        (Fl.tscLoop zs r p) (Fl.tscLoop zs' r' p')
  | [], [], r, r', p, p', _, hr, hp => by
    unfold Fl.tscLoop
    exact FlRel.pure ⟨hr, hp⟩
  | [], _ :: _, _, _, _, _, hl, _, _ => by cases hl
  | _ :: _, [], _, _, _, _, hl, _, _ => by cases hl
  | z :: zs, z' :: zs', r, r', p, p', hl, hr, hp => by
    unfold Fl.tscLoop
    refine FlRel.bind (FlRel.roundIn .eq2 hp z z' 0) fun x x' hx => ?_
    obtain ⟨a, q⟩ := x
    obtain ⟨a', q'⟩ := x'
    exact FlRel.tscLoop zs zs' _ _ q q' (Nat.succ.inj hl) (by
      show (r.push a).size = (r'.push a').size
      rw [Array.size_push, Array.size_push, hr]) hx

theorem FlRel.tscIn {P P' : Array E} (hP : SameSize P P') (lt shown dY : Nat) :
    FlRel TscAlike (Fl.tscIn P lt shown dY) (Fl.tscIn P' lt shown dY) := by
  unfold Fl.tscIn Fl.tscRounds
  simp only [bind_assoc, pure_bind]
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.claimsIn 1) fun sCl sCl' hs => ?_
  subst hs
  refine FlRel.bind (FlRel.pscBegin (SameSh.refl _)) fun p p' hp => ?_
  refine FlRel.bind (FlRel.tscLoop _ _ #[] #[] p p' (by
    rw [List.length_take, List.length_take, Array.length_toList, Array.length_toList, hP]) rfl hp)
    fun x x' hx => ?_
  obtain ⟨r, q⟩ := x
  obtain ⟨r', q'⟩ := x'
  refine FlRel.bind (FlRel.pscEnds hx.2 dY shown) fun y y' hy => ?_
  obtain ⟨sEnd, q2⟩ := y
  obtain ⟨sEnd', q2'⟩ := y'
  obtain ⟨rfl, hq2⟩ : sEnd = sEnd' ∧ PscAlike q2 q2' := hy
  refine FlRel.pure ?_
  show TscSh.mk sCl sEnd r.size (pscSh q2) (affSh {}) = TscSh.mk sCl sEnd r'.size (pscSh q2')
    (affSh {})
  rw [hx.1, hq2]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.FlRel.foldlM
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.mapM_list
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.fmap
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.shownAll
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.levelRounds
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.levelIn
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.tscLoop
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.tscIn
#print axioms OnBytes.Desc.First.K4.Rt.TscAlike
