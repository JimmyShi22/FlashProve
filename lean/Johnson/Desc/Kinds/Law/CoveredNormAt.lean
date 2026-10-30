-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CoveredNormAt.lean: reads_covered_K06, THE NORMALIZATION's SHARE, AT A HEARING's RETURN. Law/CoveredNorm.lean asks that the variables of what was
heard be covered (HeardCovered). HERE: where the output head's one hearing returns, every one of these variables NAMES NO ENTRY AT ALL: the hidden sums,
products, claimed sums and end values are bare slots; the three sumchecks' start forms are a bare slot (products, normed) or a form on the nine sums'
slots (the squares' level). So:
  coveredN_all   where hear F rs = some (H, G, left), F WellLaid, S2 ∣ d: ALL 29 FORMS AND THE FOUR KEYS name entries of reads below the lengths spent alone,
                 whatever the reads' places are: no premise on what was heard.
WHAT IT DOES NOT SAY: as in CoveredNorm.lean: where "entry r i" lies; that each read's table is long enough (Law/ReadsFitNorm.lean). Nothing on soundness.
IMPORTED, NOT THIS FILE'S: hear_parts (Law/Cut.lean) · norm_parts (Law/NormHear.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CoveredNorm
import Johnson.Desc.Kinds.Law.NormHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open Norm (lt ls d lPd T S2)

/-- The form names no entry. -/
def NoEnts (f : Form) : Prop := f.ents = #[]

theorem mapM_mem {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β),
    l.mapM f = some l' → ∀ y, y ∈ l' → ∃ x, x ∈ l ∧ f x = some y
  | [], l', h, y, hy => by
    simp at h
    subst h
    simp at hy
  | a :: l, l', h, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, e⟩ := mapM_mem f l bs hl y hy'
          exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem getD_noEnts (arr : Array Hid) (h : ∀ y, y ∈ arr.toList → NoEnts y.var) (j : Nat) :
    NoEnts (arr.getD j {}).var := by
  by_cases hj : j < arr.size
  · have : arr.getD j {} = arr[j]'hj := by simp [Array.getD, hj]
    rw [this]
    exact h _ (Array.getElem_mem_toList hj)
  · have : arr.getD j {} = {} := by simp [Array.getD, hj]
    rw [this]
    rfl

theorem hide_noEnts {v : List E} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hide v F rs = some (c, G, left)) (j : Nat) : NoEnts (c.getD j {}).var := by
  obtain ⟨_, h'⟩ := hide_some h
  obtain ⟨_, rfl⟩ := hide_unfold h'
  refine getD_noEnts _ (fun y hy => ?_) j
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [Array.getElem_toList, Array.getElem_mapIdx]
  rfl

theorem hiddenFrom_noEnts {first n : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hiddenFrom first n F rs = some (c, G, left)) (j : Nat) : NoEnts (c.getD j {}).var := by
  unfold hiddenFrom at h
  cases hr : ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h
    refine getD_noEnts _ (fun y hy => ?_) j
    obtain ⟨i, _, e⟩ := mapM_mem _ _ _ hr y (by simpa using hy)
    cases hs : F.shown (first + i) with
    | none => simp [hs] at e
    | some x =>
      simp [hs] at e
      subst e
      rfl

/-- Where the part's hearing returns. -/
theorem heardBy_noEnts {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F0 F1 : Fork}
    {t left : List Fmt.RoundView} {c : Array Hid} {s : Sum}
    (h : heardBy lead C z ends F0 t = some ((c, s), F1, left)) :
    (∀ j, NoEnts (c.getD j {}).var) ∧ (∀ j, NoEnts (s.end_ j).var) ∧
      ∃ hd, s.psc = some hd ∧ hd.start = C c := by
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, _, k1⟩ := bind_some h
  obtain ⟨ld, Fy, l1, _, k2⟩ := bind_some k1
  obtain ⟨c', Fz, l2, h3, k3⟩ := bind_some k2
  obtain ⟨Fl, Fw, l3, _, k4⟩ := bind_some k3
  obtain ⟨⟨hd, G⟩, Fv, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, _, _⟩ := need_some h5
  dsimp only at k5
  obtain ⟨G2, Fu, l5, _, k6⟩ := bind_some k5
  obtain ⟨_, Ft, l6, _, k7⟩ := bind_some k6
  obtain ⟨es, Fs, l7, h8, k8⟩ := bind_some k7
  obtain ⟨e9, _, _⟩ := pure_some k8
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  obtain ⟨_, _, _, _, _, hrec, _⟩ := Part.MaskedSum.hear_spec e5
  exact ⟨hide_noEnts h3, hiddenFrom_noEnts h8, hd, rfl, by rw [hrec]⟩

theorem sumcheck_noEnts {z : Point} {n : Nat} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (h : sumcheck z n F0 t = some (s, F1, left)) :
    NoEnts s.claimed.var ∧ (∀ j, NoEnts (s.end_ j).var) ∧
      ∃ hd, s.psc = some hd ∧ NoEnts hd.start := by
  unfold sumcheck at h
  obtain ⟨⟨c, s0⟩, G, l, h1, k1⟩ := bind_some h
  obtain ⟨rfl, _, _⟩ := pure_some k1
  obtain ⟨a, b, hd, e1, e2⟩ := heardBy_noEnts h1
  exact ⟨a 0, b, hd, e1, by rw [e2]; exact a 0⟩

theorem level_noEnts {z : Point} {start : Form} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (h : level z start F0 t = some (s, F1, left)) :
    (∀ j, NoEnts (s.end_ j).var) ∧ ∃ hd, s.psc = some hd ∧ hd.start = start := by
  unfold level at h
  obtain ⟨⟨c, s0⟩, G, l, h1, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨⟨v, g⟩, G2, l2, _, k2⟩ := bind_some k1
  dsimp only at k2
  obtain ⟨x, G3, l3, _, k3⟩ := bind_some k2
  obtain ⟨rfl, _, _⟩ := pure_some k3
  obtain ⟨_, b, hd, e1, e2⟩ := heardBy_noEnts h1
  exact ⟨b, hd, e1, e2⟩

theorem batch_noEnts {n rows : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {W : Array Hid} {g : E}
    (h : sendThenBatch n rows F rs = some ((W, g), G, left)) (j : Nat) :
    NoEnts (W.getD j {}).var := by
  unfold sendThenBatch at h
  obtain ⟨⟨v, gs⟩, G1, l1, _, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨W', G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', G3, l3, _, k3⟩ := bind_some k2
  obtain ⟨e4, _, _⟩ := pure_some k3
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, _⟩ := e4
  exact hide_noEnts h2 j

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **ALL 29 FORMS AND THE FOUR KEYS, at a hearing's return.** -/
theorem coveredN_all [FinalNorm.Reads] (hd : S2 ∣ d) {F G : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left)) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    (∀ f, f ∈ FinalNorm.forms → CoveredN f) ∧ ∀ k, CoveredN (FinalNorm.key 21 k) := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  obtain ⟨Fa, Fb, l1, hNorm, _, _, hsN, _, _⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fc, Fd, Fe, _, _, h1, _, h3, h4, h5, _⟩ := norm_parts hW hNorm
  have nW := batch_noEnts h1
  have nP := batch_noEnts h4
  obtain ⟨sqE, hq, eq1, eq2⟩ := level_noEnts h3
  obtain ⟨prC, prE, hp, ep1, ep2⟩ := sumcheck_noEnts h5
  obtain ⟨nmC, nmE, hn, en1, en2⟩ := sumcheck_noEnts hsN
  have HC : HeardCovered :=
    { W := fun s _ => cN_noEnts (nW s)
      P := fun n _ => cN_noEnts (nP n)
      sqStart := fun x hx => by
        have hx' : H.1.squares.psc = some x := hx
        rw [eq1] at hx'
        obtain rfl := Option.some.inj hx'
        rw [eq2]
        unfold Norm.squaresStart
        exact cN_smulE _ (cN_sumTo _ _ fun i _ => cN_sumTo _ _ fun s _ =>
          cN_smulE _ (cN_noEnts (nW _)))
      sqEnd := fun j _ => cN_noEnts (sqE j)
      prStart := fun x hx => by
        have hx' : H.1.products.psc = some x := hx
        rw [ep1] at hx'
        obtain rfl := Option.some.inj hx'
        exact cN_noEnts ep2
      prClaimed := cN_noEnts prC
      prEnd := fun j _ => cN_noEnts (prE j)
      nmStart := fun x hx => by
        have hx' : H.2.1.normed.psc = some x := hx
        rw [en1] at hx'
        obtain rfl := Option.some.inj hx'
        exact cN_noEnts en2
      nmClaimed := cN_noEnts nmC
      nmEnd := fun j _ => cN_noEnts (nmE j) }
  exact ⟨coveredN_forms hd HC, coveredN_key hd HC⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.coveredN_all
