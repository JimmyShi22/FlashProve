-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Cut.lean: FROM THE BLOCK's ONE HEARING TO EACH SUMCHECK AT ITS OWN ROUNDS. The laws of the
head's sumchecks (k06Out; Law/SumLaw.lean: coreG; Law/Normed.lean: normed_law) speak of a hearing
"sumcheck z n F0 t = some (S, F1, [])": at the sumcheck's own rounds t, with none left, from a ledger F0 that
is WellLaid. In the block that runs, ONE hearing (Head.lean: hear) reads all rounds in a row. Here is what
lies between. No chance in it.
  Quiet; heardBy_cut, sumcheck_cut, level_cut   a sumcheck reads its first z.size + 3 rounds (a level: one
      more) and no other: where it returns at a list of rounds, it returns the same at just these, with none
      left; what is left is the rest.
  Wl; wl_...   every hearing of HeadParts.lean, Norm.lean, HeadNorm.lean, Head.lean keeps WellLaid.
  hear_parts   where hear returns: the normalization's hearing; then "normed" at its own rounds; then the
      head's sumcheck at its own; each from a WellLaid ledger; and how the rounds are cut.
  within, noBad_within   a rule on a stretch's own fronts, as a rule on the block's fronts: it looks at the
      fronts that end inside the stretch and is empty elsewhere.
IMPORTED, NOT THIS FILE'S: Law/Sum2b.lean (bind_some and the like), Law/Ledger.lean (hideRun_frame).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Lemma2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (Aff Fork)

/-! ## 1. Hearings that read no round -/

theorem bind_eq {α β : Type} {x : Hear α} {f : α → Hear β} {F G : Fork} {rs left : List Fmt.RoundView}
    {a : α} (h : x F rs = some (a, G, left)) : (x >>= f) F rs = f a G left := by
  show (match x F rs with
    | some (a, G, left) => f a G left
    | none => none) = f a G left
  rw [h]

/-- The hearing hands the rounds on as they are, and does the same at every list of rounds. -/
def Quiet {α : Type} (x : Hear α) : Prop :=
  ∀ F l a G l', x F l = some (a, G, l') → l' = l ∧ ∀ m, x F m = some (a, G, m)

theorem quiet_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : Quiet x)
    (hf : ∀ a, Quiet (f a)) : Quiet (x >>= f) := by
  intro F l b G l' h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  obtain ⟨rfl, e1⟩ := hx _ _ _ _ _ h1
  obtain ⟨rfl, e2⟩ := hf a _ _ _ _ _ h2
  exact ⟨rfl, fun m => by rw [bind_eq (e1 m)]; exact e2 m⟩

theorem quiet_pure {α : Type} (a : α) : Quiet (pure a : Hear α) := by
  intro F l b G l' h
  obtain ⟨rfl, rfl, rfl⟩ := pure_some h
  exact ⟨rfl, fun _ => rfl⟩

theorem quiet_need {α : Type} (x : Option α) : Quiet (Hear.need x) := by
  intro F l b G l' h
  obtain ⟨rfl, rfl, rfl⟩ := need_some h
  exact ⟨rfl, fun _ => rfl⟩

theorem quiet_ledger : Quiet Hear.ledger := by
  intro F l b G l' h
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h
  exact ⟨rfl, fun _ => rfl⟩

theorem quiet_lay (X : Fork) : Quiet (Hear.lay X) := by
  intro F l b G l' h
  obtain ⟨rfl, rfl⟩ := lay_some h
  exact ⟨rfl, fun _ => rfl⟩

theorem quiet_hide (v : List E) : Quiet (hide v) := by
  intro F l b G l' h
  unfold hide at h ⊢
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray OnBytes.oneE with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩

theorem quiet_hiddenFrom (first n : Nat) : Quiet (hiddenFrom first n) := by
  intro F l b G l' h
  unfold hiddenFrom at h ⊢
  cases hr : ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩

/-- A stretch of n rounds, and then a hearing that reads no round. -/
theorem stretch_bind_cut {β : Type} (n : Nat) (f : List Fmt.RoundView → Hear β) (hf : ∀ rs, Quiet (f rs))
    {F G : Fork} {t left : List Fmt.RoundView} {x : β}
    (h : (Hear.stretch n >>= f) F t = some (x, G, left)) :
    (Hear.stretch n >>= f) F (t.take n) = some (x, G, []) ∧ left = t.drop n ∧ n ≤ t.length := by
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hst : ¬ t.length < n ∧ t.take n = rs ∧ F = Fx ∧ t.drop n = l0 := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · rename_i hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact ⟨hlt, h1.1, h1.2.1, h1.2.2⟩
  obtain ⟨hlen, rfl, rfl, rfl⟩ := hst
  obtain ⟨rfl, e⟩ := hf _ _ _ _ _ _ k1
  refine ⟨?_, rfl, by omega⟩
  have h2 : Hear.stretch n F (t.take n) = some (t.take n, F, []) := by
    unfold Hear.stretch
    have hl : (t.take n).length = n := by rw [List.length_take]; omega
    rw [if_neg (by omega), List.take_take, Nat.min_self, List.drop_eq_nil_of_le (by omega)]
  rw [bind_eq h2]
  exact e []

theorem heardBy_cut {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F G : Fork}
    {t left : List Fmt.RoundView} {x : Array Hid × Sum} (h : heardBy lead C z ends F t = some (x, G, left)) :
    heardBy lead C z ends F (t.take (z.size + 3)) = some (x, G, []) ∧ left = t.drop (z.size + 3)
      ∧ z.size + 3 ≤ t.length := by
  unfold heardBy at h ⊢
  refine stretch_bind_cut _ _ (fun rs => ?_) h
  refine quiet_bind (quiet_need _) fun _ => quiet_bind (quiet_hide _) fun _ =>
    quiet_bind quiet_ledger fun _ => quiet_bind (quiet_need _) fun y => ?_
  obtain ⟨hd, G'⟩ := y
  exact quiet_bind (quiet_need _) fun _ => quiet_bind (quiet_lay _) fun _ =>
    quiet_bind (quiet_hiddenFrom _ _) fun _ => quiet_pure _

/-- **A sumcheck reads its first z.size + 3 rounds and no other.** -/
theorem sumcheck_cut {z : Point} {n : Nat} {F G : Fork} {t left : List Fmt.RoundView} {S : Sum}
    (h : sumcheck z n F t = some (S, G, left)) :
    sumcheck z n F (t.take (z.size + 3)) = some (S, G, []) ∧ left = t.drop (z.size + 3)
      ∧ z.size + 3 ≤ t.length := by
  unfold sumcheck at h ⊢
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨e1, rfl, e3⟩ := heardBy_cut h1
  obtain ⟨c, s⟩ := cs
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k1
  exact ⟨by rw [bind_eq e1]; rfl, rfl, e3⟩

/-! ## 2. WellLaid is kept -/

/-- Wherever the hearing returns from a ledger that has a place for each of its numbers, so has the
ledger behind. -/
def Wl {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, WellLaid F → x F rs = some (a, G, left) → WellLaid G

theorem wl_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : Wl x) (hf : ∀ a, Wl (f a)) :
    Wl (x >>= f) := by
  intro F rs b G left hW h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  exact hf a _ _ _ _ _ (hx _ _ _ _ _ hW h1) h2

theorem wl_pure {α : Type} (a : α) : Wl (pure a : Hear α) := by
  intro F rs b G left hW h
  obtain ⟨_, rfl, _⟩ := pure_some h
  exact hW

theorem wl_need {α : Type} (x : Option α) : Wl (Hear.need x) := by
  intro F rs b G left hW h
  obtain ⟨_, rfl, _⟩ := need_some h
  exact hW

theorem wl_round (n k : Nat) : Wl (Hear.round n k) := by
  intro F rs b G left hW h
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some v =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]; exact hW

theorem wl_hide (v : List E) : Wl (hide v) := by
  intro F rs b G left hW h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact (hideRun_frame (F := { F with next := F.next + v.length }) hW hr).1

theorem wl_drawPoint (n : Nat) : Wl (drawPoint n) :=
  wl_bind (wl_round 0 n) fun _ => wl_pure _

theorem wl_sendThenBatch (n rows : Nat) : Wl (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine wl_bind (wl_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact wl_bind (wl_hide v) fun _ => wl_bind (wl_need _) fun _ => wl_pure _

theorem wl_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    Wl (heardBy lead C z ends) := by
  intro F0 t b F1 left hW h
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hFx : F0 = Fx := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact h1.2.1
  subst hFx
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨_, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  have W1 : WellLaid Fa := wl_hide ld _ _ _ _ _ hW h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have W2 : WellLaid G := by
    refine (hideRun_frame ?_ hrun2).1
    exact W1
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have W3 : WellLaid Fr := (hideRun_frame W2 e6).1
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact W3

theorem wl_sumcheck (z : Point) (ends : Nat) : Wl (sumcheck z ends) := by
  unfold sumcheck
  refine wl_bind (wl_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact wl_pure _

theorem wl_level (z : Point) (start : Form) : Wl (level z start) := by
  unfold level
  refine wl_bind (wl_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine wl_bind (wl_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact wl_bind (wl_need _) fun _ => wl_pure _

section Classes
variable [Sizes] [FinalNorm.In]

theorem wl_normRest (pV : Point) : Wl (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine wl_bind (wl_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine wl_bind ?_ fun rhoI => wl_bind (wl_level _ _) fun _ =>
    wl_bind (wl_sendThenBatch _ _) fun y => ?_
  · first
      | exact wl_pure _
      | (split
         · exact wl_pure _
         · exact wl_drawPoint _)
  · obtain ⟨P, om⟩ := y
    exact wl_bind (wl_sumcheck _ _) fun _ => wl_pure _

theorem wl_norm : Wl Norm.hear :=
  wl_bind (wl_drawPoint _) fun _ => wl_normRest _

/-- **Where the block's one hearing returns.** -/
theorem hear_parts {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : hear F rs = some (H, G, left)) :
    ∃ (Fa Fb : Fork) (l1 : List Fmt.RoundView),
      Norm.hear F rs = some (H.1, Fa, l1) ∧ WellLaid Fa ∧ WellLaid Fb ∧
      sumcheck FinalNorm.zt 2 Fa (l1.take ((FinalNorm.zt).size + 3))
        = some (H.2.1.normed, Fb, []) ∧
      sumcheck (FinalNorm.zt ++ halves Norm.lPd) 2 Fb
          ((l1.drop ((FinalNorm.zt).size + 3)).take ((FinalNorm.zt ++ halves Norm.lPd).size + 3))
        = some (H.2.2.logits, G, []) ∧
      left = (l1.drop ((FinalNorm.zt).size + 3)).drop ((FinalNorm.zt ++ halves Norm.lPd).size + 3) := by
  unfold hear at h
  obtain ⟨n, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨f, F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨lg, F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  have W1 : WellLaid F1 := wl_norm _ _ _ _ _ hW h1
  unfold FinalNorm.hear at h2
  obtain ⟨nm, F2', l2', h4, k4⟩ := bind_some h2
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k4
  have W2 : WellLaid F2' := wl_sumcheck _ _ _ _ _ _ _ W1 h4
  obtain ⟨c1, rfl, _⟩ := sumcheck_cut h4
  obtain ⟨c2, rfl, _⟩ := sumcheck_cut h3
  exact ⟨F1, F2', l1, h1, W1, W2, c1, c2, rfl⟩

end Classes

/-! ## 3. A rule on a stretch, as a rule on the block -/

/-- The rule bad on the fronts of the stretch of n rounds behind the first s: at a front of the block's
rounds that ends inside the stretch: bad at the front without its first s rounds; empty elsewhere. -/
def within (s n : Nat) (bad : List Fmt.RoundView → List E) (h : List Fmt.RoundView) : List E :=
  if s < h.length ∧ h.length ≤ s + n then bad (h.drop s) else []

theorem noBad_within {bad : List Fmt.RoundView → List E} {pre t post : List Fmt.RoundView}
    (h : NoBad (within pre.length t.length bad) (pre ++ t ++ post)) : NoBad bad t := by
  intro i r hi x hx
  have hil : i < t.length := (List.getElem?_eq_some_iff.mp hi).1
  have h1 : (pre ++ t ++ post)[pre.length + i]? = some r := by
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hil]
    exact hi
  have h2 := h (pre.length + i) r h1 x hx
  have h3 : (pre ++ t ++ post).take (pre.length + i) = pre ++ t.take i := by
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hil),
      List.take_zero, List.append_nil]
  unfold within at h2
  rw [h3] at h2
  have hl : (pre ++ t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }]).length
      = pre.length + i + 1 := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
    omega
  rw [if_pos (by rw [hl]; omega), List.append_assoc, List.drop_left] at h2
  exact h2

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.hear_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.noBad_within
