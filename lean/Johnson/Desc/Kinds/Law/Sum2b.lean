-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Sum2b.lean: BRIDGES FOR LEMMA 2b (the branch's form, over raw rounds and
MaskedSum4.lean). B1: what a return of HeadParts.lean's `sumcheck` says, step by step. B4: the part's
`row` is `rowForm` with `rowLaid`.
-/
import Mathlib
import Johnson.Desc.Part.MaskedSumSound
import Johnson.Desc.Kinds.Law.Lemma2a

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open Part.MaskedSum (Call Var Ends row rowForm rowLaid leadScalars challenges)

/-! ## B4 -/

theorem row_eq (h : Part.MaskedSum.Heard) (S0 : E) (kept : Aff) (F : Fork) :
    row h S0 kept F = (rowLaid h F).map fun G => (rowForm h S0 kept, G) := by
  unfold row rowLaid rowForm
  cases hG : F.hideRun h.first
      (Array.replicate (Part.MaskedSum.hidingAt (h.vars.zip h.r)).1.length OnBytes.zeroE)
      (OnBytes.subE OnBytes.zeroE OnBytes.oneE) with
  | none => simp [hG, bind, Option.bind]
  | some G => simp [hG, bind, Option.bind, pure]

/-! ## B1: the monad of a hearing -/

theorem bind_some {α β : Type} {x : Hear α} {f : α → Hear β} {F : Fork} {rs : List Fmt.RoundView}
    {r : β × Fork × List Fmt.RoundView} (h : (x >>= f) F rs = some r) :
    ∃ a G left, x F rs = some (a, G, left) ∧ f a G left = some r := by
  cases hx : x F rs with
  | none =>
    have : (x >>= f) F rs = none := by
      show (match x F rs with
        | some (a, G, left) => f a G left
        | none => none) = none
      rw [hx]
    rw [this] at h; cases h
  | some v =>
    obtain ⟨a, G, left⟩ := v
    refine ⟨a, G, left, rfl, ?_⟩
    have : (x >>= f) F rs = f a G left := by
      show (match x F rs with
        | some (a, G, left) => f a G left
        | none => none) = f a G left
      rw [hx]
    rw [← this]; exact h

theorem need_some {α : Type} {x : Option α} {F G : Fork} {rs left : List Fmt.RoundView} {a : α}
    (h : Hear.need x F rs = some (a, G, left)) : x = some a ∧ F = G ∧ rs = left := by
  unfold Hear.need at h
  cases x with
  | none => simp at h
  | some v =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.1], h.2.1, h.2.2⟩

theorem ledger_some {F G a : Fork} {rs left : List Fmt.RoundView}
    (h : Hear.ledger F rs = some (a, G, left)) : F = a ∧ F = G ∧ rs = left := by
  unfold Hear.ledger at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h

theorem lay_some {X F G : Fork} {rs left : List Fmt.RoundView} {u : Unit}
    (h : Hear.lay X F rs = some (u, G, left)) : X = G ∧ rs = left := by
  unfold Hear.lay at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.2

theorem pure_some {α : Type} {a b : α} {F G : Fork} {rs left : List Fmt.RoundView}
    (h : (pure a : Hear α) F rs = some (b, G, left)) : a = b ∧ F = G ∧ rs = left := by
  have h' : some (a, F, rs) = some (b, G, left) := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  exact h'

/-- `hide` reads no round. -/
theorem hide_some {v : List E} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hide v F rs = some (c, G, left)) : rs = left ∧ hide v F [] = some (c, G, []) := by
  unfold hide at h ⊢
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray OnBytes.oneE with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2 e3
    exact ⟨rfl, rfl⟩

/-- `hiddenFrom` reads no round and lays nothing. -/
theorem hiddenFrom_some {first n : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hiddenFrom first n F rs = some (c, G, left)) :
    F = G ∧ rs = left ∧ hiddenFrom first n F [] = some (c, F, []) := by
  unfold hiddenFrom at h ⊢
  cases hr : ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2 e3
    exact ⟨rfl, rfl, rfl⟩

/-- The call of the part that HeadParts.lean's `heardBy` makes. -/
def callOf (lead : Nat) (z : Point) (ends : Nat) : Call :=
  { lead, vs := z.toList.map (.point · 3), ends := some ⟨2, ends⟩ }

/-- **B1.** What a return of `heardBy` that leaves no round says. -/
theorem heardBy_spec {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F0 F1 : Fork}
    {t : List Fmt.RoundView} {c : Array Hid} {S : Sum}
    (h : heardBy lead C z ends F0 t = some ((c, S), F1, [])) :
    ∃ (ld : List E) (Fa G : Fork) (hd : Part.MaskedSum.Heard) (es : Array Hid),
      t.length = z.size + 3 ∧ leadScalars (callOf lead z ends) t = some ld ∧
      hide ld F0 [] = some (c, Fa, []) ∧
      Part.MaskedSum.hear (C c) (callOf lead z ends) Fa t = some (hd, G) ∧ rowLaid hd G = some F1 ∧
      hiddenFrom hd.sEnd ends F1 [] = some (es, F1, []) ∧
      S = { r := (challenges (callOf lead z ends) hd).toArray, ends := es, psc := some hd } := by
  unfold heardBy at h
  obtain ⟨rs, Fx, left, h1, k1⟩ := bind_some h
  have hst : ¬ t.length < z.size + 3 ∧ t.take (z.size + 3) = rs ∧ F0 = Fx ∧
      t.drop (z.size + 3) = left := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · rename_i hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact ⟨hlt, h1.1, h1.2.1, h1.2.2⟩
  obtain ⟨hlen, rfl, rfl, rfl⟩ := hst
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨e2, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  obtain ⟨rfl, e3⟩ := hide_some h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, e8⟩ := hiddenFrom_some h8
  obtain ⟨hcs, rfl, hnil⟩ := pure_some k8
  have hl : t.length = z.size + 3 := by
    have := congrArg List.length hnil
    simp only [List.length_nil, List.length_drop] at this
    omega
  have htake : t.take (z.size + 3) = t := List.take_of_length_le (by omega)
  rw [htake] at e2 e5
  simp only [Prod.mk.injEq] at hcs
  obtain ⟨rfl, rfl⟩ := hcs
  exact ⟨ld, Fa, G, hd, es, hl, e2, e3, e5, e6, e8, rfl⟩

/-- The same for `sumcheck`. -/
theorem sumcheck_spec {z : Point} {ends : Nat} {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (h : sumcheck z ends F0 t = some (S, F1, [])) :
    ∃ (ld : List E) (c : Array Hid) (Fa G : Fork) (hd : Part.MaskedSum.Heard) (es : Array Hid),
      t.length = z.size + 3 ∧ leadScalars (callOf 1 z ends) t = some ld ∧
      hide ld F0 [] = some (c, Fa, []) ∧
      Part.MaskedSum.hear (c.getD 0 {}).var (callOf 1 z ends) Fa t = some (hd, G) ∧
      rowLaid hd G = some F1 ∧ hiddenFrom hd.sEnd ends F1 [] = some (es, F1, []) ∧
      S = { r := (challenges (callOf 1 z ends) hd).toArray, ends := es, psc := some hd,
            claimed := c.getD 0 {} } := by
  unfold sumcheck at h
  obtain ⟨cs, F, left, h1, h⟩ := bind_some h
  obtain ⟨c, s⟩ := cs
  dsimp only at h
  obtain ⟨hS, rfl, rfl⟩ := pure_some h
  obtain ⟨ld, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, rfl⟩ := heardBy_spec h1
  exact ⟨ld, c, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hS.symm⟩

end VerifiableInference.Desc.Kinds.Head.Law
