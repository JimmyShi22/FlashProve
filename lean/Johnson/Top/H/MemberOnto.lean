-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/MemberOnto.lean: the change of shape of a member of a shape of the programs (membPort,
Johnson/Top/H/MemberOf.lean) carries forms onto: the premise hV of RowsK.fm_onto
(Johnson/Top/H/GroupRowsOnto.lean), paid at that view.
Statements and proofs.
  Reshape.comp_onto · pairL_onto · pairR_onto   onto goes through the three ways of joining.
  tabSame_onto · tabNone_onto · tabVoid_onto · maskSame_onto · pairAt_onto · mainAt_onto ·
  maskAt_onto
      the pieces: each carries a form as it is, or onto a table without a row.
  membPort_onto   the member's view.
  ofFn_onto       so for the group's data made of such members (Rows.ofFn).
Limits: onto is shown of membPort's view and its pieces, of no other view. That a group's members
are such members is the caller's matter. Three statements stand in the namespace Cb.Reshape, beside
the definitions that they speak of. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H.MemberOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Reshape
variable {E P : Type} {C C' C'' : LdCode E P}

theorem comp_onto (ρ' : Reshape C' C'') (ρ : Reshape C C') (h' : Function.Surjective ρ'.fm)
    (h : Function.Surjective ρ.fm) : Function.Surjective (ρ'.comp ρ).fm :=
  h'.comp h

theorem pairL_onto (ρ : Reshape C C') (D : LdCode E P) (h : Function.Surjective ρ.fm) :
    Function.Surjective (ρ.pairL D).fm := fun V => by
  obtain ⟨a, ha⟩ := h fun j => V (.inl j)
  refine ⟨Sum.elim a fun j => V (.inr j), funext fun j => ?_⟩
  rcases j with j | j
  · exact congrFun ha j
  · rfl

theorem pairR_onto (ρ : Reshape C C') (D : LdCode E P) (h : Function.Surjective ρ.fm) :
    Function.Surjective (ρ.pairR D).fm := fun V => by
  obtain ⟨a, ha⟩ := h fun j => V (.inr j)
  refine ⟨Sum.elim (fun j => V (.inl j)) a, funext fun j => ?_⟩
  rcases j with j | j
  · rfl
  · exact congrFun ha j

end Cb.Reshape

namespace Johnson.Top.H
open OnBytes.Slice Cb Johnson.Pack

section Tables
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (pos : Fin (2 ^ a) → Fin (2 ^ a'))

theorem tabSame_onto (e : C' = C) : Function.Surjective (tabSame C C' a a' n pos e).fm := by
  subst e
  exact fun V => ⟨V, rfl⟩

theorem tabNone_onto (h0 : n = 0) : Function.Surjective (tabNone C C' a a' n pos h0).fm :=
  fun V => ⟨fun j => absurd j.1.isLt (by omega), funext fun j => absurd j.1.isLt (by omega)⟩

theorem maskSame_onto (e : C' = C) : Function.Surjective (maskSame C C' a a' n e).fm := by
  subst e
  exact fun V => ⟨V, rfl⟩

end Tables

theorem tabVoid_onto {P P' : Type} (A : LdCode GE P') (D : LdCode GE P) (pos : P → P') (n : ℕ)
    (h0 : n = 0) : Function.Surjective (tabVoid A D pos n h0).fm :=
  fun V => ⟨fun j => absurd j.1.isLt (by omega), funext fun j => absurd j.1.isLt (by omega)⟩

theorem pairAt_onto {P P' : Type} (A B : LdCode GE P') (pos : P → P') :
    Function.Surjective (pairAt A B pos).fm := fun V => ⟨V, rfl⟩

section Port
variable (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

theorem mainAt_onto : Function.Surjective (mainAt cs sh s hM).fm := by
  unfold mainAt
  split
  · exact tabNone_onto _ _ _ _ _ _ _
  · exact tabSame_onto _ _ _ _ _ _ _

theorem maskAt_onto : Function.Surjective (maskAt cs sh s hZ).fm := by
  unfold maskAt
  split
  · exact tabVoid_onto _ _ _ _ _
  · exact maskSame_onto _ _ _ _ _ _

/-- **The view of a member of a shape of the programs carries forms onto.** -/
theorem membPort_onto : Function.Surjective (membPort cs sh em s oM oZ hM hZ).view.fm :=
  Reshape.comp_onto _ _
    (Reshape.comp_onto _ _ (Reshape.pairR_onto _ _ (maskAt_onto cs sh s hZ))
      (Reshape.pairL_onto _ _ (mainAt_onto cs sh s hM)))
    (pairAt_onto _ _ _)

end Port

/-- So for the group's data made of members whose views do. -/
theorem ofFn_onto {S : Sig GE} (s : Sg) (e : ℕ) (mem : S.O → Prop) [DecidablePred mem]
    (mb : ∀ o, mem o → MembAt (S.om o) s) (h : ∀ o k, Function.Surjective (mb o k).view.fm) :
    ∀ a, Function.Surjective ((Rows.ofFn s e mem mb).view a).fm := fun a => h a.1 a.2

end Johnson.Top.H
