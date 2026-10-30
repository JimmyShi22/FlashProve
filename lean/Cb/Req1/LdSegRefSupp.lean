-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefSupp.lean: the rows at the end of a segment's body have public supports: whatever
the state, they read the named places only.

Book-keeping on linear claims (rows): the coefficient vectors of the claims that are left at the
end of a segment's body vanish outside a fixed set of coordinates, whatever the state.
A definition, statements and proofs. Rules of the framework only; nothing of a text is rendered
here.
The rows are the linear forms `G.sl b` of `G : LdGaP` (Cb/Req1/LdSegRefRows.lean) on the entries of
all messages; their coefficients are functions of a state x : `G.Sx`.

Why: a closing asks of the rows, at all states: they vanish outside the group; they do not read the
mask entry of a split; they do not read the own entries of a later masked block. The state of a row
holds data that a malicious prover's transcript is free to shape: the lookup's mask form, the
coefficients of its recorded rows; and weights that are functions of the state.
A condition "at all states" on free coefficients could not be met. Here it can: in every form of
`G.sl` the state supplies coefficients only, laid at places by fixed maps.

Main names:
  `G.Named n`: n is one of the named places: of the packed matrix, the reads, the digits; of those
    mask entries at which some claim's mask form is not 0 at some state (the mask forms of the
    claims are computed from the state: a name that no claim's form ever reads does not count, so
    an entry that stands among the names but belongs to another block, a mask of the rows on the
    encoded index say, need not lie in the segment's group); of the entries that the lookup's rows
    and mask form read (these coefficients are free data of the state: every name counts).
  `Spec.ldSegRef_placed0`: coefficients laid at places (`placed`, Cb/Ld/LdRng.lean) give 0 at every
    coordinate that is no place.
  `Spec.ldSegRef_placed0'`: and at every coordinate at which only coefficients 0 are laid.
  `Spec.ldSegRef_supp`: G.sl b x n = 0 for every name b of a row, every state x and every n that is
    not named. No hypothesis beside the premises that are written out and whatever the arguments
    hold as proofs.
  `Spec.ldSegRef_supp_grp`: if all named places lie in members of a group, the rows vanish outside
    the group, at all states.
  `Spec.ldSegRef_supp_not`: an entry that is not named is read by no row, at all states.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

/-- The named places. -/
def LdGaP.Named {E Kc : Type} [Field E] {E₀ : ExtSpec} {Wp : Type}
    (G : LdGaP E Kc E₀ Wp) (n : G.Q.T.Ent) : Prop :=
  (∃ i c, G.pkAt i c = n) ∨ (∃ k c, G.rdAt k c = n) ∨
  (∃ r u, G.Q.lo r u = n) ∨ (∃ r u, G.Q.hi r u = n) ∨
  (∃ j, G.jAt j = n ∧ ∃ st c, G.Q.D.cl.ms st c j ≠ 0) ∨ ∃ i, G.nAt i = n

namespace Spec

def ldSegRef_placed0 : Prop :=
  ∀ (I J E : Type) [Fintype I] [DecidableEq J] [AddCommMonoid E] (at' : I → J) (a : I → E) (n : J),
    (∀ x, at' x ≠ n) → placed at' a n = 0

def ldSegRef_placed0' : Prop :=
  ∀ (I J E : Type) [Fintype I] [DecidableEq J] [AddCommMonoid E] (at' : I → J) (a : I → E) (n : J),
    (∀ x, at' x = n → a x = 0) → placed at' a n = 0

/-- Public supports. -/
def ldSegRef_supp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (G : LdGaP E Kc E₀ Wp) (b : G.B)
      (x : G.Sx) (n : G.Q.T.Ent),
    ¬ G.Named n → G.sl b x n = 0

def ldSegRef_supp_grp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (G : LdGaP E Kc E₀ Wp) (grp : Grp G.Q.T),
    (∀ n, G.Named n → grp.mem n.1) → ∀ b st (n : G.Q.T.Ent), ¬ grp.mem n.1 → G.sl b st n = 0

def ldSegRef_supp_not : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] (G : LdGaP E Kc E₀ Wp) (κ : G.Q.T.Ent),
    ¬ G.Named κ → ∀ b st, G.sl b st κ = 0

end Spec

theorem ldSegRef_placed0 : Spec.ldSegRef_placed0 := fun _ _ _ _ _ _ _ _ _ h =>
  Finset.sum_eq_zero fun x _ => if_neg (h x)

theorem ldSegRef_placed0' :
    Spec.ldSegRef_placed0' := fun _ _ _ _ _ _ at' _ n h => Finset.sum_eq_zero fun x _ => by
  by_cases e : at' x = n
  · rw [if_pos e, h x e]
  · rw [if_neg e]

theorem ldSegRef_supp : Spec.ldSegRef_supp := by
  intro E Kc E₀ Wp _ G b x n hn
  have p0 : ∀ {I : Type} [Fintype I] (at' : I → G.Q.T.Ent) (a : I → E),
      (∀ i, at' i ≠ n) → placed at' a n = 0 :=
    fun {I} _ at' a h => ldSegRef_placed0 I _ E at' a n h
  have hpk : ∀ i c, G.pkAt i c ≠ n := fun i c e => hn (Or.inl ⟨i, c, e⟩)
  have hrd : ∀ k c, G.rdAt k c ≠ n := fun k c e => hn (Or.inr (Or.inl ⟨k, c, e⟩))
  have hlo : ∀ r u, G.Q.lo r u ≠ n := fun r u e => hn (Or.inr (Or.inr (Or.inl ⟨r, u, e⟩)))
  have hhi : ∀ r u, G.Q.hi r u ≠ n := fun r u e => hn (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, u, e⟩))))
  have hj : ∀ j, G.jAt j = n → ∀ st c, G.Q.D.cl.ms st c j = 0 := fun j e st c => by
    by_contra hne
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, e, st, c, hne⟩)))))
  have hN : ∀ i, G.nAt i ≠ n := fun i e => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, e⟩)))))
  rcases b with ⟨i | k, u⟩ | j | ⟨⟩ | i
  · show placed (G.pkAt i) _ n - placed (fun k : Fin G.Q.D.p.P => G.Q.lo (i, k) u) _ n -
        _ * placed (fun k : Fin G.Q.D.p.P => G.Q.hi (i, k) u) _ n = 0
    rw [p0 _ _ (hpk i), p0 _ _ (fun k => hlo _ u), p0 _ _ (fun k => hhi _ u)]
    simp
  · show placed (G.rdAt k) _ n - placed (fun r => G.Q.lo r u) _ n -
        _ * placed (fun r => G.Q.hi r u) _ n = 0
    rw [p0 _ _ (hrd k), p0 _ _ (fun r => hlo r u), p0 _ _ (fun r => hhi r u)]
    simp
  · show placed (fun kc : G.Q.D.p.Rd × G.Q.D.p.C => G.rdAt kc.1 kc.2) _ n + placed G.jAt _ n = 0
    rw [p0 _ _ (fun kc => hrd _ _),
      ldSegRef_placed0' _ _ E G.jAt _ n fun x e => hj x e _ _, add_zero]
  · show placed (fun ru : G.Q.D.p.Row × G.Q.D.p.U => G.Q.lo ru.1 ru.2) _ n +
        placed (fun ru : G.Q.D.p.Row × G.Q.D.p.U => G.Q.hi ru.1 ru.2) _ n + placed G.nAt _ n = 0
    rw [p0 _ _ (fun ru => hlo _ _), p0 _ _ (fun ru => hhi _ _), p0 _ _ hN]
    simp
  · show placed G.nAt _ n = 0
    exact p0 _ _ hN

theorem ldSegRef_supp_grp : Spec.ldSegRef_supp_grp := fun E Kc _ _ _ G _ h b st n hn =>
  ldSegRef_supp E Kc _ _ G b st n fun hN => hn (h n hN)

theorem ldSegRef_supp_not : Spec.ldSegRef_supp_not := fun E Kc _ _ _ G κ h b st =>
  ldSegRef_supp E Kc _ _ G b st κ h

end Cb
