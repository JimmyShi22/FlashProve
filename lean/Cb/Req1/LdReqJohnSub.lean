-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqJohnSub.lean: under the hypotheses of its statements, a member of the list of a word
over a subfield is over the subfield; so an oracle message over a subfield needs a sample that is a
zero-evader on vectors over the subfield only.

Definitions, statements and proofs. Generic: any field E (finite in `o.JohnF` and the three
statements on it), any subfield K (a field K with an algebra structure on E), any code read under a
transformation. No assumed theorem.
C: `LdCode E P` (Cb/Ld/LdRel.lean); o: `OMsg E` (Cb/Ld/LdSig.lean).

Why: An oracle message all of whose rows are over a subfield K has, in a write-up of ours
(lean/CREDITS.md), pad entries in K, as many for an answer as E has dimension over K. Its sample is
then NO zero-evader on all vectors over E (Cb/Ld/LdSig.lean's head: why "Evades" and not Sample.OK);
it is one on vectors over K (Cb/Gen/OodDecPad.lean: ood_okOn_pad). That is `Spec.ood_okOn_pad`
(stated in Cb/Gen/OodDecPad.lean, proved in Cb/Gen/OodDecPadProofs.lean), under its hypotheses. What
closes the gap is a fact on codes, which Cb/Ld/LdSig.lean declares and does not prove. Here it is
proved.

Main names:
  `C.GenIn K`: the generator is over K: every entry of every row of "the transformation after the
    encoder" (`C.row x α i`, Cb/Ld/LdRel.lean) lies in K.
  `C.LongIn K f`: the native word f, read under the transformation, is over K: every coordinate of
    every long symbol lies in K.
  `Spec.ld_subfield_member`: laws, distance d as read, e below d, the generator over K, f over K as
    read, the encoding of (m, r) within e of f ⇒ all entries of m and of r lie in K. The way: a
    K-linear map ψ of E into itself that vanishes exactly on K (w minus a K-linear retraction of w).
    Applied entry by entry it commutes with a generator over K. Where the encoding agrees with f its
    image vanishes: so the encoding of (ψ m, ψ r) is other than 0 at no more than e long positions,
    fewer than d: it is the encoding of 0.
  `o.JohnF K d L`: an oracle message over K, below the Johnson radius: laws, distance d as read,
    `InJohnson |P| d e`, the bound is `listMax |P| d e`; the generator over K; the format is over K
    (every word as sent, read under the transformation, is over K); the sample is a zero-evader on
    vectors over K (`Sample.OKOn`).
  `Spec.ld_subfield_evades`: `o.JohnF K d L` ⇒ `o.Evades`.
  `Spec.ld_subfield_list`: `o.JohnF K d L` ⇒ `o.ListLE L` (the Johnson bound; the field plays no
    part).
  `Spec.ld_subfield_self`: at K = E the three clauses on K say: nothing, nothing, "the sample is a
    zero-evader" (`Sample.OK`).
All clauses of `o.JohnF` are on data: a code, a format, a sample's public coefficients.

Limits: nobody above uses this file (no file of this library but Cb/Req1/LdReqJohnSubNo.lean imports
it). The records of the reference request below the Johnson radius (Cb/Req1/LdReqJohn.lean) do not
have the case `o.JohnF`: they ask standard layouts, under which a format over a proper subfield
leaves room for pad entries alone (Cb/Req1/LdReqJohnSubNo.lean: `Spec.ld_subfield_noData`, under its
hypotheses). Who would use this file: a statement that ties a run of the programs to words over the
base field ("the members of the list are over the base field"); a standard sender with a field for
each member.
This file does not say that the decoder's (`OMsg.dec`, Cb/Ld/LdSig.lean) minimum over pairs over E
and the minimum over pairs over K have the same value (they have the same members within the radius:
that is the lemma). It says nothing on radii at or beyond the distance. It does not say that a
generator of a given code is over K (for codes of Code/Iface.lean over K read over E it is so by
construction; no lemma here). It says nothing on privacy of the sample under pads in K
(Cb/Gen/OodDecPad.lean). One pads' field for a whole family is what the standard sender's layout has
(Cb/Ld/LdSendStdL.lean): this file does not change that.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdRelProofsCode
import Cb.Ld.LdRelJohnsonProofs
import Cb.Ld.LdSigProofs
import Cb.Ld.LdTowerJohn
import Code.Derived

set_option autoImplicit false

namespace Cb
open Prob Cb.Ood

section
variable (K : Type) {E P : Type} [Field K] [Field E] [Algebra K E]

/-- The generator of "the transformation after the encoder" is over K. -/
def LdCode.GenIn (C : LdCode E P) : Prop := ∀ x α i, C.row x α i ∈ Set.range (algebraMap K E)

/-- A native word is over K as read. -/
def LdCode.LongIn (C : LdCode E P) (f : C.Word) : Prop :=
  ∀ x α, C.T f x α ∈ Set.range (algebraMap K E)

end

/-- An oracle message over K, below the Johnson radius. -/
structure OMsg.JohnF (K : Type) {E : Type} [Field K] [Field E] [Fintype E] [Algebra K E]
    (o : OMsg E) (d L : ℕ) : Prop where
  laws : o.C.Laws
  dist : o.C.Dist d
  inJ  : InJohnson (Fintype.card o.P) d o.e
  isL  : L = listMax (Fintype.card o.P) d o.e
  gen  : o.C.GenIn K
  fmt  : ∀ f : o.Str, o.C.LongIn K (o.upW f)
  smp  : o.Z.OKOn fun v => ∀ j, v j ∈ Set.range (algebraMap K E)

namespace Spec

/-- The lemma. -/
def ld_subfield_member : Prop :=
  ∀ (K E P : Type) [Field K] [Field E] [Algebra K E] [Finite P] (C : LdCode E P) (d e : ℕ), C.Laws →
    C.Dist d → e < d → C.GenIn K →
    ∀ (f : C.Word) (m : C.J → E) (r : C.Q → E), C.LongIn K f → C.Near e f (C.enc m r) →
      (∀ j, m j ∈ Set.range (algebraMap K E)) ∧ ∀ q, r q ∈ Set.range (algebraMap K E)

def ld_subfield_evades : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E] (o : OMsg E) (d L : ℕ),
    o.JohnF K d L → o.Evades

def ld_subfield_list : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [Fintype E] [Algebra K E] (o : OMsg E) (d L : ℕ),
    o.JohnF K d L → o.ListLE L

/-- At K = E. -/
def ld_subfield_self : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (o : OMsg E) (d L : ℕ),
    o.JohnF E d L ↔
    o.C.Laws ∧ o.C.Dist d ∧ InJohnson (Fintype.card o.P) d o.e ∧
    L = listMax (Fintype.card o.P) d o.e ∧ o.Z.OK

end Spec

theorem ld_subfield_member : Spec.ld_subfield_member := by
  intro K E P _ _ _ _ C d e hL hD hlt hG f m r hf hN
  obtain ⟨φ, hφ⟩ := Code.exists_form_algebraMap K E
  obtain ⟨ψ, hψ⟩ : ∃ ψ : E →ₗ[K] E, ∀ w, ψ w = w - algebraMap K E (φ w) :=
    ⟨LinearMap.id - (Algebra.linearMap K E).comp φ, fun _ => rfl⟩
  have hψ0 : ∀ c : K, ψ (algebraMap K E c) = 0 := fun c => by rw [hψ, hφ, sub_self]
  have hψm : ∀ (c : K) (w : E), ψ (algebraMap K E c * w) = algebraMap K E c * ψ w := fun c w => by
    rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
  have key : ∀ x α,
      C.T (C.enc (fun j => ψ (m j)) (fun q => ψ (r q))) x α = ψ (C.T (C.enc m r) x α) := by
    intro x α
    rw [ld_row_spec E P C hL, ld_row_spec E P C hL, map_add, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      obtain ⟨c, hc⟩ := hG x α (.inl j)
      rw [← hc, hψm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      obtain ⟨c, hc⟩ := hG x α (.inr q)
      rw [← hc, hψm]
  have hz : (fun j => ψ (m j)) = 0 ∧ (fun q => ψ (r q)) = 0 := by
    by_contra hne
    have h1 := hD _ _ hne
    have h2 : cnt (fun x => C.T (C.enc (fun j => ψ (m j)) (fun q => ψ (r q))) x ≠ 0) ≤
        cnt (fun x => C.T f x ≠ C.T (C.enc m r) x) := by
      refine cnt_mono fun x hx hxe => hx ?_
      funext α
      obtain ⟨c, hc⟩ := hf x α
      have h3 : C.T (C.enc m r) x α = algebraMap K E c := by rw [← hxe, hc]
      calc
        C.T (C.enc (fun j => ψ (m j)) (fun q => ψ (r q))) x α = ψ (C.T (C.enc m r) x α) := key x α
        _ = 0 := by rw [h3, hψ0]
    exact absurd (lt_of_le_of_lt (le_trans h1 (le_trans h2 hN)) hlt) (lt_irrefl _)
  have back : ∀ w : E, ψ w = 0 → w ∈ Set.range (algebraMap K E) := fun w hw =>
    ⟨φ w, (sub_eq_zero.1 ((hψ w).symm.trans hw)).symm⟩
  exact ⟨fun j => back _ (congrFun hz.1 j), fun q => back _ (congrFun hz.2 q)⟩

theorem ld_subfield_evades : Spec.ld_subfield_evades := by
  intro K E _ _ _ _ o d L h
  refine sig_evades_of_okOn E o _ h.smp fun f m m' hm hm' j => ?_
  obtain ⟨r, hr⟩ := hm
  obtain ⟨r', hr'⟩ := hm'
  have hlt := ldJohn_lt _ _ _ h.inJ
  obtain ⟨a, ha⟩ :=
    (ld_subfield_member K E o.P o.C d o.e h.laws h.dist hlt h.gen (o.upW f) m r (h.fmt f) hr).1 j
  obtain ⟨b, hb⟩ :=
    (ld_subfield_member K E o.P o.C d o.e h.laws h.dist hlt h.gen (o.upW f) m' r' (h.fmt f) hr').1 j
  exact ⟨a - b, by rw [map_sub, ha, hb]; rfl⟩

theorem ld_subfield_list : Spec.ld_subfield_list := by
  intro K E _ _ _ _ o d L h
  rw [h.isL]
  exact sig_list_of_code E o _ (ld_list_johnson E o.P o.C d o.e h.laws h.dist h.inJ)

theorem ld_subfield_self : Spec.ld_subfield_self := by
  intro E _ _ o d L
  constructor
  · intro h
    exact ⟨h.laws, h.dist, h.inJ, h.isL, fun v hv => h.smp v (fun j => ⟨v j, rfl⟩) hv⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun x α i => ⟨_, rfl⟩, fun f x α => ⟨_, rfl⟩, fun v _ hv => h5 v hv⟩

end Cb
