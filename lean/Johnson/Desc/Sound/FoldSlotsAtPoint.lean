-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldSlotsAtPoint.lean: A MEMBER THAT IS NO TOY for the general rule of
Johnson/Desc/Sound/FoldSlots.lean (`Spec.knowB_of_lost_both`: the key's part once, a slot's own part
N times): THE LIBRARY's OWN SHARED POINT (`LdLinP.pt`, Cb/Ld/LdLin.lean), with its own relations,
its own key and ITS OWN NUMBER.

What is shown. The library proves the clause for a batch at the shared point by a joint count made
by hand (`LdLinP.linkPt`, Cb/Ld/LdLinBProofs.lean, over `knowB_peek` and `ldk_cnt_badSh`), at the
error `errPtB εf N` = εf · q^klo + N · ((v + klo) · q^(v + klo - 1)). Here THE SAME CLAUSE, TO THE
LETTER (the field `know` of `linkPt`: `linkPt_both` lays it there), comes out of the rule:
  the key: `P.k1`: the encoded index and its record: what the slots share;
  εK = εf · q^klo, towards `lostPtK`: the point is not bad for the fold of the one table (a function
    of the key): from the library's `FoldErr` and `cnt_fst`;
  εO = (v + klo) · q^(v + klo - 1), towards `lostPtO`: the point is not a root of THIS slot's
    difference (it reads the slot's own oracle message W): the library's `ldLin_cnt_pt`
    (Schwartz-Zippel for one instance);
  where both hold, a witness behind gives one in front: the library's `LdLinP.pt_back`.
`errPtB_is`: the library's number IS εK + N · εO (by unfolding). The three facts stand as lemmas of
their own (`lostPtK_doomed`, `lostPtO_doomed`, `pt_back_both`), for whoever carries them to a block
of the description (`PieceLostBoth`, Johnson/Desc/Sound/FoldSlotsCarry.lean).

So the rule's premises can be met by what is meant, at real errors, with a part that is paid once
and a part that is paid N times in one round.

Limits. The library's typed protocol, not a block of the description: no fold, no file, no bytes.
`FoldErr` is a premise, as in `linkPt`. Nothing new is proved of the protocol: the clause was a
theorem already.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldSlotsProofs
import Cb.Ld.LdLinBProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (N : ℕ)

open Classical in
/-- What the shared point is held against in one slot: (g, w') of the slot's instance; nothing where
the slot's oracle message does not decode. (The term of `linkPt`'s own proof.) -/
noncomputable def LdLinP.gwOf (a : P.X1 × P.E1.Str) : Option ((Y → E) × (P.D.Col → E)) :=
  if h : ∃ m, P.NW.DecTo a.1.2 a.2.2 m then some (P.g a.1.1.1, P.wv h.choose) else none

/-- THE KEY's PART: the point is not bad for the fold of the table. A function of the key. (Where
the table has more than εf bad points nothing is asked: `FoldErr` speaks of the tables with on0.) -/
def LdLinP.lostPtK (εf : ℕ) (k : (ι → P.Sy) × P.D.X.Rec) (τ : Tr [drawRound P.D.Pt]) : Prop :=
  cnt (P.D.X.Bad (P.tab k.1) k.2 P.e') ≤ εf → ¬ P.D.X.Bad (P.tab k.1) k.2 P.e' (drawn τ).1

/-- A SLOT's OWN PART: the point is not bad for the w' of this slot's instance. -/
def LdLinP.lostPtO (a : P.X1 × P.E1.Str) (τ : Tr [drawRound P.D.Pt]) : Prop :=
  ¬ ∃ U, P.D.X.dec (P.tab a.2.1.1) a.1.1.2 = some U ∧
    ∃ gw, P.gwOf a = some gw ∧ P.D.BadPt U gw.1 gw.2 (drawn τ)

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The library's number for the shared point is "the key's part, and N times a slot's own". -/
theorem LdLinP.errPtB_is (εf : ℕ) :
    ((P.errPtB εf N, ()) : ℕ × Unit) =
      Err.add (s := [drawRound P.D.Pt]) ((εf * Fintype.card E ^ P.D.klo, ()) : ℕ × Unit)
        (Err.times N (s := [drawRound P.D.Pt])
          (((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1), ()) : ℕ × Unit)) :=
  rfl

omit [Nonempty ι] [Fintype Y] in
/-- THE KEY's PART IS LOST AT εf · q^klo, at every key. -/
theorem LdLinP.lostPtK_doomed (εf : ℕ) (k : (ι → P.Sy) × P.D.X.Rec) :
    Doomed [drawRound P.D.Pt] ((εf * Fintype.card E ^ P.D.klo, ()) : ℕ × Unit)
      (P.lostPtK εf k) := by
  intro m
  show cnt (fun c : P.D.Pt => ¬ (cnt (P.D.X.Bad (P.tab k.1) k.2 P.e') ≤ εf →
    ¬ P.D.X.Bad (P.tab k.1) k.2 P.e' c.1)) ≤ εf * Fintype.card E ^ P.D.klo
  by_cases h : cnt (P.D.X.Bad (P.tab k.1) k.2 P.e') ≤ εf
  · refine le_trans (cnt_mono
      (Q := fun c : P.D.Pt => P.D.X.Bad (P.tab k.1) k.2 P.e' c.1) ?_) ?_
    · intro c hc
      by_contra hn
      exact hc fun _ => hn
    · rw [cnt_fst (D := Fin P.D.klo → E) (P.D.X.Bad (P.tab k.1) k.2 P.e'),
        Fintype.card_fun, Fintype.card_fin]
      exact Nat.mul_le_mul_right _ h
  · rw [cnt_false]
    · exact Nat.zero_le _
    · intro c hc
      exact hc fun h' => absurd h' h

omit [Nonempty ι] in
/-- A SLOT's OWN PART IS LOST AT (v + klo) · q^(v + klo - 1), at every statement. -/
theorem LdLinP.lostPtO_doomed (a : P.X1 × P.E1.Str) :
    Doomed [drawRound P.D.Pt]
      (((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1), ()) : ℕ × Unit)
      (P.lostPtO a) := by
  intro m
  show cnt (fun c : P.D.Pt => ¬ ¬ ∃ U, P.D.X.dec (P.tab a.2.1.1) a.1.1.2 = some U ∧
    ∃ gw, P.gwOf a = some gw ∧ P.D.BadPt U gw.1 gw.2 c) ≤
      (P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1)
  refine le_trans (cnt_mono fun c hc => not_not.mp hc) ?_
  refine cnt_exists_unique_le (fun _ _ hb hb' => Option.some.inj (hb.symm.trans hb'))
    fun U _ => ?_
  exact cnt_exists_unique_le (fun _ _ hb hb' => Option.some.inj (hb.symm.trans hb'))
    fun gw _ => ldLin_cnt_pt P.D U gw.1 gw.2

omit [Nonempty ι] in
/-- WHERE BOTH HOLD, A WITNESS BEHIND THE POINT GIVES ONE IN FRONT. -/
theorem LdLinP.pt_back_both (εf : ℕ) (hF : P.FoldErr on0 εf) (a : P.X1 × P.E1.Str)
    (τ : Tr [drawRound P.D.Pt]) (b : P.X2 × P.E1.Str) (w' : P.W2)
    (hk : P.lostPtK εf (P.k1 a) τ) (ho : P.lostPtO a τ) (hb : P.pt.red.out a τ = some b)
    (hw' : (P.j2 on0).cf.relR b w') : (P.j1 on0).cf.relR a w'.2 := by
  classical
  obtain rfl : _ = b := Option.some.inj ((ldk_peek_out P.vPt a τ).symm.trans hb)
  by_cases ha : (P.j1 on0).on a
  · refine Or.inl ?_
    rcases hw' with hw' | hoff
    · obtain ⟨hd, haa, hev, hn, hr, hdot⟩ := hw'
      refine ⟨hd, haa, P.pt_back a.1.1 (P.tab a.2.1.1) w'.2.2.2 _ (drawn τ) w'.1
        (fun h1 => ?_) hev hn hr hdot⟩
      rcases h1 with h1 | ⟨U, hU, _, gw, hgw, hb'⟩
      · exact hk (hF _ _ ha.2.1) h1
      · refine ho ⟨U, hU, gw, ?_, hb'⟩
        have hd' : P.NW.DecTo a.1.2 a.2.2 (P.NW.msgs w'.2.1) := hd
        have hex : ∃ m, P.NW.DecTo a.1.2 a.2.2 m := ⟨_, hd'⟩
        unfold LdLinP.gwOf
        rw [dif_pos hex, hex.choose_spec.unique hd']
        exact hgw
    · exact absurd ha hoff
  · exact Or.inr ha

omit [Nonempty ι] in
/-- **The library's clause for a batch at the shared point, out of the rule.** -/
theorem LdLinP.knowPt_both (εf : ℕ) (hF : P.FoldErr on0 εf) :
    P.pt.KnowB (shAnn _) N (SameKey P.k1) (fun _ => True) (P.j1 on0).cf.relR (P.j2 on0).cf.relR
      (fun _ _ w => w.2) ((P.errPtB εf N, ()) : ℕ × Unit) :=
  knowB_of_lost_both P.X1 P.X2 _ P.E1 P.E1 P.W1 P.W2 P.pt N P.k1 (P.lostPtK εf) P.lostPtO
    (fun _ => True) (P.j1 on0).cf.relR (P.j2 on0).cf.relR (fun _ _ w => w.2)
    ((εf * Fintype.card E ^ P.D.klo, ()) : ℕ × Unit)
    (((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1), ()) : ℕ × Unit)
    (fun a _ => P.lostPtK_doomed εf (P.k1 a)) (fun a _ => P.lostPtO_doomed a)
    (fun a τ b w' _ hk ho hb hw' => P.pt_back_both on0 εf hF a τ b w' hk ho hb hw')

omit [Nonempty ι] in
/-- The library's link at the shared point, with its clause out of the rule: the same type as
`LdLinP.linkPt`. ("One key goes to one key" is the library's own.) -/
theorem LdLinP.linkPt_both (εf : ℕ) (hF : P.FoldErr on0 εf) :
    ldk_LinkB P.pt (shAnn _) N P.k1 P.k2 (P.j1 on0).cf.relR (P.j2 on0).cf.relR
      (fun _ _ w => w.2) ((P.errPtB εf N, ()) : ℕ × Unit) :=
  ⟨P.knowPt_both on0 N εf hF, (P.linkPt on0 N εf hF).adm⟩

end
end Cb

#print axioms Cb.LdLinP.errPtB_is
#print axioms Cb.LdLinP.lostPtK_doomed
#print axioms Cb.LdLinP.lostPtO_doomed
#print axioms Cb.LdLinP.pt_back_both
#print axioms Cb.LdLinP.knowPt_both
#print axioms Cb.LdLinP.linkPt_both
