-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsSupp.lean: the forms that the parts' steps put out are 0 outside every set G of
entries that holds the places that they name and outside which the forms of the state that came in
are 0; and how many values their messages in the clear have.

Statements and proofs: the lines of this stretch in the bundles Bks.Supp
(Cb/Pv/KeyLookup/AsmSupp.lean) and Bks.Sents (Cb/Pv/KeyLookup/AsmErr.lean). It uses supp_pushJ and
supp_rowUof (Cb/Ld/LdLkpSuppProofs.lean). No honest side is named. q is the number of elements of E.

Main names:
  partsXK_supp: if every place of the stretch lies in G (∀ l i, G (wP l i); ∀ l b, G (cP l b)) and
    the
    letter's verifiers pass their state on (FormK), then Inv (A.partsXK wP cP SK).R (A.SuppX G)
    (A.SuppX G): whatever the verifier puts out from a state whose forms are 0 outside G is such a
    state.
  partsXK_supp_lib, partsXK_supp_short: at the sumcheck of Cb/Ld/LdPsc.lean and at SK₀: under the
    two
    conditions on places alone.
  partsXK_sents_lib: IsS q (A.partsXK wP cP (PscLtK.lib E Ex)) ((lamParts q A.toPub).map id): the
    messages in the clear have q^1, q^3, q^2 values a step.
  partsXK_sents_short: IsS q (A.partsXK wP cP (SK₀ E Ex)) ((lamParts q A.toPub).map LRow.short):
    q^1, q^2, q^2 values a step: five scalars.

Limits: nothing is said on whether the places are pairwise different.

-/
import Cb.Pv.KeyLookup.AsmSupp
import Cb.Pv.KeyLookup.AsmErr
import Cb.Pv.KeyLookup.PartsShort
import Cb.Ld.LdLkpSuppProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers

namespace Parts
section
variable {E : Type} [Field E] [Fintype E] (D : PartsP E) (G : D.J → Prop)

theorem s_wAt (hw : ∀ l i, G (D.wAt l i)) : ∀ l i, G ((D.lv l).toJ ((D.lv l).T.wAt i))
  | 0, i => hw 0 i
  | l + 1, i => hw (l + 1) i

theorem s_slS (hc : ∀ l b, G (D.cAt l b)) : ∀ (l : ℕ) (s : (D.lv l).T.St),
    SuppIn G (D.inc ((D.lv l).base s)) → SuppIn (fun j => G ((D.lv l).toJ j)) ((D.lv l).T.slS s)
  | 0, _, h => h
  | l + 1, _, _ => fun j hj => if_neg fun (e : j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx)) =>
      hj (by
        show G j
        rw [e, D.cAt_nx l]
        exact hc l true)

theorem s_rowsAt (hw : ∀ l i, G (D.wAt l i)) (hc : ∀ l b, G (D.cAt l b)) :
    ∀ (l : ℕ) (s : (D.lv l).T.St), SuppIn G (D.inc ((D.lv l).base s)) → RowsSupp G (D.rowsAt l s)
  | 0, _, _ => fun _ h => absurd h List.not_mem_nil
  | l + 1, o, h0 => fun r h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact supp_rowUof (D.lv l).T (D.emB l) (D.lv l).toJ o G (s_wAt D G hw l)
        (s_slS D G hc l o.st h0)
    · exact s_rowsAt hw hc l o.st h0 r h

theorem s_formAt (hc : ∀ l b, G (D.cAt l b)) (k : ℕ) (x : E × (D.lv k).T.St)
    (h0 : SuppIn G (D.inc ((D.lv k).base x.2))) (i : ℕ) : SuppIn G (D.formAt k x i) := by
  unfold PartsP.formAt
  by_cases h : i < k
  · rw [if_pos h]
    exact fun j hj => if_neg fun (e : j = D.cAt i false) => hj (e.symm ▸ hc i false)
  · rw [if_neg h]
    exact supp_pushJ _ _ G (s_slS D G hc k x.2 h0)

end

/-- k copies of a list. -/
def copies (k : ℕ) (l : List ℕ) : List ℕ := (List.range k).flatMap fun _ => l

theorem copies_succ (k : ℕ) (l : List ℕ) : copies (k + 1) l = copies k l ++ l := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp

theorem sent_id (q : ℕ) : ∀ k,
    ((lamSteps q k).map id).map (fun r => q ^ r.sent) = copies k [q ^ 1, q ^ 3, q ^ 2]
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.map_append, List.map_append, sent_id q k, copies_succ]
    rfl

theorem sent_short (q : ℕ) : ∀ k,
    ((lamSteps q k).map LRow.short).map (fun r => q ^ r.sent) = copies k [q ^ 1, q ^ 2, q ^ 2]
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.map_append, List.map_append, sent_short q k, copies_succ]
    rfl

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (D : PartsP E)

omit [Field E] in
theorem card_E : Nat.card E = Fintype.card E ^ 1 := by rw [pow_one, Nat.card_eq_fintype_card]

omit [Field E] in
theorem card_fin (n : ℕ) : Nat.card (Fin n → E) = Fintype.card E ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_A (l : ℕ) : Nat.card ((D.lv l).T.A → E) = Fintype.card E ^ 2 := by
  have h : Nat.card (Bool → E) = Fintype.card E ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]
  cases l <;> exact h

theorem shape_lib (l : ℕ) :
    (D.stepK (PscLtK.lib E Ex) l).R.shape =
      [pRound0 E, pRound (pDummy E 2), pRoundV E (D.lv l).T.A] := by
  cases l <;> rfl

theorem plain_lib (l : ℕ) :
    plainList (D.stepK (PscLtK.lib E Ex) l).R.shape =
      [Fintype.card E ^ 1, Fintype.card E ^ 3, Fintype.card E ^ 2] := by
  rw [shape_lib]
  show [Nat.card E, Nat.card (Fin 3 → E), Nat.card ((D.lv l).T.A → E)] = _
  rw [card_E, card_fin, card_A]

theorem plain_short (l : ℕ) :
    plainList (D.stepK (SK₀ E Ex) l).R.shape =
      [Fintype.card E ^ 1, Fintype.card E ^ 2, Fintype.card E ^ 2] := by
  rw [parts_shape_short]
  show [Nat.card E, Nat.card (Fin 2 → E), Nat.card ((D.lv l).T.A → E)] = _
  rw [card_E, card_fin, card_A]

theorem plain_after (SK : PscLtK E Ex) {X : Type} (b : BkK X (E × (D.lv 0).T.St) Ex) (s : List ℕ)
    (h : ∀ l, plainList (D.stepK SK l).R.shape = s) :
    ∀ k, plainList (D.afterK SK b k).R.shape = plainList b.R.shape ++ copies k s
  | 0 => (List.append_nil _).symm
  | k + 1 => by
    show plainList ((D.afterK SK b k).R.shape ++ (D.stepK SK k).R.shape) = _
    have e : plainList ((D.afterK SK b k).R.shape ++ (D.stepK SK k).R.shape) =
        plainList (D.afterK SK b k).R.shape ++ plainList (D.stepK SK k).R.shape :=
      List.map_append
    rw [e, plain_after SK b s h k, h k, copies_succ, List.append_assoc]

end
end Parts

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)

/-- The state handed back keeps the property. -/
theorem Dat.partsBack_supp (G : A.J → Prop) (hw : ∀ l i, G (wP l i)) (hc : ∀ l b, G (cP l b))
    (y : E × ((A.partsD wP cP).lv (A.partsD wP cP).n).T.St) (h : A.SuppX G (A.partsOld wP cP y)) :
    A.SuppX G (A.partsBack wP cP y) := by
  refine ⟨h.all, h.run, fun i => ?_, h.planes, h.top, h.cls, fun r hr => ?_⟩
  · exact Parts.s_formAt (A.partsD wP cP) G hc _ y h.all i
  · rcases List.mem_append.1
      (show r ∈ (A.partsOld wP cP y).rows ++ A.partsRows wP cP y from hr) with h1 | h1
    · exact h.rows r h1
    · exact Parts.s_rowsAt (A.partsD wP cP) G hw hc _ y.2 h.all r (List.mem_reverse.1 h1)

/-- Whatever the stretch's verifier puts out is 0 outside G. -/
theorem partsXK_supp (SK : PscLtK E Ex) (G : A.J → Prop)
    (hF : (A.partsD wP cP).FormK SK (A.m - 1)) (hw : ∀ l i, G (wP l i)) (hc : ∀ l b, G (cP l b)) :
    Inv (A.partsXK wP cP SK).R (A.SuppX G) (A.SuppX G) := by
  have hp := partsK_passes (A.partsD wP cP) SK (mapK Ex (A.partsIn wP cP)) (fun x : A.XS => x)
    (mapK_passes _ _ _ fun _ => rfl) (A.partsD wP cP).n hF
  have h1 : Inv ((A.partsD wP cP).afterK SK (mapK Ex (A.partsIn wP cP)) (A.partsD wP cP).n).R
      (A.SuppX G) (fun y => A.SuppX G (A.partsOld wP cP y)) := fun x y τ x' hx hP => by
    have e : ((A.partsD wP cP).lv (A.partsD wP cP).n).base x'.2 = x := hp x y τ x' hx
    show A.SuppX G (((A.partsD wP cP).lv (A.partsD wP cP).n).base x'.2)
    rw [e]
    exact hP
  exact h1.post (fun y => some (A.partsBack wP cP y)) (ExtMap.id Ex) fun y _ e hQ => by
    obtain rfl := Option.some.inj e
    exact A.partsBack_supp wP cP G hw hc y hQ

theorem partsXK_supp_lib (G : A.J → Prop) (hw : ∀ l i, G (wP l i)) (hc : ∀ l b, G (cP l b)) :
    Inv (A.partsXK wP cP (PscLtK.lib E Ex)).R (A.SuppX G) (A.SuppX G) :=
  partsXK_supp A wP cP _ G (partsK_form_lib (A.partsD wP cP) _) hw hc

theorem partsXK_supp_short (G : A.J → Prop) (hw : ∀ l i, G (wP l i)) (hc : ∀ l b, G (cP l b)) :
    Inv (A.partsXK wP cP (SK₀ E Ex)).R (A.SuppX G) (A.SuppX G) :=
  partsXK_supp A wP cP _ G (partsK_form_short (A.partsD wP cP) _) hw hc

theorem partsXK_sents_lib :
    IsS (Fintype.card E) (A.partsXK wP cP (PscLtK.lib E Ex))
      ((lamParts (Fintype.card E) A.toPub).map id) := by
  show plainList _ = _
  rw [lamParts_is, Parts.sent_id]
  exact Parts.plain_after (A.partsD wP cP) _ (mapK Ex (A.partsIn wP cP)) _
    (Parts.plain_lib (A.partsD wP cP)) (A.m - 1)

theorem partsXK_sents_short :
    IsS (Fintype.card E) (A.partsXK wP cP (SK₀ E Ex))
      ((lamParts (Fintype.card E) A.toPub).map LRow.short) := by
  show plainList _ = _
  rw [lamParts_is, Parts.sent_short]
  exact Parts.plain_after (A.partsD wP cP) _ (mapK Ex (A.partsIn wP cP)) _
    (Parts.plain_short (A.partsD wP cP)) (A.m - 1)

end
end Lk6

#print axioms Lk6.partsXK_supp
#print axioms Lk6.partsXK_supp_lib
#print axioms Lk6.partsXK_supp_short
#print axioms Lk6.partsXK_sents_lib
#print axioms Lk6.partsXK_sents_short
