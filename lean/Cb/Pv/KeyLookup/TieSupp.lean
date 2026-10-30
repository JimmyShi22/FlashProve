-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieSupp.lean: whatever the verifier of the draw and the fused tie
(Cb/Pv/KeyLookup/TieM.lean) puts out, every form in the state is 0 outside a set G of entries, if
every place that the tie's record names lies in G and if the sumcheck's verifier hands its state on
(`Tie.LtForm`; the library's and the short one do). The draw and the tie together are called the
head.

The assembled lookup wants this of each of its sub-protocols (Cb/Pv/KeyLookup/AsmSupp.lean). It
imports no file of the program (OnBytes/Iop, OnBytes/Params, ...). Terms: lean/GLOSSARY.md.

Main names:
  TiePl.In L G       every place of the record lies in G: the hiding coefficients' (wAt), the one on
                     the roots' product (cZ), those on the powers and planes (cAt).
  `Tie.f_wAt`, `Tie.f_nx`, `Tie.f_slS`, `Tie.f_rowsAt`: the library's lemmas on its own tie
  (`tie_wAt`, `tie_cAt`, `tie_slS`, `tie_rowsAt`: Cb/Ld/LdLkpSuppProofs.lean), for the fused tie.
  `Tie.supp_at1`: the form that is c at one place of G is 0 outside G.
  `Tie.inv_of_passes`: what is handed on unchanged keeps every property.
  `Dat.suppX_back`: the state read back keeps the property.
  `head_supp`: LtForm, `L.In G` ⇒ `Inv (A.headK L SK n).R (fun _ => True) (A.SuppX G)`.
  `head_supp_lib`: at the library's sumcheck, under `L.In G` alone.
Limits: the conditions are `L.In G`, a shape (where the places are), and `Tie.LtForm`
(Cb/Pv/KeyLookup/TieForm.lean) on the sumcheck, which is a parameter. Nothing on an honest side;
nothing on relations.

-/
import Cb.Pv.KeyLookup.TieForm
import Cb.Pv.KeyLookup.AsmSupp
import Cb.Ld.LdLkpSuppProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Cb Cb.LdLkp Cb.LdLkp.Kn

variable {E : Type} [Field E] [Fintype E]

/-- Every place of the tie's record lies in G. -/
structure TiePl.In {J : Type} (L : TiePl E J) (G : J → Prop) : Prop where
  wAt : ∀ l i, G (L.wAt l i)
  cZ  : G L.cZ
  cAt : ∀ l b, G (L.cAt l b)

namespace Tie

section F
variable (D : TieF E) (G : D.J → Prop)

theorem f_wAt (hw : ∀ l i, G (D.wAt l i)) : ∀ l i, G ((D.lv l).toJ ((D.lv l).T.wAt i))
  | 0, i => hw 0 i
  | l + 1, i => hw (l + 1) i

theorem f_nx (hc : ∀ l b, G (D.cAt l b)) (l : ℕ) :
    G ((D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx)) := by
  rw [D.c_nx]
  exact hc l false

theorem f_slS (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l s, SuppIn (fun j => G ((D.lv l).toJ j)) ((D.lv l).T.slS s)
  | 0, _ => fun _ _ => rfl
  | l + 1, s => fun j hj => by
      show (D.TN l (D.lv l)).slS s j = 0
      unfold TieF.TN
      exact if_neg fun (e : j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx)) =>
        hj (show G j from e.symm ▸ f_nx D G hc l)

theorem f_rowsAt (hw : ∀ l i, G (D.wAt l i)) (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l s, RowsSupp G (D.rowsAt l s)
  | 0, _ => fun _ hr => absurd hr List.not_mem_nil
  | l + 1, s => fun r hr => by
      rcases List.mem_cons.1 hr with e | h
      · rw [e]
        exact supp_rowUof (D.lv l).T (D.emB l) (D.lv l).toJ s G (f_wAt D G hw l)
          (f_slS D G hc l s.st)
      · exact f_rowsAt hw hc l s.st r h

end F

omit [Fintype E] in
theorem supp_at1 {J : Type} [DecidableEq J] (G : J → Prop) (i : J) (c : E) (h : G i) :
    SuppIn G (at1 i c) :=
  fun j hj => if_neg fun (e : j = i) => hj (e.symm ▸ h)

theorem inv_of_passes {X₁ X₂ Rc : Type} {E₁ E₂ : ExtSpec} {R : IOR X₁ E₁ X₂ E₂} {r : X₁ → Rc}
    {r' : X₂ → Rc} (h : R.Passes r r') (P : Rc → Prop) :
    Inv R (fun x => P (r x)) fun x' => P (r' x') := fun x y τ x' hx hP => by
  show P (r' x')
  rw [h x y τ x' hx]
  exact hP

end Tie

/-- The state read back keeps the property. -/
theorem Dat.suppX_back (A : Dat E) (L : TiePl E A.J) (G : A.J → Prop) (hL : L.In G) (n : ℕ)
    (x : E × ((A.tie L).lv (n + 1)).T.St) (h : A.SuppX G (A.old L n x)) :
    A.SuppX G (A.back L n x) := by
  refine ⟨Tie.supp_at1 G _ _ hL.cZ, h.run, h.roots, fun j => ?_, h.top, h.cls, fun r hr => ?_⟩
  · by_cases hj : j < n + 1
    · have e : (A.back L n x).planes j =
          ⟨at1 (L.cAt j true) ((A.tie L).bT n x.2 j).1, ((A.tie L).bT n x.2 j).2⟩ := if_pos hj
      rw [e]
      exact Tie.supp_at1 G _ _ (hL.cAt j true)
    · have e : (A.back L n x).planes j = ⟨at1 (L.cAt n false) ((A.tie L).be n x.2), x.1⟩ :=
        if_neg hj
      rw [e]
      exact Tie.supp_at1 G _ _ (hL.cAt n false)
  · rcases List.mem_append.1 (show r ∈ (A.old L n x).rows ++ A.tieRows L n x from hr) with h1 | h1
    · exact h.rows r h1
    · exact Tie.f_rowsAt (A.tie L) G hL.wAt hL.cAt (n + 1) x.2 r (List.mem_reverse.1 h1)

variable {Ex : ExtSpec}

/-- Whatever the head's verifier puts out is 0 outside G. -/
theorem head_supp (A : Dat E) (L : TiePl E A.J) (SK : PscLtK E Ex) (n : ℕ) (G : A.J → Prop)
    (hF : Tie.LtForm (A.tie L) SK n) (hL : L.In G) :
    Inv (A.headK L SK n).R (fun _ => True) (A.SuppX G) := by
  have hd : Inv (A.drawK Ex).R (fun _ => True) (A.SuppX G) := by
    intro st y τ x' hx _
    rw [← Option.some.inj (show some (A.ini st (drawn τ)) = some x' from hx)]
    exact A.suppX_ini G st _
  have h1 := Tie.inv_of_passes (Tie.tie_passes (A.tie L) SK n hF) (A.SuppX G)
  have h2 : Inv (A.tieK L SK n).R (A.SuppX G) (A.SuppX G) :=
    (h1.pre (fun x : A.XS => some ((0 : E), x)) (ExtMap.id Ex) (P := A.SuppX G) fun _ _ e hP => by
      obtain rfl := Option.some.inj e
      exact hP).post (fun x => some (A.back L n x)) (ExtMap.id Ex) fun x _ e hQ => by
        obtain rfl := Option.some.inj e
        exact A.suppX_back L G hL n x hQ
  exact hd.seq h2

theorem head_supp_lib (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) (G : A.J → Prop)
    (hL : L.In G) : Inv (A.headK L (PscLtK.lib E Ex) n).R (fun _ => True) (A.SuppX G) :=
  head_supp A L _ n G (Tie.ltForm_lib (A.tie L) Ex n) hL

end Lk6

#print axioms Lk6.head_supp
#print axioms Lk6.head_supp_lib
