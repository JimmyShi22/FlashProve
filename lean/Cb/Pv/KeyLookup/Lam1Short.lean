-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Lam1Short.lean: THE LOOKUP AT THE SHORT SUMCHECK: ONE CONSTANT, `A.lamS P Ex` :=
`A.lam1 P (SK₀ E Ex)`; and of that one constant: knowledge soundness, its list of
errors and numbers of values, its form, the support of what it puts out.

It imports the library's side alone (no file of the port): Cb/Pv/KeyLookup/Lam1.lean, the bundles
(AsmErr, AsmForm, AsmSupp) and the stretches' lines at
the short sumcheck (TieShort, TieSent; PartsShort, PartsSupp; LevShort, LevSent; CloseShort,
CloseSent). `SK₀`: Cb/Pv/KeyLookup/Short0.lean: the short sumcheck (one coefficient of each round's
polynomial is not sent: the power 0), as a value of the letter.

For every field E, data A, places P, oracles Ex; q := the number of elements of E:
  `lamS_know`     UNDER `A.toPub.Adm p` (p the characteristic of E; conditions on public numbers and
                  shapes) AND NOTHING ELSE: `Know` from `A.jtIn R0 msg Mu` («every key of every part
                  is a row of the
                  table») to `A.jtOut R0 msg` («for each part the extension of its keys at its
                  point, and its mask form, give its target; and all rows hold»), beside EVERY
                  riding joint R0, for
                  every Mu. No premise on the letter is left; none reads a witness or names an
                  honest prover.
  `lamS_isL`      under four clauses of `Adm`: its errors (`Err.toList`) and numbers of values
                  (`Shape.chalList`) are the columns c and n of `Lam q A.toPub`.
  `lamS_isS`      under the same four: round by round the prover's message in the clear has q ^ sent
                  values, `sent` the list's column IN ITS SHORT FORM (`LRow.short`): the scalars
                  that the
                  port's plan counts. (The reader `plainList` is no reader of the library's:
                  Cb/Pv/KeyLookup/AsmErr.lean.)
  `lamS_passes`, `lamS_copies`   no premise: the caller's state is handed on; the oracles are only
                    copied.
  `Pl.In P G`     every place that P names, and every cell of a live plane, lies in G.
  `lamS_supp`     under `P.In G`: whatever its verifier puts out has rows and mask forms that are 0
                  outside G.
Not claimed: an honest side; that the places of P are apart.

-/
import Cb.Pv.KeyLookup.Lam1
import Cb.Pv.KeyLookup.AsmErr
import Cb.Pv.KeyLookup.AsmForm
import Cb.Pv.KeyLookup.AsmSupp
import Cb.Pv.KeyLookup.TieShort
import Cb.Pv.KeyLookup.PartsShort
import Cb.Pv.KeyLookup.PartsSupp
import Cb.Pv.KeyLookup.LevShort
import Cb.Pv.KeyLookup.CloseShort
import Cb.Pv.KeyLookup.TieSent
import Cb.Pv.KeyLookup.LevSent
import Cb.Pv.KeyLookup.CloseSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

variable {E : Type} [Field E] [Fintype E]

/-- THE LOOKUP, at the short sumcheck. -/
noncomputable def Dat.lamS (A : Dat E) (P : Pl A) (Ex : ExtSpec) : BkK A.St A.Out Ex := A.lam1 P
    (SK₀ E Ex)

theorem bks_knows_short (p : ℕ) [CharP E p] (A : Dat E) (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hA : A.toPub.Adm p) : (A.bks P (SK₀ E Ex)).Knows R0 msg Mu :=
  have four := A.four_know_short P.cl Ex hA.room Kc M Wp R0 msg Mu
  { head := head_know_short p A P.tie Ex Kc M Wp R0 msg Mu (A.pl - 2) (Nat.sub_add_cancel hA.planes)
      hA
    parts := partsXK_short A P.wP P.cP M Wp Kc R0 msg Mu hA.some
    join := four.1
    keys := A.keys_know_short P.lev Kc M Wp R0 msg Mu hA.some fun i hi => (hA.bits i hi).1
    table := A.table_know_short P.lev Kc M Wp R0 msg Mu hA.tabs
    clo := four.2.1
    zero := four.2.2.1
    bits := four.2.2.2 }

/-- THE LOOKUP IS KNOWLEDGE SOUND. -/
theorem lamS_know (p : ℕ) [CharP E p] (A : Dat E) (P : Pl A) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hA : A.toPub.Adm p) : (A.lamS P Ex).Know (A.jtIn R0 msg Mu) (A.jtOut R0 msg) :=
  (A.bks P (SK₀ E Ex)).lam1_know R0 msg Mu (bks_knows_short p A P Ex Kc M Wp R0 msg Mu hA)

theorem bks_lists_short (A : Dat E) (P : Pl A) (Ex : ExtSpec) (hp : 2 ≤ A.pl) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i) (hd : 1 ≤ A.d) : (A.bks P (SK₀ E Ex)).Lists (Fintype.card E) where
  head  := head_isL_short A P.tie Ex (A.pl - 2) (Nat.sub_add_cancel hp)
  parts := ⟨partsXK_errs_short A P.wP P.cP, partsXK_vals_short A P.wP P.cP⟩
  join  := A.join_lam Ex
  keys  := A.keys_isL_short P.lev hm hv
  table := A.table_isL_short P.lev hd
  clo   := A.clo_lam_short P.cl Ex
  zero  := A.zero_lam Ex
  bits  := A.bits_lam_short P.cl Ex

/-- ITS ERRORS AND NUMBERS OF VALUES ARE THE LIST. -/
theorem lamS_isL (A : Dat E) (P : Pl A) (Ex : ExtSpec) (hp : 2 ≤ A.pl) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i) (hd : 1 ≤ A.d) : IsL (A.lamS P Ex) (Lam (Fintype.card E) A.toPub) :=
  (A.bks P (SK₀ E Ex)).lam1_isL _ (bks_lists_short A P Ex hp hm hv hd)

/-- The same under `Adm`. -/
theorem lamS_isL_adm (p : ℕ) (A : Dat E) (P : Pl A) (Ex : ExtSpec) (hA : A.toPub.Adm p) :
    IsL (A.lamS P Ex) (Lam (Fintype.card E) A.toPub) :=
  lamS_isL A P Ex hA.planes hA.some (fun i hi => (hA.bits i hi).1) hA.tabs

theorem bks_sents_short (A : Dat E) (P : Pl A) (Ex : ExtSpec) (hp : 2 ≤ A.pl) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i) (hd : 1 ≤ A.d) :
    (A.bks P (SK₀ E Ex)).Sents (Fintype.card E) LRow.short where
  head  := head_isS_short A P.tie Ex (A.pl - 2) (Nat.sub_add_cancel hp)
  parts := partsXK_sents_short A P.wP P.cP
  join  := A.join_isS Ex LRow.short fun _ _ => rfl
  keys  := A.keys_isS_short P.lev hm hv
  table := A.table_isS_short P.lev hd
  clo   := A.clo_isS_short P.cl Ex
  zero  := A.zero_isS Ex LRow.short fun _ _ => rfl
  bits  := A.bits_isS_short P.cl Ex

/-- ITS MESSAGES IN THE CLEAR ARE THE LIST's SCALARS, IN SHORT FORM. -/
theorem lamS_isS (A : Dat E) (P : Pl A) (Ex : ExtSpec) (hp : 2 ≤ A.pl) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i) (hd : 1 ≤ A.d) :
    IsS (Fintype.card E) (A.lamS P Ex) ((Lam (Fintype.card E) A.toPub).map LRow.short) :=
  (A.bks P (SK₀ E Ex)).lam1_isS _ _ (bks_sents_short A P Ex hp hm hv hd)

theorem bks_form_short (A : Dat E) (P : Pl A) (Ex : ExtSpec) : (A.bks P (SK₀ E Ex)).Form where
  head  := head_form_short A P.tie Ex (A.pl - 2)
  parts := partsXK_form_short A P.wP P.cP
  join  := A.join_form Ex
  keys  := A.keys_form_short P.lev
  table := A.table_form_short P.lev
  clo   := A.close_form_short P.cl Ex
  zero  := A.zero_form Ex
  bits  := A.bits_form_short P.cl Ex

theorem lamS_passes (A : Dat E) (P : Pl A) (Ex : ExtSpec) : (A.lamS P Ex).R.Passes id (fun o => o.1)
    :=
  (A.bks P (SK₀ E Ex)).lam1_passes (bks_form_short A P Ex)

theorem lamS_copies (A : Dat E) (P : Pl A) (Ex : ExtSpec) : (A.lamS P Ex).R.OnlyCopies :=
  (A.bks P (SK₀ E Ex)).lam1_copies (bks_form_short A P Ex)

/-- Every place that P names, and every cell of a live plane, lies in G. -/
structure Pl.In {A : Dat E} (P : Pl A) (G : A.J → Prop) : Prop where
  cells : ∀ u j, j < A.pl → G (A.bAt u j)
  tie : P.tie.In G
  wP  : ∀ l i, G (P.wP l i)
  cP  : ∀ l b, G (P.cP l b)
  lev : P.lev.In G
  cl  : P.cl.In G

theorem bks_supp_short (A : Dat E) (P : Pl A) (Ex : ExtSpec) (G : A.J → Prop) (h : P.In G) :
    (A.bks P (SK₀ E Ex)).Supp G where
  head  := head_supp_short A P.tie Ex (A.pl - 2) G h.tie
  parts := partsXK_supp_short A P.wP P.cP G h.wP h.cP
  join  := A.join_supp G Ex
  keys  := A.keys_supp_short P.lev G h.lev
  table := A.table_supp_short P.lev G h.lev
  clo   := A.close_supp_short P.cl Ex h.cl
  zero  := A.zero_supp G Ex
  bits  := A.bits_supp_short P.cl Ex h.cl

/-- WHATEVER ITS VERIFIER PUTS OUT IS 0 OUTSIDE G. -/
theorem lamS_supp (A : Dat E) (P : Pl A) (Ex : ExtSpec) (G : A.J → Prop) (h : P.In G) :
    ∀ st y τ o, (A.lamS P Ex).R.out st y τ = some o → RowsSupp G o.2.2 ∧ ∀ i, SuppIn G (o.2.1 i).mf
        :=
  (A.bks P (SK₀ E Ex)).lam1_supp G (bks_supp_short A P Ex G h) h.cells

end Lk6

#print axioms Lk6.lamS_know
#print axioms Lk6.lamS_isL
#print axioms Lk6.lamS_isL_adm
#print axioms Lk6.lamS_isS
#print axioms Lk6.lamS_passes
#print axioms Lk6.lamS_copies
#print axioms Lk6.lamS_supp
