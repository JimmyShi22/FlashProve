-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieShort.lean: the draw and the fused tie (Cb/Pv/KeyLookup/TieM.lean) at the short
sumcheck `SK₀` (Cb/Pv/KeyLookup/Short0.lean), in which the coefficient of power 0 of each round's
polynomial is not sent. The draw and the tie together are called the head.

Each statement is the one at the library's sumcheck, under the same conditions on public numbers and
shapes, with `SK₀` in its place. It imports no file of the program (OnBytes/Iop, OnBytes/Params,
...). Terms: lean/GLOSSARY.md.

Main names:
  `tie_ltK_short`: the condition of `head_know` on the sumcheck holds at `SK₀`.
  `head_know_short`: the block at `SK₀` is `Know` from In to Tied, under `A.Adm p` with `[CharP E
  p]` and n + 2 = pl, and nothing else.
  `Tie.ltForm_short`, `head_form_short` (no condition), `head_supp_short` (under `L.In G`): the two
  properties of form, and the support, at `SK₀`.
  `Tie.chain_lists`, `Tie.head_lists`: the errors and the sizes of the challenge sets of blocks in a
  row hang on those of the blocks alone.
  `head_isL_short`: n + 2 = pl ⇒ at `SK₀` the errors and the sizes of the challenge sets are the
  columns c and n of the rows `lamHead` of the list of rounds, as at the library's sumcheck.
Limits: not said: how many scalars a message of `SK₀` holds (Cb/Pv/KeyLookup/TieSent.lean); that
`SK₀` is the program's sumcheck; anything on an honest side.

-/
import Cb.Pv.KeyLookup.TieL
import Cb.Pv.KeyLookup.TieSupp
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

variable {E : Type} [Field E] [Fintype E]

theorem tie_ltK_short (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (Kc M Wp : Type)
    (msg : M → A.J → E) (n : ℕ) : (A.tie L).LtK (SK₀ E Ex) Wp Kc msg n := fun l _ =>
  SK₀_ourK M Wp Kc ((A.tie L).lv l).T ((A.tie L).msgAt M msg l) (tieF_ok E (A.tie L) l).1
    (tieF_ok E (A.tie L) l).2.2.1 (tieF_ok E (A.tie L) l).2.2.2 (tieF_ok E (A.tie L) l).2.1

/-- Know of the head at the short sumcheck. -/
theorem head_know_short (p : ℕ) [CharP E p] (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec)
    (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (n : ℕ) (hn : n + 2 = A.pl) (hA : A.toPub.Adm p) :
    (A.headK L (SK₀ E Ex) n).Know (A.jtIn R0 msg Mu) (A.jt R0 msg Mu A.Tied) :=
  head_know p A L Ex Kc M Wp _ R0 msg Mu n hn hA (tie_ltK_short A L Ex Kc M Wp msg n)

theorem Tie.ltForm_short (D : TieF E) (Ex : ExtSpec) (n : ℕ) : Tie.LtForm D (SK₀ E Ex) n :=
  fun l _ =>
  ⟨SK₀_passes Ex (D.lv l).T.par, SK₀_copies Ex (D.lv l).T.par⟩

theorem head_form_short (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) :
    (A.headK L (SK₀ E Ex) n).R.Passes id (fun x => x.st) ∧ (A.headK L (SK₀ E Ex) n).R.OnlyCopies :=
  head_form A L _ n (Tie.ltForm_short (A.tie L) Ex n)

theorem head_supp_short (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) (G : A.J → Prop)
    (hL : L.In G) : Inv (A.headK L (SK₀ E Ex) n).R (fun _ => True) (A.SuppX G) :=
  head_supp A L _ n G (Tie.ltForm_short (A.tie L) Ex n) hL

/-- Blocks in a row: errors and numbers of values hang on those of the blocks alone. -/
theorem Tie.chain_lists {Ex : ExtSpec} (X : ℕ → Type) (b b' : ∀ l, BkK (X l) (X (l + 1)) Ex) :
    ∀ n, (∀ l ≤ n, (b l).e.toList = (b' l).e.toList ∧
        (b l).R.shape.chalList = (b' l).R.shape.chalList) →
      (BkK.chain X b n).e.toList = (BkK.chain X b' n).e.toList ∧
        (BkK.chain X b n).R.shape.chalList = (BkK.chain X b' n).R.shape.chalList
  | 0, h => h 0 (Nat.le_refl 0)
  | n + 1, h => by
    obtain ⟨i1, i2⟩ := Tie.chain_lists X b b' n fun l hl => h l (Nat.le_succ_of_le hl)
    obtain ⟨s1, s2⟩ := h (n + 1) (Nat.le_refl _)
    refine ⟨?_, ?_⟩
    · refine (Err.toList_app (BkK.chain X b n).e (b (n + 1)).e).trans ?_
      rw [i1, s1]
      exact (Err.toList_app (BkK.chain X b' n).e (b' (n + 1)).e).symm
    · refine (Shape.chalList_append (BkK.chain X b n).R.shape (b (n + 1)).R.shape).trans ?_
      rw [i2, s2]
      exact (Shape.chalList_append (BkK.chain X b' n).R.shape (b' (n + 1)).R.shape).symm

/-- The head's lists hang on the lists of the sumcheck at the steps that are laid. -/
theorem Tie.head_lists (A : Dat E) (L : TiePl E A.J) {Ex : ExtSpec} (SK SK' : PscLtK E Ex) (n : ℕ)
    (h : ∀ l ≤ n,
      (SK.full ((A.tie L).lv l).T.par).e.toList = (SK'.full ((A.tie L).lv l).T.par).e.toList ∧
      (SK.full ((A.tie L).lv l).T.par).R.shape.chalList =
        (SK'.full ((A.tie L).lv l).T.par).R.shape.chalList) :
    (A.headK L SK n).e.toList = (A.headK L SK' n).e.toList ∧
      (A.headK L SK n).R.shape.chalList = (A.headK L SK' n).R.shape.chalList := by
  obtain ⟨c1, c2⟩ := Tie.chain_lists (fun l => E × ((A.tie L).lv l).T.St) ((A.tie L).stepK SK)
    ((A.tie L).stepK SK') n h
  refine ⟨?_, ?_⟩
  · refine (Err.toList_app (A.drawK Ex).e (A.tieK L SK n).e).trans ?_
    refine Eq.trans ?_ (Err.toList_app (A.drawK Ex).e (A.tieK L SK' n).e).symm
    exact congrArg (fun t => (A.drawK Ex).e.toList ++ t) c1
  · refine (Shape.chalList_append (A.drawK Ex).R.shape (A.tieK L SK n).R.shape).trans ?_
    refine Eq.trans ?_ (Shape.chalList_append (A.drawK Ex).R.shape (A.tieK L SK' n).R.shape).symm
    exact congrArg (fun t => (A.drawK Ex).R.shape.chalList ++ t) c2

/-- At the short sumcheck the head's errors and numbers of values are its share of the list. -/
theorem head_isL_short (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) (hn : n + 2 = A.pl) :
    IsL (A.headK L (SK₀ E Ex) n) (lamHead (Fintype.card E) A.toPub) := by
  obtain ⟨h1, h2⟩ := Tie.head_lists A L (SK₀ E Ex) (PscLtK.lib E Ex) n fun l _ =>
    ⟨SK₀_errs Ex ((A.tie L).lv l).T.par, SK₀_vals Ex ((A.tie L).lv l).T.par⟩
  exact ⟨h1.trans (head_isL A L Ex n hn).1, h2.trans (head_isL A L Ex n hn).2⟩

end Lk6

#print axioms Lk6.head_know_short
#print axioms Lk6.head_form_short
#print axioms Lk6.head_supp_short
#print axioms Lk6.head_isL_short
