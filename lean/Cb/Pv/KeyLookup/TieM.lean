-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieM.lean: the first two of the ten sub-protocols in a row that make up a lookup
whose keys come in several parts (Cb/Pv/KeyLookup/Letters.lean), the draw of the first challenge and
the fused tie, as one block, called the head; and that this block is round-by-round knowledge sound
(`BkK.Know`: for each fixed tuple of messages; the extractor is the identity) from the joint In to
the joint Tied, under conditions on public numbers and shapes, if the sumcheck, which is a
parameter, is so at each step; the library's own sumcheck is.

The block has a verifier and errors and names no honest prover (`BkK`:
Cb/Pv/Lookup/Know/KnowAt.lean).
It stands between three joints of Cb/Pv/KeyLookup/Letters.lean:
  In  --(the draw of al)-->  Drawn  --(pl - 1 sumchecks, the first fused)-->  Tied.
The tie leads from the claim rest 0 = fac * pow 0 to one claim on rest 0 and one on each live
plane's root, by pl - 1 sumchecks that have no variable but the library's dummy variable Y. Step l +
1 rests on the identity pow (l + 1) = pow (l + 2)^2 * plane (l + 1). Step 0 is fused: it rests on 0
= rest 0 - fac * (pow 1^2 * plane 0), with three end values in place of two.
It imports no file of the program (OnBytes/Iop, OnBytes/Params, ...). Terms: lean/GLOSSARY.md.

Main names:
  `TiePl`: where the tie's own mask entries are.
  `A.tie L`: the record `TieF` (Cb/Pv/Lookup/Blocks/TieF.lean) at these values: a := `A.fac`, the
  public factor; PK := `A.rest .. 0`, the product of the roots of all parts; PT j := `A.plane j`; Q
  j := `A.pow j`.
  `A.back`: the step without rounds that reads the tie's nested state back into the flat state: the
  masked claim on the product of the roots into `x.all`, those on the planes' roots into `x.planes`,
  the rows behind `x.rows`, in the order of the steps.
  `A.drawK`, `A.tieK`, `A.headK`: the blocks.
  `pow_step`, `pow_top`: pow k = pow (k + 1)^2 * plane k below pl; the last is the last plane's
  root.
  `drawn_know`: the draw is `Know` from In to Drawn; its error, a count of bad challenges, is
  allKeys - 1, by `Dat.cnt_draw` (Cb/Pv/KeyLookup/PartsAt.lean).
  `tied_know`: the tie is `Know` from Drawn to Tied, by `tieK_chain` (Cb/Pv/Lookup/Know/LtK.lean);
  the sumcheck is a parameter (`PscLtK`).
  `head_know`: both in a row. `head_know_lib`: at the library's own sumcheck no condition on the
  parameter is left. (The library's sumcheck sends one coefficient more in each round with a
  polynomial than the short one of Cb/Pv/KeyLookup/TieShort.lean.) `head_ll`: at the library's
  sumcheck, round by round, for every n (the number of the tie's last step): the errors (counts of
  bad challenges) are [allKeys - 1], then n + 1 times [1, 3, 0]; the sizes of the challenge sets are
  [q], then n + 1 times [q, q - 1, 1]; q is the number of elements of the field.
  `head_rounds`: 1 + 3 (n + 1) rounds. With n + 2 = pl these are pl - 1 steps
  (Cb/Pv/KeyLookup/TieL.lean).
  `fac_poly`: the factor is the value of a monic polynomial of degree padCount; with padding that
  polynomial is not the constant 1 (its value at a given al may be 1).
  `tooth_fac`: field algebra at the values of Letters.lean, naming no block: r - a b ≠ r - 1 b if a
  ≠ 1, b ≠ 0.
Limits: the conditions on public numbers and shapes are `A.Adm p` with `[CharP E p]` and n + 2 = pl.
The condition on the parameter is `LtK`: the sumcheck is `Know` at each place where it is used. None
reads a witness; none names an honest prover. Mu, a parameter of `jt` and `jtIn`, is idle in every
`Know`: it is a further clause of the joints' honest relation, which `Know` never reads.
Not said: the honest relation and an honest run; anything on masks beyond where the entries are;
that the lists are those of the program's plan; the scalars sent, and how many end values a step has
(Cb/Pv/KeyLookup/TieSent.lean).

-/
import Cb.Pv.Lookup.Know.LtK
import Cb.Pv.KeyLookup.PartsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Finset

noncomputable section

/-- The form that is c at the place i and 0 elsewhere. -/
def at1 {E J : Type} [Zero E] [DecidableEq J] (i : J) (c : E) : J → E :=
  fun k => if k = i then c else 0

theorem sum_at1 {E J : Type} [Field E] [Fintype J] [DecidableEq J] (i : J) (c : E) (μ : J → E) :
    ∑ k, at1 i c k * μ k = c * μ i := by
  unfold at1
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

variable {E : Type} [Field E] [Fintype E]

/-- Where the tie's own mask entries are: the hiding polynomial's coefficients of step l; the entry
on the product of the roots (step 0); on the power handed on (cAt l false) and on plane l's root
(cAt l true). -/
structure TiePl (E J : Type) [Field E] [Fintype E] where
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cZ  : J
  cAt : ℕ → Bool → J

namespace Dat
variable (A : Dat E)

theorem pow_step (st : A.St) (μ : A.J → E) (al : E) {k : ℕ} (hk : k < A.pl) :
    A.pow st μ al k = A.pow st μ al (k + 1) ^ 2 * A.plane st μ al k := by
  unfold pow
  rw [Finset.prod_eq_prod_Ico_succ_bot hk, Nat.sub_self, pow_zero, pow_one, mul_comm,
    ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have h1 : k + 1 ≤ j := (Finset.mem_Ico.mp hj).1
  rw [← pow_mul, ← pow_succ]
  congr 2
  omega

theorem pow_top (st : A.St) (μ : A.J → E) (al : E) {n : ℕ} (hn : n + 2 = A.pl) :
    A.pow st μ al (n + 1) = A.plane st μ al (n + 1) := by
  unfold pow
  rw [← hn, Nat.Ico_succ_singleton, Finset.prod_singleton, Nat.sub_self, pow_zero, pow_one]

variable (L : TiePl E A.J)

/-- The fused tie (`TieF`) at the values of a lookup with parts. -/
def tie : TieF E where
  St0 := A.XS
  J := A.J
  finJ := A.finJ
  decJ := A.decJ
  a := fun x => A.fac x.st x.al
  PK := fun x μ => A.rest x.st μ x.al 0
  PT := fun x μ j => A.plane x.st μ x.al j
  Q := fun x μ j => A.pow x.st μ x.al j
  wAt := L.wAt
  cZ := L.cZ
  cAt := L.cAt

theorem tie_stepTo {n : ℕ} (hn : n + 2 = A.pl) : (A.tie L).StepTo n := fun x μ j hj =>
  A.pow_step x.st μ x.al (k := j + 1) (by omega)

/-- The state before the tie, read off the state after n + 1 steps. -/
def old (n : ℕ) (x : E × ((A.tie L).lv (n + 1)).T.St) : A.XS := ((A.tie L).lv (n + 1)).base x.2

/-- The tie's rows (on the hiding coefficients), in the order of the steps. -/
def tieRows (n : ℕ) (x : E × ((A.tie L).lv (n + 1)).T.St) : List (Row E A.J) :=
  ((A.tie L).rowsAt (n + 1) x.2).reverse

/-- Back into the flat state, after the steps 0, .., n. The claim on the last live plane's root
(number n + 1) is written at every j ≥ n + 1; a joint reads planes j at j < pl = n + 2 alone: at a
plane that is not live it stands for nothing. -/
def back (n : ℕ) (x : E × ((A.tie L).lv (n + 1)).T.St) : A.XS :=
  { A.old L n x with
    all := ⟨at1 L.cZ ((A.tie L).bK n x.2).1, ((A.tie L).bK n x.2).2⟩
    planes := fun j =>
      if j < n + 1 then ⟨at1 (L.cAt j true) ((A.tie L).bT n x.2 j).1, ((A.tie L).bT n x.2 j).2⟩
      else ⟨at1 (L.cAt n false) ((A.tie L).be n x.2), x.1⟩
    rows := (A.old L n x).rows ++ A.tieRows L n x }

variable {Ex : ExtSpec}

variable (Ex) in
/-- The draw of al. -/
def drawK : BkK A.St A.XS Ex := Kn.drawK E A.ini Ex (A.allKeys - 1)

/-- The tie: target 0; the steps 0, .., n; back into the flat state. -/
def tieK (SK : PscLtK E Ex) (n : ℕ) : BkK A.XS A.XS Ex :=
  (((A.tie L).tieK SK n).preM fun x => ((0 : E), x)).postM (A.back L n)

/-- The head: the draw, then the tie. -/
def headK (SK : PscLtK E Ex) (n : ℕ) : BkK A.St A.XS Ex := (A.drawK Ex).seq (A.tieK L SK n)

end Dat
end

/-! ### Know -/

section
variable {E : Type} [Field E] [Fintype E]

/-- Know of the draw. -/
theorem drawn_know (p : ℕ) [CharP E p] (A : Dat E) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hA : A.toPub.Adm p) :
    (A.drawK Ex).Know (A.jtIn R0 msg Mu) (A.jt R0 msg Mu A.Drawn) := by
  refine knowAt_draw Kc M A.St A.XS Ex Wp E A.ini _ _ (A.allKeys - 1) (fun _ _ _ h => h) ?_
  intro st y m _
  refine (cnt_mono fun β hβ => ?_).trans (A.cnt_draw p hA st (msg m))
  obtain ⟨wp, h1, h2⟩ := hβ
  exact ⟨⟨h1.2.1.1, h1.2.2⟩, fun h => h2 ⟨h1.1, h⟩⟩

/-- Know of the tie. -/
theorem tied_know (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (Kc M Wp : Type) (SK : PscLtK E Ex)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) (n : ℕ)
    (hn : n + 2 = A.pl) (hL : (A.tie L).LtK SK Wp Kc msg n) :
    (A.tieK L SK n).Know (A.jt R0 msg Mu A.Drawn) (A.jt R0 msg Mu A.Tied) := by
  have g2 := tieK_chain E (A.tie L) Ex M Wp Kc SK msg
    (cj R0 msg (fun x : A.XS => x.st) (fun x μ => A.Side x μ ∧ Mu x.st μ) A.Side) n hL
    (A.tie_stepTo L hn)
  rw [tieFR_cj E (A.tie L) Ex Kc A.St M Wp R0 msg (fun x : A.XS => x.st)
      (fun x μ => A.Side x μ ∧ Mu x.st μ) A.Side n] at g2
  refine know_postM (B' := A.jt R0 msg Mu A.Tied) (A.back L n)
    (know_preM (A' := A.jt R0 msg Mu A.Drawn) (fun x : A.XS => ((0 : E), x)) (fun _ _ h => h) ?_ g2)
    (fun _ _ h => h) ?_
  · intro x y w _ h
    obtain ⟨⟨hR, hS⟩, hc⟩ := h
    have hc' : A.rest x.st (msg w.1) x.al 0 -
        A.fac x.st x.al * (A.pow x.st (msg w.1) x.al 1 ^ 2 * A.plane x.st (msg w.1) x.al 0) = 0 :=
      hc
    rw [← A.pow_step x.st (msg w.1) x.al (k := 0) (by omega)] at hc'
    exact ⟨hR, hS, sub_eq_zero.mp hc'⟩
  · intro x y w _ h
    obtain ⟨hR, ⟨hBN, hRows⟩, hAll, hPl⟩ := h
    have hAll' : A.rest (A.old L n x).st (msg w.1) (A.old L n x).al 0 +
        ∑ k, at1 L.cZ ((A.tie L).bK n x.2).1 k * msg w.1 k = ((A.tie L).bK n x.2).2 := hAll
    rw [sum_at1, mul_comm] at hAll'
    refine ⟨hR, ⟨⟨hBN, fun r hr => hRows r (List.mem_append_left _ hr)⟩,
      fun r hr => hRows r (List.mem_append_right _ (List.mem_reverse.2 hr)), hAll',
      fun j hj => ?_⟩, ?_⟩
    · have hj' := hPl j (by omega)
      have hj2 : A.plane (A.old L n x).st (msg w.1) (A.old L n x).al j +
          ∑ k, at1 (L.cAt j true) ((A.tie L).bT n x.2 j).1 k * msg w.1 k =
            ((A.tie L).bT n x.2 j).2 := by
        have e : (A.back L n x).planes j =
            ⟨at1 (L.cAt j true) ((A.tie L).bT n x.2 j).1, ((A.tie L).bT n x.2 j).2⟩ := if_pos hj
        unfold SCl.Holds at hj'
        rw [e] at hj'
        exact hj'
      rw [sum_at1, mul_comm] at hj2
      exact hj2
    · have hj' := hPl (n + 1) (by omega)
      have hj2 : A.plane (A.old L n x).st (msg w.1) (A.old L n x).al (n + 1) +
          ∑ k, at1 (L.cAt n false) ((A.tie L).be n x.2) k * msg w.1 k = x.1 := by
        have e : (A.back L n x).planes (n + 1) = ⟨at1 (L.cAt n false) ((A.tie L).be n x.2), x.1⟩ :=
          if_neg (Nat.lt_irrefl _)
        unfold SCl.Holds at hj'
        rw [e] at hj'
        exact hj'
      rw [sum_at1, mul_comm, ← A.pow_top _ _ _ hn] at hj2
      exact (tieFR_open E (A.tie L) n x (msg w.1)).2 hj2

/-- Know of the head: from «every key of every part is a row of the table» to the joint after the
    tie. -/
theorem head_know (p : ℕ) [CharP E p] (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (Kc M Wp : Type)
    (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (n : ℕ) (hn : n + 2 = A.pl) (hA : A.toPub.Adm p)
    (hL : (A.tie L).LtK SK Wp Kc msg n) :
    (A.headK L SK n).Know (A.jtIn R0 msg Mu) (A.jt R0 msg Mu A.Tied) :=
  know_seq (drawn_know p A Ex Kc M Wp R0 msg Mu hA) (tied_know A L Ex Kc M Wp SK R0 msg Mu n hn hL)

/-- At the library's own sumcheck the condition on the sumcheck holds. -/
theorem tie_ltK_lib (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (Kc M Wp : Type)
    (msg : M → A.J → E) (n : ℕ) : (A.tie L).LtK (PscLtK.lib E Ex) Wp Kc msg n := fun l _ =>
  PscLtK.lib_ourK M Wp Kc ((A.tie L).lv l).T ((A.tie L).msgAt M msg l) (tieF_ok E (A.tie L) l).1
    (tieF_ok E (A.tie L) l).2.2.1 (tieF_ok E (A.tie L) l).2.2.2 (tieF_ok E (A.tie L) l).2.1

theorem head_know_lib (p : ℕ) [CharP E p] (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec)
    (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (n : ℕ) (hn : n + 2 = A.pl) (hA : A.toPub.Adm p) :
    (A.headK L (PscLtK.lib E Ex) n).Know (A.jtIn R0 msg Mu) (A.jt R0 msg Mu A.Tied) :=
  head_know p A L Ex Kc M Wp _ R0 msg Mu n hn hA (tie_ltK_lib A L Ex Kc M Wp msg n)

/-! ### rounds and errors, at the library's sumcheck -/

/-- At the library's verifiers the tie without an honest side is the verifier's side of the tie with
    one. -/
theorem tieK_lib (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) :
    toK (D.tieA msg (PscBk.lib E Ex M Wp Kc) n) = D.tieK (PscLtK.lib E Ex) n := by
  unfold TieF.tieA TieF.tieK
  rw [toK_chain]
  rfl

/-- Errors and numbers of values of the head, round by round. -/
theorem head_ll (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) :
    (A.headK L (PscLtK.lib E Ex) n).e.toList =
        [A.allKeys - 1] ++ (List.range (n + 1)).flatMap (fun _ => [1, 3, 0]) ∧
    (A.headK L (PscLtK.lib E Ex) n).R.shape.chalList =
        [Fintype.card E] ++
          (List.range (n + 1)).flatMap fun _ => [Fintype.card E, Fintype.card E - 1, 1] := by
  have h := tieF_ll E (A.tie L) Ex Unit Unit Unit (fun _ _ => 0) n
  have e := tieK_lib (A.tie L) Ex Unit Unit Unit (fun _ _ => 0) n
  have h1 : ((A.tie L).tieK (PscLtK.lib E Ex) n).e.toList =
      (List.range (n + 1)).flatMap (fun _ => [1, 3, 0]) := by
    rw [← e]
    exact h.1
  have h2 : ((A.tie L).tieK (PscLtK.lib E Ex) n).R.shape.chalList =
      (List.range (n + 1)).flatMap fun _ => [Fintype.card E, Fintype.card E - 1, 1] := by
    rw [← e]
    exact h.2
  refine ⟨?_, ?_⟩
  · refine (Err.toList_app (A.drawK Ex).e (A.tieK L (PscLtK.lib E Ex) n).e).trans ?_
    exact congrArg₂ (· ++ ·) rfl h1
  · refine (Shape.chalList_append _ _).trans ?_
    exact congrArg₂ (· ++ ·) rfl h2

/-- 1 + 3 (n + 1) rounds. -/
theorem head_rounds (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) :
    (A.headK L (PscLtK.lib E Ex) n).R.shape.length = 1 + 3 * (n + 1) := by
  have h := congrArg List.length (head_ll A L Ex n).2
  rw [chalList_len] at h
  rw [h, List.length_append, flat_len]
  simp
  ring

/-! ### the factor -/

open Polynomial in
/-- The public factor is the value of a monic polynomial in al of degree padCount; with padding that
polynomial is not the constant 1. -/
theorem fac_poly (A : Dat E) (st : A.St) :
    ∃ P : E[X], (∀ al, P.eval al = A.fac st al) ∧ P.Monic ∧ P.natDegree = A.padCount ∧
      (0 < A.padCount → P ≠ 1) := by
  refine ⟨padPoly (A.tab st) [(A.padRow, A.padCount)], fun al => ?_, padPoly_monic _ _, ?_,
    fun h => ?_⟩
  · rw [padPoly_eval]
    simp [padFac, Dat.fac]
  · rw [padPoly_natDegree]
    simp [padNum]
  · exact padPoly_ne_one _ _ (by simpa [padNum] using h)

/-- Field algebra at the values of Letters.lean (no block is named): where the factor is not 1 and
the planes' product is not 0, the difference with the factor is another than the difference
without it. -/
theorem tooth_fac (A : Dat E) (st : A.St) (μ : A.J → E) (al : E) (h1 : A.fac st al ≠ 1)
    (h2 : A.pow st μ al 0 ≠ 0) :
    A.rest st μ al 0 - A.fac st al * A.pow st μ al 0 ≠ A.rest st μ al 0 - 1 * A.pow st μ al 0 := by
  intro h
  have h3 : A.fac st al * A.pow st μ al 0 = 1 * A.pow st μ al 0 := sub_right_injective h
  exact h1 (mul_right_cancel₀ h2 h3)

end
end Lk6

#print axioms Lk6.drawn_know
#print axioms Lk6.tied_know
#print axioms Lk6.head_know
#print axioms Lk6.head_know_lib
#print axioms Lk6.head_ll
#print axioms Lk6.head_rounds
#print axioms Lk6.fac_poly
#print axioms Lk6.tooth_fac
