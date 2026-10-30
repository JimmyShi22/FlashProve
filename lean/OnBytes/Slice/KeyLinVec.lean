-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyLinVec.lean: the test for a linear claim on a stored table, on plain vectors, in
written rounds.

A stored table decodes to a matrix (OnBytes/Slice/LinkAt.lean: Sz.dcd). The verifier holds one
linear claim on that matrix, a tensor row. The library has the mathematics of the test for such a
claim on plain vectors (Cb/Ld/LdLinWords.lean): three verifier messages (a shared point, a list of
locations, a point zeta), the bad values of each with their counts, and a backward step. The vectors
w', u', ω' of that file are any vectors that are fixed before the verifier's message is drawn. Here
they are meant to be read off the decodings of sent messages (OnBytes/Slice/KeyGroup.lean: Mb.fix).

This file
 gives the library's data from the sizes of a stored table and a few numbers (KLin, KLin.D);

 takes off a written round in which the verifier draws a value, from a count of bad values
 (draw_cnt). The set of bad values may depend on the round's own prover message;
 states the three rounds in that form (KLin.lin_point, lin_loc, lin_zeta), with the library's counts
 at radii below a third of the table's distance (KLin.cnt_pt, cnt_loc, cnt_zeta);



 splits a row on two vectors into two rows with a shared element (split_back, KLin.fold_split).

Main definitions: KLin, KLin.D, KLin.tab, KLin.Cl, KLin.Codes, KLin.errPt, errLoc,
errZeta, KLin.Left.

Main theorems: draw_cnt, KLin.cnt_pt, cnt_loc, cnt_zeta, KLin.lin_point, lin_loc,
lin_zeta, split_back, KLin.fold_split.

Not claimed. Nothing on the messages from which w', u', ω' are read, on samples, or on the tests
that close the rows that are left. Nothing at a radius of a third of the table's distance or more.
That a given verifier's rows are these rows.
The way back from the three drawn values to a false row that is left (KLin.Left) is not shown.
-/
import Cb.Ld.LdLinWordsProofs
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.CorePeel

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## A written round in which a value is drawn, from a count -/

/-- **A written round in which the verifier draws a value is taken off, from a count of bad
values.** g reads the drawn values injectively as an element of D. For each prover message m of the
round at most e elements of D are bad. The prover has lost before the round, if the goal holds
wherever the round's test of work fails, and if the prover has lost after the round whenever the
drawn value is not bad. -/
theorem draw_cnt {D : Type} [Fintype D] (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → D)
    (hg : Function.Injective g) (hlog : d.entry.logN ≤ 64) (t : Shape) (εt : Err t) (e : ℕ)
    (Bad : (wRound d).Msg → D → Prop) (hc : ∀ m, cnt (Bad m) ≤ e)
    (bad : Tr (wRound d :: t) → Prop)
    (hp : ∀ m c τ, GChal.pass (b := d.entry.work) c = false → bad (m, c, τ))
    (H : ∀ m c, ¬ Bad m (g (valsOf d c)) → Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound d :: t) (e * (bsRound .two d.entry d.kind).w, εt) bad := by
  intro m
  refine le_trans (cnt_mono fun c hc' => ?_)
    (le_trans (cnt_some_le (chalTo d g) (chalTo_fib d g hg hlog) (Bad m))
      (Nat.mul_le_mul_right _ (hc m)))
  cases h : chalTo d g c with
  | none => exact absurd (doomed_of_all _ _ _ fun b => hp m c b (chalTo_none d g c h)) hc'
  | some c' =>
    refine ⟨c', rfl, ?_⟩
    by_contra hB
    rw [chalTo_some d g c c' h] at hB
    exact hc' (H m c hB)

/-! ## The library's data from the sizes of a stored table -/

/-- **The sizes of the test.** S: the sizes of the stored table. nY: the number of rows of the
matrix. klo: the number of column variables inside a row of the table. l: the number of coordinates
of zeta. lay: where an entry of the matrix stands in a row's message. py: the rows of the matrix as
vertices of a cube. e': the radius at which the fold is tested. t: the number of locations. -/
structure KLin where
  S : Sz
  nY : ℕ
  klo : ℕ
  l : ℕ
  lay : Fin nY × (Fin klo → Bool) → S.En
  py : Fin nY → Fin l → Bool
  e' : ℕ
  t : ℕ

namespace KLin
variable (K : KLin)

/-- **The library's data of the test on vectors.** Its table format is the stored table's. -/
@[reducible] noncomputable def D : LdLinW GE K.S.Pos K.S.Co K.S.En (Fin K.nY) :=
  ⟨K.S.ix, K.klo, K.l, K.lay, K.py⟩

/-- A stored table, as a table over the field. -/
noncomputable def tab (f : K.S.Pos → Run.PQ.SgX) : K.D.X.Row → K.S.Pos → GE := K.S.lk.tab f

/-- **A claim**: weights g on the rows of the matrix, a point ψ for its columns, an element that
stands for a linear form on entries of other messages, and a target. -/
structure Cl where
  g : Fin K.nY → GE
  ψ : K.D.Pt
  rest : GE
  τ : GE

/-- The distance of a row of the table. -/
def dT : ℕ := 2 ^ K.S.P.T.a - (K.S.P.T.r + K.S.P.T.l) + 1

/-- What is asked of the table's code and the two radii. -/
structure Codes : Prop where
  /-- the points of the code are different -/
  small : K.S.P.T.a ≤ 32
  /-- a row has no more coefficients than positions -/
  room : K.S.P.T.r + K.S.P.T.l ≤ 2 ^ K.S.P.T.a
  /-- the fold's radius is below a third of the distance -/
  third : 3 * K.e' < K.dT
  /-- the decoder's radius is below half the distance -/
  half : 2 * K.S.eM < K.dT
  /-- the fold's radius is at most the decoder's -/
  le : K.e' ≤ K.S.eM
  /-- different rows of the matrix are different vertices -/
  inj : Function.Injective K.py

/-- The count of the shared point's round. -/
noncomputable def errPt : ℕ :=
  K.S.P.v * (K.e' + 1) * Fintype.card GE ^ (K.S.P.v - 1) * Fintype.card GE ^ K.klo +
    (K.S.P.v + K.klo) * Fintype.card GE ^ (K.S.P.v + K.klo - 1)

/-- The count of the locations' round. -/
def errLoc : ℕ := (Fintype.card K.S.Pos - K.e' - 1) ^ K.t

/-- The count of zeta's round. -/
noncomputable def errZeta : ℕ := K.l * Fintype.card GE ^ (K.l - 1)

/-- The bad shared points, for one claim's weights g and one vector w'. -/
def BadPt (f : K.S.Pos → Run.PQ.SgX) (g : Fin K.nY → GE) (w' : K.D.Col → GE) : K.D.Pt → Prop :=
  K.D.BadSh (K.tab f) K.S.rec0 K.e' fun _ : Fin 1 => some (g, w')

/-- The bad lists of locations, at the point γ and the vector u'. -/
def BadLoc (f : K.S.Pos → Run.PQ.SgX) (γ : Fin K.D.X.v → GE) (u' : K.S.Co → GE) :
    (Fin K.t → K.S.Pos) → Prop :=
  K.D.BadLoc (K.tab f) K.S.rec0 γ u'

/-- The bad values of zeta, at the vectors u' and ω'. -/
def BadZeta (ψlo : Fin K.klo → GE) (u' : K.S.Co → GE) (ω' : Fin K.nY → GE) :
    (Fin K.l → GE) → Prop :=
  K.D.BadZeta (K.D.X.msg u') ψlo ω'

variable {K}

/-- The record's row at `rec0` says nothing: the sample map of `ix` is `Sample.nil`. -/
theorem recRow (γ : Fin K.D.X.v → GE) (u : K.S.Co → GE) : K.D.X.RecRow K.S.rec0 γ u :=
  funext fun s => s.elim

/-- The distance of the table's generator matrix. -/
theorem hasDist (h : K.Codes) : Blocks.HasDist K.D.X.G K.dT := hasDist_genOf K.S.P.T h.small h.room

/-- **The shared point's round**: the number of bad points. -/
theorem cnt_pt (h : K.Codes) (f : K.S.Pos → Run.PQ.SgX) (g : Fin K.nY → GE) (w' : K.D.Col → GE) :
    cnt (K.BadPt f g w') ≤ K.errPt := by
  have hd := hasDist h
  have hlt : K.D.X.eM < K.dT := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) h.half
  have hcoll : ¬ K.D.X.Coll (K.tab f) K.S.rec0.1 :=
    (ldFe_unique K.D.X K.dT (K.tab f) K.S.rec0 (fun _ => 0) hd h.half).2
  have hb := ldFe_cnt_nil K.D.X K.dT K.e' _ (K.tab f) K.S.rec0 (inferInstanceAs (IsEmpty Empty)) hd
    hlt h.le (mcaEq_third K.S.P.T h.small h.room K.S.ix rfl K.e' h.third) hcoll
  have h1 := ldk_cnt_badSh K.D (K.tab f) K.S.rec0 (fun _ : Fin 1 => some (g, w')) hb
  rw [Nat.one_mul] at h1
  exact h1

/-- **The locations' round**: the number of bad lists, at a shared point that is not bad. -/
theorem cnt_loc (f : K.S.Pos → Run.PQ.SgX) (g : Fin K.nY → GE) (w' : K.D.Col → GE) (ψs : K.D.Pt)
    (hψ : ¬ K.BadPt f g w' ψs) (u' : K.S.Co → GE) : cnt (K.BadLoc f ψs.1 u') ≤ K.errLoc :=
  ldLin_cnt_loc K.D K.e' K.t (K.tab f) K.S.rec0 ψs.1 u' fun hb => hψ (Or.inl hb)

/-- **Zeta's round**: the number of bad values. -/
theorem cnt_zeta (h : K.Codes) (ψlo : Fin K.klo → GE) (u' : K.S.Co → GE) (ω' : Fin K.nY → GE) :
    cnt (K.BadZeta ψlo u' ω') ≤ K.errZeta :=
  ldLin_cnt_zeta K.D (K.D.X.msg u') ψlo ω' h.inj

/-! ## The three rounds, written -/

section
variable (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (t : Shape) (εt : Err t)
  (bad : Tr (wRound d :: t) → Prop)
  (hp : ∀ m c τ, GChal.pass (b := d.entry.work) c = false → bad (m, c, τ))
include hlog hp

/-- **The shared point's round is taken off.** w' may be read off the round's own prover message. -/
theorem lin_point (h : K.Codes) (gv : Vals .two (Fmt.dsOf d.entry d.kind) → K.D.Pt)
    (hg : Function.Injective gv) (f : K.S.Pos → Run.PQ.SgX) (g : Fin K.nY → GE)
    (w' : (wRound d).Msg → K.D.Col → GE)
    (H : ∀ m c, ¬ K.BadPt f g (w' m) (gv (valsOf d c)) → Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound d :: t) (K.errPt * (bsRound .two d.entry d.kind).w, εt) bad :=
  draw_cnt d gv hg hlog t εt K.errPt (fun m => K.BadPt f g (w' m)) (fun m => cnt_pt h f g (w' m))
    bad hp H

/-- **The locations' round is taken off**, after a shared point that is not bad. -/
theorem lin_loc (gv : Vals .two (Fmt.dsOf d.entry d.kind) → Fin K.t → K.S.Pos)
    (hg : Function.Injective gv) (f : K.S.Pos → Run.PQ.SgX) (g : Fin K.nY → GE)
    (w' : K.D.Col → GE) (ψs : K.D.Pt) (hψ : ¬ K.BadPt f g w' ψs)
    (u' : (wRound d).Msg → K.S.Co → GE)
    (H : ∀ m c, ¬ K.BadLoc f ψs.1 (u' m) (gv (valsOf d c)) → Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound d :: t) (K.errLoc * (bsRound .two d.entry d.kind).w, εt) bad :=
  draw_cnt d gv hg hlog t εt K.errLoc (fun m => K.BadLoc f ψs.1 (u' m))
    (fun m => cnt_loc f g w' ψs hψ (u' m)) bad hp H

/-- **Zeta's round is taken off.** -/
theorem lin_zeta (h : K.Codes) (gv : Vals .two (Fmt.dsOf d.entry d.kind) → Fin K.l → GE)
    (hg : Function.Injective gv) (ψlo : Fin K.klo → GE) (u' : K.S.Co → GE)
    (ω' : (wRound d).Msg → Fin K.nY → GE)
    (H : ∀ m c, ¬ K.BadZeta ψlo u' (ω' m) (gv (valsOf d c)) → Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound d :: t) (K.errZeta * (bsRound .two d.entry d.kind).w, εt) bad :=
  draw_cnt d gv hg hlog t εt K.errZeta (fun m => K.BadZeta ψlo u' (ω' m))
    (fun m => cnt_zeta h ψlo u' (ω' m)) bad hp H

end

/-! ## The way back -/

variable (K) in
/-- **The rows that the test leaves**, all true of the vectors w', u', ω': the drawn columns' rows,
the fold's row, the evaluation's row and the dot product's row. -/
structure Left (f : K.S.Pos → Run.PQ.SgX) (c : K.Cl) (w' : K.D.Col → GE) (ψs : K.D.Pt)
    (u' : K.S.Co → GE) (Q : Fin K.t → K.S.Pos) (ω' : Fin K.nY → GE) (ζ : Fin K.l → GE) : Prop where
  col : K.D.ColR (K.tab f) ψs.1 u' Q
  fold : K.D.FoldR ζ ψs.2 (K.D.X.msg u') ω'
  eval : K.D.Eval c.ψ w' c.rest c.τ
  dot : K.D.Dot c.g ω' ψs w'

end KLin

/-! ## A row on two vectors, split -/

/-- A row a + b = t is split with a shared element κ and a share v: if a + κ = v and
b - κ = t - v, then a + b = t. -/
theorem split_back {a b t κ v : GE} (h1 : a + κ = v) (h2 : b - κ = t - v) : a + b = t := by
  linear_combination h1 + h2

/-- **The fold's row, split.** Its left side is a form on ω', its right side a form on u'. If the
row is false, then for every shared element κ and every share v one of the two half rows is
false. -/
theorem KLin.fold_split {K : KLin} (ζ : Fin K.l → GE) (ψlo : Fin K.klo → GE) (u' : K.S.Co → GE)
    (ω' : Fin K.nY → GE) (hno : ¬ K.D.FoldR ζ ψlo (K.D.X.msg u') ω') (κ v : GE) :
    ¬ (∑ y, Alg.eqk ζ (K.py y) * ω' y + κ = v) ∨
      ¬ (-(∑ y, Alg.eqk ζ (K.py y) * K.D.omU (K.D.X.msg u') ψlo y) - κ = 0 - v) := by
  by_contra hcon
  have h1 := not_not.1 fun h => hcon (Or.inl h)
  have h2 := not_not.1 fun h => hcon (Or.inr h)
  exact hno (eq_of_sub_eq_zero (by
    have := split_back h1 h2
    rwa [← sub_eq_add_neg] at this))

end OnBytes.Slice
