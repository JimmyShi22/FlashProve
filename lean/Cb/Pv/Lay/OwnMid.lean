-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnMid.lean: laws of the chain of a layers' sub-proof's own rounds (Cb/Pv/Lay/Own.lean)
at its middle stages: the products' scalars, the products of the rows, the terms, the draw that
combines.

`RowsL.cP`, `o3`, `o3_over` and `c4` have the very form of a clause of `LayTail.Laws`, over
predicates and a rest of the chain that are given as arguments, so that they can be used at any
value of the letters. They are put together in Cb/Pv/Lay/OwnAll.lean.

Main names:
  `RowsL.lP`, `RowsL.stg2`: from the record of Cb/Pv/Lay/Rows.lean, read off the chain's
    statements by a map π: what is claimed of the sent scalars; the letters of the sumcheck, with
    one further scalar, the claimed sum itself, of which the linear row `tie` is claimed.
  `RowsL.cP`: the law at the round of the products' scalars: before it `led` of the np sums and Q
    are claimed; if what follows the sumcheck gives Q again, at most np - 1 draws are bad.
  `rowGap`, `rowGap_iff`: a sumcheck's first output row as "a gap is 0".
  `o3`: at the sumcheck of the terms the rows on the end values are owed at the chain's end; the
    first row is among what is claimed before the next draw.
  `o3_over`: the same where the first row is claimed in the programs' form, divided by the drawn
    coefficient: then "the coefficient is not 0" is owed at the chain's end too. `knowAt_test`: a
    test of the last statement behind a reduction discharges such a claim; the errors do not turn.
  `terms_gives`: a claim G on the masked sum of the terms less k comes back from the stage's
    claim, if what follows claims G of the sent scalar less k. Where k is the value of the
    incoming masks' form, the masked sum less k is the true sum.
  `c4`: the law at the draw that combines nc gaps, from `link`: the sum claim of the sumcheck that
    follows gives that the gaps' batch by the powers of the element is 0.

Limits: `link`, and the premises that what follows gives Q or G again, are hypotheses: they are
laws on the letters, to be proved at a value; no value is built here. Nothing is said on the
honest prover, on completeness or on zero knowledge.
-/
import Cb.Pv.Lay.Own
import Cb.Pv.Lay.Rows
import Cb.Pv.Lay.Over

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-! ### The products of the rows -/

namespace RowsL
variable (L : RowsL E) (rd : M → L.J → E) {X : Type} (π : X → L.St)

/-- The statements before and behind the sumcheck of the products of the rows, in a chain whose
statements before the scalars' round are X; π reads the record's state off them. -/
abbrev XP (L : RowsL E) (X : Type) : Type := (X × (Fin L.np → E)) × E
abbrev Nx2 (L : RowsL E) (X : Type) : Type := (L.XP X × (Fin 1 → E)) × L.tok.toSum.T.par.Out

/-- the record's state behind the scalars' round -/
def st2 (x : L.XP X) : L.X2 := ((π x.1.1, x.1.2), x.2)

/-- What is claimed of the sent scalars: the claim (B). -/
def lP (x : X) (s : Fin L.np → E) (m : M) : Prop :=
  L.led (π x) (rd m) fun n => s n - rd m (L.mkAt n)

/-- The letters of the sumcheck: one further scalar, the claimed sum itself; of it the linear row is
claimed. -/
@[reducible] noncomputable def stg2 (F : ∀ st, HFixs (L.tok.toSum.T.par.vars st)) :
    Stg E M (L.XP X) where
  L := L.tok.toSum
  n := 1
  F := F
  cl := fun x r => (r 0, L.st2 π x)
  msg := rd
  Lc := fun x r m => L.tie (L.st2 π x) (r 0) (rd m)

/-- The law at the round of the products' scalars. Before it: `led` of the np sums, and Q. If what
follows the sumcheck gives Q again, at most np - 1 draws are bad. -/
theorem cP (F : ∀ st, HFixs (L.tok.toSum.T.par.vars st)) (Ow : (L.stg2 rd π F).Nx → M → Prop)
    (next : Ch E M (L.stg2 rd π F).Nx) (Q : X → M → Prop)
    (hQ : ∀ b m, next.Todo b m → Q b.1.1.1.1 m)
    (x : X) (m : M) (h : ¬ (L.Idn (π x) (rd m) ∧ Q x m)) (s : Fin L.np → E)
    (hs : L.lP rd π x s m) :
    cnt (fun β : E => ((L.stg2 rd π F).stage Ow next).Todo ((x, s), β) m) ≤ L.np - 1 := by
  by_cases hq : Q x m
  · refine le_trans (cnt_mono fun β hβ => ?_) (L.few (π x) (rd m) (fun hi => h ⟨hi, hq⟩) s)
    obtain ⟨r, h1, h2, -⟩ := hβ
    have e : tsum L.tok.toSum.T.par ((π x, s), β) (rd m) = (r : Fin 1 → E) 0 := h2
    refine (L.th_iff ((π x, s), β) (rd m)).2 ⟨hs, ?_⟩
    rw [e]
    exact h1
  · refine le_trans (le_of_eq (cnt_false fun β hβ => ?_)) (Nat.zero_le _)
    obtain ⟨r, -, -, o, h3⟩ := hβ
    exact hq (hQ _ m h3)

end RowsL

/-! ### The terms, and the draw that combines -/

/-- The gap of a sumcheck's first output row. -/
def rowGap (Y : PscPar E) (o : Y.Out) (m : Y.J → E) : E :=
  hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) +
      o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m +
      o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * Y.Gb o.st m b (Y.hp o.st o.pt) -
    (o.fin - o.eps * Y.S0 o.st (Y.hp o.st o.pt) o.vals)

omit [Fintype E] in
theorem rowGap_iff (Y : PscPar E) (o : Y.Out) (m : Y.J → E) : rowGap Y o m = 0 ↔ Y.UHolds o m :=
  sub_eq_zero

/-- At the sumcheck of the terms: the rows on the end values are owed at the chain's end; the first
row is among what is claimed before the next draw. -/
theorem o3 {X : Type} (S : Stg E M X) (P : S.Nx → M → Prop)
    (hP : ∀ b m, P b m → S.L.T.par.UHolds b.2 (S.msg m)) (b : S.Nx) (m : M)
    (h1 : ∀ a, S.L.T.par.EHolds b.2 (S.msg m) a) (h2 : P b m) : S.Out b m :=
  ⟨hP b m h2, h1⟩

/-- The same where the first row is claimed in the programs' form, solved for the kept part
(Cb/Pv/Lay/Over.lean). That form gives the row only where the drawn coefficient is not 0: so "it is
not 0" is owed at the chain's end too. It is a claim on the statement alone, which whoever follows
can test (`knowAt_test`). -/
theorem o3_over {X : Type} (S : Stg E M X) (P : S.Nx → M → Prop)
    (hP : ∀ b m, P b m →
      keptAt S.L.T.par b.2 (S.msg m) = overAt S.L.T.par b.2 (S.msg m)) (b : S.Nx) (m : M)
    (h1 : b.2.eps ≠ 0 ∧ ∀ a, S.L.T.par.EHolds b.2 (S.msg m) a) (h2 : P b m) : S.Out b m :=
  ⟨(over_iff S.L.T.par b.2 (S.msg m) h1.1).2 (hP b m h2), h1.2⟩

/-- A test of the last statement behind a reduction: what fails it is refused. A claim behind the
reduction that the test decides need not be claimed any more. The errors do not turn. -/
theorem knowAt_test {Kc Xi Xo Wp : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}
    {A : Rels Kc Xi Ei (M × Wp)} {B B' : Rels Kc Xo Eo (M × Wp)} {ε : Err R.shape}
    (hG : KnowAt R A B (fun _ _ _ wp => wp) ε) (t : Xo → Prop) [DecidablePred t]
    (hon : ∀ x y, B.on (x, y) → t x → B'.on (x, y))
    (hkn : ∀ x y w, B.on (x, y) → t x → B'.relR (x, y) w → B.relR (x, y) w) :
    KnowAt (R.post (fun x => if t x then some x else none) (ExtMap.id Eo)) A B'
      (fun _ _ _ wp => wp) ε :=
  knowAt_post (fun _ _ _ wp => wp) _ (ExtMap.id Eo) (fun _ _ w => w) hG (extMap_isLocal.1 Eo)
    (fun x y x' h e => by
      by_cases ht : t x
      · rw [if_pos ht] at e
        obtain rfl := Option.some.inj e
        exact hon x y h ht
      · rw [if_neg ht] at e
        cases e)
    (fun u x y x' w h e hw => by
      by_cases ht : t x
      · rw [if_pos ht] at e
        obtain rfl := Option.some.inj e
        exact hkn x y (u, w) h ht hw
      · rw [if_neg ht] at e
        cases e)
    (fun _ _ _ _ _ _ => rfl)

/-- What the sumcheck of the terms hands back. Its claimed sum is sent. Before it a claim G is made
of the masked sum less k; behind it the same G is made of the sent scalar less k, as a part of what
is claimed before the next draw. So the stage's claim gives G of the masked sum less k. Where k is
the value of the incoming masks' form, that is the true sum. -/
theorem terms_gives {X : Type} (S : Stg E M X) (hn : S.n = 1) (st : X → S.L.St)
    (hcl : ∀ x r, S.cl x r = (r ⟨0, by omega⟩, st x)) (k : X → M → E)
    (G : X → E → M → Prop) (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx)
    (hG : ∀ b m, next.Todo b m → G b.1.1 (b.1.2 ⟨0, by omega⟩ - k b.1.1 m) m) (x : X) (m : M)
    (h : (S.stage Ow next).Todo x m) :
    G x (tsum S.L.T.par (st x) (S.msg m) - k x m) m := by
  obtain ⟨r, -, h2, o, h3⟩ := h
  rw [hcl] at h2
  have e : tsum S.L.T.par (st x) (S.msg m) = r ⟨0, by omega⟩ := h2
  rw [e]
  exact hG _ m h3

/-- The law at the draw that combines. Before it: nc gaps are 0, and Q. `link`: the sum claim of
the sumcheck that follows gives that the gaps' batch by the element's powers is 0. If what follows
that sumcheck gives Q again, at most nc - 1 draws are bad. -/
theorem c4 {X : Type} (S : Stg E M (X × E)) (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) (nc : ℕ)
    (gap : X → M → Fin nc → E) (Q : X → M → Prop)
    (link : ∀ x β r m, S.Lc (x, β) r m → S.L.T.par.SumHolds (S.cl (x, β) r) (S.msg m) →
      ∑ i : Fin nc, β ^ (i : ℕ) * gap x m i = 0)
    (hQ : ∀ b m, next.Todo b m → Q b.1.1.1 m) (x : X) (m : M)
    (h : ¬ ((∀ i, gap x m i = 0) ∧ Q x m)) :
    cnt (fun β : E => (S.stage Ow next).Todo (x, β) m) ≤ nc - 1 :=
  law_powers nc gap Q (fun x m => (∀ i, gap x m i = 0) ∧ Q x m)
    (fun b m => (S.stage Ow next).Todo b m) (fun _ _ h1 h2 => ⟨h1, h2⟩)
    (fun x β m hT => by
      obtain ⟨r, h1, h2, o, h3⟩ := hT
      exact ⟨link x β r m h1 h2, hQ _ m h3⟩) x m h

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.RowsL.cP
#print axioms Cb.Pv.Lay.o3
#print axioms Cb.Pv.Lay.o3_over
#print axioms Cb.Pv.Lay.knowAt_test
#print axioms Cb.Pv.Lay.terms_gives
#print axioms Cb.Pv.Lay.c4
