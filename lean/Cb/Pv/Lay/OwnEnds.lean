-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnEnds.lean: the first and the last stages of the chain of a layers' sub-proof's own
rounds (Cb/Pv/Lay/Own.lean), filled from the records of the blocks, with the chain's laws on them
proved.

The chain asks, at each round that draws, for a bound on the bad draws, and at each sumcheck that
what is owed at the chain's end, with the claim that follows, gives the sumcheck's output claims.
Here these clauses are proved for the stages of the norms' squares (Cb/Pv/Lay/Squares.lean) and for
the stages behind the batched sumcheck of the inner products: the gated products (Prod.lean), the
routed experts' (Routed.lean), the weights (Weights.lean). Every claim has one form: the stage's own
open claims, and the sources of the later stages.

Each record keeps its own states and names. A map from the chain's statements to the record's
states, and a reading of the messages, are parameters.

Main names:
  `Head`: the parameters of the first stages: the squares' record; `Src`: the sources of the later
    stages, read at the first statement. `Head.pL`, `lL`, `pN`, `s1`, `p1`: the chain's letters.
    `Head.cL`, `cN`, `c1`: its laws.
  `Foot`: the parameters of the last stages, at the statements B4 behind the inner products'
    sumcheck. `Foot.s5`, `p5`, `pR`, `s6`, `p6`, `pW`, `s7`: the chain's letters. `Foot.c5`, `cR`,
    `c6`, `cW`: its laws.
  `Foot.todo5`: what the chain claims at B4. `Foot.o4`: from a seam (a premise: what is owed of the
    inner products' output claims, with the three kinds of input claims, gives these output claims)
    the chain's law on that sumcheck.

Limits: the seam in `o4` is a premise. No value of the chain's parameters is built here, and the
lemmas are not put together here: that is done in Cb/Pv/Lay/OwnAll.lean. The stage of the weights is
the one without a sent scalar (the first group's: Cb/Pv/Lay/OwnEndsFirst.lean). Nothing is said on
the honest prover, on completeness or on zero knowledge.
-/
import Cb.Pv.Lay.OwnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Cb.Pv.Att

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-! ### The first stages -/

/-- The parameters of the first stages. -/
structure Head (E : Type) [Field E] [Fintype E] (M X : Type) where
  G : SquaresL E
  /-- the record's state, off the first statement; the entries, off the messages -/
  st0 : X → G.St
  rd : M → G.J → E
  /-- the sources of the later stages -/
  Src : X → M → Prop

namespace Head
variable {M X : Type} (H : Head E M X)

/-- the number of sent scalars -/
abbrev nL : ℕ := H.G.n * H.G.ns

/-- the sent scalars by norm and place -/
def sOf (s : Fin H.nL → E) : Fin H.G.n × Fin H.G.ns → E := fun q => s (finProdFinEquiv q)

/-- the statements behind the round of the scalars -/
abbrev XN : Type := (X × (Fin H.nL → E)) × E

/-- the record's state behind that round -/
def x1 (y : H.XN) : H.G.St1 := ((H.st0 y.1.1, H.sOf y.1.2), y.2)

/-- what is claimed before the round of the scalars: the identities, and the later sources -/
def pL (x : X) (m : M) : Prop := H.G.Phi (H.st0 x) (H.rd m) ∧ H.Src x m

/-- the rows on the scalars sent -/
def lL (x : X) (s : Fin H.nL → E) (m : M) : Prop := H.G.B ((H.st0 x, H.sOf s), 0) (H.rd m)

/-- what is claimed before the join: each norm's combined claim, and the later sources -/
def pN (y : H.XN) (m : M) : Prop :=
  (∀ i, H.G.R.val (H.x1 y) (H.rd m) i = H.G.R.sh i (H.x1 y)) ∧ H.Src y.1.1 m

/-- If what is claimed before the round fails and the rows hold, few draws make the claims behind
it true. -/
theorem cL (x : X) (m : M) (h : ¬ H.pL x m) (s : Fin H.nL → E) (hs : H.lL x s m) :
    cnt (fun β : E => H.pN ((x, s), β) m) ≤ H.G.ns - 1 := by
  by_cases hQ : H.Src x m
  · refine le_trans (cnt_mono fun β hβ => ?_)
      (H.G.cnt_bad (H.st0 x) (H.rd m) (fun hp => h ⟨hp, hQ⟩) (H.sOf s))
    exact ⟨hs, hβ.1⟩
  · exact le_trans (le_of_eq (cnt_false fun β hβ => hQ hβ.2)) (Nat.zero_le _)

/-- the sumcheck of the sums of squares -/
def s1 : Stg E M (H.XN × (Fin H.G.g → E)) where
  L := H.G.R.L.toSum
  n := 0
  F := F₀ H.G.R.L.toSum.T.par
  cl := fun y _ => (H.G.R.L.tg (H.x1 y.1, y.2), (H.x1 y.1, y.2))
  msg := H.rd
  Lc := fun _ _ _ => True

/-- what is claimed before its last draw: the later sources -/
def p1 (b : H.s1.Nx) (m : M) : Prop := H.Src b.1.1.1.1.1 m

/-- If what is claimed before the join fails, few points make the sumcheck's input claim true. -/
theorem cN (T : H.s1.Nx → M → Prop) (hT : ∀ b m, T b m → H.p1 b m) (y : H.XN) (m : M)
    (h : ¬ H.pN y m) :
    cnt (fun p : Fin H.G.g → E => ∃ r, H.s1.Lc (y, p) r m ∧
      H.s1.L.T.par.SumHolds (H.s1.cl (y, p) r) (H.s1.msg m) ∧ ∃ o, T (((y, p), r), o) m) ≤
      H.G.g * Fintype.card E ^ (H.G.g - 1) :=
  law_join H.G.g H.G.n H.G.hn
    (fun (y : H.XN) m i => H.G.R.val (H.x1 y) (H.rd m) i - H.G.R.sh i (H.x1 y))
    (fun y m => H.Src y.1.1 m) H.pN
    (fun z m => ∃ r, H.s1.Lc z r m ∧ H.s1.L.T.par.SumHolds (H.s1.cl z r) (H.s1.msg m) ∧
      ∃ o, T ((z, r), o) m)
    (fun _ _ h1 h2 => ⟨fun i => sub_eq_zero.1 (h1 i), h2⟩)
    (fun y p m h0 => by
      obtain ⟨r, _, h2, o, h3⟩ := h0
      have h4 := (H.G.R.link (H.x1 y, p) (H.rd m)).1
        ((H.G.R.L.sum_iff _ _ _).1 ((H.G.R.L.ksum_iff _ _ _).1
          ((psc_our_sum E H.G.R.L.toSum.T _ _).1 h2)))
      refine ⟨?_, hT _ m h3⟩
      simp only [mul_sub, sum_sub_distrib]
      rw [h4, sub_self]) y m h

/-- The layer's last draw is read by nothing: what failed before it fails behind it. -/
theorem c1 (P : H.s1.Nx × E → M → Prop) (hP : ∀ b β m, P (b, β) m → H.p1 b m) (b : H.s1.Nx) (m : M)
    (h : ¬ H.p1 b m) : cnt (fun β : E => P (b, β) m) ≤ 1 :=
  law_idle H.p1 P hP 1 b m h

end Head

/-! ### The last stages -/

/-- The parameters of the last stages, at the statements B4. -/
structure Foot (E : Type) [Field E] [Fintype E] (M B4 : Type) where
  /-- the gated products -/
  Gp : ProdL E
  st5 : B4 → Gp.St
  rd5 : M → Gp.J → E
  /-- the routed experts' gated products -/
  Rt : RoutedL E
  st6 : B4 → Rt.St
  rd6 : M → Rt.J → E
  /-- the weights -/
  Wt : WeightsL E
  st7 : B4 → Wt.St
  rd7 : M → Wt.J → E

namespace Foot
variable {M B4 : Type} (H : Foot E M B4)

/-- the routed experts' claims; the weights' claims -/
def C6 (b : B4) (m : M) : Prop := ∀ i, H.Rt.val (H.st6 b) (H.rd6 m) i = H.Rt.sh i (H.st6 b)
def C7 (b : B4) (m : M) : Prop := ∀ a, H.Wt.val (H.st7 b) (H.rd7 m) a = H.Wt.sh a (H.st7 b)

/-- the sumcheck of the gated products -/
def s5 : Stg E M B4 where
  L := H.Gp.toSum
  n := 0
  F := F₀ H.Gp.toSum.T.par
  cl := fun b _ => (H.Gp.tg (H.st5 b), H.st5 b)
  msg := H.rd5
  Lc := fun _ _ _ => True

/-- what is claimed before its last draw: the routed experts' claims and the weights' -/
def p5 (b : H.s5.Nx) (m : M) : Prop := H.C6 b.1.1 m ∧ H.C7 b.1.1 m

/-- the same before the join of the routed experts -/
def pR (x : H.s5.Nx × E) (m : M) : Prop := H.p5 x.1 m

/-- The layer's last draw is read by nothing. -/
theorem c5 (b : H.s5.Nx) (m : M) (h : ¬ H.p5 b m) : cnt (fun β : E => H.pR (b, β) m) ≤ 1 :=
  law_idle H.p5 H.pR (fun _ _ _ h1 => h1) 1 b m h

/-- the sumcheck of the routed experts' gated products -/
def s6 : Stg E M ((H.s5.Nx × E) × (Fin H.Rt.g → E)) where
  L := H.Rt.L.toSum
  n := 0
  F := F₀ H.Rt.L.toSum.T.par
  cl := fun y _ => (H.Rt.L.tg (H.st6 y.1.1.1.1, y.2), (H.st6 y.1.1.1.1, y.2))
  msg := H.rd6
  Lc := fun _ _ _ => True

/-- what is claimed before its last draw: the weights' claims -/
def p6 (b : H.s6.Nx) (m : M) : Prop := H.C7 b.1.1.1.1.1.1 m

/-- If what is claimed before the join fails, few points make the sumcheck's input claim true. -/
theorem cR (T : H.s6.Nx → M → Prop) (hT : ∀ b m, T b m → H.p6 b m) (x : H.s5.Nx × E) (m : M)
    (h : ¬ H.pR x m) :
    cnt (fun p : Fin H.Rt.g → E => ∃ r, H.s6.Lc (x, p) r m ∧
      H.s6.L.T.par.SumHolds (H.s6.cl (x, p) r) (H.s6.msg m) ∧ ∃ o, T (((x, p), r), o) m) ≤
      H.Rt.g * Fintype.card E ^ (H.Rt.g - 1) :=
  law_join H.Rt.g H.Rt.n H.Rt.hn
    (fun (x : H.s5.Nx × E) m i =>
      H.Rt.val (H.st6 x.1.1.1) (H.rd6 m) i - H.Rt.sh i (H.st6 x.1.1.1))
    (fun x m => H.C7 x.1.1.1 m) H.pR
    (fun z m => ∃ r, H.s6.Lc z r m ∧ H.s6.L.T.par.SumHolds (H.s6.cl z r) (H.s6.msg m) ∧
      ∃ o, T ((z, r), o) m)
    (fun _ _ h1 h2 => ⟨fun i => sub_eq_zero.1 (h1 i), h2⟩)
    (fun x p m h0 => by
      obtain ⟨r, _, h2, o, h3⟩ := h0
      have h4 := (H.Rt.link (H.st6 x.1.1.1, p) (H.rd6 m)).1
        ((H.Rt.L.sum_iff _ _ _).1 ((H.Rt.L.ksum_iff _ _ _).1
          ((psc_our_sum E H.Rt.L.toSum.T _ _).1 h2)))
      refine ⟨?_, hT _ m h3⟩
      simp only [mul_sub, sum_sub_distrib]
      rw [h4, sub_self]) x m h

/-- the same before the round that batches the claims on the weights -/
def pW (x : H.s6.Nx × E) (m : M) : Prop := H.p6 x.1 m

/-- The layer's last draw is read by nothing. -/
theorem c6 (b : H.s6.Nx) (m : M) (h : ¬ H.p6 b m) : cnt (fun β : E => H.pW (b, β) m) ≤ 1 :=
  law_idle H.p6 H.pW (fun _ _ _ h1 => h1) 1 b m h

/-- the merge of the weight claims -/
def s7 : Stg E M (((H.s6.Nx × E) × (Fin 0 → E)) × E) where
  L := H.Wt.L.toSum
  n := 0
  F := fun st => pick (H.Wt.L.toSum.T.par.vars st)
  cl := fun y _ => (H.Wt.L.tg (H.st7 y.1.1.1.1.1.1.1.1.1, y.2), (H.st7 y.1.1.1.1.1.1.1.1.1, y.2))
  msg := H.rd7
  Lc := fun _ _ _ => True

/-- If what is claimed before the batching round fails, few draws make the merge's input claim
true. -/
theorem cW (T : H.s7.Nx → M → Prop) (x : H.s6.Nx × E) (m : M) (h : ¬ H.pW x m) (s : Fin 0 → E) :
    cnt (fun β : E => ∃ r, H.s7.Lc ((x, s), β) r m ∧
      H.s7.L.T.par.SumHolds (H.s7.cl ((x, s), β) r) (H.s7.msg m) ∧ ∃ o, T ((((x, s), β), r), o) m) ≤
      H.Wt.n - 1 := by
  have hv : (fun a => H.Wt.val (H.st7 x.1.1.1.1.1.1.1) (H.rd7 m) a -
      H.Wt.sh a (H.st7 x.1.1.1.1.1.1.1)) ≠ 0 :=
    fun h0 => h fun a => sub_eq_zero.1 (congrFun h0 a)
  refine le_trans (cnt_mono fun β hβ => ?_) (ok_powers E H.Wt.n _ hv)
  obtain ⟨r, _, h2, _⟩ := hβ
  have h4 := (H.Wt.link (H.st7 x.1.1.1.1.1.1.1, β) (H.rd7 m)).1
    ((H.Wt.L.sum_iff _ _ _).1 ((H.Wt.L.ksum_iff _ _ _).1
      ((psc_our_sum E H.Wt.L.toSum.T _ _).1 h2)))
  simp only [mul_sub, sum_sub_distrib]
  rw [h4, sub_self]

/-- What the chain claims at B4, if T is claimed behind the gated products' sumcheck. -/
def todo5 (T : H.s5.Nx → M → Prop) (b : B4) (m : M) : Prop :=
  ∃ r, H.s5.Lc b r m ∧ H.s5.L.T.par.SumHolds (H.s5.cl b r) (H.s5.msg m) ∧ ∃ o, T ((b, r), o) m

/-- What the chain claims there gives the gated products' claim, the routed experts' claims and the
weights' claims. -/
theorem todo5_gives (b : B4) (m : M) (h : H.todo5 H.p5 b m) :
    H.Gp.Sg (H.st5 b) (H.rd5 m) ∧ H.C6 b m ∧ H.C7 b m := by
  obtain ⟨r, _, h2, o, h3⟩ := h
  exact ⟨(H.Gp.sum_iff _ _ _).1 ((H.Gp.ksum_iff _ _ _).1 ((psc_our_sum E H.Gp.toSum.T _ _).1 h2)),
    h3.1, h3.2⟩

/-- The chain's law on the sumcheck before B4, from a seam. -/
theorem o4 (Ow Out4 : B4 → M → Prop)
    (seam : ∀ b m, Ow b m → H.Gp.Sg (H.st5 b) (H.rd5 m) → H.C6 b m → H.C7 b m → Out4 b m)
    (b : B4) (m : M) (h1 : Ow b m) (h2 : H.todo5 H.p5 b m) : Out4 b m := by
  obtain ⟨g1, g2, g3⟩ := H.todo5_gives b m h2
  exact seam b m h1 g1 g2 g3

end Foot
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.Head.cL
#print axioms Cb.Pv.Lay.Head.cN
#print axioms Cb.Pv.Lay.Head.c1
#print axioms Cb.Pv.Lay.Foot.c5
#print axioms Cb.Pv.Lay.Foot.cR
#print axioms Cb.Pv.Lay.Foot.c6
#print axioms Cb.Pv.Lay.Foot.cW
#print axioms Cb.Pv.Lay.Foot.o4
