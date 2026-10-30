-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnEndsFirst.lean: the last stages of the chain of the first layers' sub-proof's own
rounds, filled from the records of the blocks, with the chain's laws on them proved.

As the second half of Cb/Pv/Lay/OwnEnds.lean, for the first group of layers: in the round that
batches the claims on the weights one scalar is sent (Cb/Pv/Lay/WeightsFirst.lean). It splits the
embedding's identity; the row on the sent scalar is claimed with it and rides on to the chain's end.

Main names:
  `FootFirst`: the parameters, at the statements B4 behind the inner products' sumcheck.
  `FootFirst.s5`, `p5`, `pR`, `s6`, `p6`, `pW`, `lW`, `s7`: the chain's letters.
  `FootFirst.c5`, `cR`, `c6`, `cW`: its laws. `FootFirst.todo5`, `FootFirst.o4`: as in OwnEnds.lean.

Limits: the seam in `o4` is a premise. No value of the chain's parameters is built here, and the
lemmas are not put together here. Nothing is said on the honest prover, on completeness or on zero
knowledge.
-/
import Cb.Pv.Lay.OwnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Cb.Pv.Att

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-- The parameters of the last stages in the first group, at the statements B4. -/
structure FootFirst (E : Type) [Field E] [Fintype E] (M B4 : Type) where
  /-- the gated products -/
  Gp : ProdL E
  st5 : B4 → Gp.St
  rd5 : M → Gp.J → E
  /-- the routed experts' gated products -/
  Rt : RoutedL E
  st6 : B4 → Rt.St
  rd6 : M → Rt.J → E
  /-- the weights, with the embedding's identity -/
  Wf : WFirstL E
  st7 : B4 → Wf.St
  rd7 : M → Wf.J → E

namespace FootFirst
variable {M B4 : Type} (H : FootFirst E M B4)

/-- the routed experts' claims; the weights' claims and the identity -/
def C6 (b : B4) (m : M) : Prop := ∀ i, H.Rt.val (H.st6 b) (H.rd6 m) i = H.Rt.sh i (H.st6 b)
def C7 (b : B4) (m : M) : Prop := H.Wf.Phi (H.st7 b) (H.rd7 m)

/-- the sumcheck of the gated products -/
def s5 : Stg E M B4 where
  L := H.Gp.toSum
  n := 0
  F := F₀ H.Gp.toSum.T.par
  cl := fun b _ => (H.Gp.tg (H.st5 b), H.st5 b)
  msg := H.rd5
  Lc := fun _ _ _ => True

/-- what is claimed before its last draw: the routed experts' claims, the weights' claims and the
identity -/
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

/-- what is claimed before its last draw: the weights' claims and the identity -/
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

/-- the statement B4 inside a statement before the weights' round -/
def b4 (x : H.s6.Nx × E) : B4 := x.1.1.1.1.1.1.1

/-- the row on the sent scalar -/
def lW (x : H.s6.Nx × E) (s : Fin 1 → E) (m : M) : Prop :=
  H.Wf.B ((H.st7 (H.b4 x), fun _ => s 0), 0) (H.rd7 m)

/-- the record's state behind the weights' round -/
def x7 (y : ((H.s6.Nx × E) × (Fin 1 → E)) × E) : H.Wf.St1 :=
  ((H.st7 (H.b4 y.1.1), fun _ => y.1.2 0), y.2)

/-- the merge of the weight claims -/
def s7 : Stg E M (((H.s6.Nx × E) × (Fin 1 → E)) × E) where
  L := H.Wf.L.toSum
  n := 0
  F := fun st => pick (H.Wf.L.toSum.T.par.vars st)
  cl := fun y _ => (H.Wf.L.tg (H.x7 y), H.x7 y)
  msg := H.rd7
  Lc := fun _ _ _ => True

/-- If what is claimed before the batching round fails and the row on the sent scalar holds, few
draws make the merge's input claim true. -/
theorem cW (T : H.s7.Nx → M → Prop) (x : H.s6.Nx × E) (m : M) (h : ¬ H.pW x m) (s : Fin 1 → E)
    (hs : H.lW x s m) :
    cnt (fun β : E => ∃ r, H.s7.Lc ((x, s), β) r m ∧
      H.s7.L.T.par.SumHolds (H.s7.cl ((x, s), β) r) (H.s7.msg m) ∧ ∃ o, T ((((x, s), β), r), o) m) ≤
      H.Wf.n := by
  refine le_trans (cnt_mono fun β hβ => ?_)
    (H.Wf.cnt_bad (H.st7 (H.b4 x)) (H.rd7 m) h fun _ => s 0)
  obtain ⟨r, _, h2, _⟩ := hβ
  exact ⟨hs, (H.Wf.L.sum_iff _ _ _).1 ((H.Wf.L.ksum_iff _ _ _).1
    ((psc_our_sum E H.Wf.L.toSum.T _ _).1 h2))⟩

/-- What the chain claims at B4, if T is claimed behind the gated products' sumcheck. -/
def todo5 (T : H.s5.Nx → M → Prop) (b : B4) (m : M) : Prop :=
  ∃ r, H.s5.Lc b r m ∧ H.s5.L.T.par.SumHolds (H.s5.cl b r) (H.s5.msg m) ∧ ∃ o, T ((b, r), o) m

/-- What the chain claims there gives the gated products' claim, the routed experts' claims, and
the weights' claims with the identity. -/
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

end FootFirst
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.FootFirst.c5
#print axioms Cb.Pv.Lay.FootFirst.cR
#print axioms Cb.Pv.Lay.FootFirst.c6
#print axioms Cb.Pv.Lay.FootFirst.cW
#print axioms Cb.Pv.Lay.FootFirst.o4
