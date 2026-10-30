-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnTest.lean: the own rounds of a layers' sub-proof with the refusal of a coefficient 0
behind them.

The programs refuse a proof in which the coefficient drawn in the sumcheck of the terms is 0; the
model that is run on bytes keeps the name of that fault and refuses at the run's end. A chain
(Cb/Pv/Att/Chain.lean) has no stage that refuses, so in Cb/Pv/Lay/OwnAll.lean "the coefficient is
not 0" stands among what is owed at the end. Here one test of the last statement is put behind the
whole chain. What fails it is refused, and the claim leaves the last claim.

Main names:
  `last_mono_at`: what a chain claims at its end grows with what is claimed of its first
    statement; only the first statement inside the last one matters.
  `LayTail.withOw3`, `LayTail.acc2`, `LayTail.last_eq`, `LayTail.last_withOw3`: the letters with
    another claim owed of the sumcheck of the terms; the last claim written from that sumcheck on;
    if the new owed claim gives the old one at the statement inside the last one, the new last
    claim gives the old one.
  `tested R t`: a reduction, then the refusal of every last statement that fails t.
  `LayVO.epsOK`, `LayVOF.epsOK`: the test. `toOwn0`: the letters in which of the terms' output
    claims the rows on the end values alone are owed.
  `LayVO.knowAt_tested`, `LayVOF.knowAt_tested`: knowledge soundness of the tested reduction, from
    the same claim at the start to `toOwn0.ch.Last Dn`, with the chain's own errors.

Limits: those of Cb/Pv/Lay/OwnAll.lean, but for the claim on the coefficient. An honest prover is
refused where the coefficient 0 is drawn: nothing is said on completeness. The test is decided by
classical logic: no program is given for it here.
-/
import Cb.Pv.Lay.OwnAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att

noncomputable section

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-- What a chain claims at its end grows with what is claimed of its first statement; only the
first statement inside the last one matters. -/
theorem last_mono_at : ∀ {X : Type} (c : Ch E M X) (e : c.End) (Dn Dn' : X → M → Prop) (m : M),
    (Dn (c.back e) m → Dn' (c.back e) m) → c.Last Dn e m → c.Last Dn' e m
  | _, .done _, _, _, _, _, h, h1 => h h1
  | _, .ride _ _ _ _ _ _ _ next, e, _, _, m, h, h1 =>
    last_mono_at next e _ _ m (fun g => ⟨h g.1, g.2⟩) h1
  | _, .draw _ _ _ next, e, _, _, m, h, h1 => last_mono_at next e _ _ m h h1
  | _, .send _ _ _ _ _ next, e, _, _, m, h, h1 =>
    last_mono_at next e _ _ m (fun g => ⟨h g.1, g.2⟩) h1

/-- The letters with another claim owed of the sumcheck of the terms. -/
def LayTail.withOw3 {X : Type} (T : LayTail E M X) (ow : T.s3.Nx → M → Prop) : LayTail E M X :=
  { T with ow3 := ow }

/-- What has been gathered for the last claim behind the sumcheck of the products of the rows. -/
def LayTail.acc2 {X : Type} (T : LayTail E M X) (Dn : X → M → Prop) (b : T.s2.Nx) (m : M) : Prop :=
  ((((Dn b.1.1.1.1.1.1.1.1.1.1 m ∧ T.lL b.1.1.1.1.1.1.1.1.1.1 b.1.1.1.1.1.1.1.1.1.2 m) ∧
      T.s1.Lc b.1.1.1.1.1.1.1 b.1.1.1.1.1.1.2 m ∧ T.ow1 b.1.1.1.1.1 m) ∧
    T.lP b.1.1.1.1 b.1.1.1.2 m) ∧ T.s2.Lc b.1.1 b.1.2 m ∧ T.ow2 b m)

/-- The last claim, from the sumcheck of the terms on. -/
theorem LayTail.last_eq {X : Type} (T : LayTail E M X) (Dn : X → M → Prop) :
    T.ch.Last Dn =
      T.ch4.Last fun b m => T.acc2 Dn b.1.1 m ∧ T.s3.Lc b.1.1 b.1.2 m ∧ T.ow3 b m := rfl

/-- If, at the statement behind the terms that lies inside the last one, the new owed claim gives
the old one, the new last claim gives the old one. -/
theorem LayTail.last_withOw3 {X : Type} (T : LayTail E M X) (ow : T.s3.Nx → M → Prop)
    (Dn : X → M → Prop) (e : T.ch.End) (m : M)
    (h : ow (T.ch4.back e) m → T.ow3 (T.ch4.back e) m)
    (h1 : (T.withOw3 ow).ch.Last Dn e m) : T.ch.Last Dn e m := by
  have h2 : T.ch4.Last (fun b m => T.acc2 Dn b.1.1 m ∧ T.s3.Lc b.1.1 b.1.2 m ∧ ow b m) e m := h1
  rw [T.last_eq Dn]
  exact last_mono_at T.ch4 e
    (fun b m => T.acc2 Dn b.1.1 m ∧ T.s3.Lc b.1.1 b.1.2 m ∧ ow b m)
    (fun b m => T.acc2 Dn b.1.1 m ∧ T.s3.Lc b.1.1 b.1.2 m ∧ T.ow3 b m) m
    (fun g => ⟨g.1, g.2.1, h g.2.2⟩) h2

/-! ### The test behind the chain -/

open Classical in
/-- A reduction, then the refusal of every last statement that fails t. -/
def tested {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) (t : Xo → Prop) :
    IOR Xi Ei Xo Eo :=
  R.post (fun x => if t x then some x else none) (ExtMap.id Eo)

namespace LayVO
variable {X : Type} (A : LayVO E M X)

/-- The coefficient drawn in the sumcheck of the terms, read off the last statement, is not 0. -/
def epsOK (e : A.toOwn.ch.End) : Prop := (A.V.toTail.ch4.back e).2.eps ≠ 0

/-- The letters in which of the terms' output claims the rows on the end values alone are owed. -/
def toOwn0 : LayOwn E M X where
  gT := A.gT
  eT := A.gT * Fintype.card E ^ (A.gT - 1)
  pT := A.pT
  tail := A.V.toTail.withOw3 fun b m => ∀ a, A.V.Tm.toSum.T.par.EHolds b.2 (A.V.rd3 m) a

/-- Knowledge soundness of the own rounds with the refusal of a coefficient 0 behind them, as the
programs have it: "the coefficient is not 0" is no longer claimed at the end. The errors are the
chain's. -/
theorem knowAt_tested {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (tested (A.toOwn.ch.R Ex) A.epsOK) (jt A0 pr fun x m => Dn x m ∧ A.pT x m)
      (jt A0 (fun e => pr (A.toOwn.ch.back e)) (A.toOwn0.ch.Last Dn)) (fun _ _ _ wp => wp)
      (A.toOwn.ch.eps Ex) := by
  classical
  exact knowAt_test (A.knowAt Ex A0 pr Dn) A.epsOK (fun _ _ h _ => h) fun e y w _ ht hw =>
    ⟨hw.1, A.V.toTail.last_withOw3 _ (fun b m => Dn b.1 m) e w.1 (fun g => ⟨ht, g⟩) hw.2⟩

end LayVO

namespace LayVOF
variable {X : Type} (A : LayVOF E M X)

/-- The coefficient drawn in the sumcheck of the terms, read off the last statement, is not 0. -/
def epsOK (e : A.toOwn.ch.End) : Prop := (A.V.toTail.ch4.back e).2.eps ≠ 0

/-- The letters in which of the terms' output claims the rows on the end values alone are owed. -/
def toOwn0 : LayOwnFirst E M X :=
  embFirst A.gT (A.gT * Fintype.card E ^ (A.gT - 1)) A.pT A.gA A.gB A.e A.Q
    (A.V.toTail.withOw3 fun b m => ∀ a, A.V.Tm.toSum.T.par.EHolds b.2 (A.V.rd3 m) a)

/-- The same for the first sub-proof. -/
theorem knowAt_tested {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (tested (A.toOwn.ch.R Ex) A.epsOK) (jt A0 pr fun x m => Dn x m ∧ A.pT x m)
      (jt A0 (fun e => pr (A.toOwn.ch.back e)) (A.toOwn0.ch.Last Dn)) (fun _ _ _ wp => wp)
      (A.toOwn.ch.eps Ex) := by
  classical
  exact knowAt_test (A.knowAt Ex A0 pr Dn) A.epsOK (fun _ _ h _ => h) fun e y w _ ht hw =>
    ⟨hw.1, A.V.toTail.last_withOw3 _ (fun b m => Dn b.1.1.1 m) e w.1 (fun g => ⟨ht, g⟩) hw.2⟩

end LayVOF

end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.LayVO.knowAt_tested
#print axioms Cb.Pv.Lay.LayVOF.knowAt_tested
#print axioms Cb.Pv.Lay.last_mono_at
#print axioms Cb.Pv.Lay.LayTail.last_withOw3
