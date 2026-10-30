-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageFitsRest.lean: Johnson/Road/K4/StageFits.lean ENDS: the fifth and sixth stages
(the two product layers of the gated products) and the seventh (the merge). Glue over
`stgFits_ordE`, `append_reads` (StageFitsOne.lean) and `stgFits_plainAt` (StageFitsMore.lean). No
draw, no count.

  `fits5`: at every `FullPar` whose order e5 is the programs' range order: at a state st : St5: if
    st.pt reads A (of size lL + lF) and st.zt reads B: `StgFits` at
    `levelWs k (A ++ B) (orderRange k)`, k := lL + lF + lT.
  `fits6`: the like with the order e6: at a state (st : St6, jp the join's point): if jp reads A0
    (of size lL - 1), st.pt reads A (of size lFe) and st.rt reads B: at
    `levelWs k (A0 ++ A ++ B) (orderRange k)`, k := lL - 1 + (lFe + lT).
  `fits7`: the merge: plain, one scalar in the further round.

Limits. That the states' points read what K4 holds (the batched sumcheck's challenges turned round,
the lookup's token tail, the terms' end point, the drawn join point) are premises; that the value's
orders are the programs' is a premise (so at Johnson/Road/K4/ValueSlots.lean's value). `OutIs` at a
hearing is not concluded here.
-/
import Johnson.Road.K4.StageFitsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes
open OnBytes.Model (orderRange)
open OnBytes.Tie.Pv.Lay (StgFits eRange range_perm)
open OnBytes.Desc.First.P1 (gl levelWs plainWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)

variable [scl : Scl] {M Xs : Type}

/-- **The product layer of the gated products.** -/
theorem fits5 (P : FullPar Cb.Gl.E M Xs) (h9 : 9 ≤ P.D.lL + lF P.D + P.D.lT)
    (h5 : P.e5 = eRange _ h9) (st : St5 Cb.Gl.E P.D) (A B : Array E)
    (hA : A.size = P.D.lL + lF P.D) (hp : ∀ i, st.pt i = gl.val (A.getD i.val zeroE))
    (hz : ∀ i, st.zt i = gl.val (B.getD i.val zeroE)) :
    StgFits gl P.own.toOwn.tail.s5 st
      (levelWs (P.D.lL + lF P.D + P.D.lT) (A ++ B) (orderRange (P.D.lL + lF P.D + P.D.lT)))
      (P.D.lL + lF P.D + P.D.lT) 2 :=
  stgFits_ordE P.own.toOwn.tail.s5 st (orderRange _) (range_perm _ h9) _
    (Fin.append st.pt st.zt) rfl (fun _ => rfl)
    (fun j => by
      show some (Fin.append st.pt st.zt (P.e5 j)) = _
      rw [h5]
      rfl)
    (append_reads st.pt st.zt A B hA hp hz)

/-- **The product layer of the routed experts' gated products.** -/
theorem fits6 (P : FullPar Cb.Gl.E M Xs) (h9 : 9 ≤ P.D.lL - 1 + (lFe P.D + P.D.lT))
    (h6 : P.e6 = eRange _ h9) (st : St6 Cb.Gl.E P.D) (jp : Fin (P.D.lL - 1) → Cb.Gl.E)
    (A0 A B : Array E) (h0 : A0.size = P.D.lL - 1) (hA : A.size = lFe P.D)
    (hj : ∀ i, jp i = gl.val (A0.getD i.val zeroE))
    (hp : ∀ i, st.pt i = gl.val (A.getD i.val zeroE))
    (hr : ∀ i, st.rt i = gl.val (B.getD i.val zeroE)) :
    StgFits gl P.own.toOwn.tail.s6 (st, jp)
      (levelWs (P.D.lL - 1 + (lFe P.D + P.D.lT)) (A0 ++ A ++ B)
        (orderRange (P.D.lL - 1 + (lFe P.D + P.D.lT))))
      (P.D.lL - 1 + (lFe P.D + P.D.lT)) 2 :=
  stgFits_ordE P.own.toOwn.tail.s6 (st, jp) (orderRange _) (range_perm _ h9) _
    (Fin.append jp (Fin.append st.pt st.rt)) rfl (fun _ => rfl)
    (fun j => by
      show some (Fin.append jp (Fin.append st.pt st.rt) (P.e6 j)) = _
      rw [h6]
      rfl)
    (fun i => by
      rw [Array.append_assoc]
      exact append_reads jp _ A0 _ h0 hj (append_reads st.pt st.rt A B hA hp hr) i)

/-- **The merge.** -/
theorem fits7 (P : FullPar Cb.Gl.E M Xs) (st : P.own.toOwn.tail.s7.L.St) (k : ℕ)
    (hk : P.own.toOwn.tail.s7.L.S.k = k) : StgFits gl P.own.toOwn.tail.s7 st (plainWs k) k 1 :=
  stgFits_plainAt P.own.toOwn.tail.s7 st k hk rfl (fun _ => rfl) fun _ => rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fits5
#print axioms OnBytes.Road.K4.fits6
#print axioms OnBytes.Road.K4.fits7
