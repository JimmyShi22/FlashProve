-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageFitsRestFirst.lean: THE FIRST GROUP's twin of
Johnson/Road/K4/StageFitsRest.lean (its part at the typed chain): the fifth, sixth and seventh stage
fit.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `fits5F` · `fits6F` · `fits7F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StageFitsRest
import Johnson.Road.K4.StageFitsOneFirst

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
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **The product layer of the gated products.** -/
theorem fits5F (P : FullFPar Cb.Gl.E M Xs) (h9 : 9 ≤ P.D.lL + lF P.D + P.D.lT)
    (h5 : P.e5 = eRange _ h9) (st : St5 Cb.Gl.E P.D) (A B : Array E)
    (hA : A.size = P.D.lL + lF P.D) (hp : ∀ i, st.pt i = gl.val (A.getD i.val zeroE))
    (hz : ∀ i, st.zt i = gl.val (B.getD i.val zeroE)) :
    StgFits gl P.ownF.toOwn.tail.s5 st
      (levelWs (P.D.lL + lF P.D + P.D.lT) (A ++ B) (orderRange (P.D.lL + lF P.D + P.D.lT)))
      (P.D.lL + lF P.D + P.D.lT) 2 :=
  stgFits_ordE P.ownF.toOwn.tail.s5 st (orderRange _) (range_perm _ h9) _
    (Fin.append st.pt st.zt) rfl (fun _ => rfl)
    (fun j => by
      show some (Fin.append st.pt st.zt (P.e5 j)) = _
      rw [h5]
      rfl)
    (append_reads st.pt st.zt A B hA hp hz)

/-- **The product layer of the routed experts' gated products.** -/
theorem fits6F (P : FullFPar Cb.Gl.E M Xs) (h9 : 9 ≤ P.D.lL - 1 + (lFe P.D + P.D.lT))
    (h6 : P.e6 = eRange _ h9) (st : St6 Cb.Gl.E P.D) (jp : Fin (P.D.lL - 1) → Cb.Gl.E)
    (A0 A B : Array E) (h0 : A0.size = P.D.lL - 1) (hA : A.size = lFe P.D)
    (hj : ∀ i, jp i = gl.val (A0.getD i.val zeroE))
    (hp : ∀ i, st.pt i = gl.val (A.getD i.val zeroE))
    (hr : ∀ i, st.rt i = gl.val (B.getD i.val zeroE)) :
    StgFits gl P.ownF.toOwn.tail.s6 (st, jp)
      (levelWs (P.D.lL - 1 + (lFe P.D + P.D.lT)) (A0 ++ A ++ B)
        (orderRange (P.D.lL - 1 + (lFe P.D + P.D.lT))))
      (P.D.lL - 1 + (lFe P.D + P.D.lT)) 2 :=
  stgFits_ordE P.ownF.toOwn.tail.s6 (st, jp) (orderRange _) (range_perm _ h9) _
    (Fin.append jp (Fin.append st.pt st.rt)) rfl (fun _ => rfl)
    (fun j => by
      show some (Fin.append jp (Fin.append st.pt st.rt) (P.e6 j)) = _
      rw [h6]
      rfl)
    (fun i => by
      rw [Array.append_assoc]
      exact append_reads jp _ A0 _ h0 hj (append_reads st.pt st.rt A B hA hp hr) i)

/-- **The merge.** -/
theorem fits7F (P : FullFPar Cb.Gl.E M Xs) (st : P.ownF.toOwn.tail.s7.L.St) (k : ℕ)
    (hk : P.ownF.toOwn.tail.s7.L.S.k = k) : StgFits gl P.ownF.toOwn.tail.s7 st (plainWs k) k 1 :=
  stgFits_plainAt P.ownF.toOwn.tail.s7 st k hk rfl (fun _ => rfl) fun _ => rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fits5F
#print axioms OnBytes.Road.K4.fits6F
#print axioms OnBytes.Road.K4.fits7F
