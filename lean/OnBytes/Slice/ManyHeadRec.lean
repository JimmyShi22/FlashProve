-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyHeadRec.lean: the program's link, for tables with a record, run on the view of a
written transcript whose rounds after the batching are a chain of any number of stages: from the
start to the joint before the first fold.

OnBytes/Slice/BlkHeadRec.lean proves that the link's steps and the batching lead from the start of a
run to the joint before the first fold (`headRuns_atR`), for a view whose first six rounds are the
written ones, whatever rounds follow. This file says so at the written link of a chain of stages
(OnBytes/Slice/ManyView.lean: `manyTr`).


Main theorem.
 `headRuns_manyR`   the joint after the head, at the written link's view. The claim is the sum of
                    the link's rows, the two records' rows among them
                    (OnBytes/Slice/RowsXRec.lean), under the powers of the element that the batching
                    round draws. The rounds still to be read are the chain's.
What is asked: what `headRuns_atR` asks: public facts on sizes, shapes and draws, that the two keys
hold the records of r if they pass the program's two tests on keys, and `HeadKeepsR`.
Not claimed. `HeadKeepsR` stays a hypothesis. Nothing on the rounds after the batching. Nothing on
the dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkHeadRec
import OnBytes.Slice.ManyView

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (LinkShape IoppStage)

/-- The link's steps and the batching lead from the start of a run on the view of a written
transcript to the joint before the first fold. r: a pair of records with n answers each, which the
two keys hold if they pass the program's two tests on keys. The claim there is the sum of the link's
rows under the powers of the element that the batching round draws, and the rounds still to be read
are the chain's, block by block. `HeadKeepsR` is a hypothesis (`hkeep`). -/
theorem headRuns_manyR (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
    (st1 : IoppStage) (s : Start) (K : Codes) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (d1 d2 d3 d4 d5 dA : PQ.RD) (c : Chain (S.sg t₀))
    (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
    (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg)
    (c5 : (wRound d5).Chal) (mA : (wRound dA).Msg) (cA : (wRound dA).Chal) (b : c.Bl)
    (xs : List PQ.XO) (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str)
    (hs : s.samples = 1) (hi0 : first.item = 0) (hi1 : further.item = 1) (hpads : 3 * n ≤ S.P.T.l)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (hS : LinkSizes S Λ s.st.codes) (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1))
    (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hkeep : HeadKeepsR Λ first further
      (startCtx s (PQ.viewX (ckP .two) _ S.P.T.a xs y
        (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)))
      (PQ.viewX (ckP .two) _ S.P.T.a xs y
        (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)) K S.P.Z.l Tie) :
    HeadRuns Λ first further st1
      (startCtx s (PQ.viewX (ckP .two) _ S.P.T.a xs y
        (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)))
      (GroupAt (PQ.viewX (ckP .two) _ S.P.T.a xs y
        (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)) K 1 (S.sg t₀)
        (sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
          (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
            (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
          (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
            (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
        (c.rvs b) Tie) :=
  headRuns_atR S t₀ lg n Λ first further st1 s _ K Tie d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5
    c5 mA cA _ r y
    (view_rounds_many d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b S.P.T.a xs y)
    (fun o ho => opened_stored _ S.P.T.a xs y _ o ho) hs hi0 hi1 hpads hK0 hK1 hS hF hd hn0 hn1
    hkeep

end OnBytes.Slice
