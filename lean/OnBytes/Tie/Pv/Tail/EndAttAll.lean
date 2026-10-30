-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndAttAll.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the check of an attention sub-proof
(`Attention.run`, OnBytes/Model/Attention.lean), from the runs of the check's own calls alone.

Theorems with their proofs. OnBytes/Tie/Pv/Tail/EndAtt.lean leaves one premise on the steps of the
check: from the state after the start to the state that objectsF returns the arrays' shapes are
kept. Here that is shown, by the walks of OnBytes/Tie/Pv/Tail/EndWalkAtt.lean and EndWalkTail.lean
through the text of every routine that the check calls between the two.

Main names:
  `attention_shapes`: the messages, the commitment to the tables, the messages of the smallness
    test, the number of claims, the draw of the batching element, the sub-proof's claims and those
    of the smallness test keep the arrays' shapes.
  `rawRows_attention_runs`: `RawRows` as the theorems on objectsF ask it. Its premises are the
    plan's run and the runs of the calls of `Attention.run`, each as the routine applied to its
    states and the context.

Limits: the run must begin at the plan's state, and it must be a run on a view, not a dry run. The
world reads the four kinds of virtual row as sums of the arrays' entries (`ReadsRaw`,
OnBytes/Tie/Pv/Tail/EndRaw.lean). That a run of `Attention.run` is made of these runs is not shown
here.


-/
import OnBytes.Tie.Pv.Tail.EndWalkAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

/-- From the state after the start to the state that objectsF returns the shapes are kept. -/
theorem attention_shapes (P : Attention.Plan) (hd : Attention.Heard) (f : Attention.First)
    (trees : List Nat) (funs : Array HFun) (nLin used : Nat) (tl1 tlA tl : HTailF2)
    (L1 L2 L2' L3 L3' L4 : LinkCtx) (F1 F2 F3 F4 F5 F6 F7 F8 : Fork)
    (c1 c2 c2' c3 c4 c5 c5' c6 c6' c7 c7' c8 c8' c9 : Ctx)
    (hhear : Attention.hear P F1 c1 = .ok ((f, F2), c2))
    (hroot : rootInH trees L1 F2 c2' = .ok ((((), L2), F3), c3))
    (htr : tl1.transcript L2' F3 c4 = .ok (((tlA, L3), F4), c5))
    (hset : SubM.setPlanClaims nLin F4 c5' = .ok (((), F5), c6))
    (hbatch : t2Batch used L3' F5 c6' = .ok ((((), L4), F6), c7))
    (hclaims : Attention.claims P hd F6 c7' = .ok (((), F7), c8))
    (hobj : tlA.objectsF funs F7 c8' = .ok ((tl, F8), c9)) : ShapesKept F1 F8 := by
  have a1 := (inferInstance : Pres ShapesKept (Attention.hear P)).out _ _ _ _ _ hhear
  have a2 := (inferInstance : PresL ShapesKept (rootInH trees)).out _ _ _ _ _ _ _ hroot
  have a3 := (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ htr
  have a4 := (inferInstance : Pres ShapesKept (SubM.setPlanClaims nLin)).out _ _ _ _ _ hset
  have a5 := (inferInstance : PresL ShapesKept (t2Batch used)).out _ _ _ _ _ _ _ hbatch
  have a6 := (inferInstance : Pres ShapesKept (Attention.claims P hd)).out _ _ _ _ _ hclaims
  have a7 := (inferInstance : Pres ShapesKept (tlA.objectsF funs)).out _ _ _ _ _ hobj
  exact ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, from the runs of the check's own calls. -/
theorem rawRows_attention_runs (s0 : Attention.Seam) (P : Attention.Plan) (nU3 hb hbLine : Nat)
    (hd : Attention.Heard) (f : Attention.First) (trees : List Nat) (funs : Array HFun)
    (ns nLin used nMsg : Nat) (nU : Array Nat) (tl0 tl1 tlA tl : HTailF2)
    (L L1 L2 L3 L4 : LinkCtx) (F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 : Fork)
    (c c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : Ctx) (W : World K)
    (A : Nat → Nat → Nat → K) (hplan : s0.plan nU3 hb hbLine = .ok P.seam)
    (hstart : P.seam.start ns L P.seam.Fp c = .ok (((tl0, L1), F1), c1))
    (hhear : Attention.hear P F1 c1 = .ok ((f, F2), c2))
    (hroot : rootInH trees L1 F2 c2 = .ok ((((), L2), F3), c3))
    (hclosed : tl0.closeFuns funs = some tl1)
    (htr : tl1.transcript L2 F3 c4 = .ok (((tlA, L3), F4), c5))
    (hset : SubM.setPlanClaims nLin F4 c5 = .ok (((), F5), c6))
    (hbatch : t2Batch used L3 F5 c6 = .ok ((((), L4), F6), c7))
    (hclaims : Attention.claims P hd F6 c7 = .ok (((), F7), c8))
    (hobj : tlA.objectsF funs F7 c8 = .ok ((tl, F8), c9))
    (hnf : Attention.noFreeSlot nMsg F8 c9 = .ok (((), F9), c10))
    (hself : tl.selfTestF nU F9 c10 = .ok (((), F10), c11))
    (hco : tl.coefficientsF F10 c11 = .ok (((), F11), c12)) (hv : c12.ch.dry = false)
    (htile : tl.tileSelfTestF F11 c12 = .ok (((), F12), c13))
    (hW : ReadsRaw ρ tl funs F11 W A) : RawRows W tlA F8 funs (ρ.val F8.theta) A :=
  rawRows_attention ρ s0 P.seam nU3 hb hbLine ns nMsg nU funs tl0 tl1 tlA tl L L1 L2 L3
    F1 F3 F4 F7 F8 F9 F10 F11 F12 c c1 c4 c5 c8 c9 c10 c11 c12 c13 W A hplan hstart hclosed htr hobj
    (attention_shapes P hd f trees funs nLin used tl1 tlA tl L1 L2 L2 L3 L3 L4 F1 F2 F3 F4 F5 F6 F7
      F8 c1 c2 c2 c3 c4 c5 c5 c6 c6 c7 c7 c8 c8 c9 hhear hroot htr hset hbatch hclaims hobj)
    hnf hself hco hv htile hW

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.attention_shapes
#print axioms OnBytes.Tie.Pv.Tail.rawRows_attention_runs
