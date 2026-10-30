-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanPull.lean: WITH CHALLENGES AS HASH BLOCKS THE MAKER's THREE HYPOTHESES ARE MET:
THE WIRING IS LAWFUL, NOTHING ELSE ASSUMED; "Nothing assumed" means here: not the statement on
codes; the hypotheses that stand in the statement itself are assumed. AND A CLOSED LIST WITH A ROUND
OF TWO TREES. After the library's Run/PlanPull.lean (planPull_unif, planPull_okg).
A LIMIT THAT WEIGHS (the library's own, Run/PlanQSLaws.lean's head): ChalUnif is an
equation of laws: uniform blocks give an EXACTLY uniform verifier message. With challenges as
SAMPLED VALUES (ck f) it is FALSE for every round that draws a field element: wqS_okg cannot be
applied there. It holds with challenges AS HASH BLOCKS (the library's ckP f, chalP f K: a round's
verifier message is its blocks; the view applies the sampler).
  AS TEXT      planPull_unif, planPull_okg (and their statements)
  LEFT TO THE LIBRARY   ckP, chalP, bsRound, map_firstBlocks_unif, planPull_fits (it is stated entry
                        by entry and names no RD)
  NEW          two_trees_okg: the wiring of the protocol on the one round twoD e k n (two roots;
               depths 21 | 12; columns of
               36 | 3 words) is LAWFUL, for every entry with at most 64 bits of work;
               two_trees_closed: at a closed entry, WITHOUT ANY HYPOTHESIS
  NOT SAID     planPull_cut | _view | _round | _shape (ties to the road without skeletons and to
               sampled values)

Terms: lean/GLOSSARY.md.

-/
import Run.PlanPull
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Prob _root_.Iop _root_.Run

namespace Spec

def planPull_unif : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD),
    (∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) → PQ.ChalUnif (ckP f) K (chalP f K) ds

def planPull_okg : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) (dec : _root_.Run.PQ.View → Bool),
    (∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) → (∀ d ∈ ds, d.entry.work ≤ 64) →
    (PQ.wqS (ckP f) K (chalP f K) ds dec).OKG

end Spec

theorem planPull_unif : Spec.planPull_unif := fun f K _ h d hd =>
  map_firstBlocks_unif (Dig 256) (fun _ => false) (bsRound f d.entry d.kind).b K (h d hd)

/-- what was drawn holds the entry's number of positions: from the library's planPull_fits -/
theorem planPull_drawn (f : _root_.Fmt.Fld) (ds : List PQ.RD) : PQ.DrawnFits (ckP f) ds :=
  fun d _ c => le_of_eq ((planPull_fits f d.entry d.kind).2 c)

theorem planPull_okg : Spec.planPull_okg := fun f K ds dec hK hw =>
  PQ.wqS_okg (ckP f) K (chalP f K) ds dec (planPull_unif f K ds hK) (planPull_drawn f ds) hw

/-- A LAWFUL WIRING, MADE BY THE MAKER, OF A PROTOCOL WITH A ROUND OF TWO TREES. -/
theorem two_trees_okg (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (n : ℕ)
    (hw : e.work ≤ 64) (dec : _root_.Run.PQ.View → Bool) :
    (PQ.wqS (ckP f) (bsRound f e k).b (chalP f _) [PQ.twoD e k n] dec).OKG :=
  planPull_okg f _ _ dec
    (fun d hd => by rw [List.mem_singleton.1 hd]; exact Nat.le_refl _)
    (fun d hd => by rw [List.mem_singleton.1 hd]; exact hw)

/-- the same at a closed entry: no hypothesis is left -/
theorem two_trees_closed (f : _root_.Fmt.Fld) (dec : _root_.Run.PQ.View → Bool) :
    (PQ.wqS (ckP f) (bsRound f { name := "SEND", roots := 2 } .nothing).b (chalP f _)
      [PQ.twoD { name := "SEND", roots := 2 } .nothing 0] dec).OKG :=
  two_trees_okg f _ _ 0 (Nat.zero_le _) dec

end TypedOracleCompiler.Run
