-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotParsView.lean: the public numbers of the jobs of the two lots of the kind
K1, written through the library's views of the segments.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Z is any public part and G any ground.
  parsOf q gp vs w  a list of public numbers: the opening's at q and gp; for each entry of vs that
                    has a view, the reads' and the digits' at the view's two pieces; then the list
                    w.
  lotPars_view      The public numbers of lotPars Z G (LotsTest.lean) are parsOf at G.first, K1.gpOf
                    Z, the list of the segments' views (segView,
                    Johnson/AtFull/Desc/Lots/K1/Twin.lean), and the numbers at the request's own
                    table where the shape has such a message.
  parsOf_full       If q has the library's full-size codes and shapes (K1.LikeFull q), parsOf at q
                    is parsOf at the library's placeholder K1.qFull.
  lotsReadsB_map    The test lotsReadsB reads of an entry of lotPars its public numbers alone.
  laterPars_view    the step for the reads and digits.

How it fits. The library proves that in the goals' scope the list of views is a written value
(view_in_scope, Johnson/AtFull/Desc/Lots/K1/View.lean). So these laws carry the jobs' public numbers
to closed terms, at which ReadsAtWritten.lean evaluates the test on queried positions. Statements on
public data: no distribution is named. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits. General laws on lists; no public file is named.
-/
import Johnson.SendSim.Seat.LotsTest
import Johnson.AtFull.Desc.Lots.K1.Twin

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open Johnson.AtFull.Desc.K1Lot (View segView)

/-- The public numbers of the jobs of the two lists, of the first chain's parameters, the plan's two
numbers, the segments' views and the numbers at the request's own table. -/
def parsOf (q : Params.First) (gp : _root_.Desc.Plain.GPar) (vs : List (Nat × Option View))
    (w : List K1.Par) : List K1.Par :=
  K1.firstPar q gp ::
    ((vs.flatMap fun y =>
      match y.2 with
      | none => []
      | some v => [K1.parLater q gp y.1 v.1 1, K1.parLater q gp y.1 v.2.1 2]) ++ w)

/-- The reads' and digits' public numbers, through the segments' views. -/
theorem laterPars_view (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    laterPars Z G =
      (G.built.toList.zipIdx.map fun x => (x.2, segView G x)).flatMap fun y =>
        match y.2 with
        | none => []
        | some v => [K1.parLater G.first (K1.gpOf Z) y.1 v.1 1,
            K1.parLater G.first (K1.gpOf Z) y.1 v.2.1 2] := by
  unfold laterPars
  rw [List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨Y, l⟩ := x
  unfold segView
  rcases hn : K1.linkNumbers G Y with _ | ⟨pr, pd, reads, digits⟩
  · simp only [hn]
    rfl
  · simp only [hn]
    rfl

/-- **The public numbers of the jobs of the two lists.** -/
theorem lotPars_view (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (lotPars Z G).map (·.1) =
      parsOf G.first (K1.gpOf Z) (G.built.toList.zipIdx.map fun x => (x.2, segView G x))
        ((linMessageW Z.first.lin).map fun msg => K1.parW Z.first (wGp Z) 4 msg).toList := by
  unfold lotPars parsOf
  rw [List.map_append, List.map_cons, List.map_map, ← laterPars_view, List.cons_append]
  congr 2
  · exact List.map_id' _
  · cases linMessageW Z.first.lin <;> rfl

/-- Parameters with the library's full-size codes and shapes give the numbers at the library's
placeholder. -/
theorem parsOf_full {q : Params.First} (h : K1.LikeFull q) (gp : _root_.Desc.Plain.GPar)
    (vs : List (Nat × Option View)) (w : List K1.Par) :
    parsOf q gp vs w = parsOf K1.qFull gp vs w := by
  unfold parsOf
  rw [K1.firstPar_full h]
  congr 2
  refine List.flatMap_congr fun y _ => ?_
  cases y.2 with
  | none => rfl
  | some v => simp only [K1.parLater_full h]

/-- The test over the two lists reads the jobs' public numbers alone. -/
theorem lotsReadsB_map {Xi : Type} (F : FileDescription Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    lotsReadsB F Z G = ((lotPars Z G).map (·.1)).all fun P =>
      readsWithinB F P (treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != P.place))) := by
  unfold lotsReadsB
  rw [List.all_map]
  rfl

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.lotPars_view
#print axioms OnBytes.SendSim.Seat.parsOf_full
#print axioms OnBytes.SendSim.Seat.lotsReadsB_map
