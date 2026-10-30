-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlmCode.lean: THE LAST TABLE's BOOK-KEEPING's OWN DEFINITIONS WITH CODE, ALONE
IN ONE FILE WITH LIGHT IMPORTS, SO THAT A WALK CAN LOAD THEM AND WHAT IT EVALUATES IS THE VERY
CONSTANT OF THE THEOREMS: four definitions, moved unturned [by program] out of LastLayerS.lean
(`besideS`), LastTreeO.lean (`treeOB`, `yTree`) and LastRowZeroB.lean (`endedX`), which
import this file.
  THE TERM THAT THE LAW CONCLUDES AT: PLm := `besideS (fillAt p R (fun q => firstOfS (get q).2)
    (endedX X)) (yTree p.codes p.S)` at p := `ToldDesc.p14At Z`, R := the seated own test's declared
    rounds; `fillAt`: Johnson/Desc/Last/ShapeAt.lean. PLm.shape k q e s is a Bool
    with code.
No theorem. Nothing on soundness.
-/
import Johnson.Desc.Last.ShapeAt
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (S₃ SharedOut sharedOfEnd)
open _root_.Desc.K14 (St)

/-- **The layer**: a test on the last chain's own state, border by border, beside the book-keeping.
-/
def besideS {S₂ S₃' Q : Type} (PL : PromMeaningL S₂ S₃' Q) (Y : ℕ → S₃' → Bool) :
    PromMeaningL S₂ S₃' Q where
  shape := fun k q e s => PL.shape k q e s && Y k s
  nothingLeft := PL.nothingLeft

/-- **The tree of Omega's copy has the shape that the verifier's own layout makes of the plan's
notice.** -/
def treeOB (cs : Codes) (S : LinShape) (s : S₃) : Bool :=
  match layTrees cs #[⟨S.omega, S.omegaLeafClass⟩], s.book.place[s.loc.omega]? with
  | some lay, some q =>
    match s.book.trees[q.1]? with
    | some T => decide (T.shape = lay.shapes.getD 0 {})
    | none => false
  | _, _ => false

/-- The layer: that test at borders 1 and 2. -/
def yTree (cs : Codes) (S : LinShape) : ℕ → S₃ → Bool :=
  fun k s => (k != 1 && k != 2) || treeOB cs S s

/-- K14's end carried by `sharedOfEnd`, where the layer's test says yes. -/
def endedX (X : St → Bool) : St → Option SharedOut :=
  fun d => if X d = true then (_root_.Desc.K14.ended d).map sharedOfEnd else none

end LLT25
