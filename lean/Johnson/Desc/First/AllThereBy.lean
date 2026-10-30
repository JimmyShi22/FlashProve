-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/AllThereBy.lean: THE TEST `allThere` (Johnson/Desc/First/AllThere.lean) AS A
FUNCTION OF THE FIVE THINGS THAT IT READS OF THE LAYERS' DATA: so that it can be evaluated at
public parameters without a whole structure of data. Definitions with code, and that each IS the
elder. No Mathlib.
  `dataThereBy nsOf nextOf links d5 X`, `notThereBy`, `allThereBy`; `dataThere_by`, `notThere_by`,
    `allThere_by`: each elder at D is its twin at D.nsOf, D.nextOf, D.links, D.d5, D.d3.X.
Limits: those of AllThere.lean. FIVE LETTERS STAND WHERE ONE STRUCTURE IS MEANT. Nothing on
soundness.

-/
import Johnson.Desc.First.AllThere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Look (k3SortAt placeAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open H2K5.Door (K5Data)

/-- The option that the answering part reads at the item is some. -/
def dataThereBy (nsOf nextOf : Nat → Option Nat) (links : List ModelPart) (d5 : K5Data)
    (X : OnBytes.Model.Verify.Public) : Pub → Bool
  | .freeAbove m => (nsOf m).isSome
  | .callerIn m =>
    if isLay links m then (nextOf m).isSome
    else if d5.isAtt m then (d5.first? m).isSome
    else true
  | .lookIn m pc =>
    (k3SortAt X m pc).all fun dg => (placeAt X m dg).any fun p => p.shape.isSome
  | .lookOut m pc =>
    (k3SortAt X m pc).all fun dg => (placeAt X m dg).any fun p => p.shape.isSome
  | .more (some m) name =>
    if d5.isAtt m && (name == "K5.okAt" || name == "K5.plain") then (d5.W.A[m / 2]?).isSome
    else true
  | _ => true

theorem dataThere_by (D : PubData) (q : Pub) :
    dataThere D q = dataThereBy D.nsOf D.nextOf D.links D.d5 D.d3.X q := by
  cases q with
  | more sg name => cases sg <;> rfl
  | _ => rfl

def notThereBy (nsOf nextOf : Nat → Option Nat) (linksD : List ModelPart) (d5 : K5Data)
    (X : OnBytes.Model.Verify.Public) (M : More) (links : List ModelPart) (ps : List Place) :
    List (Nat × Pub) :=
  (askedAt M links ps).zipIdx.flatMap fun x =>
    (x.1.filter fun q => !dataThereBy nsOf nextOf linksD d5 X q).map fun q => (x.2, q)

def allThereBy (nsOf nextOf : Nat → Option Nat) (linksD : List ModelPart) (d5 : K5Data)
    (X : OnBytes.Model.Verify.Public) (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (askedAt M links ps).all fun Q => Q.all (dataThereBy nsOf nextOf linksD d5 X)

theorem notThere_by (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) :
    notThere D M links ps = notThereBy D.nsOf D.nextOf D.links D.d5 D.d3.X M links ps := by
  unfold notThere notThereBy
  simp only [dataThere_by]

theorem allThere_by (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) :
    allThere D M links ps = allThereBy D.nsOf D.nextOf D.links D.d5 D.d3.X M links ps := by
  unfold allThere allThereBy
  rw [show dataThere D = dataThereBy D.nsOf D.nextOf D.links D.d5 D.d3.X from
    funext (dataThere_by D)]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.dataThere_by
#print axioms VerifiableInference.Desc.First.notThere_by
#print axioms VerifiableInference.Desc.First.allThere_by
