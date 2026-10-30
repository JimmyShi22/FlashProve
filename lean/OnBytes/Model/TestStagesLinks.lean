-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestStagesLinks.lean: small cases for OnBytes/Model/StagesLinks.lean.

A chain of two links is made by hand: G0, for one group of layers, and the head H, which reads one
matrix of G0. The cases test the order of the links, the declared arrays, the comparison of given
links and numbers with them, the weight table's layout, placedAlike and samePlan. An altered copy
must be refused, with the expected name where the test gives one. The first three are tested again
with the numbers of a small configuration of five links, spelled out here. No proof is read here, so
the sub-proofs' checks are empty.

The program does not import this file.
-/
import OnBytes.Model.StagesLinks

namespace OnBytes.Model.Stages.Test

open Params (ReqLink ReqMessage ReqArray LaidBlock ReqLayout)

/-- An array of a sub-proof's plan with R rows and K columns. -/
def tree (R K : Nat) : HTree := { R := R, K := K }

/-- The plan of G0. Matrix 0 is read by G0 alone, matrix 1 by the head too. The list of arrays:
the two symbol arrays, U3 over the extension field, ZZ, BZ. -/
def planG : SubPlanH :=
  { tl := { pkMat := #[0], pxMat := #[1], gtTree := #[0, 1],
            ix := { PK := #[0], TX := #[1], U := #[none, none, some 2, none], ZZ := 3, BZ := 4 } }
    Fp := { trees := #[tree 2 4, tree 3 8, tree 1 16, tree 5 4, tree 1 32] }
    Tp := { nt := #[{}, {}, { ec := 3 }, {}, {}] }
    ns := 7, NCL := 2, run := pure none }

/-- The plan of the head. Its array 1 is read from the group `owner`. With rootIndex 1 it is matrix
1 of G0, which is number 1 among the symbol arrays of G0. -/
def planH (owner rootIndex : Option Nat := some 0) (K : Nat := 8) : SubPlanH :=
  { tl := { pkMat := #[0], gtTree := #[0],
            ix := { PK := #[0], FT := #[1], ZZ := 2, BZ := 3 }
            plFor := #[{ owner := owner, rootIndex := rootIndex }] }
    Fp := { trees := #[tree 1 2, tree 3 K, tree 5 2, tree 1 32] }
    Tp := { nt := #[{}, { foreign := true }, {}, {}] }
    ns := 3, NCL := 1, run := pure none }

/-- The two links, from a plan of the head. -/
def linksOf (H : SubPlanH) : Array LinkH := ((listLinksH 1 false #[planG] #[] H).toOption).getD #[]

/-- The two links. -/
def links : Array LinkH := linksOf (planH (some 0) (some 1))

/-- The name of a refusal; the empty string for none. -/
def why {α : Type} : Except String α → String
  | .ok _ => ""
  | .error e => e

/-! ## The order -/

#guard links.toList.map (fun X => (X.name, X.gid, X.kind, X.fv)) ==
  [("G0", 1, 0, true), ("H", 2, 2, true)]
#guard ((listLinksH 2 true #[planG, planG] #[planG, planG] planG).toOption.getD #[]).toList.map
    (fun X => (X.name, X.gid, X.kind, X.g, X.fv)) ==
  [("G0", 1, 0, 0, true), ("A0", 4, 1, 0, false), ("G1", 2, 0, 1, true), ("A1", 5, 1, 1, false),
   ("H", 3, 2, 0, true)]
#guard why (listLinksH 2 false #[planG] #[] planG) == "plan-link"
#guard why (headLast links) == ""
#guard why (headLast links.reverse) == "plan-head"
#guard why (headLast (links.extract 0 1)) == "plan-head"
#guard why (headLast (links.map fun X => { X with gid := 1 })) == "plan-link"
#guard why (linksCount links) == ""
#guard why (linksCount (links.extract 0 1)) == "plan-shape"
#guard why (linksCount (Array.replicate 65 (links.getD 0 (planG.link "" 0 0 0 true)))) ==
  "plan-shape"
#guard layersLink true 3 == 6 && layersLink false 3 == 3
#guard onTable links == 2 && why (tableRows links 1) == "" && why (tableRows links 2) == "plan-link"

/-! ## The declared arrays -/

/-- What the two links must declare. -/
def expected : Array FrameLink :=
  #[{ name := "G0"
      moment := #[#[{ name := "M0", rows := 2, columns := 4 },
                    { name := "M1", rows := 3, columns := 8, life := 1 }],
                  #[{ name := "U3", rows := 1, columns := 16, overE := true }],
                  #[{ name := "ZZ", rows := 5, columns := 4 },
                    { name := "BZ", rows := 1, columns := 32 }]] },
    { name := "H"
      moment := #[#[{ name := "M0", rows := 1, columns := 2 }],
                  #[{ name := "ZZ", rows := 5, columns := 2 },
                    { name := "BZ", rows := 1, columns := 32 }]] }]

#guard (declareLinks links 1 false).toOption.map (·.2) == some expected
#guard (declareLinks links 1 false).toOption.map (fun x => x.1.toList.map (·.arrayOf)) ==
  some [#[(0, "M0"), (0, "M1"), (0, "U3"), (0, "ZZ"), (0, "BZ")],
        #[(1, "M0"), (0, "M1"), (1, "ZZ"), (1, "BZ")]]
-- the owner's matrix 0 is not listed as read by others
#guard why (declareLinks (linksOf (planH (some 0) (some 0))) 1 false) == "plan-fold-source"
#guard why (declareLinks (linksOf (planH (some 0) (some 2))) 1 false) == "plan-fold-source"
#guard why (declareLinks (linksOf (planH (some 0) none)) 1 false) == "plan-fold-source"
-- no such group of layers; no owner
#guard why (declareLinks (linksOf (planH (some 1) (some 1))) 1 false) == "plan-fold-source"
#guard why (declareLinks (linksOf (planH none (some 1))) 1 false) == "plan-fold-source"
-- the reader works with another size
#guard why (declareLinks (linksOf (planH (some 0) (some 1) 16)) 1 false) == "plan-fold-source"
-- an array of the list that gets no name; then one that is named twice (the other then gets no
-- name; both tests refuse as plan-link, so the guard does not tell which of them has refused)
#guard why (declareLinks (links.modify 0 fun X =>
    { X with Tp := { X.Tp with nt := X.Tp.nt.push {} } }) 1 false) == "plan-link"
#guard why (declareLinks (links.modify 0 fun X =>
    { X with tl := { X.tl with ix := { X.tl.ix with BZ := 3 } } }) 1 false) == "plan-link"

/-! ## A given link against its declaration -/

/-- An oracle message of a link. -/
def msg (rows deg masks moment life : Nat) : ReqMessage :=
  { shape := { code := 0, mainRows := rows, mainDeg := deg, maskRows := masks,
               maskCode := if masks == 0 then noId else 0, answers := 1 }
    leafClass := 0, moment := moment, life := life }

/-- An array with one block. Of a block the comparison reads only its four logarithms. -/
def arr (name : String) (message sizeI sizeC : Nat) : ReqArray :=
  { name := name, message := message, sizeI := sizeI, sizeC := sizeC
    blocks := [{ firstI := 0, firstC := 0, firstRow := 0, firstPlace := 0, bitsI := 0, bitsC := 0,
                 rowBits := 0, placeBits := 0, iIsLow := true }] }

/-- The messages of G0: two at the first moment, the second of them kept for one link. -/
def givenG : ReqLink := ⟨0, [msg 4 1 1 0 0, msg 4 1 0 0 1, msg 1 3 0 1 0, msg 8 1 0 2 0]⟩

/-- The arrays of G0. -/
def arraysG : List ReqArray :=
  [arr "M0" 0 2 4, arr "M1" 1 3 8, arr "U3" 2 1 16, arr "BZ" 3 1 32, arr "ZZ" 3 5 4]

/-- The declaration of G0. -/
def declaredG : FrameLink := expected.getD 0 {}

#guard linkHeld declaredG givenG arraysG
-- kept for fewer links than the reader needs
#guard !linkHeld declaredG givenG (arr "M1" 0 3 8 :: arraysG.filter (·.name != "M1"))
-- another size; another moment; the wrong field
#guard !linkHeld declaredG givenG (arr "M0" 0 2 5 :: arraysG.filter (·.name != "M0"))
#guard !linkHeld declaredG givenG (arr "ZZ" 0 5 4 :: arraysG.filter (·.name != "ZZ"))
#guard !linkHeld declaredG { givenG with messages := givenG.messages.set 2 (msg 1 1 0 1 0) } arraysG
-- an array too few; one too many; another in the place of a declared one
#guard !linkHeld declaredG givenG (arraysG.filter (·.name != "BZ"))
#guard !linkHeld declaredG givenG (arr "X" 0 1 1 :: arraysG)
#guard !linkHeld declaredG givenG (arr "X" 0 1 1 :: arraysG.filter (·.name != "BZ"))
-- a second mask row; none; a moment too many; a class of leaves
#guard !linkHeld declaredG { givenG with messages := givenG.messages.set 1 (msg 4 1 1 0 1) } arraysG
#guard !linkHeld declaredG { givenG with messages := givenG.messages.set 0 (msg 4 1 0 0 0) } arraysG
#guard !linkHeld declaredG { givenG with messages := givenG.messages ++ [msg 1 1 0 3 0] } arraysG
#guard !linkHeld declaredG
  { givenG with messages := givenG.messages.set 3 { msg 8 1 0 2 0 with leafClass := 1 } } arraysG
-- rows over the extension field are not kept
#guard !messageHeld false 3 (msg 1 3 0 0 1) && messageHeld false 3 (msg 1 1 0 0 1)
#guard !messageHeld true 3 (msg 1 1 1 0 1)

/-! ## The given numbers of a whole chain -/

/-- The messages of H, with the reply as its plain scalar. -/
def givenH : ReqLink := ⟨1, [msg 2 1 1 0 0, msg 4 1 0 1 0]⟩

/-- The arrays of H. -/
def arraysH : List ReqArray := [arr "M0" 0 1 2, arr "ZZ" 1 5 2, arr "BZ" 1 1 32]

/-- What the parameter bytes of a first chain hold, as far as the comparisons read it. -/
def first (link : List ReqLink) (layout : List (List ReqArray)) (identifiers : List Nat)
    (pendingRows : Nat) : Params.First :=
  { given :=
      { bytes := ByteArray.empty, cfg := ByteArray.empty, items := []
        plan := { field := .two, salt := 0, nonce := 0, posB := 0, samples := 1, saved := 0,
                  entries := [] } }
    codes := {}, lin := default, binding := default, more := []
    shape := { code := 0, maskCode := 0, link := link, atStart := [], answers := 1, last := [],
               choice := ⟨true⟩ }
    layout := ⟨layout⟩, identifiers := identifiers, pendingRows := pendingRows }

#guard why (heldAgainst expected (first [givenG, givenH] [arraysG, arraysH] [1, 2] 2)) == ""
#guard why (heldAgainst expected (first [givenG, givenH] [arraysH, arraysG] [1, 2] 2)) ==
  "plan-layout"
#guard why (heldAgainst expected (first [givenG] [arraysG] [1, 2] 2)) == "plan-layout"
#guard why (heldAgainst expected (first [givenG, givenH] [arraysG] [1, 2] 2)) == "plan-layout"
#guard why (heldAgainst expected (first [givenG, givenH, givenH] [arraysG, arraysH, arraysH]
  [1, 2] 2)) == "plan-layout"
#guard why (numbersHeld links (first [givenG, givenH] [arraysG, arraysH] [1, 2] 2)) == ""
#guard why (numbersHeld links (first [givenG, givenH] [arraysG, arraysH] [2, 1] 2)) ==
  "parameters-not-admitted"
#guard why (numbersHeld links (first [givenG, givenH] [arraysG, arraysH] [1, 2] 1)) ==
  "parameters-not-admitted"
#guard why (numbersHeld links (first [givenH, givenH] [arraysG, arraysH] [1, 2] 2)) ==
  "parameters-not-admitted"
#guard why (numbersHeld links (first [givenG, givenG] [arraysG, arraysH] [1, 2] 2)) ==
  "parameters-not-admitted"

/-! ## A small configuration of five links

Five links: G0 A0 G1 A1 H. The numbers are those that the C++ verifier has at this configuration:
the sub-proofs' plans, what buildLinksH declares from them, and the shape and layout that it makes
with the configuration's layout file. Each array has a single block here, and not its real one: the
comparison requires only a block whose four logarithms are below 48. -/

/-- A plan from its numbers. sizes: the rows, the columns and ec (3: over the extension field) of
each listed array. Array 0 is U3. plFor: for each array of an earlier sub-proof the owner's group
and the array's number among the owner's symbol arrays. -/
def kitPlan (sizes : List (Nat × Nat × Nat)) (ZZ BZ : Nat)
    (PK TX FT pkMat pxMat gtTree : Array Nat) (plFor : Array (Nat × Nat)) (ns NCL : Nat) :
    SubPlanH :=
  { tl := { pkMat := pkMat, pxMat := pxMat, gtTree := gtTree
            ix := { U := #[none, none, some 0, none], ZZ := ZZ, BZ := BZ, PK := PK, TX := TX,
                    FT := FT }
            plFor := plFor.map fun x => { owner := some x.1, rootIndex := some x.2 } }
    Fp := { trees := (sizes.map fun s => tree s.1 s.2.1).toArray }
    Tp := { nt := (sizes.map fun s => ({ ec := s.2.2 } : N2)).toArray }
    ns := ns, NCL := NCL, run := pure none }

/-- The plan of G0. -/
def kitG0 : SubPlanH :=
  kitPlan
    [(1, 167328, 3), (2731, 247, 1), (2731, 247, 1), (2731, 247, 1), (1366, 160, 1), (1366, 14, 1),
     (2731, 2048, 1), (2731, 20, 1), (2731, 96, 1), (2731, 20, 1), (128, 131072, 1), (32, 2048, 1)]
    10 11 #[1, 2, 3, 4, 5, 6, 7] #[8, 9] #[] #[0, 1, 2, 3, 4, 5, 8] #[6, 7]
    #[1, 2, 3, 4, 5, 6, 8, 9, 7] #[] 3204 33

/-- The plan of A0. -/
def kitA0 : SubPlanH :=
  kitPlan
    [(1, 34152, 3), (683, 120, 1), (1366, 4, 1), (2731, 32, 1), (2731, 1024, 1), (128, 61440, 1),
     (32, 2048, 1), (2731, 96, 1)]
    5 6 #[1, 2, 3, 4] #[] #[7] #[0, 1, 2, 3] #[]
    #[1, 2, 3, 4, 7] #[(0, 7)] 3076 0

/-- The plan of G1. -/
def kitG1 : SubPlanH :=
  kitPlan
    [(1, 166688, 3), (2731, 247, 1), (2731, 247, 1), (2731, 247, 1), (1366, 160, 1), (1366, 14, 1),
     (2731, 2048, 1), (2731, 96, 1), (2731, 20, 1), (128, 131072, 1), (32, 2048, 1), (2731, 20, 1)]
    9 10 #[1, 2, 3, 4, 5, 6] #[7, 8] #[11] #[0, 1, 2, 3, 4, 5] #[6, 7]
    #[1, 2, 3, 4, 5, 6, 7, 8, 11] #[(0, 8)] 3203 32

/-- The plan of A1. -/
def kitA1 : SubPlanH :=
  kitPlan
    [(1, 34152, 3), (683, 120, 1), (1366, 4, 1), (2731, 32, 1), (2731, 1024, 1), (128, 61440, 1),
     (32, 2048, 1), (2731, 96, 1)]
    5 6 #[1, 2, 3, 4] #[] #[7] #[0, 1, 2, 3] #[]
    #[1, 2, 3, 4, 7] #[(1, 6)] 3076 0

/-- The plan of H. -/
def kitH : SubPlanH :=
  kitPlan
    [(1, 11264, 3), (5462, 20, 1), (1366, 16, 1), (1366, 2, 1), (2731, 1536, 1), (128, 81920, 1),
     (32, 2048, 1), (2731, 20, 1)]
    5 6 #[1, 2, 3, 4] #[] #[7] #[0, 1, 2, 3] #[]
    #[1, 2, 3, 4, 7] #[(1, 7)] 2879 1

/-- The five links. -/
def kitLinks : Array LinkH :=
  ((listLinksH 2 true #[kitG0, kitG1] #[kitA0, kitA1] kitH).toOption).getD #[]

/-- A declared array. -/
def fa (name : String) (rows columns : Nat) (overE : Bool) (life : Nat) : FrameArray :=
  { name := name, rows := rows, columns := columns, overE := overE, life := life }

/-- What the five links declare. -/
def kitDeclared : Array FrameLink :=
  #[{ name := "G0"
      moment :=
      #[#[fa "M0" 2731 247 false 0, fa "M1" 2731 247 false 0, fa "M2" 2731 247 false 0,
         fa "M3" 1366 160 false 0, fa "M4" 1366 14 false 0, fa "M5" 2731 2048 false 0,
         fa "M8" 2731 20 false 0, fa "M6" 2731 96 false 1, fa "M7" 2731 20 false 2],
        #[fa "U3" 1 167328 true 0],
        #[fa "ZZ" 128 131072 false 0, fa "BZ" 32 2048 false 0]] },
    { name := "A0"
      moment :=
      #[#[fa "M0" 683 120 false 0, fa "M1" 1366 4 false 0, fa "M2" 2731 32 false 0,
         fa "M3" 2731 1024 false 0],
        #[fa "U3" 1 34152 true 0],
        #[fa "ZZ" 128 61440 false 0, fa "BZ" 32 2048 false 0]] },
    { name := "G1"
      moment :=
      #[#[fa "M0" 2731 247 false 0, fa "M1" 2731 247 false 0, fa "M2" 2731 247 false 0,
         fa "M3" 1366 160 false 0, fa "M4" 1366 14 false 0, fa "M5" 2731 2048 false 0,
         fa "M6" 2731 96 false 1, fa "M7" 2731 20 false 2],
        #[fa "U3" 1 166688 true 0],
        #[fa "ZZ" 128 131072 false 0, fa "BZ" 32 2048 false 0]] },
    { name := "A1"
      moment :=
      #[#[fa "M0" 683 120 false 0, fa "M1" 1366 4 false 0, fa "M2" 2731 32 false 0,
         fa "M3" 2731 1024 false 0],
        #[fa "U3" 1 34152 true 0],
        #[fa "ZZ" 128 61440 false 0, fa "BZ" 32 2048 false 0]] },
    { name := "H"
      moment :=
      #[#[fa "M0" 5462 20 false 0, fa "M1" 1366 16 false 0, fa "M2" 1366 2 false 0,
         fa "M3" 2731 1536 false 0],
        #[fa "U3" 1 11264 true 0],
        #[fa "ZZ" 128 81920 false 0, fa "BZ" 32 2048 false 0]] }]

/-- For each link and each array of its list: the link that commits to it, and its name there. -/
def kitArrayOf : List (Array (Nat × String)) :=
  [#[(0, "U3"), (0, "M0"), (0, "M1"), (0, "M2"), (0, "M3"), (0, "M4"), (0, "M5"), (0, "M8"),
      (0, "M6"), (0, "M7"), (0, "ZZ"), (0, "BZ")],
   #[(1, "U3"), (1, "M0"), (1, "M1"), (1, "M2"), (1, "M3"), (1, "ZZ"), (1, "BZ"), (0, "M6")],
   #[(2, "U3"), (2, "M0"), (2, "M1"), (2, "M2"), (2, "M3"), (2, "M4"), (2, "M5"), (2, "M6"),
      (2, "M7"), (2, "ZZ"), (2, "BZ"), (0, "M7")],
   #[(3, "U3"), (3, "M0"), (3, "M1"), (3, "M2"), (3, "M3"), (3, "ZZ"), (3, "BZ"), (2, "M6")],
   #[(4, "U3"), (4, "M0"), (4, "M1"), (4, "M2"), (4, "M3"), (4, "ZZ"), (4, "BZ"), (2, "M7")]]

/-- The given links. -/
def kitGiven : List ReqLink :=
  [⟨0, [msg 61 1 1 0 0, msg 3 1 0 0 1, msg 1 1 0 0 2, msg 2 3 0 1 0, msg 129 1 0 2 0]⟩,
   ⟨0, [msg 23 1 1 0 0, msg 1 3 0 1 0, msg 61 1 0 2 0]⟩,
   ⟨0, [msg 60 1 1 0 0, msg 3 1 0 0 1, msg 1 1 0 0 2, msg 2 3 0 1 0, msg 129 1 0 2 0]⟩,
   ⟨0, [msg 23 1 1 0 0, msg 1 3 0 1 0, msg 61 1 0 2 0]⟩,
   ⟨1, [msg 34 1 1 0 0, msg 1 3 0 1 0, msg 81 1 0 2 0]⟩]

/-- The given arrays. -/
def kitLayout : List (List ReqArray) :=
  [[arr "M5" 0 2731 2048, arr "M0" 0 2731 247, arr "M1" 0 2731 247, arr "M2" 0 2731 247,
    arr "M3" 0 1366 160, arr "M8" 0 2731 20, arr "M4" 0 1366 14, arr "M6" 1 2731 96,
    arr "M7" 2 2731 20, arr "U3" 3 1 167328, arr "ZZ" 4 128 131072, arr "BZ" 4 32 2048],
   [arr "M3" 0 2731 1024, arr "M2" 0 2731 32, arr "M0" 0 683 120, arr "M1" 0 1366 4,
    arr "U3" 1 1 34152, arr "ZZ" 2 128 61440, arr "BZ" 2 32 2048],
   [arr "M5" 0 2731 2048, arr "M0" 0 2731 247, arr "M1" 0 2731 247, arr "M2" 0 2731 247,
    arr "M3" 0 1366 160, arr "M4" 0 1366 14, arr "M6" 1 2731 96, arr "M7" 2 2731 20,
    arr "U3" 3 1 166688, arr "ZZ" 4 128 131072, arr "BZ" 4 32 2048],
   [arr "M3" 0 2731 1024, arr "M2" 0 2731 32, arr "M0" 0 683 120, arr "M1" 0 1366 4,
    arr "U3" 1 1 34152, arr "ZZ" 2 128 61440, arr "BZ" 2 32 2048],
   [arr "M3" 0 2731 1536, arr "M0" 0 5462 20, arr "M1" 0 1366 16, arr "M2" 0 1366 2,
    arr "U3" 1 1 11264, arr "ZZ" 2 128 81920, arr "BZ" 2 32 2048]]

/-- What the parameter bytes of this configuration's first chain hold, as far as the comparisons
read. -/
def kitFirst : Params.First := first kitGiven kitLayout [1, 4, 2, 5, 3] 3

#guard kitLinks.toList.map (fun X => (X.name, X.gid, X.kind, X.g, X.ns, X.fv)) ==
  [("G0", 1, 0, 0, 3204, true), ("A0", 4, 1, 0, 3076, false), ("G1", 2, 0, 1, 3203, true),
   ("A1", 5, 1, 1, 3076, false), ("H", 3, 2, 0, 2879, true)]
#guard why (headLast kitLinks) == "" && why (linksCount kitLinks) == ""
#guard onTable kitLinks == 3 && why (tableRows kitLinks 2) == ""
#guard (declareLinks kitLinks 2 true).toOption.map (·.2) == some kitDeclared
#guard (declareLinks kitLinks 2 true).toOption.map (fun x => x.1.toList.map (·.arrayOf)) ==
  some kitArrayOf
#guard why (heldAgainst kitDeclared kitFirst) == ""
#guard why (numbersHeld kitLinks kitFirst) == ""
-- each array has one made-up block, so the guard can tell only messages and sizes apart
#guard onePlacement kitLinks ⟨kitLayout⟩
-- every array that a link reads is laid out and still kept; the mask row has 8192 entries
#guard ((declareLinks kitLinks 2 true).toOption.map fun x =>
    x.1.toList.zipIdx.all fun X =>
      why (linkLaid kitFirst.shape kitFirst.layout 8192 X.2 X.1) == "") == some true
-- one entry too few for the 3204 scalars of G0 and the pad of one answer
#guard ((declareLinks kitLinks 2 true).toOption.map fun x =>
    x.1.toList.zipIdx.all fun X =>
      why (linkLaid kitFirst.shape kitFirst.layout 3204 X.2 X.1) == "") == some false

/-! ## The weight table's layout -/

/-- A unit of kind X with so many digits. -/
def unit (X nlw rows off : Nat) : WsUnit := { X := X, nlw := nlw, rows := rows, off := off }

/-- The name with which a layout of the weight table is refused. -/
def limbs : String := "internal-weight-limbs"

-- an accepted layout; then: four digits in a unit other than the embedding; a gap; an odd number of
-- rows; a unit past the last row; rows that are no multiple of the digits; three digits; no unit
#guard why (weightLimbs { m0 := 14, U := #[unit 0 2 4 0, unit 12 4 8 4] }) == ""
#guard why (weightLimbs { m0 := 14, U := #[unit 0 2 4 0, unit 11 4 8 4] }) == limbs
#guard why (weightLimbs { m0 := 14, U := #[unit 0 2 4 0, unit 12 4 8 6] }) == limbs
#guard why (weightLimbs { m0 := 13, U := #[unit 0 2 4 0, unit 12 4 8 4] }) == limbs
#guard why (weightLimbs { m0 := 10, U := #[unit 0 2 4 0, unit 12 4 8 4] }) == limbs
#guard why (weightLimbs { m0 := 14, U := #[unit 0 2 3 0] }) == limbs
#guard why (weightLimbs { m0 := 14, U := #[unit 0 3 3 0] }) == limbs
#guard why (weightLimbs { m0 := 14, U := #[] }) == limbs

/-! ## Arrays that are placed alike -/

#guard placedAlike (some (arr "M1" 1 3 8)) (some (arr "M7" 1 3 8))
#guard !placedAlike (some (arr "M1" 1 3 8)) (some (arr "M1" 2 3 8))
#guard !placedAlike (some (arr "M1" 1 3 8)) none
#guard onePlacement links ⟨[arraysG, []]⟩
#guard !onePlacement links ⟨[arraysG.filter (·.name != "M1"), []]⟩
#guard indexMasksTaken 1 9 == 1 && indexMasksTaken 3 9 == 3 + 19

/-! ## The plan on which a check has worked -/

#guard links.all fun X => samePlan X X.Fp X.Tp
#guard !links.all fun X => samePlan X { X.Fp with trees := X.Fp.trees.set! 1 (tree 3 9) } X.Tp
#guard !links.all fun X => samePlan X { X.Fp with trees := X.Fp.trees.pop } X.Tp
#guard !links.all fun X => samePlan X X.Fp { X.Tp with nt := X.Tp.nt.push {} }
#guard links.all fun X => samePlan X { X.Fp with trees := X.Fp.trees.push (tree 1 1) } X.Tp

end OnBytes.Model.Stages.Test
