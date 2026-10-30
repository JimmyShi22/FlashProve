-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyCross.lean: tests of OnBytes/Model/VerifyCross.lean, run when this file
compiles.

The program does not import this file.

Plans are made up by hand for a request with two groups of layers, two attention sub-proofs and the
head. Each holds only what the tests read: the matrices' names, kinds, labels and columns, the
numbers of the symbol arrays, the arrays' shapes and counts, and the records of where a shared
matrix lies. What is tested: the honest plans pass, and each of a list of changes is refused under
the expected name. The names are those of the C++ sources that OnBytes/Model/VerifyCross.lean cites.
Of the seven endings after internal-a-owner-place- two are tried. crossPlans is not run without
attention.
-/
import OnBytes.Model.VerifyCross

namespace OnBytes.Model.TestVerifyCross

open Verify

/-- A record of a shared matrix's position, complete except for owner and rootIndex. -/
def placeOf (k : Nat) : PlaceF :=
  { sh := some (ShP.of 64 k 2), matrix := some (0, k, 64), hb := 128, mS := 22, lanes := 3,
    padRows := 32, J := 1, K := k, off := 0 }

/-- A matrix. -/
def mat (name : String) (k kind aId : Nat) : TMat :=
  { name := name, m := 64, k := k, kind := kind, aId := aId }

/-- An array of the list: its count a, and its shape. -/
def arr (a K : Nat) : N2 × HTree := ({ a := a }, { R := 32, K := K })

/-- A plan from its closing part and its arrays. -/
def planOf (tl : HTailF2) (arrays : Array (N2 × HTree)) : SubPlan :=
  { tl := tl, F := { trees := arrays.map (·.2) }, T := { nt := arrays.map (·.1) } }

/-- The plan of the group of layers g. It owns "af", which no other sub-proof reads, and "qa" and
"xbO", each of which one other sub-proof reads. From the second group on it reads the "xbO" of the
group before it. -/
def layers (g : Nat) : SubPlan :=
  let own : Array TMat := #[mat "af" 5 0 (256 * g), mat "qa" 7 0 (256 * g + 1),
    mat "xbO" 9 0 (256 * g + 2)]
  let read : Array TMat := if g == 0 then #[] else #[mat "xbI" 9 1 (256 * (g - 1) + 2)]
  planOf
    { mats := own ++ read
      ix := { PK := #[0], TX := #[1, 2], FT := if g == 0 then #[] else #[3] }
      pkMat := #[0]
      pxMat := #[1, 2]
      plOwn := #[{ placeOf 7 with owner := some g, rootIndex := some 1 },
                 { placeOf 9 with owner := some g, rootIndex := some 2 }]
      plFor := if g == 0 then #[]
        else #[{ placeOf 9 with owner := some (g - 1), rootIndex := some 2 }] }
    (#[arr 1 5, arr 2 7, arr 2 9] ++ if g == 0 then #[] else #[arr 2 9])

/-- The plan of the attention sub-proof g, before its record names the owner and the array. -/
def attention (g : Nat) : SubPlan :=
  planOf
    { mats := #[mat "qa" 7 1 (256 * g + 1), mat "sc" 4 0 (256 * (10 + g))]
      ix := { PK := #[1], FT := #[0] }
      pkMat := #[1]
      plFor := #[placeOf 7] }
    #[arr 2 7, arr 1 4]

/-- The plan of the head. -/
def head : SubPlan :=
  planOf
    { mats := #[mat "xbL" 9 1 (256 + 2), mat "hf" 6 0 (256 * 3)]
      ix := { PK := #[1], FT := #[0] }
      pkMat := #[1]
      plFor := #[{ placeOf 9 with owner := some 1, rootIndex := some 2 }] }
    #[arr 2 9, arr 1 6]

/-- The plans of the layers. -/
def G : Array SubPlan := #[layers 0, layers 1]

/-- The plans of attention. -/
def A : Array SubPlan := #[attention 0, attention 1]

/-- The lists of the layers' matrices. -/
def tails : Array Tail := G.map fun P => { mats := P.tl.mats }

/-- Both steps on given plans: the name of the refusal, or nothing if all pass. -/
def verdict (G A : Array SubPlan) (H : SubPlan) (cmp : Nat := 4)
    (tails : Array Tail := tails) : Option String :=
  let run : Except String Unit := do
    crossPlans cmp 2 true tails G (← attentionOwners true 2 G A) H
  match run with
  | .ok _ => none
  | .error e => some e

/-- The plan with another closing part. -/
def withTl (P : SubPlan) (f : HTailF2 → HTailF2) : SubPlan := { P with tl := f P.tl }

/-- The plan with other numbers of its arrays. -/
def withIx (P : SubPlan) (f : T2Map → T2Map) : SubPlan :=
  withTl P fun tl => { tl with ix := f tl.ix }

/-- The plan with another count a of array t. -/
def withCount (P : SubPlan) (t a : Nat) : SubPlan :=
  { P with T := { P.T with nt := P.T.nt.modify t fun (n : N2) => { n with a := a } } }

#guard verdict G A head == none
-- attentionOwners fills the readers' records
#guard ((attentionOwners true 2 G A).toOption.map fun X =>
  X.toList.map fun P => (P.tl.plFor.getD 0 {}).owner) == some [some 0, some 1]
#guard ((attentionOwners false 2 G A).toOption.map fun X =>
  X.toList.map fun P => (P.tl.plFor.getD 0 {}).owner) == some [none, none]
-- the shape of qa differs between owner and reader
#guard verdict G (A.modify 1 fun P => withCount P 0 3) head == some "internal-a-owner-shape"
-- a plan of attention is missing
#guard verdict G (A.pop) head == some "internal-a-owner-shape"
-- numbers of arrays that neither list has: two missing arrays must not count as equal
#guard verdict (G.modify 0 fun P => withIx P fun ix => { ix with TX := #[9, 2] })
  (A.modify 0 fun P => withIx P fun ix => { ix with FT := #[9] }) head
  == some "internal-a-owner-shape"
#guard verdict (G.modify 0 fun P => withIx P fun ix => { ix with PK := #[9] }) A head
  == some "policy-sym-readers"
-- the record differs: the columns of the matrix
#guard verdict G (A.modify 0 fun P => withTl P fun tl =>
  { tl with plFor := #[{ placeOf 7 with matrix := some (0, 6, 64) }] }) head
  == some "internal-a-owner-place-P3"
#guard verdict G (A.modify 0 fun P => withTl P fun tl =>
  { tl with plFor := #[{ placeOf 7 with hb := 127 }] }) head == some "internal-a-owner-place-P6"
-- a record that already names an owner; no record
#guard verdict G (A.modify 0 fun P => withTl P fun tl =>
  { tl with plFor := #[{ placeOf 7 with owner := some 0 }] }) head == some "internal-border-count"
#guard verdict G (A.modify 0 fun P => withTl P fun tl => { tl with plFor := #[] }) head
  == some "internal-border-count"
-- the counts
#guard verdict G A head 3 == some "internal-border-count"
#guard verdict G A (withTl head fun tl => { tl with plFor := #[] }) == some "internal-border-count"
-- the three counts agree with each other and not with the number of groups
#guard (borderCount 4 2 true G A head).isOk
#guard (borderCount 4 3 true G A head).toOption.isNone
-- the readers
#guard verdict (G.modify 0 fun P => withCount P 2 1) A head == some "policy-sym-readers"
#guard verdict (G.modify 1 fun P => withCount P 0 2) A head == some "policy-sym-readers"
#guard verdict G A (withCount head 1 2) == some "policy-sym-readers"
#guard verdict G A (withTl head fun tl => { tl with ix := { tl.ix with TX := #[1] } })
  == some "policy-sym-readers"
#guard verdict G A (withTl head fun tl =>
  { tl with plFor := #[{ placeOf 9 with owner := some 0, rootIndex := some 2 }] })
  == some "policy-sym-readers"
-- an array of attention with a reader; an array of attention that another sub-proof reads
#guard verdict G (A.modify 0 fun P => withCount P 1 2) head == some "policy-sym-readers"
#guard verdict G (A.modify 0 fun P => withIx P fun ix => { ix with TX := #[1] }) head
  == some "policy-sym-readers"
-- the columns
#guard verdict G A head 4 (tails.modify 1 fun t => { mats := t.mats.pop })
  == some "internal-fold-columns"
-- the labels: owned twice; read and owned by nobody; a third kind
#guard verdict G A (withTl head fun tl => { tl with mats := tl.mats.push (mat "x" 1 0 257) })
  == some "internal-nmlab"
#guard verdict G A (withTl head fun tl => { tl with mats := tl.mats.push (mat "x" 1 1 999) })
  == some "internal-nmlab"
#guard verdict G A (withTl head fun tl => { tl with mats := tl.mats.push (mat "x" 1 2 999) })
  == some "internal-nmlab"
-- no matrix at all
#guard (labelsHeld #[] #[] (planOf {} #[])).toOption.isNone

-- every name that was met above is in the file's list
#guard ["internal-a-owner-shape", "internal-a-owner-place-P3", "internal-a-owner-place-P6",
  "internal-border-count", "policy-sym-readers", "internal-fold-columns", "internal-nmlab"].all
  Cross.names.contains

end OnBytes.Model.TestVerifyCross
