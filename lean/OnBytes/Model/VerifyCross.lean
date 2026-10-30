-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyCross.lean: the tests that compare the plans of a request's sub-proofs with each
other.

A request's proof is cut into sub-proofs: groups of layers G_0, G_1, .., one attention sub-proof A_g
for each group, and the head H. Before any proof is read, the verifier makes a plan of each from the
configuration files. Some matrices are committed to by one sub-proof, the owner, and read by
another: G_g reads the stream that G_(g-1) leaves, A_g reads a matrix "qa" of G_g, and H reads the
stream of the last group. Owner and reader each describe such a matrix from their own numbers. The
tests here compare the descriptions and count them over the whole request.

Words. A sub-proof commits to arrays, and its plan lists them in a fixed order
(OnBytes/Model/Tail.lean). A symbol array holds the cells of a matrix, packed into symbols. For each
array a plan has the list's entry (N2) and the array's shape (HTree). A record (PlaceF) says where a
shared matrix lies in its symbol array: the owner keeps one in plOwn, the reader one in plFor.

It follows the end of vf_layers_plan.inc (A_g against G_g) and the two blocks of tests that
follow the plans in runStage, verifier/src/cp_verify.cpp. These blocks have no names in the C++. All
data here are public, so a test may say why it refuses: it throws the name under which the C++
verifier refuses (Except String). A missing plan and an array's number outside its list are refused
under the name of the test that finds them (in attentionOwnerPlaces: under the name of
attentionOwnerShapes). The C++ has no test for these two cases. It takes the plans and the numbers
straight from its own planners, where a function here takes them as arguments.

A plan comes as a SubPlan: the three parts that the plans of all three kinds of sub-proof have.

Main definitions: SubPlan, attentionOwnerShapes, attentionOwnerPlaces, attentionOwners, borderCount,
readersOf, symReaders, foldColumnsHeld, labelsHeld, crossPlans.

What this file does not do: it makes no plan, reads no message and tests no equation of a proof. The
comparisons of G_g with G_(g-1) and of H with the last group are made where the plans of the layers
and of the head are made. No theorem is stated here.
-/
import OnBytes.Model.Tail

namespace OnBytes.Model.Verify

/-- What these tests read of the plan of a sub-proof. -/
structure SubPlan where
  /-- the state of the sub-proof's smallness test (OnBytes/Model/Tail.lean) -/
  tl : HTailF2
  /-- the sub-proof's state, with the arrays of its list -/
  F : Fork
  /-- the list's entries, one for each array -/
  T : Tail2

/-! ## A_g reads a matrix of G_g -/

/-- Array number t of a plan's list: its entry and its shape. Nothing if the list has no such
array. -/
def arrayOf (P : SubPlan) (t : Nat) : Option (N2 × HTree) :=
  match P.T.nt[t]?, P.F.trees[t]? with
  | some n, some X => some (n, X)
  | _, _ => none

/-- True if both numbers are there, both name an array of their list, and array o of the owner's
plan O has the shape of array x of the reader's plan X. -/
def sameArray (O : SubPlan) (o : Option Nat) (X : SubPlan) (x : Option Nat) : Bool :=
  match o.bind (arrayOf O), x.bind (arrayOf X) with
  | some a, some b => t2SameShape a.1 a.2 b.1 b.2
  | _, _ => false

/-- A_g reads the first of the symbol arrays of G_g that another sub-proof reads. Its shape in the
plan of A_g must be the shape in the owner's plan. Tested for each g below NGr. A missing plan is
refused as well. -/
def attentionOwnerShapes (NGr : Nat) (G A : Array SubPlan) : Except String Unit :=
  if (List.range NGr).all fun g =>
      match G[g]?, A[g]? with
      | some O, some X => sameArray O (O.tl.ix.TX[0]?) X (X.tl.ix.FT[0]?)
      | _, _ => false
  then pure ()
  else throw "internal-a-owner-shape"

/-- A_g reads one array of another sub-proof. First the record of A_g for that array is filled: the
owner is G_g, and the array is the first of those symbol arrays of G_g that another sub-proof reads.
These are numbered after the arrays that no other sub-proof reads. Then the record of A_g of where
the matrix "qa" lies must equal the owner's. Returns the plan of A_g with the record filled. -/
def attentionOwnerPlace (g : Nat) (O X : SubPlan) : Except String SubPlan := do
  let tl ← X.tl.borderMeans 0 g O.tl.pkMat.size
  let own ← O.tl.ownEntry "qa"
  let df := samePlaceF own (tl.plFor.getD 0 {})
  if df != "" then throw ("internal-a-owner-place-" ++ df)
  pure { X with tl := tl }

/-- attentionOwnerPlace for each g below NGr, in their order. Returns the plans of attention with
their records filled. A missing plan is refused as "internal-a-owner-shape", the name of the test
that attentionOwners runs first: after that test none is missing. Each call is one comparison of
records. Nothing counts the calls: see crossPlans. -/
def attentionOwnerPlaces (NGr : Nat) (G A : Array SubPlan) :
    Except String (Array SubPlan) :=
  (List.range NGr).foldlM
    (fun (out : Array SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape")
    A

/-- The end of the layers' plans: all shapes are compared first, then all records. Without
attention (p4 false) nothing is tested. Returns the plans of attention with their records filled.
C++: the last two loops of verifier/src/vf_layers_plan.inc. -/
def attentionOwners (p4 : Bool) (NGr : Nat) (G A : Array SubPlan) :
    Except String (Array SubPlan) :=
  if p4 then do
    attentionOwnerShapes NGr G A
    attentionOwnerPlaces NGr G A
  else pure A

/-! ## Counts over the whole request -/

/-- The sum of a number over some plans. -/
def sumOver (f : SubPlan → Nat) (Ps : Array SubPlan) : Nat :=
  Ps.foldl (fun s P => s + f P) 0

/-- Each array that another sub-proof reads has exactly one reader and is compared once. So four
numbers are equal: the number of comparisons of records (borderCmpF; see crossPlans), the owners'
records, the readers' records, and NGr, or twice NGr with attention. -/
def borderCount (borderCmpF NGr : Nat) (p4 : Bool) (G A : Array SubPlan) (H : SubPlan) :
    Except String Unit :=
  let own := sumOver (·.tl.plOwn.size) G
  let fts := sumOver (·.tl.plFor.size) G + H.tl.plFor.size + sumOver (·.tl.plFor.size) A
  if borderCmpF != own || own != fts || fts != NGr + (if p4 then NGr else 0) then
    throw "internal-border-count"
  else pure ()

/-- The number of readers' records, over the whole request, that name the array number idx among
the symbol arrays of the group of layers number owner. -/
def readersOf (G A : Array SubPlan) (H : SubPlan) (owner idx : Nat) : Nat :=
  let look := fun (P : SubPlan) =>
    (P.tl.plFor.filter fun pl => pl.owner == some owner && pl.rootIndex == some idx).size
  sumOver look G + look H + sumOver look A

/-- True if each of the arrays ts of the plan P is in the plan's list and has the count
a = 1 + (its readers). Array number i of ts is number first + i among the owner's symbol arrays. -/
def countsHeld (readers : Nat → Nat) (P : SubPlan) (ts : Array Nat) (first : Nat) : Bool :=
  (List.range ts.size).all fun i =>
    match ts[i]?.bind (P.T.nt[·]?) with
    | some n => n.a == 1 + readers (first + i)
    | none => false

/-- Every symbol array has in its owner's list the count a = 1 + the number of sub-proofs other than
the owner that read it, by the readers' own records. The number of random coordinates of the array
follows from a. The protocol's pages state this condition for hiding; this program only tests the
condition. A reader's record can name only an array of a group of layers, so the arrays of the head
and of attention have a = 1 and none of them is read by another sub-proof. -/
def symReaders (G A : Array SubPlan) (H : SubPlan) : Except String Unit :=
  let alone := fun (P : SubPlan) =>
    countsHeld (fun _ => 0) P P.tl.ix.PK 0 && P.tl.ix.TX.isEmpty
  if ((List.range G.size).all fun g =>
        match G[g]? with
        | some P =>
          countsHeld (readersOf G A H g) P P.tl.ix.PK 0 &&
            countsHeld (readersOf G A H g) P P.tl.ix.TX P.tl.ix.PK.size
        | none => false) &&
      alone H && A.all alone then
    pure ()
  else throw "policy-sym-readers"

/-- The list tails[g] and the plan of G_g each name the matrices of that sub-proof. The number of
columns of all matrices together must be the same in both. -/
def foldColumnsHeld (NGr : Nat) (tails : Array Tail) (G : Array SubPlan) :
    Except String Unit :=
  if (List.range NGr).all fun g =>
      match G[g]?, tails[g]? with
      | some P, some t => P.tl.foldColumns == t.foldColumns
      | _, _ => false
  then pure ()
  else throw "internal-fold-columns"

/-- The labels of the matrices met so far. -/
structure Labels where
  /-- the labels of the matrices that some sub-proof owns -/
  owned : List Nat := []
  /-- the labels of the matrices that some sub-proof reads as another's -/
  foreign : List Nat := []

/-- Adds the label of one matrix. Nothing if its label is owned already, or if its kind is
neither 0 (owned) nor 1 (another's). -/
def Labels.take (l : Labels) (M : TMat) : Option Labels :=
  if M.kind == 0 then
    if l.owned.contains M.aId then none else some { l with owned := M.aId :: l.owned }
  else if M.kind == 1 then some { l with foreign := M.aId :: l.foreign }
  else none

/-- Over all matrices of all plans: no label is owned twice, the label of every matrix that is read
as another's is owned by some sub-proof, no matrix is of a third kind, and some matrix is owned. -/
def labelsHeld (G A : Array SubPlan) (H : SubPlan) : Except String Unit :=
  let mats := (G.toList ++ [H] ++ A.toList).flatMap fun P => P.tl.mats.toList
  match mats.foldlM Labels.take {} with
  | none => throw "internal-nmlab"
  | some l =>
    if l.foreign.all l.owned.contains && !l.owned.isEmpty then pure ()
    else throw "internal-nmlab"

/-- The four tests over the whole request, in the order of the C++. attentionOwners is not among
them: the caller runs it first. borderCmpF: the number of comparisons of records that are made while
the plans are made: one for each group of layers but the first, one for each attention sub-proof,
one for the head. The C++ counts them as they are made. Here the caller computes the number from the
numbers of plans, so it does not show that they were made. tails: for each group of layers the list
of its matrices. C++: the two blocks after the plans in runStage, verifier/src/cp_verify.cpp. -/
def crossPlans (borderCmpF NGr : Nat) (p4 : Bool) (tails : Array Tail) (G A : Array SubPlan)
    (H : SubPlan) : Except String Unit := do
  borderCount borderCmpF NGr p4 G A H
  symReaders G A H
  foldColumnsHeld NGr tails G
  labelsHeld G A H

/-- The names under which the functions of this file refuse. The endings after
"internal-a-owner-place-" are those that samePlaceF can return. -/
def Cross.names : List String :=
  ["internal-a-owner-shape", "internal-border-count", "policy-sym-readers", "internal-fold-columns",
   "internal-nmlab"] ++
  ["P0", "P1", "P3", "P4", "P5", "P6", "P9"].map ("internal-a-owner-place-" ++ ·)

end OnBytes.Model.Verify
