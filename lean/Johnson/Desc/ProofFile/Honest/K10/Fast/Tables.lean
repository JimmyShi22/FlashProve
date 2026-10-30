-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Fast/Tables.lean: a faster way to build the two tables that the closing of a segment
(K10) hands to a fold, with theorems that it yields the same arrays, word for word, as the first text (`closeMain`,
`closeMask`, Honest/K10/Job.lean). Definitions with code, and theorems.

A group's table has 2^k rows (2^h for the mask table). The row of an index J is J modulo the number of rows. The first
text makes each entry as a sum over all oracle messages of the statement. At each summand it asks the library's weight
(`mainWeight`, OnBytes/Iop/RowLaws.lean; `maskWeight`, OnBytes/Iop/MaskLaws.lean), which is 1 or 0, and adds the
message's own entry where the weight is 1 and the element 0 elsewhere. The text here asks the weights once for each
row and each oracle message. It keeps, for each row, the list of the messages whose weight is 1 there, by increasing
number. An entry is then the sum over the list of its row, in the same order.

  `addF_addF_zero`, `addE_addE_zeroE`, `addE_zeroE_zeroE`   adding 0 to a result of the program's addition, or to 0,
                 gives back the same words
  `sumOver`, `foldl_skip`, `addUp_skip`   the sum over a list; a summand 0 can be left out of a sum that starts at 0
  `blockBits_row`, `mainWeight_row`, `maskWeight_row`   the library's weights depend on an index only through its row
  `rowOwners`, `rowOwners_getD`   for each row the list of the messages of weight 1
  `tableWith`, `tableBy`, `tableBy_eq`   the building of a table, for any weight and any map from an index of the
                 group's table back to an index of a message's own table
  `closeMainF`, `closeMaskF`   the two tables, built the faster way
  `closeMainF_eq`, `closeMaskF_eq`, `closeMainF_fun`, `closeMaskF_fun`   they are the first text's arrays, for every
                 statement, every layout and all entries: the theorems have no premise
  `closeAskBy`, `closeAskBy_first`   the text of `closeAsk` (Honest/K10/Job.lean) with the two builders of tables as
                 parameters; with the first text's builders it is `closeAsk`
  `closeAskF`, `closeAskF_eq`   `closeAsk` with the faster builders; it returns what `closeAsk` returns

Why the equations hold. An element of the program is three words, and the type admits words that are not below the
prime. The addition reduces such words, so adding 0 does not give back every element. It does give back 0 and every
result of the addition, and each partial sum of the first text is one of these two. So a summand 0 can be left out,
and nothing is asked of the messages' entries. A weight reads of an index J only the number J / 2^a % 2^(k - a), where
a is the message's number of row bits (h in place of k for the mask table). For a at most k the row J % 2^k gives the
same number; for a above k the number is 0 for every J.

Limits. The equations are between arrays of the program's words. What is saved is the weights and the additions of 0:
the first text asks a weight for each entry and each oracle message, this one for each row and each oracle message. What
is not saved: for each message in the list of an entry's row, the entry still costs one call of the map back
(`mainBack`, `maskBack`) and one call of the function w that gives the message's own entries. The first text makes the
same calls. With the w that `closeAsk` passes (`wordAt` over `rowsAt`, Honest/K10/Job.lean), each call that falls on a
row that was sent, and inside that row's message, searches the group's array of members for the message's number and
then walks a list to the member found; both take a number of steps that grows with the number of members; then the
member's own function is called. The rest of `closeAsk` is as it was: the batching, the writing out of the row's 2^(k +
logEll) coefficients, and `closeKept`, which sums over the whole main table of each kept member through the same w. The
callers in Honest/K10/Job.lean make the whole ask anew at each of the fold's k + 1 moves, and they call `closeAsk`: the
part as it stands gains nothing until a caller is changed. "Faster" is said of the count of calls, with both texts run
the same way (both compiled, or both interpreted). That the lists are made once is read in the text (they are an
argument of `tableWith`, and compiled code evaluates an argument before the call); no line tests it. Nothing is measured
here: no time and no memory. Nothing is said on whether a row has one message, several or none: the lists are what the
weights say. `closeAskBy` writes the text of `closeAsk` a second time. `closeAskBy_first`, which is proved by unfolding
alone, holds the two together: it stops compiling if one of them is changed so that the two no longer unfold to the same
term. No caller of `closeAsk` is changed: whoever wants the faster tables calls `closeAskF`. No property of the protocol
is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Job
import OnBytes.Field.ZeroE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE addE addF Statement GroupLayout mainWeight mainBack maskWeight maskBack)
open VerifiableInference.Desc.First.Close (entries bat)

variable {W : Type}

/-! ## 1 Adding 0, on words -/

/-- Adding the word 0 to a result of the base field's addition gives back the same word. -/
theorem addF_addF_zero (a b : UInt64) : addF (addF a b) 0 = addF a b :=
  UInt64.toNat_inj.1 (by
    rw [OnBytes.toNat_addF, OnBytes.toNat_addF, UInt64.toNat_zero, Nat.add_zero, Nat.mod_mod])

/-- Adding the element 0 to a result of the addition of elements gives back the same three words. -/
theorem addE_addE_zeroE (a b : E) : addE (addE a b) zeroE = addE a b := by
  unfold addE zeroE
  simp only [E.c0_mk3, E.c1_mk3, E.c2_mk3, addF_addF_zero]

/-- The sum of the element 0 and the element 0 is the element 0, word for word. -/
theorem addE_zeroE_zeroE : addE zeroE zeroE = zeroE := by
  unfold addE zeroE
  simp only [E.c0_mk3, E.c1_mk3, E.c2_mk3, OnBytes.addF_zero_zero]

/-! ## 2 A summand 0 can be left out -/

/-- The sum of f i over the numbers i of a list, added from the left to the element 0, in the program's arithmetic. -/
def sumOver (l : List Nat) (f : Nat → E) : E := l.foldl (fun a i => addE a (f i)) zeroE

/-- Take a start a that adding 0 gives back. Adding to it, for each i of a list, f i where P i holds and 0 elsewhere
gives the same words as adding f i for those i of the list at which P holds. -/
theorem foldl_skip (P : Nat → Prop) [DecidablePred P] (f : Nat → E) (l : List Nat) :
    ∀ a : E, addE a zeroE = a →
      l.foldl (fun s i => addE s (if P i then f i else zeroE)) a =
        (l.filter fun i => decide (P i)).foldl (fun s i => addE s (f i)) a := by
  induction l with
  | nil =>
    intro a _
    simp only [List.filter_nil, List.foldl_nil]
  | cons i l ih =>
    intro a h
    by_cases hp : P i
    · have e : (i :: l).filter (fun i => decide (P i)) = i :: l.filter fun i => decide (P i) :=
        List.filter_cons_of_pos (decide_eq_true hp)
      rw [e, List.foldl_cons, List.foldl_cons, if_pos hp]
      exact ih _ (addE_addE_zeroE a (f i))
    · have e : (i :: l).filter (fun i => decide (P i)) = l.filter fun i => decide (P i) :=
        List.filter_cons_of_neg fun c => hp (of_decide_eq_true c)
      rw [e, List.foldl_cons, if_neg hp, h]
      exact ih a h

/-- The first text's sum over 0 .. n - 1, with 0 where P fails, is the sum over the numbers below n at which P holds.
It is `foldl_skip` at the start 0. -/
theorem addUp_skip (n : Nat) (P : Nat → Prop) [DecidablePred P] (f : Nat → E) :
    addUp n (fun o => if P o then f o else zeroE) =
      sumOver ((List.range n).filter fun o => decide (P o)) f :=
  foldl_skip P f (List.range n) zeroE addE_zeroE_zeroE

/-! ## 3 The library's weights depend on an index only through its row -/

/-- The bits a .. k - 1 of an index J are those of its row J % 2^k. For a above k both sides are 0. -/
theorem blockBits_row (J a k : Nat) : J % 2 ^ k / 2 ^ a % 2 ^ (k - a) = J / 2 ^ a % 2 ^ (k - a) := by
  by_cases h : a ≤ k
  · have h3 : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← Nat.pow_add, Nat.add_sub_cancel' h]
    rw [h3, Nat.mod_mul_right_div_self, Nat.mod_mod]
  · have h0 : k - a = 0 := by omega
    rw [h0, Nat.pow_zero, Nat.mod_one, Nat.mod_one]

/-- The weight on the group's main table is the same at an index and at the index's row. -/
theorem mainWeight_row {K : Type} [CommRing K] (S : Statement) (L : GroupLayout) (o J : Nat) :
    mainWeight (K := K) S L o (J % 2 ^ L.k) = mainWeight (K := K) S L o J := by
  unfold mainWeight
  simp only [blockBits_row]

/-- The weight on the group's mask table is the same at an index and at the index's row. -/
theorem maskWeight_row {K : Type} [CommRing K] (S : Statement) (L : GroupLayout) (o J : Nat) :
    maskWeight (K := K) S L o (J % 2 ^ L.h) = maskWeight (K := K) S L o J := by
  unfold maskWeight
  simp only [blockBits_row]

/-! ## 4 Building a table, for any weight -/

/-- For each of the rows 0 .. rows - 1 the list of the numbers o below n with wt o r = 1 at that row r, increasing. -/
def rowOwners (rows n : Nat) (wt : Nat → Nat → Int) : Array (List Nat) :=
  Array.ofFn (n := rows) fun r => (List.range n).filter fun o => decide (wt o r.val = 1)

/-- What `rowOwners` holds at a row r below rows. -/
theorem rowOwners_getD (rows n : Nat) (wt : Nat → Nat → Int) (r : Nat) (h : r < rows) :
    (rowOwners rows n wt).getD r [] = (List.range n).filter fun o => decide (wt o r = 1) := by
  unfold rowOwners
  simp [Array.getD, h]

/-- A table with size entries. The entry at the index J is the sum of w o (back o J) over the messages o in the list
that own holds at J's row. own: a list of messages for each row. rows: the number of rows. back o J: the index in o's
own table that belongs to J. w o i: the entry at the index i of o's own table. -/
def tableWith (own : Array (List Nat)) (rows size : Nat) (back : Nat → Nat → Nat) (w : Nat → Nat → E) : Array E :=
  Array.ofFn (n := size) fun J => sumOver (own.getD (J.val % rows) []) fun o => w o (back o J.val)

/-- `tableWith` at the lists that `rowOwners` makes of the weight wt and the number n of messages. The lists are an
argument of `tableWith`, so that they are made once, before the first entry. -/
def tableBy (rows size n : Nat) (wt : Nat → Nat → Int) (back : Nat → Nat → Nat) (w : Nat → Nat → E) : Array E :=
  tableWith (rowOwners rows n wt) rows size back w

/-- If there is at least one row and the weight is the same at an index and at the index's row, then `tableBy` yields
the array in which each entry is a sum over all n messages, with 0 where the weight is not 1. -/
theorem tableBy_eq (rows size n : Nat) (wt : Nat → Nat → Int) (back : Nat → Nat → Nat) (w : Nat → Nat → E)
    (hpos : 0 < rows) (hrow : ∀ o J, wt o (J % rows) = wt o J) :
    tableBy rows size n wt back w =
      Array.ofFn (n := size) fun J =>
        addUp n fun o => if wt o J.val = 1 then w o (back o J.val) else zeroE := by
  unfold tableBy tableWith
  refine congrArg (Array.ofFn (n := size)) (funext fun J => ?_)
  have e : (fun o => decide (wt o (J.val % rows) = 1)) = fun o => decide (wt o J.val = 1) :=
    funext fun o => by
      show decide (wt o (J.val % rows) = 1) = decide (wt o J.val = 1)
      rw [hrow]
  show sumOver ((rowOwners rows n wt).getD (J.val % rows) []) (fun o => w o (back o J.val)) =
    addUp n fun o => if wt o J.val = 1 then w o (back o J.val) else zeroE
  rw [rowOwners_getD rows n wt _ (Nat.mod_lt _ hpos), e]
  exact (addUp_skip n (fun o => wt o J.val = 1) fun o => w o (back o J.val)).symm

/-! ## 5 The two tables -/

/-- **The group's main table, built the faster way**: the library's weight is asked once for each of the 2^k rows and
each oracle message; an entry is the sum over the messages of weight 1 at its row. w: the entries of the messages' own
main tables. -/
def closeMainF (S : Statement) (L : GroupLayout) (w : Nat → Nat → E) : Array E :=
  tableBy (2 ^ L.k) (2 ^ (L.k + L.logEll)) S.oracles.size (mainWeight (K := Int) S L) (mainBack S L) w

/-- **The group's mask table, built the faster way**: the same over the 2^h rows, with the library's weight and map
back for mask tables. w: the entries of the messages' own mask tables. -/
def closeMaskF (S : Statement) (L : GroupLayout) (w : Nat → Nat → E) : Array E :=
  tableBy (2 ^ L.h) (2 ^ (L.h + L.logEllZk)) S.oracles.size (maskWeight (K := Int) S L) (maskBack S L) w

/-- **The faster main table is the first text's**, word for word, for every statement, every layout and all
entries. -/
theorem closeMainF_eq (S : Statement) (L : GroupLayout) (w : Nat → Nat → E) :
    closeMainF S L w = closeMain S L w := by
  unfold closeMainF closeMain
  exact tableBy_eq (2 ^ L.k) (2 ^ (L.k + L.logEll)) S.oracles.size (mainWeight (K := Int) S L) (mainBack S L) w
    (Nat.two_pow_pos _) fun o J => mainWeight_row S L o J

/-- **The faster mask table is the first text's**, word for word, for every statement, every layout and all
entries. -/
theorem closeMaskF_eq (S : Statement) (L : GroupLayout) (w : Nat → Nat → E) :
    closeMaskF S L w = closeMask S L w := by
  unfold closeMaskF closeMask
  exact tableBy_eq (2 ^ L.h) (2 ^ (L.h + L.logEllZk)) S.oracles.size (maskWeight (K := Int) S L) (maskBack S L) w
    (Nat.two_pow_pos _) fun o J => maskWeight_row S L o J

/-- `closeMainF` and `closeMain` are the same function. -/
theorem closeMainF_fun : closeMainF = closeMain :=
  funext fun S => funext fun L => funext fun w => closeMainF_eq S L w

/-- `closeMaskF` and `closeMask` are the same function. -/
theorem closeMaskF_fun : closeMaskF = closeMask :=
  funext fun S => funext fun L => funext fun w => closeMaskF_eq S L w

/-! ## 6 What the closing hands to the fold -/

/-- **The text of `closeAsk` (Honest/K10/Job.lean), with the builders of the two tables as parameters**: mainT builds
the group's main table, maskT its mask table. Everything else is `closeAsk`'s text line for line. The other arguments,
what is returned and the refusals are described at `closeAsk`. -/
def closeAskBy (mainT maskT : Statement → GroupLayout → (Nat → Nat → E) → Array E)
    (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    Except String (Option FoldAsk) := do
  let eB ← match (entries J.pub.par).head? with
    | some e => pure e
    | none => throw "K10: no entry"
  match J.stAt w seen front with
  | .error _ => pure none
  | .ok (S, g) =>
    let (row, L, S1) ← (bat S g eB ⟨[], x⟩).mapError fun e =>
      "K10: the verifier's batching refuses: " ++ e
    if L.k != J.pub.par.k || L.h != J.pub.par.h then
      throw "K10: the layout's k, h are not the place's"
    if row.d.size != 2 ^ (L.h + L.logEllZk) then
      throw "K10: the batched row does not fit the mask table"
    let G ← match S.groups[g]? with
      | some G => pure G
      | none => throw "K10: no group"
    let R ← J.rows w front ca
    if !rowsFit S G R then throw "K10: the group's rows do not fit the statement's group"
    let mainW := fun o => wordAt S1 R.base.ell (rowsAt G R (·.main)) o .main
    let maskW := fun o => wordAt S1 R.zk.ell (rowsAt G R (·.mask)) o .mask
    pure (some
      { k := J.pub.par.k, h := J.pub.par.h
        c := row.c.writeOut (L.k + L.logEll), d := row.d
        m := mainT S1 L mainW, mu := maskT S1 L maskW
        keptV := closeKept S1 row.kept mainW
        w := u })

/-- With `closeMain` and `closeMask` as the two builders, `closeAskBy` is `closeAsk`. -/
theorem closeAskBy_first (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    closeAskBy closeMain closeMask J w seen front x u ca = closeAsk J w seen front x u ca := rfl

/-- **What the closing hands to the fold, with the two tables built the faster way.** Arguments as `closeAsk`'s. -/
def closeAskF (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    Except String (Option FoldAsk) :=
  closeAskBy closeMainF closeMaskF J w seen front x u ca

/-- **`closeAskF` returns what `closeAsk` returns**, for every job and all arguments: the same data, or nothing, or
the same refusal. -/
theorem closeAskF_eq (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    closeAskF J w seen front x u ca = closeAsk J w seen front x u ca := by
  unfold closeAskF
  rw [closeMainF_fun, closeMaskF_fun]
  exact closeAskBy_first J w seen front x u ca

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.addF_addF_zero
#print axioms ProofFile.Honest.K10.addE_addE_zeroE
#print axioms ProofFile.Honest.K10.addE_zeroE_zeroE
#print axioms ProofFile.Honest.K10.sumOver
#print axioms ProofFile.Honest.K10.foldl_skip
#print axioms ProofFile.Honest.K10.addUp_skip
#print axioms ProofFile.Honest.K10.blockBits_row
#print axioms ProofFile.Honest.K10.mainWeight_row
#print axioms ProofFile.Honest.K10.maskWeight_row
#print axioms ProofFile.Honest.K10.rowOwners
#print axioms ProofFile.Honest.K10.rowOwners_getD
#print axioms ProofFile.Honest.K10.tableWith
#print axioms ProofFile.Honest.K10.tableBy
#print axioms ProofFile.Honest.K10.tableBy_eq
#print axioms ProofFile.Honest.K10.closeMainF
#print axioms ProofFile.Honest.K10.closeMaskF
#print axioms ProofFile.Honest.K10.closeMainF_eq
#print axioms ProofFile.Honest.K10.closeMaskF_eq
#print axioms ProofFile.Honest.K10.closeMainF_fun
#print axioms ProofFile.Honest.K10.closeMaskF_fun
#print axioms ProofFile.Honest.K10.closeAskBy
#print axioms ProofFile.Honest.K10.closeAskBy_first
#print axioms ProofFile.Honest.K10.closeAskF
#print axioms ProofFile.Honest.K10.closeAskF_eq
