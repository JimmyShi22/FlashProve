-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TableStrong.lean: a few columns of a committed table, as the format's own encoder writes it,
have a law that does not depend on the rows' messages. Definitions, statements and proofs.

The encoder. A committed table has 2^v rows and 2^a columns. Each row is a Reed-Solomon code word:
the values, at 2^a points of the base field, of the polynomial whose lowest r coefficients are the
row's encoding randomness and whose next l coefficients are the row's message (pads included). A
column holds its position and one 64-bit word for each row. This is the encoder of
`codingHonest` (OnBytes/Flat/CodingHonest.lean): `honestTab` at `rowWords` and `tailWords`, made
with the format's `Fmt.M1.symF`. Each row has its own r elements of encoding randomness.

What is shown.
  `ok_symF`, `ofF_toF`, `symF_word`: a symbol that the encoder writes is a word below the prime, so
    it is the word of its own field value. Without this, equal laws of field values would not give
    equal laws of stored words.
  `toF_sym`: the field value of a row's symbol at the position x is the message's share
    (`share`) plus the value at x of the polynomial with the row's encoding randomness as
    coefficients (the library's `Code.RS.gen` at the exponents 0, ..., r - 1).
  `honestTab_col`: so a column is `colOf` of these field values.
  `table_law`: for a ≤ 32, every set Q of at most r positions and every table of messages: over
    uniform encoding randomness the columns at Q have the law of `colOf` at uniform, independent
    field values. The right-hand side does not name the messages.
  **`strong_codingHonest`**: so the configuration with that encoder has the library's property
    `ConfigurationWithOutOfDomainSample.Strong` (Hiop/RecRows.lean) at b = r.

Who reads each letter. S (the code, the number of rows): all. Z, cut, A, Pad, holdW (the sample map,
where the pads begin, the claims, how a matrix is held): nobody here; they stand in the type of the
configuration alone. The messages are under "for all": every function on (row, entry), whether or
not it holds a matrix; of an entry the encoder reads the first coordinate alone.

Limits.
- At r = 0 the theorem speaks of the empty set of positions and says nothing. At Q = ∅ it says
  nothing at any r.
- The bound r is a number of COLUMNS of one table, counted over everything that is ever opened of
  that table. The theorem is for one set Q that is fixed before the encoding randomness is sampled.
- That r cannot be raised is not shown in this file: E2E/TableStrongGuard.lean shows that the
  property fails at r + 1.
- The law is over the encoding randomness alone, at fixed messages, so at fixed pads. Nothing is
  said here on OOD answers, which read the messages and not the encoding randomness
  (E2E/TableMasked.lean, E2E/TableHides.lean).
- That a program writes its tables with this encoder, or samples its encoding randomness uniformly
  and anew for each table, is not said: no file of a program is compared here.
- No verifier, no protocol, no commitment, no hash function occurs here. A Merkle tree over the
  columns is not treated.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import OnBytes.Flat.CodingHonest
import OnBytes.Slice.Points
import Code.RS
import Hiop.RecRows

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Table
open Iop Prob Hiop
open OnBytes.Flat (relationsAndEncodingOfClaims Coding codingHonest rowWords tailWords)
open OnBytes.Slice (Sz GF GE toF ofF ptOf honestTab)

/-! ## A stored word is the word of its field value -/

/-- A value of the format's evaluation of a polynomial is a word below the prime. -/
theorem ok_hornerF (z : UInt64) :
    ∀ cs : List UInt64, Fmt.Fld.two.ok (Fmt.M1.hornerF z cs) = true
  | [] => by
      show Fmt.Fld.two.ok 0 = true
      decide
  | c :: cs => by
      have step : Fmt.M1.hornerF z (c :: cs) =
          Fmt.Fld.two.add c (Fmt.Fld.two.mul z (Fmt.M1.hornerF z cs)) := rfl
      rw [step]
      exact Fmt.Fld.ok_add _ _ _

/-- A symbol that the format's encoder writes is a word below the prime. -/
theorem ok_symF (C : Fmt.M1.Code) (x : ℕ) (m rho : List UInt64) :
    Fmt.Fld.two.ok (Fmt.M1.symF C x m rho) = true := by
  unfold Fmt.M1.symF
  exact ok_hornerF _ _

/-- A word below the prime is the word of its field value. -/
theorem ofF_toF (a : UInt64) (ha : Fmt.Fld.two.ok a = true) : ofF (toF a) = a :=
  OnBytes.Slice.toF_inj _ _ (OnBytes.Slice.ok_ofF _) ha (OnBytes.Slice.toF_ofF _)

/-- **A symbol that the format's encoder writes is the word of its field value.** -/
theorem symF_word (C : Fmt.M1.Code) (x : ℕ) (m rho : List UInt64) :
    Fmt.M1.symF C x m rho = ofF (toF (Fmt.M1.symF C x m rho)) :=
  (ofF_toF _ (ok_symF C x m rho)).symm

/-! ## Lists as functions -/

/-- A list made over the numbers below n is the list made over `Fin n`. -/
theorem map_range_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn fun a : Fin n => f a.val := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [List.length_map, List.length_range, List.length_ofFn]
  · rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]

variable (S : Sz)

/-- The words of the encoding randomness of row number a. -/
theorem tailWords_val (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) (a : Fin (2 ^ S.P.v)) :
    tailWords S ρ a.val = List.ofFn fun q : Fin S.P.T.r => ofF (ρ a q) := by
  unfold OnBytes.Flat.tailWords
  exact dif_pos a.isLt

/-- Read in the field, word q of the encoding randomness of row number a is its element q. -/
theorem toF_tailWords (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) (a : Fin (2 ^ S.P.v))
    (q : Fin S.P.T.r) : toF ((tailWords S ρ a.val).getD q.val 0) = ρ a q := by
  have hl : q.val < (List.ofFn fun q : Fin S.P.T.r => ofF (ρ a q)).length := by
    rw [List.length_ofFn]
    exact q.isLt
  rw [tailWords_val S ρ a, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  exact OnBytes.Slice.toF_ofF _

/-! ## A symbol's field value -/

/-- The message's share of the symbol of row number a at the position x: the values of the
monomials from the exponent r on, weighted with the message's words as they are read in the field.
-/
def share (m : S.ix.Row × S.En → GE) (a : Fin (2 ^ S.P.v)) (x : S.Pos) : GF :=
  ∑ j ∈ Finset.range S.P.T.l,
    ptOf S.P.T.a x ^ (S.P.T.r + j) * toF ((rowWords S m a.val).getD j 0)

/-- **The field value of a symbol**: the message's share, plus the value at the position's point of
the polynomial whose coefficients are the row's encoding randomness. -/
theorem toF_sym (m : S.ix.Row × S.En → GE) (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)
    (a : Fin (2 ^ S.P.v)) (x : S.Pos) :
    toF (Fmt.M1.symF S.P.T x.val (rowWords S m a.val) (tailWords S ρ a.val)) =
      share S m a x +
        Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (ρ a) x := by
  have h1 : (∑ q ∈ Finset.range S.P.T.r, toF (Fmt.M1.point S.P.T.a x.val) ^ q *
      toF ((tailWords S ρ a.val).getD q 0)) =
      Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (ρ a) x := by
    rw [Finset.sum_range, Code.RS.gen_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [toF_tailWords S ρ a q]
    exact mul_comm _ _
  rw [OnBytes.Slice.toF_symF, h1]
  exact add_comm _ _

/-! ## A column -/

/-- The stored column at the position x whose rows have the field values c. -/
def colOf (x : S.Pos) (c : Fin (2 ^ S.P.v) → GF) : _root_.Run.PQ.SgX :=
  (x.val, List.ofFn fun a => ofF (c a))

/-- **A column of the encoder's table is the column of its rows' field values.** -/
theorem honestTab_col (m : S.ix.Row × S.En → GE) (ρ : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)
    (x : S.Pos) :
    honestTab S (rowWords S m) (tailWords S ρ) x =
      colOf S x fun a => share S m a x +
        Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (ρ a) x := by
  show (x.val, (List.range (2 ^ S.P.v)).map fun b =>
      Fmt.M1.symF S.P.T x.val (rowWords S m b) (tailWords S ρ b)) = _
  rw [map_range_ofFn]
  refine congrArg (Prod.mk x.val) (congrArg List.ofFn (funext fun a => ?_))
  show Fmt.M1.symF S.P.T x.val (rowWords S m a.val) (tailWords S ρ a.val) =
    ofF (share S m a x + Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (ρ a) x)
  rw [← toF_sym S m ρ a x]
  exact symF_word _ _ _ _

/-! ## The law of a few columns -/

/-- **The law of at most r columns.** The code has at most 2^32 positions (ha), Q is a set of at
most r positions (hQ), m is any table of messages. Over uniform encoding randomness, r elements for
each row, the columns at Q have the law of the columns of uniform and independent field values. -/
theorem table_law (ha : S.P.T.a ≤ 32) (Q : Finset S.Pos) (hQ : Q.card ≤ S.P.T.r)
    (m : S.ix.Row × S.En → GE) :
    (unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
        (fun ρ => fun p : Q => honestTab S (rowWords S m) (tailWords S ρ) p) =
      (unif (Q → Fin (2 ^ S.P.v) → GF)).map (fun w => fun p : Q => colOf S p (w p)) := by
  have h := (Code.RS.ontoUpTo_gen (OnBytes.Slice.ptOf_inj S.P.T.a ha) S.P.T.r).map_uniform_table
    (R := Fin (2 ^ S.P.v)) hQ (share S m)
  calc (unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
        (fun ρ => fun p : Q => honestTab S (rowWords S m) (tailWords S ρ) p)
      = (unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
          ((fun w => fun p : Q => colOf S p (w p)) ∘
            fun μ => fun (j : Q) (a : Fin (2 ^ S.P.v)) => share S m a j +
              Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (μ a) j) :=
        congrArg (fun f => (unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map f)
          (funext fun ρ => funext fun p => honestTab_col S m ρ p)
    _ = ((unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
          fun μ => fun (j : Q) (a : Fin (2 ^ S.P.v)) => share S m a j +
            Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (μ a) j).map
          (fun w => fun p : Q => colOf S p (w p)) := (PMF.map_comp _ _ _).symm
    _ = (unif (Q → Fin (2 ^ S.P.v) → GF)).map (fun w => fun p : Q => colOf S p (w p)) :=
        congrArg (fun μ => PMF.map (fun w => fun p : Q => colOf S p (w p)) μ) h

variable (Z : Cb.Ood.Sample GE S.En) (cut : ℕ) {X : Type} (A : (S.toDecR Z cut).Claims X)
  (Pad : Type) [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)

/-- **The format's encoder is strong at b = r**: at the configuration of a committed table whose
honest side is `codingHonest`, for a code of at most 2^32 positions, the law of the table at any r
columns, over the encoding randomness alone, is the same for all tables of messages. -/
theorem strong_codingHonest (ha : S.P.T.a ≤ 32) :
    (OnBytes.Slice.DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW))).Strong S.P.T.r :=
  fun Q hQ m m' => (table_law S ha Q hQ m).trans (table_law S ha Q hQ m').symm

end AtPublicFiles.Table

#print axioms AtPublicFiles.Table.symF_word
#print axioms AtPublicFiles.Table.toF_sym
#print axioms AtPublicFiles.Table.honestTab_col
#print axioms AtPublicFiles.Table.table_law
#print axioms AtPublicFiles.Table.strong_codingHonest
