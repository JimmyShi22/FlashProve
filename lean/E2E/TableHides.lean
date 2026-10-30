-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TableHides.lean: at every OOD seed the joint law of a committed table's OOD answers and of any
44,040,191 of its columns is the same for all matrices. Statements and proofs.

It joins E2E/TableStrong.lean (a few columns, over the encoding randomness) and E2E/TableMasked.lean
(the OOD answers, over the pads) by the library's `rec_hides_of_rows` (Hiop/RecRows.lean), first at
any size, then at the full size's code: Reed-Solomon over the base field, 2^32 columns, 2^11 rows,
402,653,184 entries in a row's message, of which the last three are the row's pad, and 44,040,191
elements of encoding randomness in each row.

What is shown.
  `hides_cells`: at any size S with at most 2^32 columns whose rows end in a pad of three entries:
    the configuration `confCells` has the library's `ConfigurationWithOutOfDomainSample.Hides` at every b ≤ r, r the number of
    elements of encoding randomness in a row.
  `full_numbers`: the four numbers of the full size's code and table that stand above.
  **`hides_full`**: at the full size's decoder, sample map, cut and matrix, for every table pp of
    scales and policy and every reading req of instances: `ConfigurationWithOutOfDomainSample.Hides b` at every b ≤ 44,040,191.
  `HidE L b`: the clause `hidE` of `HolographicProtocol.ReadsR` (Hiop/RecInterface.lean), alone, as a name.
  **`obj_hidE`**: for EVERY configuration C, all three protocols F over it and all honest provers P:
    `C.Hides b` gives `HidE (F.withProvers P) b`. Neither F nor P is read: the clause speaks of the
    committer's side alone.
  `obj_hidE_full`: the two together.

What `Hides b` says, written out. Fix a set Q of at most b columns and an OOD seed s. Sample the
pads and the encoding randomness uniformly. Then the pair (all rows' OOD answers at s, the columns
at Q) has a law that is the same for all matrices. "All matrices" is every matrix of cells of the
full size's shape, in range or not.

Limits.
- Q AND s ARE FIXED BEFORE THE SAMPLING. A verifier that chooses columns after it has seen answers
  or other columns is not treated here: that step is the library's theorem on the whole object.
  In the byte format the OOD seed is derived by hash from the table's root (the head of
  OnBytes/Slice/RecordRead.lean), so after, and from, what was sampled. Nothing here treats an OOD
  seed that hangs on the table: that is a matter of the compiled protocol.
- ONE OOD seed for each table, and b counts ALL columns of that table that are ever opened, by
  whichever protocol. One table's randomness is used under one set of public files alone. The same
  rows and pads under other public files would get another seed, and of two OOD samples on one
  table's pads this file says nothing. (In the byte format the OOD seed is derived from the table's
  root and the digest of the public files: the head of OnBytes/Slice/RecordRead.lean.) Each
  committed table (the first table, each copy) needs pads and encoding randomness of its own.
- At b = 0 the statement is on the OOD answers alone. The number 44,040,191 is the code's r. At one
  column more the first step of the proof fails (E2E/TableStrongGuard.lean), and so does the clause
  itself: `not_hides_full`, `not_hidE_full`, `differ_at_full` (E2E/TableHidesGuard.lean),
  `not_hidE_filesAt`, `not_hidE_objAt`, `every_set_objAt` (E2E/TableHidesGuardAtFiles.lean): by the
  last at some OOD seed, at two matrices in range, at every set of 44,040,192 positions; no size of
  the difference is stated there.
- The statement is on the table's columns and OOD answers. It is not on a Merkle root, on salts, on
  authentication paths, or on any message of a prover: what the three protocols' provers send
  about a table beyond opened columns is not covered.
- Of a cell the encoder reads the first coordinate alone: two matrices that differ outside the base
  field alone have the same tables (the head of Johnson/Flat/CodingCells.lean). No matrix in range
  has such a cell.
- It says "the same law for all matrices". It names no simulator and is no statement of zero
  knowledge of any protocol.
- All limits of E2E/TableStrong.lean and E2E/TableMasked.lean stand: nothing is said on what a
  program writes or how it samples.

`HidE` and `Spec.hides_full` are statements on an encoder: they may be read as a goal.
They are not among this library's goals.

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
import E2E.TableStrong
import E2E.TableMasked
import OnBytes.Slice.FullRecLink
import OnBytes.Flat.Object

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Table
open Iop Prob Hiop
open OnBytes.Flat (Files relationsAndEncodingOfClaims codingCells MatrixNums claimsLedgerOnAt)
open OnBytes.Slice (Sz GE recZ frS frZ)
open VerifiableInference.OnPublicFiles (numsRef)

/-- The property at b gives it at every smaller number. -/
theorem strong_mono {C : ConfigurationWithOutOfDomainSample} {b b' : ℕ} (h : C.Strong b) (hb : b' ≤ b) : C.Strong b' :=
  fun Q hQ => h Q (hQ.trans hb)

/-- **At any size**: the code has at most 2^32 columns (ha), and the last three entries of a row's
message are its pad (hc). Then at every OOD seed the law of (OOD answers, any b columns), over pads
and encoding randomness, is the same for all matrices, for every b up to the number of elements of
encoding randomness in a row. -/
theorem hides_cells (S : Sz) (cut lg : ℕ) (N : MatrixNums) {X : Type} (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref) (ha : S.P.T.a ≤ 32)
    (hc : cut + 3 = S.P.T.l) (b : ℕ) (hb : b ≤ S.P.T.r) :
    (confCells S cut lg N pp req).Hides b :=
  rec_hides_of_rows _ (rowsOf S cut lg N pp req) b (rowsOf_laws S cut lg N pp req hc)
    (strong_mono (strong_codingHonest S (recZ S.P.T.l lg 1) cut
      (claimsLedgerOnAt (S.toDecR (recZ S.P.T.l lg 1) cut) N pp req) (OnBytes.Flat.PadsOf S cut)
      (OnBytes.Flat.cellWords S (recZ S.P.T.l lg 1) cut N) ha) hb)

/-- The full size's numbers, as this file's head says them: 2^32 columns, 402,653,184 entries in a
row's message, 44,040,191 elements of encoding randomness in a row, 2^11 rows. -/
theorem full_numbers : frS.P.T.a = 32 ∧ frS.P.T.l = 402653184 ∧ frS.P.T.r = 44040191 ∧
    frS.P.v = 11 := ⟨rfl, rfl, rfl, rfl⟩

/-- The statement of `hides_full`. -/
def Spec.hides_full : Prop :=
  ∀ (X : Type) (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref) (b : ℕ),
    b ≤ 44040191 →
      (OnBytes.Slice.DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
        (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req))).Hides b

/-- **At the full size's code**: at every OOD seed the law of (all rows' OOD answers, any b columns
of the table), over pads and encoding randomness, is the same for all matrices, for every
b ≤ 44,040,191. -/
theorem hides_full : Spec.hides_full :=
  fun _ pp req b hb => hides_cells frS 402653181 29 numsRef pp req (Nat.le_refl 32) rfl b hb

/-- The clause `hidE` of `HolographicProtocol.ReadsR` (Hiop/RecInterface.lean), alone, to the letter: for every set
S of at most b positions, every OOD seed s and all indices i, i': over the committer's uniform
randomness the pair (honest OOD answers at s, the encoded index at S) has the same law at i and at
i'. -/
def HidE {I X : Type} (L : HolographicProtocol I X) (b : ℕ) : Prop :=
  ∀ (S : Finset (Fin L.wordLength)), S.card ≤ b →
    ∀ (s : L.OutOfDomainSeed) i i', (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i r s, fun p : S => L.encodeIndex i r p)) =
      (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i' r s, fun p : S => L.encodeIndex i' r p))

/-- It is that clause. -/
theorem hidE_of_reads {I X : Type} {L : HolographicProtocol I X} {b qT qpar qch qon : ℕ}
    (h : L.ReadsR b qT qpar qch qon) : HidE L b := h.hidE

/-- **In the words of an object with OOD samples**: the property of the configuration is the clause
`hidE` of `HolographicProtocol.ReadsR` at `F.withProvers P`, for all three protocols F and all honest provers P. -/
theorem obj_hidE {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) {b : ℕ} (h : C.Hides b) :
    HidE (F.withProvers P) b :=
  fun Q hQ s i i' => h Q hQ s i i'

/-- **The clause at the full size**, for all three protocols over the full size's configuration and
all honest provers. -/
theorem obj_hidE_full {X : Type} (pp : Inst.Model.ScalesAndPolicy)
    (req : X → Inst.Model.Instance Inst.Model.ppref)
    (F : Files (OnBytes.Slice.DecR.configurationOfStoredTable
      (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
      (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req)))) (P : F.Provers) :
    HidE (F.withProvers P) 44040191 :=
  obj_hidE F P (hides_full X pp req 44040191 (Nat.le_refl _))

end AtPublicFiles.Table

#print axioms AtPublicFiles.Table.hides_cells
#print axioms AtPublicFiles.Table.full_numbers
#print axioms AtPublicFiles.Table.hides_full
#print axioms AtPublicFiles.Table.hidE_of_reads
#print axioms AtPublicFiles.Table.obj_hidE
#print axioms AtPublicFiles.Table.obj_hidE_full
