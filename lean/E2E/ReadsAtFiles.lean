-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsAtFiles.lean: the library's property `HolographicProtocol.ReadsR` at the object from which `VerifierAndGoals.verify`
is compiled, with its proof of work in the rounds, at three public files Z: its clause on the table
at every Z; the whole property at every Z in scope, with the gate open or shut, and at the library's
two named sets of files; at every matrix as index, and cut to the matrices in range. Statements and
proofs.

What is shown.
  **`hidE_filesAt`**, **`hidE_objAt`**: AT EVERY Z, in scope or not, with the gate open or shut, for
    all provers P, AT EVERY OOD SEED (`HidE`, E2E/TableHides.lean): the joint law of a committed
    table's OOD answers and of any 44,040,191 of its columns, over uniform pads and encoding
    randomness, is the same for all matrices (for all matrices in range, at the cut object). No
    premise is left. An OOD seed of the object is, by type, any point of 29 coordinates in the
    extension field with any factor other than 0. The values that the library's reading of the byte
    format lays where the format's sampling runs out (a coordinate 0; the factor 1; for a missing
    OOD seed the point 0 with the factor 1: `seedOf1`, `seedOf`, OnBytes/Slice/RecordRead.lean) are
    members of that type.
  `key_data`, `proof_data`: in scope, with the gate open, the key file's and the proof file's
    rounds' data of the IOP as written in Lean are the library's written data. (The first is the
    library's `pin_at_seat`; the second is put together from four of its lemmas.)
  **`reads_filesAt`**: there, for all provers P of the three protocols `filesAt Z`
    (E2E/ObjectAtFiles.lean): `((filesAt Z).withProvers P).ReadsR 44040191 62 62 62 64`.
  **`reads_objAt`**: the same of `objAt Z P`, the object cut to the matrices in range.
  `reads_filesAt_shut`: where the gate is shut, in scope or not: `ReadsR 44040191 0 62 62 0`.
  **`reads_filesAt_scope`**, **`reads_objAt_scope`**: so the premise on the gate goes: at EVERY Z in
    scope, with the gate open or shut: `ReadsR 44040191 62 62 62 64`.
  **`reads_filesAt_named`**, `reads_objAt_named`: at the library's two named sets of public files
    (`VerifierAndGoals.NamedFiles`): the same, with no premise.

In plain words, at such Z. At every verifier randomness the key file's verifier reads at most 62
columns of the first table; the verifier of a copy's file at most 62 columns of the first table and
62 of the copy; one batch, all its requests together, at most 64 columns of its copy. And at every
OOD seed the joint law of a committed table's OOD answers and of any 44,040,191 of its columns, over
uniform pads and encoding randomness, is the same for all matrices.

The premises of the counts. `scope`: the library's test `InScope` on the three public files: the
layout is the stored one, the policy file has the standard form. The library shows it of its two
named sets of public files (`VerifierAndGoals.filesRead`, Johnson/Goal/Files/FilesReadProof.lean), so at these
two no premise is left (`reads_filesAt_named`). `live`: the tests that the IOP's own gate runs on
the files (`protocolDataWellFormed`). That it accepts any Z is shown nowhere here; the counts do not need it:
where the gate is shut the key file's and the proof file's rounds' data are three empty lists each
(`data_shut`), so these two verifiers read no column there (`reads_filesAt_shut`). Out of scope with
the gate open the rounds' data hang on the files, and nothing is said on the counts.

Limits.
- THE PROVERS ARE NOT READ. The statement holds for every P, also for provers that send fixed
  messages. It says nothing on what a prover's messages show, and it is no statement of zero
  knowledge of any protocol.
- Counts for ONE run each. The budget of a table is the user's to add up: a copy that serves one
  link proof and n batches is read at no more than 62 + 64 n columns, the first table under one
  one-time proof and m link proofs at no more than 62 + 62 m. No theorem here adds them up, and no
  verifier tests them.
- One OOD seed for each table, fixed before the sampling (E2E/TableHides.lean's limits). One table's
  randomness is used under one set of public files alone. The same rows and pads under other public
  files would get another seed, and of two OOD samples on one table's pads this file says nothing.
- All limits of E2E/ReadsAtWritten.lean, E2E/ReadsCount.lean and E2E/ObjectAtFiles.lean stand.

The statements under `Spec.` say what is to be proved at public files Z: they may be read as goals.
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
import E2E.ReadsAtWritten
import E2E.ObjectAtFiles
import Johnson.Goal.Conditions.KeyAtTheSeat
import Johnson.Goal.Conditions.LiveAtThe
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Flat.Dec.DataAtWritten
import Johnson.P5J.AtName
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Reads
open Iop Prob Hiop
open OnBytes.Slice (frS frZ)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (XF)
open AtPublicFiles.AtFiles (filesAt objAt FullSizeMatrix inRange)
open AtPublicFiles.Table (HidE)

/-! ## 1. The committer's side: at every Z -/

/-- The clause is kept by a cut of the index type. General in the object. -/
theorem hidE_cut {I X : Type} {L : HolographicProtocol I X} (p : I → Prop) {b : ℕ} (h : HidE L b) :
    HidE (AtPublicFiles.Cut.cut L p) b :=
  fun S hS s i i' => h S hS s i.1 i'.1

/-- **At every Z, for all provers, at every OOD seed**: the law of (all rows' OOD answers, any
44,040,191 columns of the table), over pads and encoding randomness, is the same for all matrices.
The clause `hidE` of `HolographicProtocol.ReadsR` at the three protocols from which the verifier is compiled. -/
theorem hidE_filesAt (Z : PublicFiles) (P : (filesAt Z).Provers) : HidE ((filesAt Z).withProvers P) 44040191 :=
  AtPublicFiles.Table.obj_hidE_full _ Subtype.val (filesAt Z) P

/-- **The same at the object cut to the matrices in range.** -/
theorem hidE_objAt (Z : PublicFiles) (P : (filesAt Z).Provers) : HidE (objAt Z P) 44040191 :=
  hidE_cut (I := FullSizeMatrix) (X := XF) inRange (hidE_filesAt Z P)

/-! ## 2. The counts: in scope, with the gate open -/

/-- In scope, with the gate open, the key file's data are the library's written data. -/
theorem key_data (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK.at frS.P.T.a = Johnson.G.writtenKFull :=
  VerifierAndGoals.AtTheName.pin_at_seat Z scope live

/-- In scope, with the gate open, the proof file's data are the library's written data. -/
theorem proof_data (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DP.at frS.P.T.a = Johnson.G.writtenPFull :=
  (congrArg (fun D : WholeD => D.at frS.P.T.a)
    ((FlashProve.dp_built_live Z live).trans
      (LPFD.Full.laidPOf_written scope (P5J.laid_at_name live)))).trans
    VerifiableInference.OnPublicFiles.writtenPFull_at

/-- The statement of `reads_filesAt`. -/
def Spec.reads_filesAt : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ P : (filesAt Z).Provers,
    ((filesAt Z).withProvers P).ReadsR 44040191 62 62 62 64

/-- **`ReadsR` at the three protocols from which the verifier is compiled**, with their proof of
work in the rounds, at every Z in scope at which the gate is open, for all provers. The index is any
matrix. -/
theorem reads_filesAt : Spec.reads_filesAt :=
  fun Z scope live P =>
    reads_written XF _ Subtype.val (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK
      (dataAtFiles flashProveData Z).runP (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
      (dataAtFiles flashProveData Z).G.z₀.2 (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves
      (dataAtFiles flashProveData Z).G.early (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) P (key_data Z scope live)
      (proof_data Z scope live)

/-- The statement of `reads_objAt`. -/
def Spec.reads_objAt : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ P : (filesAt Z).Provers,
    (objAt Z P).ReadsR 44040191 62 62 62 64

/-- **The same of the object cut to the matrices in range.** -/
theorem reads_objAt : Spec.reads_objAt :=
  fun Z scope live P =>
    AtPublicFiles.Cut.reads_cut (I := FullSizeMatrix) (X := XF) inRange (reads_filesAt Z scope live P)

/-! ## 3. The counts without the premise on the gate -/

/-- Where the gate is shut the key file's and the proof file's data are three empty lists each. -/
theorem data_shut (Z : PublicFiles) (shut : protocolDataWellFormed (asDescriptionFiles Z) = false) :
    (dataAtFiles flashProveData Z).DK = FlashProve.emptyRoundsData ∧ (dataAtFiles flashProveData Z).DP = FlashProve.emptyRoundsData := by
  constructor
  · show flashProveData.keyRoundsOrEmpty (asDescriptionFiles Z) = _
    unfold FlashProve.DescriptionData.keyRoundsOrEmpty
    rw [show flashProveData.live (asDescriptionFiles Z) = false from shut]
    rfl
  · show flashProveData.proofRoundsOrEmpty (asDescriptionFiles Z) = _
    unfold FlashProve.DescriptionData.proofRoundsOrEmpty
    rw [show flashProveData.live (asDescriptionFiles Z) = false from shut]
    rfl

/-- These data have the sums 0. -/
theorem dead_sums : storedSum FlashProve.emptyRoundsData.ds₁ = 0 ∧ storedSum FlashProve.emptyRoundsData.ds₂ = 0 ∧
    storedSum FlashProve.emptyRoundsData.ds₃ = 0 := by decide +kernel

/-- **Where the gate is shut**, in scope or not: the key file's verifier and a batch read no column;
the verifier of a copy's file, whose rounds' data do not hang on Z, at most 62 and 62. -/
theorem reads_filesAt_shut (Z : PublicFiles) (shut : protocolDataWellFormed (asDescriptionFiles Z) = false)
    (P : (filesAt Z).Provers) : ((filesAt Z).withProvers P).ReadsR 44040191 0 62 62 0 :=
  reads_fullD (dataAtFiles flashProveData Z).A (OnBytes.Flat.relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF
    PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) P
    (by
      rw [(data_shut Z shut).1]
      show storedSum FlashProve.emptyRoundsData.ds₁ +
        (storedSum FlashProve.emptyRoundsData.ds₂ + storedSum FlashProve.emptyRoundsData.ds₃) ≤ 0
      rw [dead_sums.1, dead_sums.2.1, dead_sums.2.2])
    (by rw [(data_shut Z shut).2]; exact dead_sums.1)
    (by rw [(data_shut Z shut).2]; exact dead_sums.2.1.le)
    (by rw [(data_shut Z shut).2]; exact dead_sums.2.2)
    link_own link_counts.1.le link_counts.2.le
    (AtPublicFiles.Table.hides_full XF _ Subtype.val 44040191 (Nat.le_refl _))

/-- The four counts may be raised. -/
theorem reads_mono {I X : Type} {L : HolographicProtocol I X} {b qT qpar qch qon qT' qpar' qch' qon' : ℕ}
    (h : L.ReadsR b qT qpar qch qon) (hT : qT ≤ qT') (hp : qpar ≤ qpar') (hc : qch ≤ qch')
    (ho : qon ≤ qon') : L.ReadsR b qT' qpar' qch' qon' :=
  ⟨fun x ρ => (h.cntT x ρ).trans hT, fun x ρ => (h.cntLp x ρ).trans hp,
    fun x ρ => (h.cntLc x ρ).trans hc, fun x ρ => (h.cntB x ρ).trans ho, h.hidE⟩

/-- The statement of `reads_filesAt_scope`. -/
def Spec.reads_filesAt_scope : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → ∀ P : (filesAt Z).Provers,
    ((filesAt Z).withProvers P).ReadsR 44040191 62 62 62 64

/-- **`ReadsR` at every Z in scope, with the gate open or shut**, for all provers. -/
theorem reads_filesAt_scope : Spec.reads_filesAt_scope := fun Z scope P => by
  cases live : protocolDataWellFormed (asDescriptionFiles Z) with
  | true => exact reads_filesAt Z scope live P
  | false =>
    exact reads_mono (reads_filesAt_shut Z live P) (Nat.zero_le _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.zero_le _)

/-- The statement of `reads_objAt_scope`. -/
def Spec.reads_objAt_scope : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → ∀ P : (filesAt Z).Provers,
    (objAt Z P).ReadsR 44040191 62 62 62 64

/-- **The same of the object cut to the matrices in range.** -/
theorem reads_objAt_scope : Spec.reads_objAt_scope :=
  fun Z scope P => AtPublicFiles.Cut.reads_cut (I := FullSizeMatrix) (X := XF) inRange (reads_filesAt_scope Z scope P)

/-- **At the library's two named sets of public files no premise is left.** -/
theorem reads_filesAt_named (Z : PublicFiles) (h : VerifierAndGoals.NamedFiles Z) (P : (filesAt Z).Provers) :
    ((filesAt Z).withProvers P).ReadsR 44040191 62 62 62 64 := by
  rcases h with rfl | rfl
  · exact reads_filesAt_scope _ VerifierAndGoals.filesRead.full.1 P
  · exact reads_filesAt_scope _ VerifierAndGoals.filesRead.other.1 P

theorem reads_objAt_named (Z : PublicFiles) (h : VerifierAndGoals.NamedFiles Z) (P : (filesAt Z).Provers) :
    (objAt Z P).ReadsR 44040191 62 62 62 64 :=
  AtPublicFiles.Cut.reads_cut (I := FullSizeMatrix) (X := XF) inRange (reads_filesAt_named Z h P)

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.hidE_cut
#print axioms AtPublicFiles.Reads.hidE_filesAt
#print axioms AtPublicFiles.Reads.hidE_objAt
#print axioms AtPublicFiles.Reads.key_data
#print axioms AtPublicFiles.Reads.proof_data
#print axioms AtPublicFiles.Reads.reads_filesAt
#print axioms AtPublicFiles.Reads.reads_objAt
#print axioms AtPublicFiles.Reads.data_shut
#print axioms AtPublicFiles.Reads.dead_sums
#print axioms AtPublicFiles.Reads.reads_filesAt_shut
#print axioms AtPublicFiles.Reads.reads_filesAt_scope
#print axioms AtPublicFiles.Reads.reads_objAt_scope
#print axioms AtPublicFiles.Reads.reads_filesAt_named
#print axioms AtPublicFiles.Reads.reads_objAt_named
