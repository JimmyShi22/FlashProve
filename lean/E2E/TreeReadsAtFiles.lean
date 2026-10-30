-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TreeReadsAtFiles.lean: the property `FileWithin` (E2E/TreeReads.lean) at the IOP from which
`VerifierAndGoals.verify` is compiled: at its own rounds' data and at the sizes of its own public part, at
three public files Z in scope at which its gate is open. Statements and proofs.

In plain words, at such Z. For every tree that a run of the key file's, the proof file's or a copy's
file's protocol sends, the sampled positions of all declared rounds that open it, repeats counted,
are at most r, the number of elements of encoding randomness of each row beneath it: over the three
chains (Fiat-Shamir hash chains) of a file, and in the proof file over all 64 requests of a batch.
So, at every verifier randomness, each row is read at no more than r distinct positions of its own
code: the statements on positions take `ThreeWithin` and the letters of a whole file's verifier (f,
tF, tJ, t3 and the data DP); closed at Z are `three_of_laid`, `three_atFiles` and `slots_atFiles`;
no closed statement at Z on positions is typed. One sampled position more in any round that opens a
tree, or a 65th request, makes the property false.

The two premises. `scope`: the library's test `InScope` on the three public files. `live`: the tests
that the IOP's own gate runs on them (`protocolDataWellFormed`). Both are evaluations: that they accept any Z is
shown nowhere here (at the library's two named sets of public files:
AtFullSide/E2E/AtWrittenFiles.lean).

Whose the two sides are.
  The rounds' data are the object's own: `(dataAtFiles flashProveData Z).DK` and `.DP` at the tables' depth, and
    the written rounds of a copy's file: the data over which the three protocols are made
    (E2E/ObjectAtFiles.lean, `filesAt`). In scope, with the gate open, they are the library's
    written data (`key_data`, `proof_data`: the library's `pin_at_seat`, and four of its lemmas; the
    same two equations stand in E2E/ReadsAtFiles.lean).
  The sizes, with the codes, are those of the public part Zp that the proof file's IOP as written in
    Lean (below: its description) computes from Z: `Zp.p.chains.made.sized`. `P5J.LaidAt`
    (Johnson/P5J/LaidOpens.lean) says what ties Zp to the object: the description made of Zp has the
    object's rounds' data and its decision. With the gate open such a Zp exists (`laid_opens`); in
    scope its sizes are the written ones (`sized_at`: the library's `pins_of_laid` and
    `made_in_scope`).

What is shown.
  `sized_at`, `key_data`, `proof_data`: the pins.
  `ThreeWithin DK DP z`: `FileWithin` for the three files at rounds' data DK, DP and sizes z; the
    number of requests in a batch is the sizes' own, `z.lines.slots` (`written_slots`: 64).
  **`three_of_laid`**: in scope, with the gate open, for EVERY Zp of which `LaidAt` holds:
    `ThreeWithin` at the object's data and Zp's sizes.
  **`three_atFiles`**: and there is such a Zp, tied to the object's own data and decision.
    (`LaidAt.pub` is an equation for Zp: at most one.)
  **`more_breaks_atFiles`**, **`one_request_more_atFiles`**: there, at the same table, the property
    of the proof file is false with one sampled position more in any round that opens a tree, and
    with one request more than the sizes say.
  **`slots_atFiles`**: there the object's number of requests in a batch, its slots (`Files.N`,
    OnBytes/Flat/Frame.lean), is 64.
  `fits_ckP`: the kit of the object's protocols samples as many positions as a round's entry says.
  **`proof_batch_points`**, **`proof_slots_points`**, **`proof_run_points`**: the proof file's
    verifier itself, under `ThreeWithin`: over no more runs than the sizes say, with the same
    verifier messages in the second chain, at every verifier randomness, every row beneath a tree
    that the batch shares is read at no more than r distinct positions of its own code; the same
    over the slots of the library's own batch; and every row beneath a request's own tree in one
    run.

How this stands to the conditions that the programs ask of the parameters. These conditions
(OnBytes/Params/Gate.lean) compare r with numbers of positions too, stage by stage of each proximity
test. Which list of positions reads which rows is written into their text by hand. Here it is read
off the declared rounds: which trees each round opens; and off `layTrees`: which rows lie beneath a
tree. So the two are different statements, and neither is used for the other.

Limits.
- WHERE THE GATE IS SHUT NOTHING IS SAID: the key file's and the proof file's rounds' data are then
  three empty lists each.
- It speaks of the verifier's declared rounds alone. No prover, no coin and no witness occurs: it is
  no statement on what a prover's messages show, and none of zero knowledge.
- NOT EVERY ROW IS FILLED: E2E/TreeReadsAtWritten.lean's head names the three rows a file with more
  encoding randomness than reads, and the one tree a file without a filled row.
- For the key file and a copy's file nothing ties Zp's sizes to their protocols but that both sides
  are pinned to written values: Zp is the public part of the PROOF file's description.
- THE COUNT IS BY TREE, and positions of trees alone are counted: E2E/TreeReads.lean's limits.
- THE TABLE IS A READING: that the decision's sub-protocols treat a row beneath a tree as a word of
  the code that the table names is not shown: the table is made of the sizes by E2E/TreeRows.lean's
  lists, and E2E/TreeReadsAtWritten.lean's limits say at which trees another code of the same length
  would make the property false.
- The positions counted are those that the protocol declares as read. That its decision hangs on the
  oracles at these alone is the library's `wholeIOR_local` (OnBytes/Maker/WholeLocal.lean).
- The theorems on positions in this file are typed for the proof file. For the key file and for a
  copy's file, whose verifier is of another make (`linkProtocolOfRoundData`, OnBytes/Flat/LinkSib.lean), they are in
  E2E/TreeReadsKeyAndCopy.lean, with limits of their own.
- All limits of E2E/TreeReads.lean, E2E/TreeRows.lean and E2E/TreeReadsAtWritten.lean stand. Nothing
  on hiding follows from this file alone.

`ThreeWithin` and the statements under `Spec` may be read as part of a goal. They count as none.


-/
import E2E.TreeReadsAtWritten
import Johnson.Goal.Conditions.KeyAtTheSeat
import Johnson.Goal.Conditions.LiveAtThe
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Flat.Dec.DataAtWritten
import Johnson.P5J.AtName
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Goal.Numbers.MadeInScope
import Run.PlanPull
import E2E.ObjectAtFiles
import Johnson.Goal.Description.PlanKey
import Johnson.Desc.ProofFile.Law.PlainIsPlanned

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.TreeReads
open VerifiableInference VerifiableInference.PlanWritten VerifiableInference.Number.ByRuns
open VerifiableInference.PlanWritten.Joined (writtenSized writtenMade made_in_scope)
open VerifiableInference.Desc (Chain)
open OnBytes OnBytes.Params Johnson.G Johnson.G.MadeFree Lk6.AtPlan
open OnBytes.Maker
open OnBytes.Slice (frS frZ)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData theProofData theProofRun)
open P5J

/-! ## 1. The pins -/

/-- In scope, with the gate open, the key file's data are the library's written data. -/
theorem key_data (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK.at frS.P.T.a = writtenKFull :=
  VerifierAndGoals.AtTheName.pin_at_seat Z scope live

/-- In scope, with the gate open, the proof file's data are the library's written data. -/
theorem proof_data (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DP.at frS.P.T.a = writtenPFull :=
  (congrArg (fun D : WholeD => D.at frS.P.T.a)
    ((FlashProve.dp_built_live Z live).trans
      (LPFD.Full.laidPOf_written scope (P5J.laid_at_name live)))).trans
    VerifiableInference.OnPublicFiles.writtenPFull_at

/-- In scope the sizes of a public part that is tied to the object are the written sizes. -/
theorem sized_at {Z : PublicFiles} (scope : InScope Z = true) {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    Zp.p.chains.made.sized = writtenSized :=
  congrArg Free.sized (made_in_scope scope L.pub (pins_of_laid scope L).1)

theorem written_key : writtenSized.key = keyFull := rfl
theorem written_proof : writtenSized.proof = proofSizedFull := rfl
theorem written_link : writtenSized.link = writtenLink := rfl
theorem written_codes : writtenSized.entryCodes = recordCodes := rfl
theorem written_set : writtenSized.set = recordSet := rfl

/-- The written sizes' number of requests in a batch. -/
theorem written_slots : writtenSized.lines.slots = 64 := by decide +kernel

/-- The data with another depth of the tables open the same. -/
theorem opensOf_at (D : WholeD) (a : ℕ) : opensOf (D.at a) = opensOf D := rfl

/-! ## 2. The property -/

/-- What is said of the three files, at rounds' data DK, DP and sizes z. The number of requests in a
batch is the sizes' own. -/
def ThreeWithin (DK DP : WholeD) (z : Sized) : Prop :=
  FileWithin (opensOf DK) 1 (tableKey DK z.key z.set.samples) 21 keySlack ∧
    FileWithin (opensOf DP) z.lines.slots (tableProof DP z.proof z.set.samples) 98 proofSlack ∧
    FileWithin (opensOne PV.EntryFive.dsF) 1
      (tableLink PV.EntryFive.dsF z.link z.entryCodes z.set.samples) 5 []

/-- At the written values. -/
theorem three_written : ThreeWithin writtenKFull writtenPFull writtenSized := by
  unfold ThreeWithin
  rw [written_key, written_proof, written_link, written_codes, written_set, written_slots]
  exact ⟨file_key, file_proof, file_link⟩

/-- The statement of `three_of_laid`. -/
def Spec.three_of_laid : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl),
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
      ThreeWithin ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
        Zp.p.chains.made.sized

/-- **In scope, with the gate open: the reads of every tree lie within the encoding randomness of
every row beneath it**, at the object's rounds' data and the sizes of every public part Zp of which
`LaidAt` holds, at whatever data D and decision r. (`LaidAt.pub` is an equation for Zp: there is at
most one.) -/
theorem three_of_laid : Spec.three_of_laid := fun Z scope live _ _ _ _ _ L => by
  rw [key_data Z scope live, proof_data Z scope live, sized_at scope L]
  exact three_written

/-- The statement of `three_atFiles`. -/
def Spec.three_atFiles : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl),
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z)) (theProofRun (asDescriptionFiles Z))
        Zp Np cF ∧
      ThreeWithin ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
        Zp.p.chains.made.sized

/-- **And such a public part exists**: the one that the proof file's description computes. -/
theorem three_atFiles : Spec.three_atFiles := fun Z scope live => by
  obtain ⟨Zp, Np, cF, L⟩ := laid_opens (laid_at_name live)
  exact ⟨Zp, Np, cF, L, three_of_laid Z scope live _ _ Zp Np cF L⟩

/-! ## 3. It can fail -/

/-- One sampled position more in any round of the proof file that opens a tree makes its property
false. General in the data and the sizes. -/
theorem proof_more_breaks_of {DK DP : WholeD} {z : Sized} (h : ThreeWithin DK DP z)
    (hN : 0 < z.lines.slots) {T : List Beneath}
    (e : tableProof DP z.proof z.set.samples = some T) (c i : ℕ) (p : ℕ × List ℕ)
    (hp : ((opensOf DP).chain c)[i]? = some p) (hne : p.2 ≠ []) :
    ¬ Within ((opensOf DP).more c i) z.lines.slots T :=
  FileWithin.more_breaks h.2.1 hN e c i p hp hne

/-- The statement of `more_breaks_atFiles`. -/
def Spec.more_breaks_atFiles : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl),
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
      ∀ T : List Beneath,
        tableProof ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) Zp.p.chains.made.sized.proof
          Zp.p.chains.made.sized.set.samples = some T →
        ∀ (c i : ℕ) (p : ℕ × List ℕ),
          ((opensOf ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)).chain c)[i]? = some p → p.2 ≠ [] →
          ¬ Within ((opensOf ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)).more c i)
            Zp.p.chains.made.sized.lines.slots T

/-- **In scope, with the gate open: one sampled position more in any round of the proof file that
opens a tree makes the property false.** c: the chain, from 0. i: the round's number in the chain's
data, from 0. -/
theorem more_breaks_atFiles : Spec.more_breaks_atFiles :=
  fun Z scope live D r Zp Np cF L T e c i p hp hne =>
    proof_more_breaks_of (three_of_laid Z scope live D r Zp Np cF L)
      (by rw [sized_at scope L, written_slots]; decide) e c i p hp hne

/-- The statement of `one_request_more_atFiles`. -/
def Spec.one_request_more_atFiles : Prop :=
  ∀ (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl),
      LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
      ∀ T : List Beneath,
        tableProof ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) Zp.p.chains.made.sized.proof
          Zp.p.chains.made.sized.set.samples = some T →
        ¬ Within (opensOf ((dataAtFiles flashProveData Z).DP.at frS.P.T.a))
          (Zp.p.chains.made.sized.lines.slots + 1) T

/-- **In scope, with the gate open: with one request more in a batch than the sizes say, the 65th,
the property of the proof file is false.** -/
theorem one_request_more_atFiles : Spec.one_request_more_atFiles :=
  fun Z scope live _ _ _ _ _ L T e => by
    rw [proof_data Z scope live, sized_at scope L, written_proof, written_set] at e
    rw [proof_data Z scope live, sized_at scope L, written_slots]
    exact proof_65_breaks e

/-! ## 4. At the verifier itself -/

/-- The kit of the object's protocols samples as many positions as a round's entry says. -/
theorem fits_ckP (f : _root_.Fmt.Fld) (ds : List RDT) : DrawnFitsT (_root_.Run.ckP f) ds :=
  fun d _ c => le_of_eq ((_root_.Run.planPull_fits f d.entry d.kind).2 c)

section
open Iop
variable {DK DP : WholeD} {z : Sized} {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **A tree that the batch shares**: over no more runs of the proof file's verifier than the sizes
say requests in a batch, with the same verifier messages in the second chain, at every verifier
randomness: every row beneath it is read at no more than r distinct positions of its own code.
General in the data and the sizes; f: the field's letter of the kit. -/
theorem proof_batch_points (f : _root_.Fmt.Fld) (h : ThreeWithin DK DP z) {T : List Beneath}
    (e : tableProof DP z.proof z.set.samples = some T) {j : ℕ}
    (hj : DP.t₁ ≤ j ∧ j < DP.t₁ + DP.t₂) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows) (ρs : List (Rho (chainsOf (_root_.Run.ckP f) DP tF tJ t3).sh))
    (hN : ρs.length ≤ z.lines.slots) (r₂ : Rho (uLT (_root_.Run.ckP f) DP.ds₂))
    (hsh : ∀ ρ ∈ ρs, (chainsOf (_root_.Run.ckP f) DP tF tJ t3).rho₂ ρ = r₂) :
    ((((ρs.flatMap (runLeaves (_root_.Run.ckP f) DP tF tJ t3 j))).map
      (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  obtain ⟨T', e', -, hW, -, -⟩ := h.2.1
  obtain rfl : T' = T := Option.some.inj (e'.symm.trans e)
  exact hW.batch_points tF tJ t3 (fits_ckP f _) (fits_ckP f _) (fits_ckP f _) hj hB hc ρs hN r₂ hsh

/-- **The same over the slots of the library's batch** of as many slots as the sizes say. -/
theorem proof_slots_points (f : _root_.Fmt.Fld) (h : ThreeWithin DK DP z) {T : List Beneath}
    (e : tableProof DP z.proof z.set.samples = some T) {j : ℕ}
    (hj : DP.t₁ ≤ j ∧ j < DP.t₁ + DP.t₂) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows)
    (β : BRho z.lines.slots (chainsOf (_root_.Run.ckP f) DP tF tJ t3).sh
      (chainsOf (_root_.Run.ckP f) DP tF tJ t3).ann) :
    (((((List.finRange z.lines.slots).map fun i => β.slot i).flatMap
      (runLeaves (_root_.Run.ckP f) DP tF tJ t3 j)).map (· % 2 ^ c.logN)).toFinset).card ≤ c.r := by
  obtain ⟨T', e', -, hW, -, -⟩ := h.2.1
  obtain rfl : T' = T := Option.some.inj (e'.symm.trans e)
  exact hW.slots_points tF tJ t3 (fits_ckP f _) (fits_ckP f _) (fits_ckP f _) hj hB hc β

/-- **A request's own tree**: in one run of the proof file's verifier, at every verifier randomness:
every row beneath it is read at no more than r distinct positions of its own code. -/
theorem proof_run_points (f : _root_.Fmt.Fld) (h : ThreeWithin DK DP z) {T : List Beneath}
    (e : tableProof DP z.proof z.set.samples = some T) {j : ℕ}
    (hj : ¬ (DP.t₁ ≤ j ∧ j < DP.t₁ + DP.t₂)) {B : Beneath} (hB : T[j]? = some B) {c : Code}
    (hc : c ∈ B.rows) (ρ : Rho (chainsOf (_root_.Run.ckP f) DP tF tJ t3).sh) :
    (((runLeaves (_root_.Run.ckP f) DP tF tJ t3 j ρ).map (· % 2 ^ c.logN)).toFinset).card ≤
      c.r := by
  obtain ⟨T', e', -, hW, -, -⟩ := h.2.1
  obtain rfl : T' = T := Option.some.inj (e'.symm.trans e)
  exact hW.run_points tF tJ t3 (fits_ckP f _) (fits_ckP f _) (fits_ckP f _) hj hB hc ρ

end

/-! ## 5. The object's number of slots -/

/-- In scope, with the gate open, the Merkle tree over a batch's requests has the depth 6 in the
values, computed from the public files, of which the object's three protocols are made. These values
and those inside the proof file's description come from one routine at one public part and one
constant where the digest would stand (`thePlan_key`, Johnson/Goal/Description/PlanKey.lean;
`pub_chainsOf`, Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean), and the second are held to the
written value. -/
theorem logLeaves_atFiles (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves = 6 := by
  obtain ⟨X₀, m, hX, -, hG, hc, -⟩ := FlashProve.thePlan_key Z live
  obtain ⟨Zp, Np, cF, L⟩ := laid_opens (laid_at_name live)
  obtain rfl : X₀ = Zp.p.X := Except.ok.inj (hX.symm.trans L.publicO)
  have ech : m.p.chains = Zp.p.chains :=
    Except.ok.inj (hc.symm.trans (ProofFile.Law.pub_chainsOf L.pub))
  have hf : Zp.first.binding = ⟨6, 40⟩ :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope scope L.pub
      (pins_of_laid scope L).1).2.2.2.2.1
  rw [FlashProve.g_built_live Z live, hG]
  show m.p.chains.proof.first.binding.logLeaves = 6
  rw [ech]
  exact congrArg (·.logLeaves) hf

/-- **In scope, with the gate open, the object has 64 slots**: as many as the sizes say requests in
a batch. -/
theorem slots_atFiles (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (AtPublicFiles.AtFiles.filesAt Z).N = 64 := by
  show 2 ^ (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves = 64
  rw [logLeaves_atFiles Z scope live]
  rfl

end AtPublicFiles.TreeReads

#print axioms AtPublicFiles.TreeReads.key_data
#print axioms AtPublicFiles.TreeReads.proof_data
#print axioms AtPublicFiles.TreeReads.sized_at
#print axioms AtPublicFiles.TreeReads.written_slots
#print axioms AtPublicFiles.TreeReads.three_written
#print axioms AtPublicFiles.TreeReads.three_of_laid
#print axioms AtPublicFiles.TreeReads.three_atFiles
#print axioms AtPublicFiles.TreeReads.proof_more_breaks_of
#print axioms AtPublicFiles.TreeReads.more_breaks_atFiles
#print axioms AtPublicFiles.TreeReads.one_request_more_atFiles
#print axioms AtPublicFiles.TreeReads.fits_ckP
#print axioms AtPublicFiles.TreeReads.proof_batch_points
#print axioms AtPublicFiles.TreeReads.proof_slots_points
#print axioms AtPublicFiles.TreeReads.proof_run_points
#print axioms AtPublicFiles.TreeReads.logLeaves_atFiles
#print axioms AtPublicFiles.TreeReads.slots_atFiles
