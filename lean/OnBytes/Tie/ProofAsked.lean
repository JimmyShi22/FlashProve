-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ProofAsked.lean: the asking half of a proof file's typing: the twin of the
program's reading of a proof file, with every hash asked of the oracle; then any plain map.

After the pattern of OnBytes/Tie/EntryAsked.lean (the entry file's asking half). The program's
reading of a proof file calls the hash: in the three chains' queries, in the openings' leaves and
vertices, in the binding tree, in the table's key. OnBytes/ChecksWithHashAsArgument/M/Proof/File.lean holds that
reading written once more over a monad in which the hash is asked (`M.Proof.readProof`), and
OnBytes/ChecksWithHashAsArgument/M/AtPort/ its three laws. Here it is run from the empty record of vertices, a
refusal's name is dropped, and a plain map is laid behind it, so that it has the type that a reading
in front of the proof file's arm has. Definitions, statements and proofs.

Main names:
  `askedP c table copy request words block file`: the asking half: what the reader has read, or
    nothing. request: the value of the item "request"; words: the request file's own bytes.
  `askedPAt O …`: its value at a function O in the place of the hash: plain.
  `askedP_det`: at every oracle f the asking half's result is `askedPAt` at the function that f
    induces. No hypothesis.
  `askedP_noCoin`: it tosses no coin. No hypothesis. (So "its result" is one value.)
  `askedP_le`, `askedP_asks`: at most (2 N1 + tailN … N2 N3) · 2 questions, under the
  three premises of
    `readProof_asks` (a number for each chain that holds whatever was read).
  `typedP asm …`, `typedPR asm …`: the asking half, then a plain map asm; the second in the
    library's generic language of trees, over the family with one oracle. `typedP_det`,
    `typedPR_det`, `typedPR_noCoin`, `typedPR_asks`.
  `askedPAt_oBits`: at the oracle on bit strings made from the format's hash the value is that at
    the format's own oracle.
  `ProofTwinAtO c table copy request words block file`: THE NAMED PREMISE, in the spelling of the
    key file's half: what the program's own reading of this file returns from the empty record of
    vertices, the twin's reading at the hash over the format's oracle returns too.
  `askedPAt_program`, `typedPR_program`: under it, where the program's `Proof.readProof` returns r:
    the value at the format's oracle is r, and the reading in front of the arm, at the oracle made
    from the format's hash, makes asm r.
  `asksIn_pinOn`: an algorithm whose queries at the strings of a finite set are answered by a table
    (`pinOn`, OnBytes/Slice/AtSet.lean) asks no string of that set.
  `readerP S T asm …`: THE READING IN FRONT OF THE ARM: `typedPR` with the queries at the strings of
    S answered by the table T. `readerP_off` (it asks no string of S), `readerP_det`,
    `readerP_noCoin`, `readerP_asks`, `readerP_program` (at the oracle made from the format's hash,
    if T holds that oracle's own values on S).
Limits: values and a count alone: of which strings are asked no more is said than that `readerP`
asks none of S. `ProofTwinAtO` is a premise: the two hashes agree on the hash's domain alone, and
that every call of this reading lies in it is not shown here. The three premises on numbers are not
paid here. No decision is taken on what was read. No plain map, no set of public strings and no
table is given: nothing here ties T to answers of the oracle. The proof file's half alone: in a
reading of all files the table comes from the entry file's reading. The program does not call any
function of this file. Nothing on soundness.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Lands
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Asks
import OnBytes.Tie.EntryAskedCost
import OnBytes.Slice.OverSelf
import Rom.SigmaExits

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort
open ZKCP
open OnBytes.Params (TableName ProofChains)
open OnBytes.Proof (FirstEnd ProofRead)

/-- THE ASKING HALF. The program does not call it. -/
def askedP (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) : OComp 256 (Option ProofRead) := do
  match ← (M.Proof.readProof (Fmt.HM Run.askB) c table copy request words block file
    Session.start).run with
  | .error _ => pure none
  | .ok r => pure (some r.1)

/-- Its value at a function O in the place of the hash: plain. -/
def askedPAt (O : ByteArray → ByteArray) (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Option ProofRead :=
  match (M.Proof.readProof (m := Id) (Fmt.HO O) c table copy request words block file
    Session.start).run with
  | .error _ => none
  | .ok r => some r.1

/-- THE LAW: at every oracle f the asking half's result is `askedPAt` at the function that f
induces. NO HYPOTHESIS. -/
theorem askedP_det (f : ZKCP.Oracle 256) (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    (askedP c table copy request words block file).det f =
      askedPAt (Run.oB f) c table copy request words block file := by
  rw [← Run.detHom_app f]
  unfold askedP askedPAt
  rw [(Run.detHom f).app_bind, Run.detHom_app, M.Lands.readProof_det]
  cases (M.Proof.readProof (m := Id) (Fmt.HO (Run.oB f)) c table copy request words block file
    Session.start).run with
  | error e =>
    show (Run.detHom f).app (pure none) = _
    rw [(Run.detHom f).app_pure]
    rfl
  | ok r =>
    show (Run.detHom f).app (pure _) = _
    rw [(Run.detHom f).app_pure]
    rfl

/-- It tosses no coin. NO HYPOTHESIS. -/
theorem askedP_noCoin (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) :
    (askedP c table copy request words block file).NoCoin :=
  OComp.NoCoin.bind (M.Lands.readProof_noCoin c table copy request words block file Session.start)
    fun r => by cases r <;> trivial

/-! ## The count -/

section Count
open OnBytes.TwoPort.M.Asks

variable {N1 N2 N3 : Nat}

/-- In the library's count of questions: at most (2 N1 + tailN … N2 N3) · 2. The three premises are
those of `readProof_asks` (OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean). -/
theorem askedP_le (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) (h1 : FirstBelow c table copy request words block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic c table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart c.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic c table) x.2 first N3) :
    (Run.qp 256).le (askedP c table copy request words block file)
      ((2 * N1 + tailN (OnBytes.Proof.tailPublic c table) N2 N3) * 2 + 0) fun _ => True :=
  (Run.qp 256).le_bind _ _ _ _ _ _
    (leR_readProof (Run.qp 256) 2 (Fmt.HM Run.askB) Run.qp_HM c table copy request words block file
      h1 h2 h3 Session.start) fun r _ => by
      cases r <;> exact (Run.qp 256).le_pure _ _ trivial

/-- No coin, and at most that many questions. -/
theorem askedP_asks (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) (h1 : FirstBelow c table copy request words block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic c table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart c.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic c table) x.2 first N3) :
    (askedP c table copy request words block file).NoCoin ∧
      (askedP c table copy request words block file).QueryBound
        ((2 * N1 + tailN (OnBytes.Proof.tailPublic c table) N2 N3) * 2) :=
  have e := askedP_le c table copy request words block file h1 h2 h3
  ⟨e.1, e.2.1⟩

end Count

/-! ## The asking half, then any plain map -/

/-- A typing: the asking half, then a plain map `asm` from what was read to a typed value. All
questions are the asking half's. -/
def typedP {Out : Type} (asm : ProofRead → Option Out) (c : ProofChains) (table : TableName)
    (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    OComp 256 (Option Out) := do
  let a ← askedP c table copy request words block file
  pure (a.bind asm)

/-- Its value at every oracle. -/
theorem typedP_det {Out : Type} (asm : ProofRead → Option Out) (f : ZKCP.Oracle 256)
    (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) :
    (typedP asm c table copy request words block file).det f =
      (askedPAt (Run.oB f) c table copy request words block file).bind asm := by
  rw [← Run.detHom_app f]
  unfold typedP
  rw [(Run.detHom f).app_bind, Run.detHom_app, askedP_det]
  show (Run.detHom f).app (pure _) = _
  rw [(Run.detHom f).app_pure]
  rfl

/-- The same as a tree in the library's generic language, over the family with one oracle: the type
that a reading in front of an arm has. -/
def typedPR {Out : Type} (asm : ProofRead → Option Out) (c : ProofChains) (table : TableName)
    (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    Rom.OComp (Rom.rom 256) (Option Out) :=
  Rom.toRom (typedP asm c table copy request words block file)

/-- Its value at every family of oracle functions. -/
theorem typedPR_det {Out : Type} (asm : ProofRead → Option Out) (g : Rom.Fam (Rom.rom 256))
    (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) :
    (typedPR asm c table copy request words block file).det g =
      (askedPAt (Run.oB (g ())) c table copy request words block file).bind asm :=
  (OComp.det_toRom g (typedP asm c table copy request words block file)).trans
    (typedP_det asm (g ()) c table copy request words block file)

/-- It tosses no coin. NO HYPOTHESIS. -/
theorem typedPR_noCoin {Out : Type} (asm : ProofRead → Option Out) (c : ProofChains)
    (table : TableName) (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd)
    (file : ByteArray) : (typedPR asm c table copy request words block file).NoCoin :=
  noCoin_toRom _ (OComp.NoCoin.bind (askedP_noCoin c table copy request words block file)
    fun _ => trivial)

section Count
open OnBytes.TwoPort.M.Asks

/-- For any plain map behind the asking half: no coin, and the asking half's number. -/
theorem typedPR_asks {Out : Type} (asm : ProofRead → Option Out) {N1 N2 N3 : Nat}
    (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) (h1 : FirstBelow c table copy request words block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic c table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart c.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic c table) x.2 first N3) :
    (typedPR asm c table copy request words block file).NoCoin ∧
      (typedPR asm c table copy request words block file).QueryBound
        ((2 * N1 + tailN (OnBytes.Proof.tailPublic c table) N2 N3) * 2) := by
  have e' := askedP_le c table copy request words block file h1 h2 h3
  have e'' : (Run.qp 256).le (typedP asm c table copy request words block file)
      ((2 * N1 + tailN (OnBytes.Proof.tailPublic c table) N2 N3) * 2 + 0 + 0) fun _ => True :=
    (Run.qp 256).le_bind _ _ _ _ (fun _ => True) _ e' fun _ _ => (Run.qp 256).le_pure _ _ trivial
  exact toRom_out _ _ ⟨e''.1, e''.2.1⟩

end Count

/-! ## At the oracle made from the format's hash; the program -/

/-- At the oracle on bit strings made from the format's hash the value is that at the format's own
oracle. -/
theorem askedPAt_oBits : askedPAt (Run.oB (Run.oBits ())) = askedPAt Fmt.oracle := by
  funext c table copy request words block file
  unfold askedPAt
  rw [HO_oBits]

/-- THE NAMED PREMISE, in one spelling for both halves,
letter for letter: what the program's
own reading of this proof file returns from the empty record of vertices, the twin's reading at the
hash over the format's oracle returns too. One direction, at one file, on readers alone. -/
def ProofTwinAtO (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) : Prop :=
  ∀ r, (OnBytes.Proof.readProof c table copy request words block file).fromStart = .ok r →
    (M.Proof.readProof (m := Id) (Fmt.HO Fmt.oracle) c table copy request words block
      file).fromStart = .ok r

/-- The value at a function O, by the twin's run from the empty record. -/
theorem askedPAt_fromStart (O : ByteArray → ByteArray) (c : ProofChains) (table : TableName)
    (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    askedPAt O c table copy request words block file =
      match (M.Proof.readProof (m := Id) (Fmt.HO O) c table copy request words block
        file).fromStart with
      | .error _ => none
      | .ok r => some r := by
  unfold askedPAt M.Proof.Reading.fromStart
  cases (M.Proof.readProof (m := Id) (Fmt.HO O) c table copy request words block file
    Session.start).run <;> rfl

/-- Under the named premise: where the program's own reading returns r, the value at the format's
oracle is r. -/
theorem askedPAt_program (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray)
    (h : ProofTwinAtO c table copy request words block file) (r : ProofRead)
    (hr : (OnBytes.Proof.readProof c table copy request words block file).fromStart = .ok r) :
    askedPAt Fmt.oracle c table copy request words block file = some r := by
  rw [askedPAt_fromStart, h r hr]

/-- So at the oracle on bit strings made from the format's hash the reading in front of the arm
makes asm of what the program has read. -/
theorem typedPR_program {Out : Type} (asm : ProofRead → Option Out) (c : ProofChains)
    (table : TableName) (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd)
    (file : ByteArray) (h : ProofTwinAtO c table copy request words block file) (r : ProofRead)
    (hr : (OnBytes.Proof.readProof c table copy request words block file).fromStart = .ok r) :
    (typedPR asm c table copy request words block file).det Run.oBits = asm r := by
  rw [typedPR_det, askedPAt_oBits, askedPAt_program c table copy request words block file h r hr]
  rfl

/-! ## With the public strings answered and not asked -/

section Pin
open Rom OnBytes.Slice
open _root_.Iop (Dig)

/-- An algorithm whose queries at the strings of S are answered by a table asks no string of S. -/
theorem asksIn_pinOn {lam : ℕ} {α : Type} (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (c : Rom.OComp (rom lam) α) : (pinOn S T c).AsksIn fun _ (s : List Bool) => s ∉ S := by
  induction c with
  | pure a => trivial
  | query o s k ih =>
    cases o
    by_cases hs : s ∈ S
    · simp only [pinOn, if_pos hs]
      exact ih _
    · simp only [pinOn, if_neg hs]
      exact ⟨hs, fun r => ih r⟩
  | sample n k ih => exact fun r => ih r

/-- THE READING IN FRONT OF THE ARM: the asking half and the plain map, with the queries at the
strings of S answered by the table T and not asked. -/
noncomputable def readerP {Out : Type} (S : Finset (List Bool)) (T : List Bool → Dig 256)
    (asm : ProofRead → Option Out) (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    Rom.OComp (rom 256) (Option Out) :=
  pinOn S T (typedPR asm c table copy request words block file)

variable {Out : Type} (S : Finset (List Bool)) (T : List Bool → Dig 256)
  (asm : ProofRead → Option Out) (c : ProofChains) (table : TableName) (copy : Nat)
  (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray)

/-- It asks no string of S. -/
theorem readerP_off :
    (readerP S T asm c table copy request words block file).AsksIn fun _ (s : List Bool) => s ∉ S :=
  asksIn_pinOn S T _

/-- Its value at every family: the plain value at the function that the family with the table put
over it induces. -/
theorem readerP_det (g : Rom.Fam (rom 256)) :
    (readerP S T asm c table copy request words block file).det g =
      (askedPAt (Run.oB (OnBytes.Slice.over S T g ())) c table copy request words block
        file).bind asm := by
  unfold readerP
  rw [det_pinOn, typedPR_det]

/-- It tosses no coin. NO HYPOTHESIS. -/
theorem readerP_noCoin : (readerP S T asm c table copy request words block file).NoCoin :=
  noCoin_pinOn _ _ _ (typedPR_noCoin asm c table copy request words block file)

open OnBytes.TwoPort.M.Asks in
/-- No coin, and the asking half's number. -/
theorem readerP_asks {N1 N2 N3 : Nat} (h1 : FirstBelow c table copy request words block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic c table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart c.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic c table) x.2 first N3) :
    (readerP S T asm c table copy request words block file).NoCoin ∧
      (readerP S T asm c table copy request words block file).QueryBound
        ((2 * N1 + tailN (OnBytes.Proof.tailPublic c table) N2 N3) * 2) := by
  obtain ⟨a, b⟩ := typedPR_asks asm c table copy request words block file h1 h2 h3
  exact ⟨noCoin_pinOn _ _ _ a, queryBound_pinOn _ _ _ _ b⟩

/-- At the oracle made from the format's hash, if the table holds that oracle's own values at the
strings of S, and under the named premise: it makes asm of what the program has read. -/
theorem readerP_program (hT : ∀ x ∈ S, T x = Run.oBits () x)
    (h : ProofTwinAtO c table copy request words block file) (r : ProofRead)
    (hr : (OnBytes.Proof.readProof c table copy request words block file).fromStart = .ok r) :
    (readerP S T asm c table copy request words block file).det Run.oBits = asm r := by
  unfold readerP
  rw [det_pinOn_of_eq S T Run.oBits hT]
  exact typedPR_program asm c table copy request words block file h r hr

end Pin

end OnBytes.Tie

#print axioms OnBytes.Tie.askedP_det
#print axioms OnBytes.Tie.readerP_noCoin
#print axioms OnBytes.Tie.typedPR_det
#print axioms OnBytes.Tie.typedPR_asks
#print axioms OnBytes.Tie.typedPR_program
#print axioms OnBytes.Tie.asksIn_pinOn
#print axioms OnBytes.Tie.readerP_det
#print axioms OnBytes.Tie.readerP_asks
#print axioms OnBytes.Tie.readerP_program
