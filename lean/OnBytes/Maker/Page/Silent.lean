-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Silent.lean: the labels, the parameters' digests, and how the three statements'
bytes and the two later run's values are read off a typed first query and a silent round's message,
for a key file and for a proof file; and that they give back what the verifier program's three
describes lay.

Definitions, statements and proofs. OnBytes/Maker/Page/Fill.lean leaves these data open
(`SilentJ`). OnBytes/Maker/SilentParts.lean says what the three silent rounds of a file send: the
front the record's answers and the stored copy's number; the joining round the answers and the
second chain's run's value; the seam the third chain's run's value. The table's root is the first of
the outer roots in the typed query; the binding tree's root is the request root; the two seals are
the two strings of the third chain's first query, the shared chain's first.

Main names:
  `tableOf cms answers`: the table as a statement names it.
  `silentKey h k`, `silentProof h c req`: the data. h: the hash; req: from the instance, two
    strings: the first is the value of the statement's item "request", the second the request
    file's bytes.
  `default_empty`: where a typed first query holds no instance both strings are empty.
  `tableOf_eq`, `key_stm₁`, `proof_stm₁`, `key_stm₂`, `proof_stm₂`, `key_stm₃`, `proof_stm₃`: the
    statements of OnBytes/Params/Chains.lean come back, for roots and seals of 32 bytes.
  `pdOf_described`: the parameters' digest of a description that `Params.describeWith` returns.
  `key_pd`, `proof_pd`: so the three digests of the data are those of the three descriptions.
No letter stands under "there is".
req is a free letter: nothing here asks that it is the format's spelling of the instance, or one to
one, or that its two strings say one request; a constant function meets every law of this file.
The three digests are answers of h itself.
What of a typed first query no statement's bytes hold: of the outer roots `tableOf` takes the first
alone; a key file's first statement reads neither the instance nor the stored copy's number
(`key_stm₁` holds for every x and copy). The answers, the copy's number and the two later run's
values come off the silent rounds' messages, which are the prover's. So two typed queries can spell
one string.
Limits: that a typed query at a file's value holds these outer roots, request root and seals, and
that a silent round's message as embedded is read back, is not shown here. That roots and seals have
32 bytes is a premise. Nothing on soundness.


-/
import OnBytes.Maker.Page.Fill
import OnBytes.Maker.Page.FirstCalls
import OnBytes.Maker.SilentParts

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run
open _root_.Iop (Dig)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.Maker (FrontMsg frontOf)
open OnBytes.Params (Rounds)

/-- The table as a statement names it: the root is the first of the outer roots. -/
def tableOf (cms : List (Dig 256)) (answers : List E) : Params.TableName :=
  ⟨digToBytes (cms.headD fun _ => false), answers⟩

/-- **The data of a key file.** -/
def silentKey (h : HId) (k : Params.KeyChains) (X : Type) :
    SilentJ X (FrontMsg (List E)) (JoinMsg (List E) ByteArray) ByteArray where
  lab₁ := Params.labelOneTime
  lab₂ := Params.labelShared
  lab₃ := Params.labelSecond
  pd₁ := h 169 0 1 Fmt.zero32 k.oneTime.given.bytes
  pd₂ := h 169 0 1 Fmt.zero32 k.shared.given.bytes
  pd₃ := h 169 0 1 Fmt.zero32 k.second.given.bytes
  stm₁ := fun cms _ p => Params.OneTime.statement (tableOf cms p.answers)
  stm₂ := fun cms rtreq p => Params.Shared.statement (tableOf cms p.answers) (bitsToBytes rtreq)
  run₂ := fun p => bytesToBits p.run
  stm₃ := fun ρ0 c _ => Params.Second.statement (bitsToBytes c) (bitsToBytes ρ0)
  run₃ := bytesToBits

/-- **The data of a proof file.** req: from the instance, two strings: `.1` is the value of the
statement's item "request", `.2` the request file's bytes, the value of the item "the request file's
words". -/
def silentProof (h : HId) (c : Params.ProofChains) {X : Type} (req : X → ByteArray × ByteArray) :
    SilentJ X (FrontMsg (List E)) (JoinMsg (List E) ByteArray) ByteArray where
  lab₁ := Params.labelFirst
  lab₂ := Params.labelSharedProof
  lab₃ := Params.labelSecondProof
  pd₁ := h 169 0 1 Fmt.zero32 c.first.given.bytes
  pd₂ := h 169 0 1 Fmt.zero32 c.shared.given.bytes
  pd₃ := h 169 0 1 Fmt.zero32 c.second.given.bytes
  stm₁ := fun cms x p =>
    Params.First.statement (tableOf cms p.answers) p.copy ((x.map req).getD default).1
      ((x.map req).getD default).2
  stm₂ := fun cms rtreq p => Params.Shared.statement (tableOf cms p.answers) (bitsToBytes rtreq)
  run₂ := fun p => bytesToBits p.run
  stm₃ := fun ρ0 c' _ => Params.Second.statement (bitsToBytes c') (bitsToBytes ρ0)
  run₃ := bytesToBits

/-- Where a typed first query holds no instance the two strings are empty. -/
theorem default_empty : (default : ByteArray × ByteArray) = (ByteArray.empty, ByteArray.empty) :=
  rfl

/-! ## The statements come back -/

/-- 32 bytes, as a digest, as bits, as bytes. -/
theorem bits_dig (b : ByteArray) (h : b.size = 32) : bitsToBytes (List.ofFn (bytesToDig b)) = b :=
  TieTree.dig_bytes b h

theorem tableOf_eq (table : Params.TableName) (h : table.root.size = 32)
    (rest : List (Dig 256)) : tableOf (bytesToDig table.root :: rest) table.answers = table := by
  unfold tableOf
  rw [List.headD_cons, TieTree.dig_bytes _ h]

section
variable (h : HId) (table : Params.TableName) (h32 : table.root.size = 32) (rest : List (Dig 256))
include h32

/-- A key's one-time chain. -/
theorem key_stm₁ (k : Params.KeyChains) {X : Type} (x : Option X) (copy : ℕ) :
    (silentKey h k X).stm₁ (bytesToDig table.root :: rest) x (frontOf table.answers copy) =
      Params.OneTime.statement table := by
  show Params.OneTime.statement (tableOf _ table.answers) = _
  rw [tableOf_eq table h32]

/-- A proof's first chain. -/
theorem proof_stm₁ (c : Params.ProofChains) {X : Type} (req : X → ByteArray × ByteArray) (x : X)
    (copy : ℕ) :
    (silentProof h c req).stm₁ (bytesToDig table.root :: rest) (some x)
        (frontOf table.answers copy) = Params.First.statement table copy (req x).1 (req x).2 := by
  show Params.First.statement (tableOf _ table.answers) copy _ _ = _
  rw [tableOf_eq table h32]
  rfl

/-- The shared chain of a key file. root: the binding tree's. -/
theorem key_stm₂ (k : Params.KeyChains) (X : Type) (root run : ByteArray) (hr : root.size = 32) :
    (silentKey h k X).stm₂ (bytesToDig table.root :: rest) (List.ofFn (bytesToDig root))
        ⟨table.answers, run⟩ = Params.Shared.statement table root := by
  show Params.Shared.statement (tableOf _ table.answers) _ = _
  rw [tableOf_eq table h32, bits_dig root hr]

/-- The shared chain of a proof file. -/
theorem proof_stm₂ (c : Params.ProofChains) {X : Type} (req : X → ByteArray × ByteArray) (root run :
    ByteArray)
    (hr : root.size = 32) :
    (silentProof h c req).stm₂ (bytesToDig table.root :: rest) (List.ofFn (bytesToDig root))
        ⟨table.answers, run⟩ = Params.Shared.statement table root := by
  show Params.Shared.statement (tableOf _ table.answers) _ = _
  rw [tableOf_eq table h32, bits_dig root hr]

end

/-- The third chain of a key file. The shared chain's seal stands first in the typed query. -/
theorem key_stm₃ (h : HId) (k : Params.KeyChains) (X : Type) (seal1 seal2 p : ByteArray)
    (h1 : seal1.size = 32) (h2 : seal2.size = 32) :
    (silentKey h k X).stm₃ (List.ofFn (bytesToDig seal2)) (List.ofFn (bytesToDig seal1)) p =
      Params.Second.statement seal1 seal2 := by
  show Params.Second.statement _ _ = _
  rw [bits_dig seal1 h1, bits_dig seal2 h2]

/-- The third chain of a proof file. -/
theorem proof_stm₃ (h : HId) (c : Params.ProofChains) {X : Type} (req : X → ByteArray × ByteArray)
    (seal1 seal2 p : ByteArray) (h1 : seal1.size = 32) (h2 : seal2.size = 32) :
    (silentProof h c req).stm₃ (List.ofFn (bytesToDig seal2)) (List.ofFn (bytesToDig seal1)) p =
      Params.Second.statement seal1 seal2 := by
  show Params.Second.statement _ _ = _
  rw [bits_dig seal1 h1, bits_dig seal2 h2]

/-! ## The parameters' digests -/

/-- The parameters' digest of a description that is returned is that of the parameter bytes. -/
theorem pdOf_described (h : HId) {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (e : Params.describeWith g label st rand R ft = some S) :
    pdOf h S = h 169 0 1 Fmt.zero32 g.bytes := by
  unfold Params.describeWith at e
  unfold pdOf
  rw [Params.Given.describe_eq e]

/-- The three digests of a key file's data are those of its three descriptions. -/
theorem key_pd (h : HId) (k : Params.KeyChains) (X : Type) {table : Params.TableName}
    {root seal1 seal2 : ByteArray} {R₁ R₂ R₃ : Rounds} {ft : ℕ} {S₁ S₂ S₃ : Fmt.SpecX}
    (e₁ : k.oneTime.describe table R₁ = some S₁) (e₂ : k.shared.describe Params.labelShared table
        root R₂ = some S₂)
    (e₃ : k.second.describe Params.labelSecond seal1 seal2 R₃ ft = some S₃) :
    (silentKey h k X).pd₁ = pdOf h S₁ ∧ (silentKey h k X).pd₂ = pdOf h S₂ ∧
      (silentKey h k X).pd₃ = pdOf h S₃ :=
  ⟨(pdOf_described h e₁).symm, (pdOf_described h e₂).symm, (pdOf_described h e₃).symm⟩

/-- The three digests of a proof file's data are those of its three descriptions. -/
theorem proof_pd (h : HId) (c : Params.ProofChains) {X : Type} (req : X → ByteArray × ByteArray)
    {table : Params.TableName} {copy : ℕ} {request words root seal1 seal2 : ByteArray}
    {R₁ R₂ R₃ : Rounds} {ft : ℕ} {S₁ S₂ S₃ : Fmt.SpecX}
    (e₁ : c.first.describe table copy request words R₁ = some S₁)
    (e₂ : c.shared.describe Params.labelSharedProof table root R₂ = some S₂)
    (e₃ : c.second.describe Params.labelSecondProof seal1 seal2 R₃ ft = some S₃) :
    (silentProof h c req).pd₁ = pdOf h S₁ ∧ (silentProof h c req).pd₂ = pdOf h S₂ ∧
      (silentProof h c req).pd₃ = pdOf h S₃ :=
  ⟨(pdOf_described h e₁).symm, (pdOf_described h e₂).symm, (pdOf_described h e₃).symm⟩

end OnBytes.Maker.Page
