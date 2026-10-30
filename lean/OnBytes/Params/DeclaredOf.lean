-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/DeclaredOf.lean: the value of the declared structure (Decl/Declared.lean) at given
public files, and a test that a declared structure runs what it hashes.

Decl/Declared.lean has the type: what is public before any proof, as plain data, with no value of
the hash among its fields. The planner that derives plans and shapes from the public files lies
under OnBytes/Params/, which imports Fmt/ and not the other way. So the value is computed here:
`declared`, one term from the three public files. It fills the files' text, the setting, the tables'
shape, the link's chain of an entry file, and the three chains of a key file and of a proof file.

Each chain is read off a layout (OnBytes/Params/EntryLayout.lean, KeyLayout.lean, ProofLayout.lean):
the label, the parameter items behind the item "configuration", the number of the first own tree,
and the rounds that the dry run of the verifier's own block has noted. A tree that is taken over is
named by the chain that has sent it and its place there, which the layout holds as a mark. Three
things are no fields of the declared structure, which derives them: a chain's plan, from the rounds'
entries (`Fmt.Declared.plan`); a round's kind, from its name (`Fmt.kindOf`); the cut of a round's
message into items, from its entry's words (`Fmt.Entry.cut`).

Two things are told anew here. The case of each chain's random bytes (in the file; the statement's
item 1; in the file), which the program has in its functions `describe`
(OnBytes/Params/Chains.lean). Nothing in this file compares the two. In the test of this file
whole descriptions are compared: for the link's chain with
`EntryShape.spec`, which a law ties to the program's description; for a key file's chains with
descriptions whose case the test itself types; for a proof file's chains there is no test in the
tree. And the flag that a chain's plan begins with the entry RECORD if tables have a record: true
for a link's chain and a key file's first chain. Where tables have a record, the comparison of the
plans holds it; where they have none, nothing here does.

THE PROOF FILE's CHAINS ARE THOSE OF ONE MADE-UP REQUEST. Their entries are the plan's, whatever the
request. Which trees a round opens, and which stored trees, is what the dry runs have noted at the
request of no content (tokens 0, the last position alone covered) and the reply 0
(OnBytes/Params/ProofLayout.lean). That every request gives the same is not proved.

A declared structure tells one thing in two fields: the parameter items, whose bytes are hashed, and
the rounds, which are run. `runsWhatItHashes D` is the test that the two agree, for the link's and
the key file's chains. It spells the parameter bytes that D tells the hash (at a digest of zeros),
reads them with the program's own readers, which also compare the items that two chains of a file
must share, runs the program's own blocks dry on what was read, and compares the chains that come
out with D's, field by field. No rule is written a second time for it. A word of an item that shapes
no round can be turned, in every chain that shares the item, and the test still says yes: such a D
still runs what it hashes, as far as its rounds go. The test is not made for a proof file's chains:
their first block also takes what `Model.Verify.planned` makes of the model's lines, which are no
parameter item. For these there is
`isDeclared D`: D is what `declared` returns at the files whose text D holds.

What `declared` compares before it returns a value. The digest of the files in the order in which D
holds them (`Fmt.Declared.cfg`) is the digest that the program has made of the three files. For all
seven chains, the plan that D makes of its rounds is the planner's, word for word; the parameter
bytes that D spells at that digest are the program's; each round's kind is the kind of its name; and
its items, as the dry run has noted them, are the cut of its entry. The key file's and the proof
file's tables have the entry file's shape. `runsWhatItHashes D`.

The road. The link's chain comes from `entryShape`, on whose way no hash is called. The other chains
come from `Model.Verify.planned`, the routine by which the program makes the seven chains'
parameter bytes; it calls the hash, at the least for the digest of the three files. That no field of
these chains depends on an answer of the hash is not proved. What such a law would rest on: the
text of `planned` with the digest as an argument, and that what it returns at one digest it returns
at another, the same but for the digest and the parameter bytes. `declared` also refuses by
comparisons that are made at the format's own hash.

A VALUE IS NO ADMISSION OF THE PUBLIC FILES: `planned` takes no bits of a caller, and the program's
stages ask further tests before they say yes.

Main definitions: `roundDecl`, `chainDecl`, `tableShapeOf`, `linkDecl`, `threeDecl`, `kindsTold`,
`tellsPlan`, `relink`, `rekey`, `runsWhatItHashes`, `declaredKey`, `withProofOf`, `withProof`,
`declared`, `isDeclared`.
What is not claimed: no theorem is stated here; those that lie are in
OnBytes/Params/DeclaredOfLaws.lean. That `declared` returns a value at any files is tested alone.

-/
import OnBytes.Params.ProofLayout
import Fmt.Parsed

set_option autoImplicit false

namespace OnBytes.Params

/-- A round of a layout as a declared round: a tree that is taken over is named by its mark. The
round's kind and the cut of its message are no fields: the declared structure takes the one from the
round's name (`Fmt.kindOf`), the other from the entry's words (`Fmt.Entry.cut`). -/
def roundDecl (r : Fmt.Round × List Fmt.Stored) : Fmt.DeclaredRound :=
  { entry := r.1.entry, stored := r.2,
    opens := r.1.opens.map fun o => (o.1, match o.2 with
      | .own n => .own n
      | .given root _ => .taken (markOf root).1 (markOf root).2) }

/-- A chain of a layout as a declared chain. `others`: the parameter items behind "configuration".
`record`: whether it is a chain whose plan begins with the entry RECORD if tables have a record: a
link's chain and a key file's one-time chain (R13.15). -/
def chainDecl (S : Fmt.SpecX) (others : List (String × ByteArray)) (rand : Fmt.RandAt)
    (record : Bool := false) : Fmt.ChainDecl :=
  { label := S.base.label
    record := record
    others := others
    rand := rand
    firstTree := S.base.firstTree
    rounds := (S.base.rounds.zip S.stored).map roundDecl }

/-- The tables' shape in the declared structure's letters (R4.10's order). -/
def tableShapeOf (s : IndexShape) : Fmt.TableShape :=
  ⟨s.code.logN, s.code.ell, s.code.r, s.v, s.answers, s.saltBytes⟩

/-- True if each round's kind is the kind of its name and its message's items are the cut of its
entry, so that the declared structure, which has the entry alone, runs the round as the layout does.
-/
def kindsTold (S : Fmt.SpecX) : Bool :=
  S.base.rounds.all fun r => Fmt.kindOf r.entry.name == some r.kind && r.items == r.entry.cut

/-- True if the plan that the declared structure makes of the chain's rounds is the plan P, word for
word, and the parameter bytes that it spells at the digest c are b. -/
def tellsPlan (D : Fmt.Declared) (x : Fmt.ChainDecl) (P : Fmt.Plan) (c b : ByteArray) : Bool :=
  (D.plan x).entries == P.entries && (D.plan x).field == P.field && (D.plan x).salt == P.salt &&
    (D.plan x).nonce == P.nonce && (D.plan x).posB == P.posB && (D.plan x).samples == P.samples &&
    (D.plan x).saved == P.saved && D.params x c == b

/-- The link's chain of an entry file, off its shape. -/
def linkDecl (E : EntryShape) : Fmt.ChainDecl := chainDecl E.blankSpec E.items .inFile true

/-- The three chains of a key file or of a proof file, off the first chain's layout and items and
the tail's layout. `record`: the first chain's flag: true for a key file, false for a proof file. -/
def threeDecl (first : ChainLayout) (items : List (String × ByteArray)) (shared : Shared)
    (second : Second) (t : TailLayout) (record : Bool) : Fmt.ThreeDecl :=
  { first := chainDecl first.spec items .inFile record
    bind := ⟨t.binding.logLeaves, t.binding.saltBytes⟩
    shared := chainDecl t.shared.spec shared.given.items (.item 1)
    second := chainDecl t.second.spec second.given.items .inFile }

/-- The link's chain, made anew from the parameter bytes that D tells the hash. -/
def relink (D : Fmt.Declared) : Option (Fmt.ChainDecl × Fmt.TableShape) := do
  let p ← Link.read (D.params D.link Fmt.zero32)
  let E ← entryShapeOf p.given.plan p.codes p.link
  pure (linkDecl E, tableShapeOf E.table)

/-- A key file's chains, made anew from the parameter bytes that D tells the hash. -/
def rekey (D : Fmt.Declared) : Option (Fmt.ThreeDecl × Fmt.TableShape) := do
  let k ← KeyChains.read (D.params D.key.first Fmt.zero32) (D.params D.key.shared Fmt.zero32)
    (D.params D.key.second Fmt.zero32)
  let K ← keyLayoutOf k
  pure (threeDecl K.oneTime k.oneTime.given.items k.shared k.second K.tail true,
    tableShapeOf K.table)

/-- **True if D runs what it hashes**, as far as the link's and a key file's chains go: made anew
from the parameter bytes that D itself spells, by the program's readers and blocks, these chains and
the tables' shape are D's. It sees what shapes a round, and no more: the head of this file. -/
def runsWhatItHashes (D : Fmt.Declared) : Bool :=
  relink D == some (D.link, D.table) && rekey D == some (D.key, D.table)

/-- The declared structure without a proof file's chains, from the three public files and what
`Model.Verify.planned` has made of them. It is no admission of the files. -/
def declaredKey (x : ConfigurationFiles) (p : Model.Verify.Planned) : Except String Fmt.Declared := do
  let E ← entryShape x.policy
  let K ← orRefuse (keyLayoutOf p.chains.key) "key-parameters"
  let P := E.plan
  let D : Fmt.Declared :=
    { files := [x.policy, x.layout, x.scales]
      setting := ⟨P.field, P.salt, P.nonce, P.posB, P.samples, P.saved⟩
      table := tableShapeOf E.table
      link := linkDecl E
      key := threeDecl K.oneTime K.chains.oneTime.given.items K.chains.shared K.chains.second
        K.tail true }
  let c := p.cfg
  if D.cfg == c && tellsPlan D D.link P c (p.chains.bytes .link) &&
      tellsPlan D D.key.first K.chains.oneTime.given.plan c (p.chains.bytes .keyOneTime) &&
      tellsPlan D D.key.shared K.chains.shared.given.plan c (p.chains.bytes .keyShared) &&
      tellsPlan D D.key.second K.chains.second.given.plan c (p.chains.bytes .keySecond) &&
      tableShapeOf K.table == D.table &&
      [E.blankSpec, K.oneTime.spec, K.tail.shared.spec, K.tail.second.spec].all kindsTold &&
      runsWhatItHashes D then pure D
  else throw "declared-plan"

/-- D with a proof file's chains filled in, off a layout of a proof file. -/
def withProofOf (p : Model.Verify.Planned) (D : Fmt.Declared) (L : ProofLayout) :
    Except String Fmt.Declared :=
  let D' : Fmt.Declared :=
    { D with
      proof := threeDecl L.first L.chains.first.given.items L.chains.shared L.chains.second L.tail
        false }
  let c := p.cfg
  if tellsPlan D' D'.proof.first L.chains.first.given.plan c (p.chains.bytes .proofFirst) &&
      tellsPlan D' D'.proof.shared L.chains.shared.given.plan c (p.chains.bytes .proofShared) &&
      tellsPlan D' D'.proof.second L.chains.second.given.plan c (p.chains.bytes .proofSecond) &&
      tableShapeOf L.chains.first.lin.fold.index == D.table &&
      [L.first.spec, L.tail.shared.spec, L.tail.second.spec].all kindsTold then pure D'
  else throw "declared-plan"

/-- D with a proof file's chains filled in, as the dry runs give them at the request of no content
and the reply 0. -/
def withProof (x : ConfigurationFiles) (p : Model.Verify.Planned) (D : Fmt.Declared) :
    Except String Fmt.Declared := do
  withProofOf p D (← proofLayoutAt x p (blankRequest p.X.T))

/-- **The declared structure at three public files.** It is no admission of the files. The proof
file's chains are those of one made-up request: the head of this file. Refused where
`Model.Verify.planned` refuses the files, where a layout is not made, and where one of the
comparisons fails that the head of this file lists. -/
def declared (x : ConfigurationFiles) : Except String Fmt.Declared := do
  let p ← plannedOf x
  withProof x p (← declaredKey x p)

/-- **True if D is the declared structure of its own files**: `declared`, at the three files whose
text D holds, returns D. It covers a proof file's chains too, as `declared` makes them: at one
made-up request. It costs what `declared` costs. It
ties D to this function and to nothing else: a fault in `declared`, or in the layouts below it,
passes it. -/
def isDeclared (D : Fmt.Declared) : Bool :=
  match D.files with
  | [a, b, c] => (declared ⟨a, b, c⟩).toOption == some D
  | _ => false

end OnBytes.Params
