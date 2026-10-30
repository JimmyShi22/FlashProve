-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Decide3.lean: the shipped verifier's three decisions on a file's three chains as one
function of three views, behind the test that the words of the views' field elements and of the
key's seeds are below the prime.

The shipped verifier judges a key file or a proof file by three runs of blocks, each on the view of
one chain (OnBytes/Key/File.lean: `keyRefusal`; OnBytes/Proof/File.lean: `refusalOn`;
OnBytes/Proof/Tail.lean: `tailRefusal`): the second chain's block starts from the public data alone,
the third from what the first two have returned. This file lays the three runs behind each other as
one Boolean function (`runs3`), for a protocol whose rounds are all three chains'. `decide3` is the
test `okSeeds` on the key, the test `okView` on each of the three views (OnBytes/Maker/OkView.lean),
and then `runs3`: the shipped verifier's readers refuse a word of a field's element that is not
below the prime, and draw a seed's words below it; a view that is made of a typed transcript has
passed no reader, and the key is a letter here.

Beside these tests, which the shipped text has in its readers and draws, three things differ from
the shipped text.
  The trees that the third chain takes over are named by made-up names (OnBytes/Three/Data.lean:
  `tagChain`) and not by the roots and run values that were read: a protocol's decision is fixed
  before any root is.
  In a protocol of three stretches the round in which the first chain is sealed is the joining round
  and no written round of the first stretch. So the first view comes one round short, and
  `withSeal` puts that round back: no item, nothing drawn.

  The shipped text makes the table's key from the table's name (root and answers) that it holds
  (OnBytes/Proof/Tail.lean: `readTail`). Here the key is an argument, and the table's name is read
  nowhere (`decide3_table`).

Main definitions: `sealRV`, `withSeal`, `runs3`, `decide3`, `decideKey`, `decideProof`.
`decide3_parts`, `decide3_of`: a yes of `decide3` is a yes of the five parts.

What is not said. That the key is the one that `tableKey` makes of a table's name: THAT THE SEEDS
ARE THE TABLE's IS TESTED NOWHERE HERE. Why the seeds' words are tested: the shared chain's block
asks of a seed's factor that its words are not all 0 (OnBytes/Iop/Foldeq.lean, `foldeqRequire`), and
a factor with the words (p, 0, 0) would pass that and be 0 in the field. The words of the key's
answers (`TableKey.record`) are not tested (`keyCleanB`, Johnson/Maker/Page/ValuesM.lean
[not in this library], tests them too). What a round draws is not tested either. What of the shipped
verifier is not in
`decide3`: the readers' other tests (form, work, listed positions, openings, vertices, the place in
the binding tree, bytes left over), the tests on the public values (field, admitted values, a digest
of zeros), the number of the stored copy. That `decide3` at the views of a file as read is the
shipped verifier's own verdict: that needs that a block's run does not hang on the names of trees
taken over, nor on the digest that a sealing round draws, and that the key and the views as read
pass the two tests.
Nothing on soundness.


-/
import OnBytes.Maker.OkView
import OnBytes.Three.Data
import OnBytes.Key.File
import OnBytes.Proof.File

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof (TailPublic FirstEnd sharedBlock secondBlock sharedStart secondStart)

/-- A sealing round as a decision sees it, without its digest. -/
def sealRV : Fmt.RoundView := ⟨[], ⟨[], [], [], none⟩⟩

/-- A view with the sealing round put back behind its rounds. -/
def withSeal (v : Fmt.View) : Fmt.View := { v with rounds := v.rounds ++ [sealRV] }

/-- The three runs, one behind the other. b₁, s₁: the first chain's block and its start. n₁, n₂: the
numbers of trees that the first and the second chain send. -/
def runs3 (p : TailPublic) (key : TableKey) (b₁ : Blk FirstEnd) (s₁ : Start) (n₁ n₂ : Nat)
    (v₁ v₂ v₃ : Fmt.View) : Bool :=
  match b₁.runOn s₁ (withSeal v₁) with
  | .error _ => false
  | .ok e =>
    match (sharedBlock p.lin key).runOn (sharedStart p) v₂ with
    | .error _ => false
    | .ok e₂ =>
      match (secondBlock p.lin e.lin (e₂.goesOn (Three.tagChain 2 n₂))).runOn
          (secondStart p e (Three.tagChain 1 n₁)) v₃ with
      | .error _ => false
      | .ok _ => true

/-- **The three decisions as one**: the words of the key's seeds and of the three views' field
elements are below the prime, and the three runs end well. -/
def decide3 (p : TailPublic) (key : TableKey) (b₁ : Blk FirstEnd) (s₁ : Start) (n₁ n₂ : Nat)
    (v₁ v₂ v₃ : Fmt.View) : Bool :=
  okSeeds key && okView v₁ && okView v₂ && okView v₃ && runs3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃

/-- What a yes says, part by part. -/
theorem decide3_parts {p : TailPublic} {key : TableKey} {b₁ : Blk FirstEnd} {s₁ : Start}
    {n₁ n₂ : Nat} {v₁ v₂ v₃ : Fmt.View} (h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true) :
    okSeeds key = true ∧ okView v₁ = true ∧ okView v₂ = true ∧ okView v₃ = true ∧
      runs3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true := by
  unfold decide3 at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The five parts give the yes. -/
theorem decide3_of {p : TailPublic} {key : TableKey} {b₁ : Blk FirstEnd} {s₁ : Start}
    {n₁ n₂ : Nat} {v₁ v₂ v₃ : Fmt.View} (h0 : okSeeds key = true) (h1 : okView v₁ = true)
    (h2 : okView v₂ = true) (h3 : okView v₃ = true)
    (h : runs3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true) :
    decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true := by
  unfold decide3
  rw [h0, h1, h2, h3, h]
  rfl

/-- A table's name that holds nothing. -/
def noTable : Params.TableName := ⟨.empty, []⟩

/-- The three decisions do not read the table's name. -/
theorem decide3_table (p : TailPublic) (t : Params.TableName) (key : TableKey) (b₁ : Blk FirstEnd)
    (s₁ : Start) (n₁ n₂ : Nat) (v₁ v₂ v₃ : Fmt.View) :
    decide3 { p with table := t } key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ :=
  rfl

/-- At a key file. -/
def decideKey (k : Params.KeyChains) (key : TableKey) (n₁ n₂ : Nat) (v₁ v₂ v₃ : Fmt.View) : Bool :=
  decide3 (Key.tailPublic k noTable) key (Key.oneTime k.oneTime) (Key.startOf k.oneTime) n₁ n₂
    v₁ v₂ v₃

/-- At a proof file. block: the first chain's block, made at the request and the reply. -/
def decideProof (c : Params.ProofChains) (key : TableKey) (block : Blk FirstEnd) (n₁ n₂ : Nat)
    (v₁ v₂ v₃ : Fmt.View) : Bool :=
  decide3 (Proof.tailPublic c noTable) key block (Proof.firstStart c.first) n₁ n₂ v₁ v₂ v₃

end OnBytes.Maker
