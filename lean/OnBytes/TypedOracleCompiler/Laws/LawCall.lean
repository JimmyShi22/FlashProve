-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawCall.lean: law 2 ("blind") in the forms that a user will call.

Main names.
  `refusalOn_blind`    a proof file: refusalOn c table block v r = refusalOn c table block v' r',
                       for a first chain's block that carries law 2's relation, if the keys in r
                       and r' are equal, the three views (v and v'; the shared chain's; the second
                       chain's) are equal but for digests, and the first chains have read as many
                       roots (hv, hk, h2, h3, hn)
  `keyRefusal_blind`   a key file: Key.keyRefusal k table r = Key.keyRefusal k table r', under the
                       like five hypotheses on r and r' (h1, hk, h2, h3, hn). No hypothesis on a
                       block: `Key.oneTime` is walked (OnBytes/TypedOracleCompiler/Laws/LawKey.lean).
  `standChain v n`     a stand-in for a chain as read: the view v, no run's value, n roots (all
                       empty). Its trees are all named "given ∅ ∅" (`standChain_trees`).
  `standIn key v1 v2 v3 n`   a stand-in for a tail as read: the key, three views, n roots on the
                       first chain. It holds nothing that a typed decision cannot know.
  `refusalOn_standIn`, `keyRefusal_standIn`   the program's decision at what was read is its
                       decision at the stand-in, if the three views are equal but for digests and n
                       is the number of roots that the first chain has read
  `tailRefusal_table`, `sharedStart_table`, `secondStart_table`, `refusalOn_table`,
  `keyRefusal_table`   the decision reads neither the stored table's name (root, answers) nor the
                       shape of the binding tree: both may be replaced at will

The hypothesis hn. hn : r.first.roots.length = n says: the number of roots that the strict reader
has read on the first chain is n, where n must be the number of items .root in the first chain's
description. The decision hangs on it: the second chain's first own tree has the number n + 1
(`secondFirstTree`). It is a law on the reader (a chain that is read by a description holds as many
roots as the description has items .root), and it is not shown here. For a proof file n is a
constant only by law 1 at the first chain.

Not claimed. That a typed transcript's views meet `ViewAlike`. Nothing on reading.

-/
import OnBytes.TypedOracleCompiler.Laws.LawProof
import OnBytes.TypedOracleCompiler.Laws.LawKey
import OnBytes.Key.File

namespace OnBytes.TwoLaws

open OnBytes OnBytes.Proof

/-! ## The two decisions -/

theorem refusalOn_blind (c : Params.ProofChains) (table : Params.TableName) {block : Blk FirstEnd}
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) block block) {v v' : Fmt.View}
    (hv : ViewAlike v v') (r r' : ProofRead) (hk : r.key = r'.key)
    (h2 : ViewAlike r.shared.view r'.shared.view) (h3 : ViewAlike r.second.view r'.second.view)
    (hn : r.first.roots.length = r'.first.roots.length) :
    refusalOn c table block v r = refusalOn c table block v' r' := by
  unfold refusalOn
  rcases judge_alike hb (firstStart_alike c.first) hv "first-chain-" with
    ⟨why, e1, e2⟩ | ⟨x, y, e1, e2, q⟩
  · rw [e1, e2]
  · rw [e1, e2]
    exact tailRefusal_blind _ q r r' hk h2 h3 hn

theorem keyRefusal_blind (k : Params.KeyChains) (table : Params.TableName) (r r' : TailRead)
    (h1 : ViewAlike r.first.view r'.first.view) (hk : r.key = r'.key)
    (h2 : ViewAlike r.shared.view r'.shared.view) (h3 : ViewAlike r.second.view r'.second.view)
    (hn : r.first.roots.length = r'.first.roots.length) :
    Key.keyRefusal k table r = Key.keyRefusal k table r' := by
  unfold Key.keyRefusal
  dsimp only
  rcases judge_alike (carries_oneTime (G := AnyGiven) (d := false) k.oneTime)
      (startOf_alike k.oneTime) h1 "one-time-chain-" with ⟨why, e1, e2⟩ | ⟨x, y, e1, e2, q⟩
  · rw [e1, e2]
  · rw [e1, e2]
    exact tailRefusal_blind _ q r r' hk h2 h3 hn

/-! ## The stand-in -/

/-- A stand-in for a chain as read: the view v, no run's value, n roots, all empty. -/
def standChain (v : Fmt.View) (n : Nat) : ChainRead where
  out :=
    { pd := .empty, run := none, rho0 := .empty, rho := .empty, seen := []
      rounds := #[{ msg := .empty, vals := List.replicate n (.root .empty), nonce := 0
                    drawn := ⟨[], [], [], none⟩, list := [], opens := [] }] }
  view := v
  next := 0

theorem rootsT_replicate (n : Nat) (x : ByteArray) :
    (rootsT (List.replicate n (Fmt.ItemValue.root x))).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    unfold rootsT at ih ⊢
    rw [List.filterMap_cons]
    simp only [List.length_cons, ih]

theorem standChain_roots (v : Fmt.View) (n : Nat) : (standChain v n).roots.length = n := by
  unfold ChainRead.roots standChain
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact rootsT_replicate n _

theorem standChain_trees (v : Fmt.View) (n m : Nat) :
    treesOf (standChain v n) m = .given ByteArray.empty ByteArray.empty := by
  unfold treesOf ChainRead.tree
  split
  · rename_i h1 h2
    cases h2
  · rfl

/-- A stand-in for a tail as read. -/
def standIn (key : TableKey) (v1 v2 v3 : Fmt.View) (n : Nat) : TailRead :=
  ⟨standChain v1 n, ⟨0, .empty, 0, 0⟩, key, standChain v2 0, standChain v3 0⟩

theorem refusalOn_standIn (c : Params.ProofChains) (table : Params.TableName) {block : Blk FirstEnd}
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) block block) {v v1 v2 v3 : Fmt.View}
    (r : ProofRead) (h1 : ViewAlike v v1) (h2 : ViewAlike r.shared.view v2)
    (h3 : ViewAlike r.second.view v3) {n : Nat} (hn : r.first.roots.length = n) :
    refusalOn c table block v r = refusalOn c table block v1 (standIn r.key v1 v2 v3 n) :=
  refusalOn_blind c table hb h1 r _ rfl h2 h3 (hn.trans (standChain_roots _ _).symm)

theorem keyRefusal_standIn (k : Params.KeyChains) (table : Params.TableName) {v1 v2 v3 : Fmt.View}
    (r : TailRead) (h1 : ViewAlike r.first.view v1) (h2 : ViewAlike r.shared.view v2)
    (h3 : ViewAlike r.second.view v3) {n : Nat} (hn : r.first.roots.length = n) :
    Key.keyRefusal k table r = Key.keyRefusal k table (standIn r.key v1 v2 v3 n) :=
  keyRefusal_blind k table r _ h1 rfl h2 h3 (hn.trans (standChain_roots _ _).symm)

/-! ## What the decision does not read of what is public about a tail -/

theorem sharedStart_table (p : TailPublic) (t : Params.TableName) (b : Params.LinBindingShape) :
    sharedStart { p with table := t, binding := b } = sharedStart p := rfl

theorem secondStart_table (p : TailPublic) (t : Params.TableName) (b : Params.LinBindingShape)
    (e : FirstEnd) (first : ChainRead) :
    secondStart { p with table := t, binding := b } e first = secondStart p e first := rfl

theorem tailRefusal_table (p : TailPublic) (t : Params.TableName) (b : Params.LinBindingShape)
    (real : FirstEnd) (r : TailRead) :
    tailRefusal { p with table := t, binding := b } real r = tailRefusal p real r := rfl

theorem refusalOn_table (c : Params.ProofChains) (t t' : Params.TableName) (block : Blk FirstEnd)
    (v : Fmt.View) (r : ProofRead) : refusalOn c t block v r = refusalOn c t' block v r := rfl

theorem keyRefusal_table (k : Params.KeyChains) (t t' : Params.TableName) (r : TailRead) :
    Key.keyRefusal k t r = Key.keyRefusal k t' r := rfl

#print axioms refusalOn_blind
#print axioms keyRefusal_blind
#print axioms refusalOn_standIn
#print axioms keyRefusal_standIn
#print axioms tailRefusal_table
#print axioms refusalOn_table
#print axioms keyRefusal_table

end OnBytes.TwoLaws
