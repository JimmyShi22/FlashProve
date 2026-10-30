-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/DigestKey.lean: the scheme whose verifier's key is the hash of another scheme's.

The verifier's key and the prover's key of a scheme are its `IVK` and `ISK` (ZKCP/Defs.lean); "key"
alone is the verifier's. A scheme is an `Arg`, a hash function an `Oracle`, a query log a `Trace`.
Given a scheme A and a coding `enc` of its keys as bit strings, `Arg.digestKey A enc` is the scheme
with a digest as the verifier's key:
  the committer   runs A's committer and queries the hash function once more, at the code of the
                  key (`keyDigest`); the answer is the new key; the prover's key is A's two keys
  the prover      runs A's prover and sends A's key with the proof
  the verifier    queries the hash function at the code of the key that it is sent, rejects unless
                  the answer is the digest that it holds, and then runs A's verifier
                  (`verifyDigestKey`)
  the extractor   looks in the committer's query log for the first key whose code has that digest
                  as its answer (`firstKey`) and gives the index that a given extractor for A gives
                  at that key; for the witness it reads the key that the proof brings
                  (`Extractor.digestKey`)
`enc` is a parameter. It need not be defined on every key. For a key without a code the committer
makes no further query and outputs the digest of zeros, and the verifier rejects every proof that
brings such a key. `CodeIsOneToOne enc` and `Arg.KeysHaveCodes A enc` are the two conditions on the
coding that the theorems on this scheme name; `exists_total_code` shows that both can be met if the
keys are countable. One theorem names one more, on the extractor and `enc` together
(Compile/DigestKeyArg.lean).
This file has the definitions, the bounds on queries (at most one more for the committer, none more
for the prover, at most one more for the verifier), "the verifier samples nothing if A's samples
nothing", and the committer's and the prover's outputs under each hash function.
What the scheme keeps of A's properties, at which price, and what it does not give:
Compile/DigestKeyArg.lean.
-/
import ZKCP.ManyOfOne
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-! ## 1. Definitions -/

/-- The coding gives no bit string to two different keys. -/
def CodeIsOneToOne (enc : IVK → Option Str) : Prop :=
  ∀ key key' code, enc key = some code → enc key' = some code → key = key'

/-- Every verifier's key that the committer of A can output has a code. -/
def Arg.KeysHaveCodes (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str) : Prop :=
  ∀ i f, ∀ keys ∈ ((A.C i).run f).support, enc keys.1 ≠ none

/-- The digest of a key under the hash function f: the value of f at the key's code. A key without a
code gets the digest of zeros. -/
def digestUnder (f : Oracle lam) (enc : IVK → Option Str) (key : IVK) : Digest lam :=
  ((enc key).map f).getD fun _ => false

/-- The algorithm that computes the digest of a key: one query, at the key's code. For a key without
a code it returns the digest of zeros and makes no query. -/
def keyDigest (enc : IVK → Option Str) (key : IVK) : OComp lam (Digest lam) :=
  match enc key with
  | some code => .query code fun answer => .pure answer
  | none => .pure fun _ => false

/-- The verifier that holds a digest. A proof is a key of the verifier V with a proof for V. It
queries the hash function at the key's code, rejects unless the answer is the digest, and then runs
V with that key. It rejects a key without a code, and makes no query then. -/
def verifyDigestKey (V : IVK → X → Pf → OComp lam Bool) (enc : IVK → Option Str) :
    Digest lam → X → IVK × Pf → OComp lam Bool := fun digest x proof =>
  match enc proof.1 with
  | some code => .query code fun answer =>
      if answer = digest then V proof.1 x proof.2 else .pure false
  | none => .pure false

/-- The scheme A with the digest of its verifier's key as the verifier's key. The prover's key is
A's two keys; each proof is A's verifier's key with a proof of A. -/
def Arg.digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str) :
    Arg lam I X W (Digest lam) (IVK × ISK) (IVK × Pf) where
  C := fun i => (A.C i).bind fun keys => (keyDigest enc keys.1).mapO fun digest => (digest, keys)
  P := fun keys x w => (A.P keys.2 x w).mapO fun proof => (keys.1, proof)
  V := verifyDigestKey A.V enc

open Classical in
/-- A key of which a bit string is the code, if there is one; the only one if the coding is one to
one. It is picked by choice, not by an algorithm. -/
def keyOfCode (enc : IVK → Option Str) (code : Str) : Option IVK :=
  if h : ∃ key, enc key = some code then some h.choose else none

open Classical in
/-- The first entry of a query log whose answer is the digest and whose query is the code of a key:
that key. -/
def firstKey (enc : IVK → Option Str) (digest : Digest lam) (log : Trace lam) :
    Option IVK :=
  log.findSome? fun entry => if entry.2 = digest then keyOfCode enc entry.1 else none

/-- The extractor for `Arg.digestKey`. For the index it reads the digest and the committer's query
log alone: it gives what E gives at `firstKey` and the whole log, and nothing if the log has no such
key. For the witness it gives what E gives at the key that the proof brings. It inverts `enc` by
choice, not by an algorithm. -/
def Extractor.digestKey (E : Extractor lam I X W IVK Pf) (enc : IVK → Option Str) :
    Extractor lam I X W (Digest lam) (IVK × Pf) where
  Ei digest log := (firstKey enc digest log).bind fun key => E.Ei key log
  Ew _ log x proof log' := E.Ew proof.1 log x proof.2 log'

/-! ## 2. The coding -/

theorem keyOfCode_enc {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc) {key : IVK} {code : Str}
    (h : enc key = some code) : keyOfCode enc code = some key := by
  unfold keyOfCode
  rw [dif_pos ⟨key, h⟩]
  exact congrArg some
    (hinj _ _ code (Exists.choose_spec (⟨key, h⟩ : ∃ key, enc key = some code)) h)

/-- The two conditions on a coding can be met: countably many keys have a coding that is defined
everywhere and one to one. -/
theorem exists_total_code (IVK : Type) [Countable IVK] :
    ∃ enc : IVK → Option Str, CodeIsOneToOne enc ∧ ∀ key, enc key ≠ none := by
  obtain ⟨number, hnumber⟩ := exists_injective_nat IVK
  refine ⟨fun key => some (List.replicate (number key) true), fun key key' code h h' => ?_,
    fun _ => Option.some_ne_none _⟩
  have e : List.replicate (number key) true = List.replicate (number key') true :=
    Option.some.inj (h.trans h'.symm)
  have e' := congrArg List.length e
  rw [List.length_replicate, List.length_replicate] at e'
  exact hnumber e'

/-- A coding that is defined everywhere gives a code to every key of every committer. -/
theorem Arg.keysHaveCodes_of_total (A : Arg lam I X W IVK ISK Pf) {enc : IVK → Option Str}
    (h : ∀ key, enc key ≠ none) : A.KeysHaveCodes enc :=
  fun _ _ keys _ => h keys.1

/-! ## 3. Queries and random choices -/

/-- An algorithm has an output: its type of outputs is not empty. -/
theorem OComp.nonempty {α : Type} : OComp lam α → Nonempty α
  | .pure a => ⟨a⟩
  | .query _ k => OComp.nonempty (k fun _ => false)
  | .sample _ k => OComp.nonempty (k 0)

theorem queryBound_keyDigest (enc : IVK → Option Str) (key : IVK) :
    (keyDigest (lam := lam) enc key).QueryBound 1 := by
  unfold keyDigest
  cases enc key with
  | none => trivial
  | some code => exact fun _ => trivial

theorem drawsNoCoin_keyDigest (enc : IVK → Option Str) (key : IVK) :
    (keyDigest (lam := lam) enc key).DrawsNoCoin := by
  unfold keyDigest
  cases enc key with
  | none => trivial
  | some code => exact fun _ => trivial

/-- The committer makes at most one query more than A's. -/
theorem queryBound_C_digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str) (i : I)
    (t : ℕ) (h : (A.C i).QueryBound t) : ((A.digestKey enc).C i).QueryBound (t + 1) :=
  OComp.QueryBound.bind
    (fun keys : IVK × ISK => (keyDigest enc keys.1).mapO fun digest => (digest, keys)) 1
    (fun keys => OComp.QueryBound.mapO _ (keyDigest enc keys.1) 1 (queryBound_keyDigest enc keys.1))
    (A.C i) t h

/-- The prover makes no more queries than A's. -/
theorem queryBound_P_digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str)
    (keys : IVK × ISK) (x : X) (w : W) (t : ℕ) (h : (A.P keys.2 x w).QueryBound t) :
    ((A.digestKey enc).P keys x w).QueryBound t :=
  OComp.QueryBound.mapO _ _ t h

/-- The verifier makes at most one query more than V. -/
theorem queryBound_verifyDigestKey {V : IVK → X → Pf → OComp lam Bool} (enc : IVK → Option Str)
    (t : ℕ) (h : ∀ key x proof, (V key x proof).QueryBound t) (digest : Digest lam) (x : X)
    (proof : IVK × Pf) : (verifyDigestKey V enc digest x proof).QueryBound (t + 1) := by
  unfold verifyDigestKey
  cases enc proof.1 with
  | none => trivial
  | some code =>
    refine fun answer => ?_
    show (if answer = digest then V proof.1 x proof.2
      else .pure false : OComp lam Bool).QueryBound t
    split
    · exact h _ _ _
    · trivial

/-- The verifier samples nothing if V samples nothing. -/
theorem drawsNoCoin_verifyDigestKey {V : IVK → X → Pf → OComp lam Bool} (enc : IVK → Option Str)
    (h : ∀ key x proof, (V key x proof).DrawsNoCoin) (digest : Digest lam) (x : X)
    (proof : IVK × Pf) : (verifyDigestKey V enc digest x proof).DrawsNoCoin := by
  unfold verifyDigestKey
  cases enc proof.1 with
  | none => trivial
  | some code =>
    refine fun answer => ?_
    show (if answer = digest then V proof.1 x proof.2
      else .pure false : OComp lam Bool).DrawsNoCoin
    split
    · exact h _ _ _
    · trivial

/-! ## 4. Under each hash function -/

theorem digestUnder_of_some (f : Oracle lam) {enc : IVK → Option Str} {key : IVK} {code : Str}
    (h : enc key = some code) : digestUnder f enc key = f code := by
  have e : digestUnder f enc key = ((some code).map f).getD fun _ => false := by
    unfold digestUnder
    rw [h]
  exact e

theorem run_keyDigest (f : Oracle lam) (enc : IVK → Option Str) (key : IVK) :
    (keyDigest enc key).run f = PMF.pure (digestUnder f enc key) := by
  unfold keyDigest digestUnder
  cases enc key with
  | none => rfl
  | some code => rfl

/-- The committer's output: A's two keys, with the digest of the verifier's in front. -/
theorem run_C_digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str) (f : Oracle lam)
    (i : I) : ((A.digestKey enc).C i).run f
      = ((A.C i).run f).map fun keys => (digestUnder f enc keys.1, keys) := by
  show ((A.C i).bind fun keys =>
      (keyDigest enc keys.1).mapO fun digest => (digest, keys)).run f = _
  rw [run_bind]
  show _ = ((A.C i).run f).bind fun keys => PMF.pure (digestUnder f enc keys.1, keys)
  refine congrArg _ (funext fun keys => ?_)
  rw [OComp.run_mapO, run_keyDigest, PMF.pure_map]

/-- The prover's output: A's proof, with A's verifier's key in front. -/
theorem run_P_digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str) (f : Oracle lam)
    (keys : IVK × ISK) (x : X) (w : W) : ((A.digestKey enc).P keys x w).run f
      = ((A.P keys.2 x w).run f).map fun proof => (keys.1, proof) :=
  OComp.run_mapO f _ _

/-- The verifier on a key with a code: it compares the value of f at the code with the digest,
rejects unless they are equal, and then runs V. -/
theorem run_verifyDigestKey (V : IVK → X → Pf → OComp lam Bool) {enc : IVK → Option Str}
    (f : Oracle lam) (digest : Digest lam) (x : X) (proof : IVK × Pf) {code : Str}
    (h : enc proof.1 = some code) : (verifyDigestKey V enc digest x proof).run f
      = (if f code = digest then V proof.1 x proof.2 else .pure false : OComp lam Bool).run f := by
  unfold verifyDigestKey
  rw [h]
  rfl

/-- The verifier on a key without a code is the algorithm that rejects. -/
theorem verifyDigestKey_of_none (V : IVK → X → Pf → OComp lam Bool) {enc : IVK → Option Str}
    (digest : Digest lam) (x : X) (proof : IVK × Pf) (h : enc proof.1 = none) :
    verifyDigestKey V enc digest x proof = .pure false := by
  unfold verifyDigestKey
  rw [h]

end ZKCP
