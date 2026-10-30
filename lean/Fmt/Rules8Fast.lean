-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8Fast.lean: the reader of a proof file at the format's hash `formatHash`, in a form that evaluates
fast, with a proof that it is the reader of Fmt/Rules8.lean.

A proof file of the programs (the C++ implementation that comes with this Lean code) is a chain of
rounds. Fmt/Rules8.lean's reader of such a file is written over a variable monad, with the hash
handed in as a function, so each hash call of a round is computed from its start. Here the same text
stands once more at the identity monad, with the step of the chain as a parameter (`stepQ`,
`foldRoundsQ`, `readChainQ`, `wholeChainQ`).

Sources. Section 8 of the format page (docs/format/FORMAT.md, which comes with the programs);
this file has not been held against the page as it ships, and may differ from it,
for instance at R8.7. No Mathlib.



1. What the file contains.
   `stepQ`, `foldRoundsQ`, `readChainQ`, `wholeChainQ`: The reader's text with the chain's step as a
     parameter.
   `wholeChainF S b`: That text at `Chain.queryF` (Fmt/Rules5Fast.lean: a round's blocks are made
     with the hash's state kept) and at `HF` (the hash in its flat form) for all other hashes.

2. What is checked when the file compiles. Two tests (#guard), at the format page's known answer of
its section 8, in both fields: the fast reader and the reader end in the same value of the chain,
the same digest of the parameters and as many rounds; the fast reader reads the file, and refuses it
with its last byte cut off.

3. Theorems.
   `stepQ_eq`, `foldRoundsQ_eq`, `restQ_eq`, `readChainQ_eq`: The four steps to the next theorem:
     one round, the fold, what stands behind the random bytes, the chain from a place on.
   `readerQ`: At the chain's step `Chain.query` and the format's hash `formatHash` the text with a parameter
     is Fmt/Rules8.lean's reader at the identity monad.
   `wholeChainF_eq`: `wholeChainF S b = wholeChain (m := Id) formatHash S b`, for every description `S`
     (`Spec`, Fmt/Rules8.lean) and every file `b`.

4. What is not claimed. This file claims nothing on time (it is measured elsewhere).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.Rules8
import Fmt.Rules5Fast

namespace Fmt

/-- The type of a chain's step, which the definitions below take as a parameter. -/
abbrev Qry : Type := Chain → ByteArray → Kind → Nat → Nat → Nat → Option (Chain × Array ByteArray)
abbrev Hash : Type := Nat → Nat → Nat → ByteArray → ByteArray → ByteArray

/-- One round. -/
def stepQ (qry : Qry) (h : Hash) (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) : Option St :=
  match slice b s.pos r.entry.msg with
  | none => none
  | some msg =>
    match whole (readItems P.field r.items) msg with
    | none => none
    | some vals =>
      match readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => none
      | some (nonce, i1) =>
        match qry s.chain msg r.kind r.entry.work nonce ((wordsAtMost r.entry r.kind + 3) / 4) with
        | none => none
        | some (c, vb) =>
          let drawn := drawRound P.field r.entry r.kind (rowOf vb)
          let l := listOf drawn.poss
          match readList P r.entry.poss l b i1 with
          | none => none
          | some (_, i2) =>
            let roots := s.roots ++ (rootsOf vals).toArray
            match readOpens (m := Id) h cfg P run roots drawn.poss b r.opens s.seen i2 with
            | none => none
            | some (cols, sn, i3) =>
              some ⟨i3, c, roots, sn, s.out.push ⟨msg, vals, nonce, drawn, l, cols⟩⟩

def foldRoundsQ (qry : Qry) (h : Hash) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) : List Round → St → Option St
  | [], s => some s
  | r :: rs, s =>
    match stepQ qry h cfg P run b s r with
    | none => none
    | some s' => foldRoundsQ qry h cfg P run b rs s'

/-- Behind the random bytes. -/
def restQ (qry : Qry) (h : Hash) (S : Spec) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) : Option (ChainOut × Nat) :=
  match startChainW (m := Id) h S.label (paramsDigestW (m := Id) h S.params) S.statement x with
  | none => none
  | some hd =>
    match foldRoundsQ qry h S.cfg S.plan hd.run b S.rounds
        ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
    | none => none
    | some s =>
      some
        (⟨paramsDigestW (m := Id) h S.params, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩, s.pos)

def readChainQ (qry : Qry) (h : Hash) (S : Spec) (seen : Seen) (b : ByteArray) (i : Nat) :
    Option (ChainOut × Nat) :=
  if !S.ok then none
  else
    match S.rand with
    | .inFile =>
      match slice b i 32 with
      | none => none
      | some x => restQ qry h S seen b (some x) (i + 32)
    | .given x => restQ qry h S seen b (some x) i
    | .none => restQ qry h S seen b none i

def wholeChainQ (qry : Qry) (h : Hash) (S : Spec) (b : ByteArray) : Option ChainOut :=
  match readChainQ qry h S [] b 0 with
  | some (o, j) => if j == b.size then some o else none
  | none => none

/-- The reader, fast. -/
def wholeChainF (S : Spec) (b : ByteArray) : Option ChainOut := wholeChainQ Chain.queryF HF S b

namespace Spec
def readerQ : Prop :=
  ∀ (S : _root_.Fmt.Spec) (b : ByteArray),
    wholeChainQ Chain.query formatHash S b = wholeChain (m := Id) formatHash S b
def wholeChainF_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (b : ByteArray), wholeChainF S b = wholeChain (m := Id) formatHash S b
end Spec

theorem stepQ_eq (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) :
    stepQ Chain.query formatHash cfg P run b s r = step (m := Id) formatHash cfg P run b s r := by
  unfold stepQ step
  cases slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases whole (readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some x => rfl

theorem foldRoundsQ_eq (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List Round) (s : St),
      foldRoundsQ Chain.query formatHash cfg P run b rs s = foldRounds (m := Id) formatHash cfg P run b rs s
  | [], _ => rfl
  | r :: rs, s => by
    unfold foldRoundsQ foldRounds
    rw [stepQ_eq]
    show _ = (match step (m := Id) formatHash cfg P run b s r with
      | none => none
      | some s' => foldRounds (m := Id) formatHash cfg P run b rs s')
    cases step (m := Id) formatHash cfg P run b s r with
    | none => rfl
    | some s' => exact foldRoundsQ_eq cfg P run b rs s'

theorem restQ_eq (S : Spec) (seen : Seen) (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    restQ Chain.query formatHash S seen b x i0 = (match startChainW (m := Id) formatHash S.label (paramsDigestW (m := Id) formatHash S.params) S.statement x with
               | none => none
               | some hd =>
                 match foldRounds (m := Id) formatHash S.cfg S.plan hd.run b S.rounds
                     ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
                 | none => none
                 | some s =>
                     some (⟨paramsDigestW (m := Id) formatHash S.params, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩,
                           s.pos)) := by
  unfold restQ
  cases startChainW (m := Id) formatHash S.label (paramsDigestW (m := Id) formatHash S.params) S.statement x with
  | none => rfl
  | some hd =>
    dsimp only
    rw [foldRoundsQ_eq]
    rfl

theorem readChainQ_eq (S : Spec) (seen : Seen) (b : ByteArray) (i : Nat) :
    readChainQ Chain.query formatHash S seen b i = readChain (m := Id) formatHash S seen b i := by
  unfold readChainQ readChain
  cases !S.ok with
  | true => rfl
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    cases S.rand with
    | inFile =>
      dsimp only
      cases slice b i 32 with
      | none => rfl
      | some x => exact restQ_eq S seen b (some x) (i + 32)
    | given x => exact restQ_eq S seen b (some x) i
    | none => exact restQ_eq S seen b none i

theorem readerQ : Spec.readerQ := by
  intro S b
  unfold wholeChainQ wholeChain
  rw [readChainQ_eq]
  rfl

theorem wholeChainF_eq : Spec.wholeChainF_eq := by
  intro S b
  have hq : Chain.queryF = Chain.query := by
    funext c msg kind work nonce K
    exact queryF_eq c msg kind work nonce K
  unfold wholeChainF
  rw [hq, HF_eq]
  exact readerQ S b

-- the page's known answer of section 8, both fields: the same chain value, digest, count of rounds
#guard [(Fld.one, Known8.file1), (Fld.two, Known8.file2)].all fun x => (wholeChainF (Known8.spec x.1) x.2).map (fun o => (o.rho, o.pd, o.rounds.size)) == (wholeChain (m := Id) formatHash (Known8.spec x.1) x.2).map (fun o => (o.rho, o.pd, o.rounds.size))
#guard [(Fld.one, Known8.file1), (Fld.two, Known8.file2)].all fun x => (wholeChainF (Known8.spec x.1) x.2).isSome && (wholeChainF (Known8.spec x.1) (x.2.extract 0 (x.2.size - 1))).isNone

end Fmt
