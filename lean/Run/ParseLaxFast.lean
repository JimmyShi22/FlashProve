-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseLaxFast.lean: the lenient reader of a proof file, and the reader that fills whole paths, on
the fast form of a round's hash calls, with proofs that they are the same functions.

The two readers are `laxWhole` (Run/ParseLax.lean), which only cuts a file into its parts (to do so
it recomputes the hash chain, and it refuses some files; what it refuses: part 1 of the head of
Run/ParseLax.lean), and `fullWhole` (Run/ParseFull.lean), which also hashes the opened leaves and
walks up each opened tree (no root is compared).

Why. All calls of one round hash the same label and message, and then two words, of which the first
holds the call's number. Fmt/Rules5Fast.lean keeps the hash's state after the whole blocks of what
the calls share (`fetchF`), and has the hash on a linear form of BLAKE2b (`HF`); both are proved
equal to the rules' own functions. A state cannot be kept across calls of a hash that is handed in
as a function, so the fast form is a new definition, at the identity monad, proved equal to the old
one at all arguments. At a message of some 77,000 bytes with eleven calls, hashing each call from
its start (`fetchW`, Fmt/Rules5.lean) is most of a reader's time.

1. What the file contains.  Definitions that can be evaluated.
    `cutStepQ`, `cutFoldQ`, `cutChainQ`, `cutWholeQ`: the text of Run/ParseLax.lean's `cutStep` to
      `cutWhole` once more, with the chain's step as a parameter q.
    `laxQueryF`: the step without the test of work, by `fetchF`.
    `laxWholeF S b`, `fullWholeF S b`: the two readers.
    `parseLaxFP P S T file`, `parseFullFP P S T file`: the two parsers in the form of
      Run/ParseThin.lean.

2. What is checked when the file compiles.  Four tests (#guard).

3. Theorems (the last four stated in `Run.Spec`), for all arguments. Many statements of this library
   are written twice: a definition in the namespace `Spec` states a proposition, and a theorem of
   the same name outside that namespace proves it (lean/GLOSSARY.md).
   `cutWholeQ_eq`: `cutWholeQ h (laxQueryW h) ops S b = cutWhole h ops S b`, at every monad.
   `laxFast_query`: `laxQueryF = laxQueryW (m := Id) Fmt.formatHash`.
   `laxFast_lax`: `laxWholeF S b = laxWhole (m := Id) Fmt.formatHash S b`. `laxFast_full`:
     `fullWholeF S b = fullWhole (m := Id) Fmt.formatHash S b`.
   `laxFast_parse`: `parseLaxFP P S T file = parseLaxWP (m := Id) Fmt.formatHash P S T file`; the same for
     `parseFullFP`.

4. What is not claimed.  Nothing on time: that is measured, not proved.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ParseThin
import Fmt.Rules5Fast

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch
open _root_.Fmt (Plan Src OpenOut Spec St ChainOut Chain)

/-- A chain's step. Its arguments: the chain, the message, the kind, the work, the nonce, the number
of blocks of the verifier's message. -/
abbrev QryW (m : Type → Type) : Type :=
  Chain → ByteArray → _root_.Fmt.Kind → Nat → Nat → Nat → m (Option (Chain × Array ByteArray))

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- One round: as `cutStep` (Run/ParseLax.lean), at the chain's step q. -/
def cutStepQ (q : QryW m) (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s : St) (r : _root_.Fmt.Round) : m (Option St) :=
  match _root_.Fmt.slice b s.pos r.entry.msg with
  | none => pure none
  | some msg =>
    match _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) msg with
    | none => pure none
    | some vals =>
      match _root_.Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => pure none
      | some (nonce, i1) => do
        match ← q s.chain msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => pure none
        | some (c, vb) =>
          let drawn := _root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf vb)
          let l := _root_.Fmt.listOf drawn.poss
          match _root_.Fmt.readList P r.entry.poss l b i1 with
          | none => pure none
          | some (_, i2) =>
            let roots := s.roots ++ (_root_.Fmt.rootsOf vals).toArray
            match ← ops run roots drawn.poss r.opens i2 with
            | none => pure none
            | some (cols, i3) =>
              pure (some ⟨i3, c, roots, s.seen, s.out.push ⟨msg, vals, nonce, drawn, l, cols⟩⟩)

/-- The fold of `cutStepQ` over the rounds. -/
def cutFoldQ (q : QryW m) (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List _root_.Fmt.Round → St → m (Option St)
  | [], s => pure (some s)
  | r :: rs, s => do
    match ← cutStepQ q ops P run b s r with
    | none => pure none
    | some s' => cutFoldQ q ops P run b rs s'

/-- A chain in a file, from the place i on. -/
def cutChainQ (q : QryW m) (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) (i : Nat) :
    m (Option (ChainOut × Nat)) :=
  if !S.ok then pure none
  else
    let rnd : Option (Option ByteArray × Nat) :=
      match S.rand with
      | .inFile => (_root_.Fmt.slice b i 32).map fun x => (some x, i + 32)
      | .given x => some (some x, i)
      | .none => some (none, i)
    match rnd with
    | none => pure none
    | some (x, i0) => do
      let pd ← _root_.Fmt.paramsDigestW h S.params
      match ← _root_.Fmt.startChainW h S.label pd S.statement x with
      | none => pure none
      | some hd =>
        match ← cutFoldQ q (ops b) S.plan hd.run b S.rounds
            ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
        | none => pure none
        | some s => pure (some (⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩, s.pos))

/-- The same, and nothing stands behind the chain. -/
def cutWholeQ (q : QryW m) (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) :
    m (Option ChainOut) := do
  match ← cutChainQ h q ops S b 0 with
  | some (o, j) => pure (if j == b.size then some o else none)
  | none => pure none

end

/-! ## At the step `laxQueryW h` these functions are those of Run/ParseLax.lean -/

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

theorem cutStepQ_eq (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s : St) (r : _root_.Fmt.Round) :
    cutStepQ (laxQueryW h) ops P run b s r = cutStep h ops P run b s r := rfl

theorem cutFoldQ_eq (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List _root_.Fmt.Round) (s : St),
      cutFoldQ (laxQueryW h) ops P run b rs s = cutFold h ops P run b rs s
  | [], _ => rfl
  | r :: rs, s => by
      show (cutStepQ (laxQueryW h) ops P run b s r >>= fun x => match x with
          | none => pure none
          | some s' => cutFoldQ (laxQueryW h) ops P run b rs s') =
        (cutStep h ops P run b s r >>= fun x => match x with
          | none => pure none
          | some s' => cutFold h ops P run b rs s')
      rw [cutStepQ_eq]
      congr 1
      funext x
      cases x with
      | none => rfl
      | some s' => exact cutFoldQ_eq ops P run b rs s'

theorem cutChainQ_eq (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) (i : Nat) :
    cutChainQ h (laxQueryW h) ops S b i = cutChain h ops S b i := by
  unfold cutChainQ cutChain
  simp only [cutFoldQ_eq]
  rfl

theorem cutWholeQ_eq (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) :
    cutWholeQ h (laxQueryW h) ops S b = cutWhole h ops S b := by
  unfold cutWholeQ cutWhole
  simp only [cutChainQ_eq]
  rfl

end

/-! ## The fast forms -/

/-- The step of a chain without the work test, by the fast form of a round's calls. -/
def laxQueryF : QryW Id := fun c msg kind work nonce K =>
  if _root_.Fmt.askOK c.label c.rho (c.round + 1) msg kind work nonce then
    let bs := _root_.Fmt.fetchF
      c.label c.rho (c.round + 1) msg kind work nonce (_root_.Fmt.firstBlock work + K)
    some (⟨c.label, _root_.Fmt.nextA work bs, c.round + 1⟩, _root_.Fmt.msgA work bs)
  else none

/-- The lenient reader, in the fast form. -/
def laxWholeF (S : Spec) (b : ByteArray) : Option ChainOut :=
  cutWholeQ (m := Id) _root_.Fmt.HF laxQueryF
    (fun b _ roots poss os i => laxOpens S.plan roots poss b os i) S b

/-- The reader that also hashes the opened leaves and walks, in the fast form. -/
def fullWholeF (S : Spec) (b : ByteArray) : Option ChainOut :=
  cutWholeQ (m := Id) _root_.Fmt.HF laxQueryF
    (fun b run roots poss os i =>
      fullOpens (m := Id) _root_.Fmt.HF S.cfg S.plan b run roots poss os i)
    S b

/-- The lenient parser, in the form of Run/ParseThin.lean and on the fast reader. -/
def parseLaxFP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (S : Spec)
    (T : TypingP P) (file : ByteArray) :
    Option (List (Dig 256) × OneProtocolProof 256 P.up) :=
  (laxWholeF S file).bind (toBPrfP P T)

/-- The parser that fills whole paths, in the form of Run/ParseThin.lean and on the fast reader. -/
def parseFullFP {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (S : Spec)
    (T : TypingP P) (file : ByteArray) :
    Option (List (Dig 256) × OneProtocolProof 256 P.up) :=
  (fullWholeF S file).bind (toBPrfFullP P T)

def Spec.laxFast_query : Prop := laxQueryF = laxQueryW (m := Id) _root_.Fmt.formatHash
def Spec.laxFast_lax : Prop :=
  ∀ (S : _root_.Fmt.Spec) (b : ByteArray), laxWholeF S b = laxWhole (m := Id) _root_.Fmt.formatHash S b
def Spec.laxFast_full : Prop :=
  ∀ (S : _root_.Fmt.Spec) (b : ByteArray), fullWholeF S b = fullWhole (m := Id) _root_.Fmt.formatHash S b
def Spec.laxFast_parse : Prop :=
  ∀ {Y : Type} {E : ExtSpec} (P : Twin.PS Y E) (S : _root_.Fmt.Spec)
      (T : TypingP P) (file : ByteArray),
    parseLaxFP P S T file = parseLaxWP (m := Id) _root_.Fmt.formatHash P S T file ∧
    parseFullFP P S T file = parseFullWP (m := Id) _root_.Fmt.formatHash P S T file

theorem laxFast_query : Spec.laxFast_query := by
  funext c msg kind work nonce K
  unfold laxQueryF laxQueryW
  rw [_root_.Fmt.fetchF_eq]
  rfl

theorem laxFast_lax : Spec.laxFast_lax := by
  intro S b
  unfold laxWholeF laxWhole
  rw [_root_.Fmt.HF_eq, laxFast_query, cutWholeQ_eq]
  rfl

theorem laxFast_full : Spec.laxFast_full := by
  intro S b
  unfold fullWholeF fullWhole
  rw [_root_.Fmt.HF_eq, laxFast_query, cutWholeQ_eq]

theorem laxFast_parse : Spec.laxFast_parse := by
  intro Y E P S T file
  refine ⟨?_, ?_⟩
  · unfold parseLaxFP parseLaxWP
    rw [laxFast_lax]
    rfl
  · unfold parseFullFP parseFullWP
    rw [laxFast_full]
    rfl

/-! ## Guards, at the example file of Run/ParseChain.lean -/

#guard (laxWholeF (ParseEx.spec (1, 2, 3)) ParseEx.file).map ParseEx.view == (ParseEx.lax (1, 2, 3) ParseEx.file).map ParseEx.view
#guard (laxWholeF (ParseEx.spec (1, 2, 3)) ParseEx.file).isSome
#guard (fullWholeF (ParseEx.spec (1, 2, 3)) ParseEx.file).map ParseEx.view == (ParseEx.full (1, 2, 3) ParseEx.file).map ParseEx.view
#guard (laxWholeF (ParseEx.spec (1, 2, 3)) (ParseEx.file.extract 0 511)).isNone

end Run
