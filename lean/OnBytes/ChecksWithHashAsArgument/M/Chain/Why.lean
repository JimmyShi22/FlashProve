-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/Why.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Chain/Why.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.
The step of a chain is no argument here: it is `Fmt.Chain.queryW` at the hash (Fmt/Rules5.lean),
which hashes a round's message anew in each of the round's calls. The port's step `queryH` hashes
once what the calls share; at `formatHashFastForm` the two are equal (`step_port`,
OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean). Where the root's `main` is `programFront`
(OnBytes/Shell/Front.lean), it runs this text at the identity monad and `formatHashFastForm`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM

namespace OnBytes.TwoPort.M

open Fmt (Qry Hash Plan St Round Stored SpecX Seen Shape Src Fld)
section

variable {m : Type → Type} [Monad m]

def tryOpening (h : HashM m) (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start root : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (sn : List Rooted) :
    m (Except ReaderCheck (List Rooted × Nat)) := do
  match ← openingM h cfg f salt sh start xs b i with
  | none => pure (.error .form)
  | some o =>
    match Keeper.indexed.add root (Fmt.entered o.seen) sn with
    | none => pure (.error .vertex)
    | some sn' => pure (if o.root == root then .ok (sn', o.next) else .error .opening)

def tryStored (h : HashM m) (cfg statement : ByteArray) (P : Plan) (poss : List Nat)
    (b : ByteArray) : List Stored → List Rooted → Nat → m (Except ReaderCheck (List Rooted × Nat))
  | [], sn, i => pure (.ok (sn, i))
  | t :: ts, sn, i =>
    match Fmt.itemRoot statement t.item with
    | none => pure (.error .description)
    | some root => do
      match ← tryOpening h cfg P.field t.salt t.sh cfg root
          (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i sn with
      | .error e => pure (.error e)
      | .ok (sn', j) => tryStored h cfg statement P poss b ts sn' j

def tryOpens (h : HashM m) (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    List (Shape × Src) → List Rooted → Nat → m (Except ReaderCheck (List Rooted × Nat))
  | [], sn, i => pure (.ok (sn, i))
  | (sh, src) :: os, sn, i =>
    let rs : Option (ByteArray × ByteArray) :=
      match src with
      | .own n =>
        match roots[n]?, run with
        | some r, some s => some (r, s)
        | _, _ => none
      | .given r s => some (r, s)
    match rs with
    | none => pure (.error .description)
    | some (root, start) => do
      match ← tryOpening h cfg P.field P.salt sh start root
          (listOfT (poss.map (· % 2 ^ sh.a))) b i sn with
      | .error e => pure (.error e)
      | .ok (sn', j) => tryOpens h cfg P run roots poss b os sn' j

def whyRound (h : HashM m) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK (List Rooted)) (r : Round)
    (ts : List Stored) : m (Except ReaderCheck (StK (List Rooted))) :=
  match Fmt.slice b s.pos r.entry.msg with
  | none => pure (.error .form)
  | some msg =>
    match Fmt.whole (readItemsT P.field r.items) msg with
    | none => pure (.error .form)
    | some vals =>
      match Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => pure (.error .form)
      | some (nonce, i1) => do
        match ← Fmt.Chain.queryW h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => pure (.error (if r.entry.work == 0 then .description else .work))
        | some (c, vb) =>
          let drawn := drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)
          match readListT P r.entry.poss (listOfT drawn.poss) b i1 with
          | none => pure (.error .listed)
          | some (_, i2) =>
            match ← tryStored h cfg statement P drawn.poss b ts s.kept i2 with
            | .error e => pure (.error e)
            | .ok (sn1, i2') =>
              let roots := s.roots ++ (rootsT vals).toArray
              match ← tryOpens h cfg P run roots drawn.poss b r.opens sn1 i2' with
              | .error e => pure (.error e)
              | .ok (sn, i3) => pure (.ok ⟨i3, c, roots, sn, #[]⟩)

def whyRounds (h : HashM m) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    List (Round × List Stored) → StK (List Rooted) → Nat → m (Option (ReaderCheck × Nat))
  | [], _, _ => pure none
  | r :: rs, s, k => do
    match ← whyRound h cfg statement P run b s r.1 r.2 with
    | .ok s' => whyRounds h cfg statement P run b rs s' (k + 1)
    | .error e => pure (some (e, k))

def whyRest (h : HashM m) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) : m (Option (ReaderCheck × Nat)) := do
  let pd ← Fmt.paramsDigestW h S.base.params
  match ← Fmt.startChainW h S.base.label pd S.base.statement x with
  | none => pure (some (.form, 0))
  | some hd =>
    whyRounds h S.base.cfg S.base.statement S.base.plan hd.run b
      (zipT S.base.rounds S.stored)
      ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], Keeper.indexed.ofSeen seen, #[]⟩ 0

def whyRefused (hh : HashM m) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    m (Option (ReaderCheck × Nat)) :=
  if !specXOk S then pure (some (.description, 0))
  else
    match S.base.rand with
    | .inFile =>
      match Fmt.slice b i 32 with
      | none => pure (some (.form, 0))
      | some x => whyRest hh S seen b (some x) (i + 32)
    | .given x => whyRest hh S seen b (some x) i
    | .none => whyRest hh S seen b none i

end

end OnBytes.TwoPort.M
