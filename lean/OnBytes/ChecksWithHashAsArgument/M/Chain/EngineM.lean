-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineM.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Chain/Engine.lean that hash, or hand a hash on, written once more
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
import OnBytes.Chain.Engine

namespace OnBytes.TwoPort.M

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)

abbrev HashM (m : Type → Type) : Type := Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray

section

variable {m : Type → Type} [Monad m]
section walk

variable {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))

def loneM (d i : Nat) (x : α) (s : σ) : m (Option ((Nat × α) × σ)) :=
  match give d (if i % 2 == 0 then i + 1 else i - 1) s with
  | none => pure none
  | some (o, s') => do
    let v ← if i % 2 == 0 then comb (d - 1) (i / 2) x o else comb (d - 1) (i / 2) o x
    pure (some ((i / 2, v), s'))

def levelLoopM (d : Nat) :
    List (Nat × α) → σ → Array (Nat × α) → m (Option (List (Nat × α) × σ))
  | [], s, acc => pure (some (acc.toList, s))
  | [(i, x)], s, acc => do
    match ← loneM comb give d i x s with
    | none => pure none
    | some (p, s') => pure (some ((acc.push p).toList, s'))
  | (i, x) :: (i', x') :: rest, s, acc =>
    if i % 2 == 0 && i' == i + 1 then do
      let v ← comb (d - 1) (i / 2) x x'
      levelLoopM d rest s (acc.push (i / 2, v))
    else do
      match ← loneM comb give d i x s with
      | none => pure none
      | some (p, s') => levelLoopM d ((i', x') :: rest) s' (acc.push p)

def walkM : Nat → List (Nat × α) → σ → List (Nat × Nat × α) →
    m (Option (α × σ × List (Nat × Nat × α)))
  | 0, [(i, r)], s, met => pure (some (r, s, (0, i, r) :: met))
  | 0, _, _, _ => pure none
  | d + 1, now, s, met => do
    match ← levelLoopM comb give (d + 1) now s #[] with
    | none => pure none
    | some (nxt, s') => walkM d nxt s' (now.map (fun v => (d + 1, v.1, v.2)) ++ met)

end walk

def leavesLoopM (h : HashM m) (sh : Shape) (start : ByteArray) :
    List Nat → List (List UInt64 × ByteArray) → Array (Nat × ByteArray) →
      m (List (Nat × ByteArray))
  | x :: xs, (col, salt) :: cs, acc => do
    let v ← Fmt.leafW h (Fmt.leafNo sh.stored) sh.tree sh.a x start col salt
    leavesLoopM h sh start xs cs (acc.push (x, v))
  | _, _, acc => pure acc.toList

def openingM (h : HashM m) (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) : m (Option OpenOut) :=
  if Fmt.listOK sh.a xs && Fmt.saltLenOK salt then
    match rdOpeningT f salt sh xs b i with
    | none => pure none
    | some ((cs, given), next) => do
      let ls ← leavesLoopM h sh start xs cs #[]
      let w ← walkM (fun _ _ l r => Fmt.vertexW h cfg l r) Fmt.takeGiven sh.a ls (given, []) []
      pure (w.map fun r => ⟨cs.map (·.1), cs.map (·.2), given, r.1, r.2.2 ++ r.2.1.2, next⟩)
  else pure none

def storedLoopM {R : Type} (K : Keeper R) (h : HashM m) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) :
    List Stored → R → Nat → Array (Shape × List Nat × OpenOut) →
      m (Option (List (Shape × List Nat × OpenOut) × R × Nat))
  | [], sn, i, acc => pure (some (acc.toList, sn, i))
  | t :: ts, sn, i, acc => do
    match ← openingM h cfg P.field t.salt t.sh cfg
        (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
    | none => pure none
    | some o =>
      if some o.root == Fmt.itemRoot statement t.item then
        match K.add o.root (Fmt.entered o.seen) sn with
        | none => pure none
        | some sn' =>
          storedLoopM K h cfg statement P poss b ts sn' o.next
            (acc.push (t.sh, listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a)), o))
      else pure none

def opensLoopM {R : Type} (K : Keeper R) (h : HashM m) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    List (Shape × Src) → R → Nat → Array (Shape × List Nat × OpenOut) →
      m (Option (List (Shape × List Nat × OpenOut) × R × Nat))
  | [], sn, i, acc => pure (some (acc.toList, sn, i))
  | (sh, src) :: os, sn, i, acc =>
    match rootAndStart roots run src with
    | none => pure none
    | some (root, start) => do
      match ← openingM h cfg P.field P.salt sh start (listOfT (poss.map (· % 2 ^ sh.a))) b i with
      | none => pure none
      | some o =>
        if o.root == root then
          match K.add root (Fmt.entered o.seen) sn with
          | none => pure none
          | some sn' =>
            opensLoopM K h cfg P run roots poss b os sn' o.next
              (acc.push (sh, listOfT (poss.map (· % 2 ^ sh.a)), o))
        else pure none

def roundM {R : Type} (K : Keeper R) (h : HashM m) (cfg statement : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round)
    (ts : List Stored) : m (Option (StK R)) :=
  match Fmt.slice b s.pos r.entry.msg with
  | none => pure none
  | some msg =>
    match Fmt.whole (readItemsT P.field r.items) msg with
    | none => pure none
    | some vals =>
      match Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => pure none
      | some (nonce, i1) => do
        match ← Fmt.Chain.queryW h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => pure none
        | some (c, vb) =>
          let drawn := drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)
          let l := listOfT drawn.poss
          match readListT P r.entry.poss l b i1 with
          | none => pure none
          | some (_, i2) =>
            let roots := s.roots ++ (rootsT vals).toArray
            match ← storedLoopM K h cfg statement P drawn.poss b ts s.kept i2 #[] with
            | none => pure none
            | some (colsS, sn1, i2') =>
              match ← opensLoopM K h cfg P run roots drawn.poss b r.opens sn1 i2' #[] with
              | none => pure none
              | some (cols, sn, i3) =>
                pure (some ⟨i3, c, roots, sn,
                  s.out.push ⟨msg, vals, nonce, drawn, l, colsS ++ cols⟩⟩)

def foldRoundsM {R : Type} (K : Keeper R) (h : HashM m) (cfg statement : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List (Round × List Stored) → StK R → m (Option (StK R))
  | [], s => pure (some s)
  | r :: rs, s => do
    match ← roundM K h cfg statement P run b s r.1 r.2 with
    | none => pure none
    | some s' => foldRoundsM K h cfg statement P run b rs s'

def restM {R : Type} (K : Keeper R) (h : HashM m) (S : SpecX) (seen : Seen)
    (b : ByteArray) (x : Option ByteArray) (i0 : Nat) : m (Option (ChainOut × Nat)) := do
  let pd ← Fmt.paramsDigestW h S.base.params
  match ← Fmt.startChainW h S.base.label pd S.base.statement x with
  | none => pure none
  | some hd =>
    match ← foldRoundsM K h S.base.cfg S.base.statement S.base.plan hd.run b
        (zipT S.base.rounds S.stored)
        ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], K.ofSeen seen, #[]⟩ with
    | none => pure none
    | some s =>
      pure (some (⟨pd, hd.run, hd.rho0, s.chain.rho, K.toSeen s.kept, s.out⟩, s.pos))

def readChainM {R : Type} (K : Keeper R) (h : HashM m) (S : SpecX) (seen : Seen)
    (b : ByteArray) (i : Nat) : m (Option (ChainOut × Nat)) :=
  if !specXOk S then pure none
  else
    match S.base.rand with
    | .inFile =>
      match Fmt.slice b i 32 with
      | none => pure none
      | some x => restM K h S seen b (some x) (i + 32)
    | .given x => restM K h S seen b (some x) i
    | .none => restM K h S seen b none i

end

end OnBytes.TwoPort.M
