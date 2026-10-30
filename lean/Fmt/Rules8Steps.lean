-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8Steps.lean: the reader of a proof file, cut into stages, so that "the reader gives this on
that file" can be proved piece by piece.

The reader (`wholeChain`, Fmt/Rules8.lean) is the verifier's parser of a proof file: a fold over the
chain's rounds.

Why: a run of Fmt/Rules8.lean's reader on a closed file can be checked by Lean's kernel ("by decide
+kernel"), but as one theorem it needs more memory than there is; memory is given back between
declarations. So the file is laid out for one theorem for each stage, with closed data between them,
and it has the lemmas that join them. Everything is at the identity monad, for any hash h that is a
function.

Sources. The format page (docs/format/FORMAT.md); this file has not been held against the page as
it ships, and may differ from it. No Mathlib.

1. What the file contains.
   `Core`: the place in the file; the chain's label, value and number of rounds done; the roots sent
     so far; the vertices met under each root. What was read is not in it: the fold only lays it
     behind what was read before.
   `stepI`: The text of Fmt/Rules8.lean's `step`, without the monad.
   `foldI`.
   `rndOf`: the head's first piece: the chain's random bytes (from the file, given, or none) and the
     place behind them.
   Equality that computes: `Core`, `RoundOut`, `OpenOut`, `Chain`, `ChainHead`, `ChainOut` get a
     decidable equality by the deriving handler (field by field; nothing made by a simplifier).

2. What is checked when the file compiles. Only the proofs.

3. Theorems.
   `step_stepI`: `step` at a state = `stepI` at its `Core`, with the round's reading laid behind
     what the state held.
   `fold_foldI`: the same for the fold.
   `foldI_cons`: a stage joins.
   `whole_of_stages`: the composition: if the data are in order (`S.ok = true`), and given the
     random bytes, the parameters' digest, the chain's head, the fold on Cores, and that the last
     place is the file's end, then wholeChain h S b = some (what these pieces say).
   `whole_refused`: if the fold on Cores gives nothing, with all before it as above, then
     wholeChain h S b = none.

4. What is not claimed. Any stage at any file: the stages' theorems are made elsewhere, by programs.
   No file of Fmt/ or Run/ has such a theorem. Nothing at another monad.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules8

namespace Fmt

deriving instance DecidableEq for OpenOut
deriving instance DecidableEq for RoundOut
deriving instance DecidableEq for Chain
deriving instance DecidableEq for ChainHead
deriving instance DecidableEq for ChainOut

/-- What a round hands to the next. -/
structure Core where
  pos   : Nat
  chain : Chain
  roots : Array ByteArray
  seen  : Seen
  deriving DecidableEq

def St.core (s : St) : Core := ⟨s.pos, s.chain, s.roots, s.seen⟩

/-- a Core with what was read so far -/
def Core.st (c : Core) (out : Array RoundOut) : St := ⟨c.pos, c.chain, c.roots, c.seen, out⟩

section
variable (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)

/-- One round, on a `Core`. -/
def stepI (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s : Core) (r : Round) : Option (Core × RoundOut) :=
  match slice b s.pos r.entry.msg with
  | none => none
  | some msg =>
    match whole (readItems P.field r.items) msg with
    | none => none
    | some vals =>
      match readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => none
      | some (nonce, i1) =>
        match Id.run
            (Chain.queryW h s.chain msg r.kind r.entry.work nonce
              ((wordsAtMost r.entry r.kind + 3) / 4)) with
        | none => none
        | some (c, vb) =>
          match readList P r.entry.poss
              (listOf (drawRound P.field r.entry r.kind (rowOf vb)).poss) b i1 with
          | none => none
          | some (_, i2) =>
            match Id.run
                (readOpens h cfg P run (s.roots ++ (rootsOf vals).toArray)
                  (drawRound P.field r.entry r.kind (rowOf vb)).poss b r.opens s.seen i2) with
            | none => none
            | some (cols, sn, i3) =>
              some (⟨i3, c, s.roots ++ (rootsOf vals).toArray, sn⟩,
                ⟨msg, vals, nonce, drawRound P.field r.entry r.kind (rowOf vb),
                  listOf (drawRound P.field r.entry r.kind (rowOf vb)).poss, cols⟩)

/-- the rounds one after the other -/
def foldI (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List Round → Core → Option (Core × List RoundOut)
  | [], c => some (c, [])
  | r :: rs, c =>
    match stepI h cfg P run b c r with
    | none => none
    | some (c', o) =>
      match foldI cfg P run b rs c' with
      | none => none
      | some (cN, os) => some (cN, o :: os)

end

/-- the chain's random bytes and the place behind them -/
def rndOf (S : Spec) (b : ByteArray) (i : Nat) : Option (Option ByteArray × Nat) :=
  match S.rand with
  | .inFile => (slice b i 32).map fun x => (some x, i + 32)
  | .given x => some (some x, i)
  | .none => some (none, i)

/-- the Core before the first round -/
def core0 (S : Spec) (i0 : Nat) (hd : ChainHead) (seen : Seen) : Core :=
  ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen⟩

namespace Spec

def step_stepI : Prop :=
  ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
      (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St) (r : Round),
    Id.run (step h cfg P run b s r) =
      (stepI h cfg P run b s.core r).map fun x => x.1.st (s.out.push x.2)

def fold_foldI : Prop :=
  ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (cfg : ByteArray) (P : Plan)
      (run : Option ByteArray) (b : ByteArray) (rs : List Round) (s : St),
    Id.run (foldRounds h cfg P run b rs s) =
      (foldI h cfg P run b rs s.core).map fun x => x.1.st (s.out ++ x.2.toArray)

def foldI_cons : Prop :=
  ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (cfg : ByteArray) (P : Plan)
      (run : Option ByteArray) (b : ByteArray) (r : Round) (rs : List Round) (c c' cN : Core)
      (o : RoundOut) (os : List RoundOut),
    stepI h cfg P run b c r = some (c', o) → foldI h cfg P run b rs c' = some (cN, os) →
    foldI h cfg P run b (r :: rs) c = some (cN, o :: os)

def whole_of_stages : Prop :=
  ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Fmt.Spec)
      (b : ByteArray) (x : Option ByteArray) (i0 : Nat) (pd : ByteArray) (hd : ChainHead)
      (cN : Core) (os : List RoundOut),
    S.ok = true → rndOf S b 0 = some (x, i0) → Id.run (paramsDigestW h S.params) = pd →
    Id.run (startChainW h S.label pd S.statement x) = some hd →
    foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd []) = some (cN, os) → cN.pos = b.size →
    Id.run (wholeChain h S b) = some ⟨pd, hd.run, hd.rho0, cN.chain.rho, cN.seen, os.toArray⟩

def whole_refused : Prop :=
  ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Fmt.Spec) (b : ByteArray)
      (x : Option ByteArray) (i0 : Nat) (pd : ByteArray) (hd : ChainHead),
    rndOf S b 0 = some (x, i0) → Id.run (paramsDigestW h S.params) = pd →
    Id.run (startChainW h S.label pd S.statement x) = some hd →
    foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd []) = none →
    Id.run (wholeChain h S b) = none

end Spec

theorem step_stepI : Spec.step_stepI := by
  intro h cfg P run b s r
  unfold step stepI St.core
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
      | some ni =>
        obtain ⟨nonce, i1⟩ := ni
        dsimp only
        generalize Chain.queryW h s.chain msg r.kind r.entry.work nonce
            ((wordsAtMost r.entry r.kind + 3) / 4) = q
        cases q with
        | none => rfl
        | some cv =>
          obtain ⟨c, vb⟩ := cv
          show Id.run (match readList P r.entry.poss (listOf (drawRound P.field r.entry r.kind (rowOf vb)).poss) b i1 with
            | none => pure none
            | some (_, i2) => _) = _
          dsimp only [Id.run]
          cases readList P r.entry.poss
              (listOf (drawRound P.field r.entry r.kind (rowOf vb)).poss) b i1 with
          | none => rfl
          | some ui =>
            obtain ⟨u, i2⟩ := ui
            dsimp only
            generalize readOpens h cfg P run (s.roots ++ (rootsOf vals).toArray)
                (drawRound P.field r.entry r.kind (rowOf vb)).poss b r.opens s.seen i2 = q2
            cases q2 with
            | none => rfl
            | some t =>
              obtain ⟨cols, sn, i3⟩ := t
              rfl

theorem foldI_cons : Spec.foldI_cons := by
  intro h cfg P run b r rs c c' cN o os h1 h2
  show (match stepI h cfg P run b c r with
    | none => none
    | some (c', o) =>
      match foldI h cfg P run b rs c' with
      | none => none
      | some (cN, os) => some (cN, o :: os)) = _
  rw [h1]
  dsimp only
  rw [h2]

theorem fold_foldI : Spec.fold_foldI := by
  intro h cfg P run b rs
  induction rs with
  | nil =>
    intro s
    show some s = some (s.core.st (s.out ++ #[]))
    rw [Array.append_empty]
    rfl
  | cons r rs ih =>
    intro s
    have h1 := step_stepI h cfg P run b s r
    show Id.run (do
      match ← step h cfg P run b s r with
      | none => pure none
      | some s' => foldRounds h cfg P run b rs s') = _
    show (match Id.run (step h cfg P run b s r) with
      | none => none
      | some s' => Id.run (foldRounds h cfg P run b rs s')) = _
    rw [h1]
    show _ = (match stepI h cfg P run b s.core r with
      | none => none
      | some (c', o) =>
        match foldI h cfg P run b rs c' with
        | none => none
        | some (cN, os) => some (cN, o :: os)).map _
    cases stepI h cfg P run b s.core r with
    | none => rfl
    | some co =>
      obtain ⟨c', o⟩ := co
      show Id.run (foldRounds h cfg P run b rs (c'.st (s.out.push o))) = (match foldI h cfg P run b rs c' with
        | none => none
        | some (cN, os) => some (cN, o :: os)).map fun (x : Core × List RoundOut) => x.1.st (s.out ++ x.2.toArray)
      rw [ih]
      show (foldI h cfg P run b rs c').map
          (fun (x : Core × List RoundOut) => x.1.st (s.out.push o ++ x.2.toArray)) = _
      generalize foldI h cfg P run b rs c' = y
      cases y with
      | none => rfl
      | some x =>
        obtain ⟨cN, os⟩ := x
        show some (cN.st (s.out.push o ++ os.toArray)) = some (cN.st (s.out ++ (o :: os).toArray))
        congr 2
        rw [Array.push_eq_append, Array.append_assoc, ← List.toArray_cons]

/-- a chain from a place on, on Cores: the text of Fmt/Rules8.lean's readChain, without the monad -/
def readI (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Fmt.Spec) (seen : Seen)
    (b : ByteArray) (i : Nat) : Option (ChainOut × Nat) :=
  if !S.ok then none
  else
    match rndOf S b i with
    | none => none
    | some (x, i0) =>
      match Id.run (startChainW h S.label (Id.run (paramsDigestW h S.params)) S.statement x) with
      | none => none
      | some hd =>
        match foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd seen) with
        | none => none
        | some (cN, os) =>
          some (⟨Id.run (paramsDigestW h S.params), hd.run, hd.rho0,
                cN.chain.rho, cN.seen, os.toArray⟩,
              cN.pos)

theorem readChain_tail (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Fmt.Spec)
    (seen : Seen) (b : ByteArray) (pd : ByteArray) (hd : ChainHead) (i0 : Nat) :
    (match Id.run (foldRounds h S.cfg S.plan hd.run b S.rounds ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩) with
      | none => none
      | some s => some ((⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩ : ChainOut), s.pos)) =
    (match foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd seen) with
      | none => none
      | some (cN, os) =>
          some ((⟨pd, hd.run, hd.rho0, cN.chain.rho, cN.seen, os.toArray⟩ : ChainOut),
                cN.pos)) := by
  rw [fold_foldI h S.cfg S.plan hd.run b S.rounds ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩]
  show (match (foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd seen)).map
    (fun (x : Core × List RoundOut) => x.1.st (#[] ++ x.2.toArray)) with
      | none => none
      | some s => some ((⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩ : ChainOut), s.pos)) = _
  generalize foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd seen) = y
  cases y with
  | none => rfl
  | some x =>
    obtain ⟨cN, os⟩ := x
    show some
        ((⟨pd, hd.run, hd.rho0, cN.chain.rho, cN.seen, #[] ++ os.toArray⟩ : ChainOut), cN.pos) = _
    rw [Array.empty_append]

theorem readChain_readI (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Fmt.Spec)
    (seen : Seen) (b : ByteArray) (i : Nat) :
    Id.run (readChain h S seen b i) = readI h S seen b i := by
  unfold readChain readI
  cases S.ok with
  | false => rfl
  | true =>
    show Id.run (match rndOf S b i with
      | none => pure none
      | some (x, i0) => _) = (match rndOf S b i with
      | none => none
      | some (x, i0) => _)
    generalize rndOf S b i = q
    cases q with
    | none => rfl
    | some xi =>
      obtain ⟨x, i0⟩ := xi
      show (match Id.run (startChainW h S.label (Id.run (paramsDigestW h S.params)) S.statement x) with
        | none => none
        | some hd =>
          match Id.run
              (foldRounds h S.cfg S.plan hd.run b S.rounds
                ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩) with
          | none => none
          | some s =>
            some ((⟨Id.run (paramsDigestW h S.params), hd.run, hd.rho0, s.chain.rho,
                  s.seen, s.out⟩ : ChainOut),
                s.pos)) =
        (match Id.run (startChainW h S.label (Id.run (paramsDigestW h S.params)) S.statement x) with
        | none => none
        | some hd =>
          match foldI h S.cfg S.plan hd.run b S.rounds (core0 S i0 hd seen) with
          | none => none
          | some (cN, os) =>
            some ((⟨Id.run (paramsDigestW h S.params), hd.run, hd.rho0, cN.chain.rho,
                  cN.seen, os.toArray⟩ : ChainOut),
                cN.pos))
      generalize Id.run (startChainW h S.label (Id.run (paramsDigestW h S.params)) S.statement x) =
        q2
      cases q2 with
      | none => rfl
      | some hd => exact readChain_tail h S seen b _ hd i0

theorem wholeChain_readI (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (S : Fmt.Spec) (b : ByteArray) :
    Id.run (wholeChain h S b) = (match readI h S [] b 0 with
      | some (o, j) => if j == b.size then some o else none
      | none => none) := by
  rw [← readChain_readI]
  unfold wholeChain
  generalize readChain h S [] b 0 = q
  cases q with
  | none => rfl
  | some oj =>
    obtain ⟨o, j⟩ := oj
    rfl

theorem whole_of_stages : Spec.whole_of_stages := by
  intro h S b x i0 pd hd cN os hok hr hpd hst hf hend
  rw [wholeChain_readI]
  unfold readI
  rw [hok, hr]
  dsimp only
  rw [hpd, hst]
  dsimp only
  rw [hf]
  dsimp only
  rw [hend, if_neg (by decide)]
  dsimp only
  rw [beq_self_eq_true]
  rfl

theorem whole_refused : Spec.whole_refused := by
  intro h S b x i0 pd hd hr hpd hst hf
  rw [wholeChain_readI]
  unfold readI
  cases S.ok with
  | false => rfl
  | true =>
    rw [hr]
    dsimp only
    rw [hpd, hst]
    dsimp only
    rw [hf]
    rfl

end Fmt
