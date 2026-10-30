-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/AskX.lean: the library's strict reader of a chain that opens stored tables, as a
computation that asks an oracle on strings, tied to the same reader at a function, with its
questions counted.

The library writes that reader once, over a variable monad, with the hash as its first argument
(Fmt/Rules8X.lean: `Fmt.readChainX`). Here it is read in the library's monad of trees of queries
(`ZKCP.OComp 256`), at the hash that asks for each of its strings, but for one string. The string of
the call that hashes the parameter bytes is not asked: it is answered with the format's own digest
of these bytes, a value of BLAKE2b, as a constant (OnBytes/Tie/DigestPoint.lean: `digestStr`,
`pinned`).

Main definitions.
 `askPinned params s`   no question and the constant, if s is `digestStr params`; else one question.
 `readAsk S seen b i`   `Fmt.readChainX` at the hash `Fmt.HM (askPinned S.base.params)`.
Main theorems, for every description S, record of met vertices, byte string b and place i.
 `readAsk_det`     at every oracle f, the result of `readAsk` is what `Fmt.readChainX` reads in the
                   identity monad at the hash that `pinned (Run.oB f) S.base.params` induces.
 `readAsk_bound`   `readAsk` tosses no coin, and asks at most `fileNX S * 2` questions on every path
                   (OnBytes/Tie/CostX.lean: `fileNX`, a function of the description alone).
 `readAsk_run`     its run at f, a distribution by the library's definition, is the point mass at
                   that result.
 `readAsk_readInAt`   `readInAt (pinned (Run.oB f) S.base.params)` (OnBytes/Tie/StoredAt.lean) in
                   terms of the result of `readAsk` at f.
 `readAskR`, `readAskR_det`, `readAskR_bound`, `readAskR_runEager`   the same computation and the
                   same three facts in the library's generic language of trees, over the family
                   with one oracle (`Rom.OComp (Rom.rom 256)`, by Rom/Bridge.lean's `Rom.toRom`).
 `HO_pinned_oBits`, `readAsk_program`, `readAskR_program`   at the library's oracle on bit strings
                   that is made from BLAKE2b (`Run.oBits`), and within the bounds `smallFX`, the
                   result of the reader that asks is what the program's reader `readIn` returns.

What is not claimed. Nothing on soundness. No probability: `readAsk_run` speaks of one fixed f, and
no oracle is drawn. The reader takes BLAKE2b's digest of the parameter bytes as a constant: it is
not the reader that asks for every hash. Nothing says which strings are asked, or in what order:
that is read off `readAsk`'s text. An oracle is read at bit strings of whole bytes alone. That
either side of `readAsk_det` is other than "refused", at any oracle and any bytes, is not shown
here; a test that is not in this library tests it at one made-up file and BLAKE2b's oracle. The
bound is an
upper bound; nothing says that it is attained. Every call of the hash is counted as two questions,
though only a round's call (number 162) asks two, and the call on the parameter bytes is counted,
though it asks none: the bound can be twice the truth. It is evaluated at no description here
(a test that is not in this library evaluates it at three). No decision is taken on what was read.
The
program does not call any function of this file: "the program" is the Lean port that is built from
OnBytes/, not the C++ verifier. `readAsk` is tied to the program's reader at one oracle alone,
`Run.oBits`.

-/
import OnBytes.Tie.HomX
import OnBytes.Tie.CostX
import OnBytes.Tie.DigestPoint
import Run.OCompHom
import Run.OCompCostP
import Run.ParserHashProofs

set_option autoImplicit false

namespace OnBytes.Tie
open ZKCP

/-- One string of the hash as a computation: the string of the call that hashes `params` is
answered, without a question, with the format's own digest of `params`, a value of BLAKE2b. Every
other string is one question to the oracle. -/
def askPinned (params s : ByteArray) : OComp 256 ByteArray :=
  if s = digestStr params then pure (Fmt.paramsDigest params) else Run.askB s

/-- **The reader that asks**: the library's strict reader of a chain that opens stored tables, from
the place i of b on, at the hash that asks by `askPinned S.base.params`. No decision is taken. The
program does not call this function. -/
def readAsk (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    OComp 256 (Option (Fmt.ChainOut × Nat)) :=
  Fmt.readChainX (Fmt.HM (askPinned S.base.params)) S seen b i

/-! ## At an oracle -/

/-- At the oracle f, `askPinned params s` gives what `pinned (Run.oB f) params` gives at s. -/
theorem det_askPinned (f : ZKCP.Oracle 256) (params s : ByteArray) :
    (askPinned params s).det f = pinned (Run.oB f) params s := by
  unfold askPinned pinned
  split <;> rfl

/-- The hash that asks by `askPinned params`, read through "run at f", is the hash that the function
`pinned (Run.oB f) params` induces. -/
theorem detHom_on_askPinned (f : ZKCP.Oracle 256) (params : ByteArray) :
    (Run.detHom f).on (Fmt.HM (askPinned params)) = Fmt.HO (pinned (Run.oB f) params) := by
  funext number tree index start bytes
  have e : (fun s => (Run.detHom f).app (askPinned params s)) = pinned (Run.oB f) params :=
    funext fun s => det_askPinned f params s
  exact ((Run.detHom f).HM (askPinned params) number tree index start bytes).trans
    ((congrArg (fun a => Fmt.HM (m := Id) a number tree index start bytes) e).trans
      (Fmt.HM_id _ number tree index start bytes))

/-- **At every oracle f, the result of the reader that asks is what the strict reader reads, in the
identity monad, at the hash that `pinned (Run.oB f) S.base.params` induces.** No condition on S, on
the record, on b or on i. An equation between two results; both may be "refused". The reader is the
library's, not the program's. Nothing on soundness; no probability. -/
theorem readAsk_det (f : ZKCP.Oracle 256) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : Nat) :
    (readAsk S seen b i).det f =
      Fmt.readChainX (m := Id) (Fmt.HO (pinned (Run.oB f) S.base.params)) S seen b i := by
  rw [← Run.detHom_app f]
  exact (HomX.app_readChainX (Run.detHom f) (Fmt.HM (askPinned S.base.params)) S seen b i).trans
    (congrArg (fun h => Fmt.readChainX (m := Id) h S seen b i)
      (detHom_on_askPinned f S.base.params))

/-! ## No coin, and the count -/

/-- `askPinned params s` tosses no coin and asks at most one question. -/
theorem qp_askPinned (params s : ByteArray) :
    (Run.qp 256).le (askPinned params s) 1 fun _ => True := by
  unfold askPinned
  split
  · exact ⟨trivial, trivial, trivial⟩
  · exact ⟨Run.noCoin_askB s, Run.asks_askB s, OComp.all_true _⟩

/-- Each call of the hash that asks by `askPinned params` tosses no coin and asks at most two
questions. -/
theorem qp_HM_askPinned (params : ByteArray) (number tree index : Nat) (start bytes : ByteArray) :
    (Run.qp 256).le (Fmt.HM (askPinned params) number tree index start bytes) 2 fun _ => True :=
  Run.CostP.HM (Run.qp 256) (askPinned params) 1 (qp_askPinned params) number tree index start bytes

/-- If `Run.qp 256` bounds a tree by t, with no condition on its output, the tree tosses no coin and
asks at most t questions. Stated for any tree, so that Lean need not unfold the reader. -/
theorem out_of_qp {α : Type} (c : OComp 256 α) (t : ℕ) (h : (Run.qp 256).le c t fun _ => True) :
    c.NoCoin ∧ c.QueryBound t := ⟨h.1, h.2.1⟩

/-- A tree without coins, run at f, is the point mass at a value to which its result at f is equal.
Stated for any tree, and with the pair that `out_of_qp` gives as its hypothesis, so that Lean need
not unfold the reader; the bound t is not used. -/
theorem run_of_out {α : Type} (f : ZKCP.Oracle 256) (c : OComp 256 α) (v : α) (t : ℕ)
    (h : c.NoCoin ∧ c.QueryBound t) (e : c.det f = v) : c.run f = PMF.pure v := by
  rw [OComp.run_of_noCoin f c h.1, e]

/-- **The reader that asks tosses no coin, and on every path it asks at most `fileNX S * 2`
questions.** The number depends on the description alone: not on the bytes, the place, the record of
met vertices or the answers. It is an upper bound. A repeated question counts again. Nothing says
that the bound is attained; it can be twice the truth. Nothing on which strings are asked. -/
theorem readAsk_bound (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    (readAsk S seen b i).NoCoin ∧ (readAsk S seen b i).QueryBound (CostX.fileNX S * 2) :=
  out_of_qp (readAsk S seen b i) (CostX.fileNX S * 2)
    (CostX.le_readChainX (Run.qp 256) (Fmt.HM (askPinned S.base.params)) 2
      (qp_HM_askPinned S.base.params) S seen b i)

/-- **The run of the reader that asks at a fixed oracle f**, a distribution by the library's
definition of a run, **is the point mass at what the strict reader reads at the hash that
`pinned (Run.oB f) S.base.params` induces.** No oracle is drawn here. -/
theorem readAsk_run (f : ZKCP.Oracle 256) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : Nat) :
    (readAsk S seen b i).run f =
      PMF.pure (Fmt.readChainX (m := Id) (Fmt.HO (pinned (Run.oB f) S.base.params)) S seen b i) :=
  run_of_out f (readAsk S seen b i) _ (CostX.fileNX S * 2) (readAsk_bound S seen b i)
    (readAsk_det f S seen b i)

/-! ## The reader within a session -/

/-- `readInAt` at the function `pinned (Run.oB f) S.base.params`, in terms of the result at f of the
reader that asks: refused where that is refused; else what was read, its view, the place behind the
chain, and the record handed on. -/
theorem readAsk_readInAt (f : ZKCP.Oracle 256) (S : Fmt.SpecX) (b : ByteArray) (i : Nat)
    (s : Session) :
    readInAt (pinned (Run.oB f) S.base.params) S b i s =
      match (readAsk S s.seen b i).det f with
      | none => none
      | some (o, j) => some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩) := by
  rw [readAsk_det]
  rfl

/-! ## The same computation in the generic language of trees -/

/-- `Rom.toRom` keeps "no path has a coin toss". -/
theorem noCoin_toRom {lam : ℕ} {α : Type} :
    ∀ (c : OComp lam α), c.NoCoin → (Rom.toRom c).NoCoin
  | .pure _, _ => trivial
  | .query _ k, h => fun r => noCoin_toRom (k r) (h r)
  | .sample _ _, h => h.elim

/-- `Rom.toRom` keeps "no coin" and "at most t questions". Stated for any tree, so that Lean need
not unfold the reader. -/
theorem toRom_out {α : Type} (c : OComp 256 α) (t : ℕ) (h : c.NoCoin ∧ c.QueryBound t) :
    (Rom.toRom c).NoCoin ∧ (Rom.toRom c).QueryBound t :=
  ⟨noCoin_toRom c h.1, (Rom.queryBound_toRom c t).2 h.2⟩

/-- A generic tree without coins, run at fixed oracles g, is the point mass at a value to which its
result at g is equal. Stated for any tree, with the pair that `toRom_out` gives as its hypothesis;
the bound t is not used. -/
theorem runEager_of_out {α : Type} (g : Rom.Fam (Rom.rom 256)) (c : Rom.OComp (Rom.rom 256) α)
    (v : α) (t : ℕ) (h : c.NoCoin ∧ c.QueryBound t) (e : c.det g = v) :
    c.runEager g = PMF.pure v := by
  rw [h.1.runEager g, e]

/-- The reader that asks, as a tree in the library's generic language, over the family with one
oracle: `readAsk`, node by node. -/
def readAskR (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    Rom.OComp (Rom.rom 256) (Option (Fmt.ChainOut × Nat)) :=
  Rom.toRom (readAsk S seen b i)

/-- At every family g with one oracle, the result of `readAskR` is what the strict reader reads, in
the identity monad, at the hash that `pinned (Run.oB (g ())) S.base.params` induces. An equation
between two results; both may be "refused". The reader is the library's, not the program's. Nothing
on soundness; no probability. -/
theorem readAskR_det (g : Rom.Fam (Rom.rom 256)) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : Nat) :
    (readAskR S seen b i).det g =
      Fmt.readChainX (m := Id) (Fmt.HO (pinned (Run.oB (g ())) S.base.params)) S seen b i :=
  (OComp.det_toRom g (readAsk S seen b i)).trans (readAsk_det (g ()) S seen b i)

/-- `readAskR` tosses no coin, and on every path it asks at most `fileNX S * 2` questions, in the
generic language's sense of both. A repeated question counts again. Nothing says that the bound is
attained; it can be twice the truth. Nothing on which strings are asked. -/
theorem readAskR_bound (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    (readAskR S seen b i).NoCoin ∧ (readAskR S seen b i).QueryBound (CostX.fileNX S * 2) :=
  toRom_out (readAsk S seen b i) (CostX.fileNX S * 2) (readAsk_bound S seen b i)

/-- The run of `readAskR` at a fixed family g is the point mass at what the strict reader reads at
the hash that `pinned (Run.oB (g ())) S.base.params` induces. No oracle is drawn here. -/
theorem readAskR_runEager (g : Rom.Fam (Rom.rom 256)) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) :
    (readAskR S seen b i).runEager g =
      PMF.pure
        (Fmt.readChainX (m := Id) (Fmt.HO (pinned (Run.oB (g ())) S.base.params)) S seen b i) :=
  runEager_of_out g (readAskR S seen b i) _ (CostX.fileNX S * 2) (readAskR_bound S seen b i)
    (readAskR_det g S seen b i)

/-! ## At the oracle that is made from BLAKE2b -/

/-- The hash that `pinned (Run.oB (Run.oBits ())) params` induces is the hash that
`pinned Fmt.oracle params` induces. `Run.oBits` is the library's oracle on bit strings that is made
from the format's oracle, and so from BLAKE2b. As functions on byte strings `Run.oB (Run.oBits ())`
and `Fmt.oracle` differ; they agree at the strings of the hash's calls (`Run.ph_oStr`). -/
theorem HO_pinned_oBits (params : ByteArray) :
    Fmt.HO (pinned (Run.oB (Run.oBits ())) params) = Fmt.HO (pinned Fmt.oracle params) := by
  funext n t i st bs
  have hp : ∀ half : UInt8, half = 0 ∨ half = 1 →
      pinned (Run.oB (Run.oBits ())) params (Fmt.oStr half n t i st bs) =
        pinned Fmt.oracle params (Fmt.oStr half n t i st bs) := by
    intro half hh
    unfold pinned
    rw [Run.ph_oStr half n t i st bs hh]
  unfold Fmt.HO
  rw [hp 0 (Or.inl rfl), hp 1 (Or.inr rfl)]

/-- **At the oracle that is made from BLAKE2b, the reader that asks returns what the program's
reader returns**, within the bounds `smallFX` on description and bytes: refused where `readIn`
refuses; else the same chain, view, place and record. One oracle; nothing on soundness; no
probability. -/
theorem readAsk_program (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session)
    (hsm : smallFX S b = true) :
    (match (readAsk S s.seen b i).det (Run.oBits ()) with
      | none => none
      | some (o, j) => some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩)) = readIn S b i s := by
  rw [← readAsk_readInAt, ← readInPinned_oracle S b i s hsm]
  unfold readInAt
  rw [HO_pinned_oBits]

/-- The same for the reader that asks as a tree in the library's generic language, at the family
`Run.oBits`. -/
theorem readAskR_program (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session)
    (hsm : smallFX S b = true) :
    (match (readAskR S s.seen b i).det Run.oBits with
      | none => none
      | some (o, j) => some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩)) = readIn S b i s := by
  rw [show (readAskR S s.seen b i).det Run.oBits = (readAsk S s.seen b i).det (Run.oBits ()) from
    OComp.det_toRom Run.oBits (readAsk S s.seen b i)]
  exact readAsk_program S b i s hsm

end OnBytes.Tie
