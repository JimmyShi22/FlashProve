-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryPlanAtCfg.lean: the planner's `configure` puts the digest of the public files into
one field of its value and into the spelling of the seven strings of parameter bytes, and reads it
nowhere.

`Params.configure` (OnBytes/Params/Configure.lean) makes the plans and the parameter bytes of a
call's seven chains from the parameter file's lines, the shapes and the digest of the public files.
`Params.entryParams` (OnBytes/Params/Derive.lean) makes the bytes of the entry's chain alone; the
program does not call it, and `Params.configure_entry` (OnBytes/Params/ConfigureLaws.lean) ties it
to `configure`. A bound under a random oracle for a verifier that forms that digest by the oracle
speaks of these bytes at every value of the digest. The whole call's text over a monad forms the
digest by the hash that it is handed (`M.Model.Verify.planned`,
OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean), and `K.Oracle.askedAt` (OnBytes/K/Oracle/SpineAsked.lean
[not in this library]) runs that text at an oracle; nothing is stated of either here. No such bound
for the program stands in OnBytes/: the program forms the digest by BLAKE2b. This file writes
`configure`'s value out as a function of the digest.

Main definitions: `linItems`, `entryItems`, `proofFirstItems`, `madeAt`.
Main theorems.
- `configure_at`: if `configure` returns `made` at some digest, there are six plans, those in
  `made`, such that at every digest c' it returns `madeAt ... c'`: `made` with c' as its digest and
  each of the seven strings spelled from a named plan, c' and a named list of items, which are
  functions of `made`'s sizes, the lines and the shapes. No condition on the digests. `madeAt_self`:
  at the first digest that is `made`.
- `configure_refuses`: if `configure` refuses at one digest, it refuses at every digest.
- `entryParams_of`, `entryParams_spelled`, `entryParams_refuses`: the like for `entryParams`; where
  it refuses, it refuses at every digest with the same name.







What is not claimed. No probability and nothing on soundness. That `configure` refuses at every
digest with the same name is not stated. That `configure` returns a value at any lines is not shown.
The program does not stop at `configure`: `Model.Verify.chainsOf` reads the seven strings back; see
OnBytes/Tie/ChainsAtCfg.lean.

All limits in the heads of the
files named above hold here too. For proofs only; the program does not import this file.

-/
import OnBytes.Tie.EntryAtCfg
import OnBytes.Params.EntrySizedLaws
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false

namespace OnBytes.Tie

/-- What `Params.entryParams` returns at a digest c is spelled from a plan, c and items, and at
every c' it returns the spelling from the same plan and items. -/
theorem entryParams_spelled {l : Params.Lines} {c b : ByteArray}
    (h : Params.entryParams l c = .ok b) :
    ∃ (P : Fmt.Plan) (I : List (String × ByteArray)), b = Fmt.paramsBytes P c I ∧
      ∀ c', Params.entryParams l c' = .ok (Fmt.paramsBytes P c' I) := by
  unfold Params.entryParams at h
  cases hs : Params.entrySized l with
  | error e =>
    rw [hs] at h
    cases h
  | ok y =>
    obtain ⟨x, codes, p⟩ := y
    rw [hs] at h
    refine ⟨p.plan, [("codes", Params.spellCodes codes), ("the link", Params.spellLink x.shape)],
      (Except.ok.inj h).symm, fun c' => ?_⟩
    unfold Params.entryParams
    rw [hs]
    rfl

/-- Where `Params.entryParams` refuses at one digest, it refuses at every digest, with the same
name. -/
theorem entryParams_refuses {l : Params.Lines} {c : ByteArray} {e : String}
    (h : Params.entryParams l c = .error e) : ∀ c', Params.entryParams l c' = .error e := by
  intro c'
  unfold Params.entryParams at h ⊢
  cases hs : Params.entrySized l with
  | error e' =>
    rw [hs] at h
    exact h
  | ok y =>
    rw [hs] at h
    cases h

/-- A step that returned a value, followed by another: the other on that value. -/
theorem exc_step {ε α β : Type} {x : Except ε α} {a : α} (f : α → Except ε β) (h : x = .ok a) :
    (x >>= f) = f a := by
  rw [h]
  rfl

/-- If a test that can refuse is followed by steps that return a value, the test did not refuse, and
the steps returned the value. -/
theorem exc_not {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β}
    {b : β}
    (h : (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) = .ok b) :
    ¬ c ∧ next PUnit.unit = .ok b := by
  split at h
  · cases h
  · rename_i hc
    exact ⟨hc, h⟩

/-- A test that does not refuse, followed by steps: the steps. -/
theorem exc_go {ε β : Type} {c : Prop} [Decidable c] {e : ε} (next : PUnit → Except ε β)
    (hc : ¬ c) :
    (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) =
      next PUnit.unit := by
  rw [if_neg hc]
  rfl

open Params in
/-- The two items of a shared chain, which a key's one-time chain and a proof's first chain hold
too. -/
def linItems (codes : Codes) (S : LinShape) : List (String × ByteArray) :=
  [("codes", spellCodes codes), ("the test on the table", spellLin S)]

open Params in
/-- The seven items of a proof's first chain, as `Params.configure` spells them. -/
def proofFirstItems (l : Lines) (x : Shapes) (z : Sized) : List (String × ByteArray) :=
  linItems z.proof.codes z.proof.batch.shape ++
    [("request's shape", spellReq z.proof.request), ("layout", spellLayout x.layout),
     ("links' identifiers", spellWords x.identifiers),
     ("pending rows", spellWord x.sub.pendingRows),
     ("binding tree", spellBinding ⟨clog2 l.slots, z.set.saltBytes⟩)]

open Params in
/-- The two items of an entry's chain, as `Params.configure` spells them. -/
def entryItems (z : Sized) : List (String × ByteArray) :=
  [("codes", spellCodes z.entryCodes), ("the link", spellLink z.link.shape)]

open Params in
/-- A value of `Params.configure` with c' as its digest and the seven strings of parameter bytes
spelled at c' from six given plans, the entry's plan in the value, and the items that follow from
the value's sizes, the lines and the shapes. -/
def madeAt (l : Lines) (x : Shapes) (made : Configured) (k1 k2 k3 p1 p2 p3 : Planned)
    (c' : ByteArray) : Configured :=
  { made with
    configuration := c'
    keyOneTime := Fmt.paramsBytes k1.plan c' (Plan.oneTimeItems made.sized.key)
    keyShared := Fmt.paramsBytes k2.plan c'
      (linItems made.sized.key.codes made.sized.key.once.shape)
    keySecond := Fmt.paramsBytes k3.plan c' []
    entryLink := Fmt.paramsBytes made.entry.plan c' (entryItems made.sized)
    first := Fmt.paramsBytes p1.plan c' (proofFirstItems l x made.sized)
    shared := Fmt.paramsBytes p2.plan c'
      (linItems made.sized.proof.codes made.sized.proof.batch.shape)
    second := Fmt.paramsBytes p3.plan c' [] }

open Params in
/-- **The planner's value as a function of the digest.** If `Params.configure` returns `made` at a
digest c, then `made` holds three plans for the key's chains and three for the proof's, and at every
digest c' `configure` returns `madeAt` of `made`, these six plans and c'. The proof follows the text
of `configure` step by step, first in the hypothesis, then in the goal. No condition on c or c'. -/
theorem configure_at {l : Lines} {x : Shapes} {c : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x c bits = .ok made) :
    ∃ k1 k2 k3 p1 p2 p3 : Planned, made.key = [k1, k2, k3] ∧ made.proof = [p1, p2, p3] ∧
      ∀ c', configure l x c' bits = .ok (madeAt l x made k1 k2 k3 p1 p2 p3 c') := by
  unfold configure at h
  obtain ⟨z, k1, h⟩ := exc_bind h
  obtain ⟨proof, k2, h⟩ := exc_bind h
  obtain ⟨oneTime, k3, h⟩ := exc_bind h
  obtain ⟨keyShared, k4, h⟩ := exc_bind h
  obtain ⟨keySecond, k5, h⟩ := exc_bind h
  obtain ⟨entry, k6, h⟩ := exc_bind h
  split at h
  · obtain ⟨m1, k7, h⟩ := exc_bind h
    obtain ⟨g1, h⟩ := exc_not h
    obtain ⟨g2, h⟩ := exc_not h
    obtain ⟨g3, h⟩ := exc_not h
    obtain ⟨g4, h⟩ := exc_not h
    obtain ⟨g5, h⟩ := exc_not h
    obtain ⟨g6, h⟩ := exc_not h
    obtain ⟨g7, h⟩ := exc_not h
    cases h
    refine ⟨oneTime, keyShared, keySecond, _, _, _, rfl, rfl, fun c' => ?_⟩
    unfold configure
    refine (exc_step _ k1).trans ?_
    refine (exc_step _ k2).trans ?_
    refine (exc_step _ k3).trans ?_
    refine (exc_step _ k4).trans ?_
    refine (exc_step _ k5).trans ?_
    refine (exc_step _ k6).trans ?_
    refine (exc_step _ k7).trans ?_
    refine (exc_go _ g1).trans ?_
    refine (exc_go _ g2).trans ?_
    refine (exc_go _ g3).trans ?_
    refine (exc_go _ g4).trans ?_
    refine (exc_go _ g5).trans ?_
    refine (exc_go _ g6).trans ?_
    refine (exc_go _ g7).trans ?_
    rfl
  · cases h

open Params in
/-- At the digest at which `made` was returned, `madeAt` is `made`. -/
theorem madeAt_self {l : Lines} {x : Shapes} {c : ByteArray} {bits : Nat} {made : Configured}
    {k1 k2 k3 p1 p2 p3 : Planned} (h : configure l x c bits = .ok made)
    (hall : ∀ c', configure l x c' bits = .ok (madeAt l x made k1 k2 k3 p1 p2 p3 c')) :
    madeAt l x made k1 k2 k3 p1 p2 p3 c = made :=
  Except.ok.inj ((hall c).symm.trans h)

open Params in
/-- `Params.entryParams` written out: where `Params.entrySized` returns sizes, codes and a plan on
the lines, it returns at every digest the bytes spelled from that plan, the digest and the two
items. -/
theorem entryParams_of {l : Lines} {y : LinkSized × Codes × Planned}
    (h : entrySized l = .ok y) (c : ByteArray) :
    entryParams l c = .ok (Fmt.paramsBytes y.2.2.plan c
      [("codes", spellCodes y.2.1), ("the link", spellLink y.1.shape)]) := by
  unfold entryParams
  rw [h]
  rfl

open Params in
/-- If `Params.configure` refuses at one digest, it refuses at every digest. That the name is the
same is not stated. -/
theorem configure_refuses {l : Lines} {x : Shapes} {c : ByteArray} {bits : Nat} {e : String}
    (h : configure l x c bits = .error e) (c' : ByteArray) :
    ∃ e', configure l x c' bits = .error e' := by
  cases h' : configure l x c' bits with
  | error e' => exact ⟨e', rfl⟩
  | ok made' =>
    obtain ⟨_, _, _, _, _, _, -, -, hall⟩ := configure_at h'
    rw [hall c] at h
    cases h

end OnBytes.Tie

#print axioms OnBytes.Tie.entryParams_spelled
#print axioms OnBytes.Tie.configure_at
#print axioms OnBytes.Tie.entryParams_of
#print axioms OnBytes.Tie.configure_refuses
#print axioms OnBytes.Tie.entryParams_refuses
