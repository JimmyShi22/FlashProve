-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxWalksGround.lean: all that is owed for the walks (`WalkParts`,
OnBytes/K/Left/LaxWalks.lean), at the family that runs, from the strict reader's equation.

`walkParts_at` (OnBytes/K/Left/LaxWalksAt.lean) has four of the fourteen fields by theorem and takes
the other ten, with `ShapeFacts`, as premises. Here these are paid from
`Fmt.readChainX h S seen b i = some (o, j)`: the reader's yes at every opening
(OnBytes/K/Left/LaxReadAs.lean), the lengths and the depth (LaxLens.lean), the stored shapes
(LaxShape.lean), the run value (Asm.lean), and the forms and roots (LaxForms.lean), at
`Fm := FmOf D`, `Rt := RtOf o`.

Main names:
  `hOfG_oracle`: the reader's hash of these files is the format's hash over the format's own oracle
    (`ho_oBits`, OnBytes/K/Left/LaxChain.lean, read at `hOfG oBits`).
  `rand_some`: a description within the typing's limits has its random bytes in the file.
  `shapeFacts_of_read`: `ShapeFacts D o`.
  `walkParts_of_read`: `WalkParts` for any description D within the limits.
  `stored_same_at`: at `entryXD G c`, from `Tie.withinX`: every stored table has the depth `D.a` and
    the plan's length of salts.
  `walkParts_ground`: `WalkParts` at `entryXD G c`, from the equation at the format's own oracle.

Hypotheses of the last: `PQ.ok (entryXD G c).base`; `Tie.withinX` of the program's description at an
empty statement; the digest's 32 bytes; the reader's equation; each stored table's root stands in
the statement's item 0 or 1 (the last clause of `ground`, OnBytes/K/Left/LaxGround.lean).

Limits: values alone. Nothing on soundness; no probability. That some file meets the equation is not
shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxWalksAt
import OnBytes.K.Left.LaxForms
import OnBytes.K.Left.LaxShape
import OnBytes.TypedOracleCompiler.Slice.TieYes
import OnBytes.K.Left.LaxChain

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.RowsG (hOfG)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Tie (EntryGround linkAtCfg)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- The reader's hash of these files is the format's hash over the format's own oracle. -/
theorem hOfG_oracle : hOfG oBits = _root_.Fmt.HO _root_.Fmt.oracle := ho_oBits

/-- A description within the typing's limits has its random bytes in the file. -/
theorem rand_some {S₀ : _root_.Fmt.Spec} (hok : TypedOracleCompiler.Run.PQ.ok S₀ = true) :
    S₀.rand ≠ .none := by
  intro h
  simp only [TypedOracleCompiler.Run.PQ.ok, Bool.and_eq_true, h] at hok
  exact absurd hok.2 (by simp)

section
variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (d₁ : Sd1 lg s)
  (hD : D.base.cfg.size = 32) (sh : OnBytes.Params.IndexShape)
  (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
  (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
  {st : ByteArray} {seen : _root_.Fmt.Seen} {b : ByteArray} {i : ℕ} {o : _root_.Fmt.ChainOut}
  {j : ℕ} (e : _root_.Fmt.readChainX (m := Id) (hOfG oBits) (specOf D st) seen b i = some (o, j))

include hok hsame e in
/-- What the laws at the leaves ask. -/
theorem shapeFacts_of_read : ShapeFacts D o where
  ownTree := own_tree D hok e
  stoTree := fun op hop =>
    (sto_facts e (opens_own (S₀ := D.base) hok) hsame rfl op hop).2.1
  stoWidth := fun op hop =>
    (sto_facts e (opens_own (S₀ := D.base) hok) hsame rfl op hop).2.2.2.1
  stoDeep := fun op hop =>
    (sto_facts e (opens_own (S₀ := D.base) hok) hsame rfl op hop).2.2.2.2
  run32 := fun run hrun => by
    obtain ⟨run', h1, h2⟩ := run_of_read (size_hOfG oBits) e (rand_some (S₀ := D.base) hok)
    rw [hrun] at h1
    obtain rfl := Option.some.inj h1
    exact h2
  salt8 := salt_small (base_ok hok)

include hok hsame e in
/-- All that is owed for the walks, from the reader's equation. r0, r1: the two roots that the
statement's items hold. -/
theorem walkParts_of_read (r0 r1 : ByteArray)
    (hit : ∀ t ∈ D.stored.flatten,
      _root_.Fmt.itemRoot st t.item = some (if t.item == 1 then r1 else r0)) :
    WalkParts D d₁ (EntryRunTop.famOf D hD d₁ sh) (bytesToDig r0) (bytesToDig r1) o (hOfG oBits)
      (FmOf D) (RtOf o) :=
  walkParts_at D d₁ hD sh hok (shapeFacts_of_read D hok hsame e)
    (fun run hrun op hop => by
      obtain ⟨-, -, -, -, -, R⟩ := readAs_own e (opens_own (S₀ := D.base) hok) hrun op hop
      exact R)
    (fun op hop => by
      obtain ⟨-, -, -, R⟩ := readAs_sto e (opens_own (S₀ := D.base) hok) op hop
      exact R)
    (fun op hop sl hsl => by
      by_cases hf : op.sh.stored = true
      · exact (lens_sto_at e (opens_own (S₀ := D.base) hok) hsame rfl op
          (List.mem_filter.2 ⟨hop, hf⟩)).2.2 sl hsl
      · exact (lens_own e op (List.mem_filter.2 ⟨hop, by simp [hf]⟩)).2 sl hsl)
    (fun op hop => (lens_sto_at e (opens_own (S₀ := D.base) hok) hsame rfl op hop).2.1)
    (forms_on D) (rts_on D hok e) (own_form D hok e) (own_root D hok e)
    (fun op hop => (lens_sto_at e (opens_own (S₀ := D.base) hok) hsame rfl op hop).1)
    (sto_root D hok e r0 r1 hit)

end

/-- At the entry's description, within the limits: every stored table has the depth `D.a` and the
plan's length of salts. -/
theorem stored_same_at (G : EntryGround) (c : ByteArray)
    (hw : OnBytes.Tie.withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true) :
    ∀ t ∈ (entryXD G c).stored.flatten,
      t.sh.a = (entryXD G c).a ∧ t.salt = (entryXD G c).base.plan.salt :=
  stored_same (withinT_spec _ (fun _ _ => ByteArray.empty) (withinT_of_withinX _ hw)).1

/-- All that is owed for the walks, at the entry's description, from the strict reader's
equation at the format's own oracle. -/
theorem walkParts_ground {lg s : ℕ} [DecidableEq (Sd1 lg s)] (G : EntryGround) (c : ByteArray)
    (d₁ : Sd1 lg s) (hD : (entryXD G c).base.cfg.size = 32) (sh : OnBytes.Params.IndexShape)
    (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (hw : OnBytes.Tie.withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)
    {st : ByteArray} {seen : _root_.Fmt.Seen} {b : ByteArray} {i : ℕ} {o : _root_.Fmt.ChainOut}
    {j : ℕ}
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle)
      (TypedOracleCompiler.Run.PQ.withStatement (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) st)
      seen b i = some (o, j))
    (r0 r1 : ByteArray)
    (hit : ∀ t ∈ (entryXD G c).stored.flatten,
      _root_.Fmt.itemRoot st t.item = some (if t.item == 1 then r1 else r0)) :
    WalkParts (entryXD G c) d₁ (EntryRunTop.famOf (entryXD G c) hD d₁ sh) (bytesToDig r0)
      (bytesToDig r1) o (hOfG oBits) (FmOf (entryXD G c)) (RtOf o) :=
  walkParts_of_read (entryXD G c) d₁ hD sh hok (stored_same_at G c hw) (st := st)
    (by rw [hOfG_oracle]; exact e) r0 r1 hit

end OnBytes.K.Left
