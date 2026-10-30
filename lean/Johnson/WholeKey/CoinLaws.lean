-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/CoinLaws.lean: LAWS ON THE HONEST SIDE's COINS THAT CAN BE MET, for the scheme with
the whole key published (Johnson/WholeKey/Defs.lean): on a table's salts and on the coins of a
compiled run; each with a member.

General definitions, and two theorems with their proofs which show that the laws can be met. This
file states no goal of the release.

Why. The library's law on an enumeration is "each member of the type is listed once" (Enum.OK,
Iop/Wire.lean). A table's salts are a function on all natural numbers, and the coins of a compiled
run (Coins, OnBytes/Prover/Defs.lean) hold such functions. These types are infinite: no finite
enumeration lists all their members, so Enum.OK is FALSE at every enumeration of them, and a theorem
with that premise would be true and empty. HonestSide's fields sl, coT, coL and coB are enumerations
of these types (the library's committer takes an enumeration of that type too). What is asked
instead is a law on THE FINITELY MANY COORDINATES WITHIN A WINDOW, as an equation of two
distributions. For the encoding's randomness and the three strategies' coins, which are finite types
where a law on them is wanted, Enum.OK serves.

The form of a salt. Where bytes are reached, the typed salt of a leaf begins with a public string
and goes on with secret bits (Run.leafSalt, Run/ParseBS.lean: "the run's value, then the file's
salt"). A bound on guessing a salt may count the free bits alone. For a TABLE the start is a fixed
string, and the law has it as a letter (pre). For a COMPILED RUN the start is laid by the scheme
(dress, Johnson/WholeKey/Defs.lean), from strings that the proof string shows; the coins that are
DRAWN hold the free bits alone, and the law speaks of these.

Main names (namespace OnBytes.WholeKey).
  SaltsLaw sl m pre ℓ   at the first m places the salts are pre followed by ℓ bits, all these bits
      uniform and independent.
  saltsPre, saltsLaw_saltsPre   a member, from an enumeration of a finite type that lists each
      member once.
  RunLaw e …   of the coins that are drawn for a compiled run: the first salt has sFS bits; within
      the window (rounds below nR, trees below nK, leaves below nJ) a leaf has ℓ free bits; the
      string behind the slot's value has ℓr free bits; there are dq sibling digests; all these bits
      uniform and independent; the padding and the slot are fixed.
  coinsPre, runLaw_coinsPre   a member.

Limits. That a compiled run reads its coins within a window alone is not shown here. Nothing is said
on coordinates outside the window. Which numbers fit a given wire is not said. No bound on any
probability is derived.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import Prob.Linear

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## A table's salts -/

/-- The law of a table's salts: at the first m places each salt is the public string pre followed by
ℓ bits, and all these bits are uniform and independent. -/
def SaltsLaw (sl : Enum (ℕ → Bits)) (m : ℕ) (pre : Bits) (ℓ : ℕ) : Prop :=
  (unif (Fin (sl.n + 1))).map (fun a => fun j : Fin m => sl.e a j.val) =
    (unif (Fin m → Fin ℓ → Bool)).map fun u => fun j => pre ++ List.ofFn (u j)

/-- Salts of that form, the free bits running through E; no bits beyond the first m places. -/
def saltsPre (pre : Bits) (m ℓ : ℕ) (E : Enum (Fin m → Fin ℓ → Bool)) : Enum (ℕ → Bits) where
  n := E.n
  e := fun c j => if h : j < m then pre ++ List.ofFn (E.e c ⟨j, h⟩) else []

/-- **The law on a table's salts can be met.** -/
theorem saltsLaw_saltsPre (pre : Bits) (m ℓ : ℕ) (E : Enum (Fin m → Fin ℓ → Bool)) (hE : E.OK) :
    SaltsLaw (saltsPre pre m ℓ E) m pre ℓ := by
  unfold SaltsLaw
  rw [← map_unif_of_bijective hE, PMF.map_comp]
  refine congrArg (fun F => (unif (Fin (E.n + 1))).map F) (funext fun a => funext fun j => ?_)
  show (if h : j.val < m then pre ++ List.ofFn (E.e a ⟨j.val, h⟩) else []) = _
  rw [dif_pos j.isLt]
  rfl

/-! ## The coins of a compiled run -/

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The free bits of a compiled run's coins within a window: those of the first salt; of the leaves'
salts (round, own component?, tree, leaf); of the string behind the slot's value; the sibling
digests. -/
abbrev RunBits (lam nR nK nJ sFS ℓ ℓr dq : ℕ) : Type :=
  (Fin sFS → Bool) × (Fin nR → Bool → Fin nK → Fin nJ → Fin ℓ → Bool) × (Fin ℓr → Bool) ×
    (Fin dq → Dig lam)

/-- What the law speaks of, out of a run's coins: the first salt, the leaves' salts within the
window, the string behind the slot's value, the sibling digests. -/
def windowOf (nR nK nJ : ℕ) (co : Coins lam L) :
    Bits × (Fin nR → Bool → Fin nK → Fin nJ → Bits) × Bits × List (Dig lam) :=
  (co.salt, (fun i b k j => co.leaf i.val b k.val j.val), co.rsalt, co.path)

/-- The same out of the free bits. -/
def windowBits {nR nK nJ sFS ℓ ℓr dq : ℕ} (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) :
    Bits × (Fin nR → Bool → Fin nK → Fin nJ → Bits) × Bits × List (Dig lam) :=
  (List.ofFn u.1, (fun i b k j => List.ofFn (u.2.1 i b k j)), List.ofFn u.2.2.1,
    List.ofFn u.2.2.2)

/-- The law of the coins that are drawn for a compiled run. -/
structure RunLaw (e : Enum (Coins lam L)) (nR nK nJ sFS ℓ ℓr dq : ℕ) (pad : Body L) (slot : ℕ) :
    Prop where
  /-- the body of a leaf at which no position stands is fixed -/
  pad : ∀ a, (e.e a).pad = pad
  /-- the slot is fixed -/
  slot : ∀ a, (e.e a).slot = slot
  /-- all free bits are uniform and independent -/
  law : (unif (Fin (e.n + 1))).map (fun a => windowOf nR nK nJ (e.e a)) =
    (unif (RunBits lam nR nK nJ sFS ℓ ℓr dq)).map windowBits

/-- Coins of that form, the free bits running through E; outside the window a leaf's salt is the
fixed string fill. -/
def coinsPre (nR nK nJ sFS ℓ ℓr dq : ℕ) (pad : Body L) (slot : ℕ) (fill : Bits)
    (E : Enum (RunBits lam nR nK nJ sFS ℓ ℓr dq)) : Enum (Coins lam L) where
  n := E.n
  e := fun c =>
    { salt := List.ofFn (E.e c).1
      leaf := fun i b k j =>
        if h : i < nR ∧ k < nK ∧ j < nJ then
          List.ofFn ((E.e c).2.1 ⟨i, h.1⟩ b ⟨k, h.2.1⟩ ⟨j, h.2.2⟩)
        else fill
      pad := pad
      slot := slot
      path := List.ofFn (E.e c).2.2.2
      rsalt := List.ofFn (E.e c).2.2.1 }

/-- **The law on the coins of a compiled run can be met.** -/
theorem runLaw_coinsPre (nR nK nJ sFS ℓ ℓr dq : ℕ) (pad : Body L) (slot : ℕ) (fill : Bits)
    (E : Enum (RunBits lam nR nK nJ sFS ℓ ℓr dq)) (hE : E.OK) :
    RunLaw (coinsPre nR nK nJ sFS ℓ ℓr dq pad slot fill E) nR nK nJ sFS ℓ ℓr dq pad slot where
  pad := fun _ => rfl
  slot := fun _ => rfl
  law := by
    rw [← map_unif_of_bijective hE, PMF.map_comp]
    refine congrArg (fun F => (unif (Fin (E.n + 1))).map F) (funext fun a => ?_)
    show (List.ofFn (E.e a).1, _, List.ofFn (E.e a).2.2.1, List.ofFn (E.e a).2.2.2) =
      windowBits (E.e a)
    unfold windowBits
    refine Prod.ext rfl (Prod.ext (funext fun i => funext fun b => funext fun k => funext fun j =>
      ?_) rfl)
    exact dif_pos ⟨i.isLt, k.isLt, j.isLt⟩

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.saltsLaw_saltsPre
#print axioms OnBytes.WholeKey.runLaw_coinsPre
