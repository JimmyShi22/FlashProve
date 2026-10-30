-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/HoldsAt.lean: what the relation before the smallness test's round gives, said in
the world that the committed entries give at a state of the verifier (`portWorld`,
OnBytes/Tie/Pv/Led/LedPort.lean).

OnBytes/Tie/Pv/Tail/LettersAt.lean has the statement at the early entries and at cells of the lay.
Here all committed entries m are given, the messages of the typed block are their early part, and
an entry of the vector of reads is written as the verifier's claims write it: an entry of a virtual
row.

Main names:
  `earlyOf`, `otherOf`, `glue_of`: the early part of all entries, the other part; both together.
  `u3At_of`, `symAt_of`: at the early part, an entry of the vector of reads and a symbol are the
    cells of m.
  `holds_at`: before the round there is one integer matrix for each committed matrix, small, whose
    packing is the committed symbols, such that for every table Fn of the record's list and all c,
    sg, pos with `tl.tabAt Fn c sg = some pos`:
      (portWorld ρ Y F m).entry iU3 (pos / K3) (pos % K3) =
        the sum over j below Fn.len of ρ.val Fn.phi[j] times cell (sg * Fn.len + j) of column c.

Limits: premises of `holds_at`: the cells of the array iU3 and of the symbol arrays are early; iU3
has one row with the weight 1 (`RowsBelow`, `UnitRow`: OnBytes/Tie/Pv/Tail/EndPort.lean,
EndRaw.lean); every place that a table names lies below K3. None is shown here.
Which record is meant: in a plan's own record the list of tables and the list of first columns are
still empty (a run fills them): there `sizeOf tl` has no table, and what is said here says nothing
of a read. The statements are meant at a record in which the tables' shapes and the first columns
are laid.

-/
import OnBytes.Tie.Pv.Tail.EndPortUnit
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Road.Rows Cb.Pv.Tail Iop

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (tl : HTailF2)

/-- The early part of all entries; the other part. -/
def earlyOf (m : J → K) : JE Y tl → K := fun j => m j.1
def otherOf (m : J → K) : JL Y tl → K := fun j => m j.1

omit [Field K] [Fintype J] in
theorem glue_of (m : J → K) : glue Y tl (earlyOf Y tl m) (otherOf Y tl m) = m := by
  funext j
  unfold glue
  split <;> rfl

theorem cellAt_of (m : J → K) (t r c : ℕ) (he : early tl (.cell t r c) = true) :
    Y.cellAt (glue Y tl (earlyOf Y tl m) fun _ => 0) t r c = Y.cellAt m t r c := by
  rw [cellAt_glue Y tl _ (fun _ => 0) (otherOf Y tl m) t r c he, glue_of]

theorem u3At_of (iU3 K3 : ℕ) (m : J → K) (pos : ℕ)
    (he : ∀ r c, early tl (.cell iU3 r c) = true) :
    u3At Y tl iU3 K3 (earlyOf Y tl m) pos = Y.cellAt m iU3 (pos / K3) (pos % K3) :=
  cellAt_of Y tl m _ _ _ (he _ _)

theorem symAt_of (m : J → K) (μ i' c : ℕ)
    (he : early tl (.cell (tl.gtTree.getD μ 0) i' c) = true) :
    symAt Y tl (earlyOf Y tl m) μ i' c = Y.cellAt m (tl.gtTree.getD μ 0) i' c :=
  cellAt_of Y tl m _ _ _ he

/-- Before the round, in the world of the committed entries. -/
theorem holds_at (F : Fork) (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop) {x : X} (m : J → K)
    (heU : ∀ r c, early tl (.cell iU3 r c) = true)
    (heS : ∀ μ i' c, μ < tl.NM → early tl (.cell (tl.gtTree.getD μ 0) i' c) = true)
    (hR : RowsBelow Y F iU3) (hU : UnitRow F iU3)
    (hpos : ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < K3)
    (h : relIn (thetaAt ρ Y tl iU3 K3 X Ex W₀ ride).letters x (earlyOf Y tl m)) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Y.cellAt m (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              K)) ∧
      (∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
        (portWorld ρ Y F m).entry iU3 (pos / K3) (pos % K3) =
          ∑ j ∈ Finset.range Fn.len,
            ρ.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : K)) := by
  obtain ⟨a, h1, h2, h3⟩ := reads_at ρ Y tl iU3 K3 X Ex W₀ ride h
  refine ⟨a, h1, fun μ hμ c hc i' hi' => ?_, fun n Fn hn c sg pos hp => ?_⟩
  · rw [← symAt_of Y tl m μ i' c (heS μ i' c hμ)]
    exact h2 μ hμ c hc i' hi'
  · rw [portWorld_unitAt ρ Y F m iU3 hR hU K3 pos (hpos n Fn hn c sg pos hp),
      ← u3At_of Y tl iU3 K3 m pos heU]
    exact h3 n Fn hn c sg pos hp

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.holds_at
