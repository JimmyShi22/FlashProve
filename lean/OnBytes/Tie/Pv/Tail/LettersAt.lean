-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/LettersAt.lean: the letters of the typed smallness test
(Cb/Pv/Tail/Tables.lean) at the verifier's own record of a smallness test and at a lay of the
committed entries (OnBytes/Tie/Pv/Led/LedJoint.lean).

A lay gives every committed entry an address: a cell (array, row, column) or an entry of the mask
row. Here the entries are cut in two by type. The early ones are the cells of the arrays that the
verifier tests as fixed before it draws the matrix (fixedBeforeTheMatrixF, OnBytes/Model/Tail.lean):
the symbol arrays of all matrices and the sub-proof's vectors. All others are left out: the digits
and the planes of counts, which are sent behind the draw; and also the mask row, which is sent
before it but is not in the test's list. The messages of the typed block are the early entries
alone.

Main names:
  `early tl a`: the address is a cell of a symbol array or of one of the vectors.
  `JE`, `JL`: the early entries and the others. `glue`: both together. `cellAt_glue`: an early cell
    does not hang on the other entries.
  `symAt`: the symbol (matrix μ, row i' of symbols, column c) is the cell (gtTree μ, i', c).
  `u3At`: entry pos of the vector of reads is the cell (iU3, pos / K3, pos % K3).
  `phiAt`: weight j of table number n is the reading of the record's own weight.
  `thetaAt`: the letters. `knowAt_at`: the block's soundness property at them.
  `tabAt_some`: what the record's `tabAt` says where it names an entry.
  `lateTest`, `early_zz`, `early_bz`: a test on the record's public numbers: the digits' and the
    planes' arrays are not in that list; where it is true their cells are not early.
  `reads_at`: before the round there is one integer matrix for each committed matrix, small, whose
    packing is the committed symbols, such that for every table Fn of the record's list and all c,
    sg, pos with `tl.tabAt Fn c sg = some pos`, entry pos of the vector of reads is the sum over j
    below Fn.len of the reading of Fn.phi[j] times cell (sg * Fn.len + j) of column c of matrix
    Fn.mat.

Limits: iU3 and K3 are letters: that iU3 is the array of the reads and K3 the number of its columns
is not said. That the verifier's test of the order passes is not used and not said: `early` takes
the test's list of arrays, no more. The explicit statement, the implicit instance, the witness
behind and what rides stay letters. Nothing on an honest prover.
Which record is meant: in a plan's own record the list of tables and the list of first columns are
still empty (a run fills them): there `sizeOf tl` has no table, and what is said here says nothing
of a read. The statements are meant at a record in which the tables' shapes and the first columns
are laid.

-/
import OnBytes.Model.HideLaws
import OnBytes.Tie.Pv.Led.LedLay
import OnBytes.Tie.Pv.Tail.SizeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Road.Rows Cb.Pv.Tail Iop

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (tl : HTailF2)

/-- The address is a cell of an array that the verifier tests as fixed before the matrix is drawn:
a symbol array of a matrix, or one of the vectors. -/
def early (a : Addr) : Bool :=
  match a with
  | .cell t _ _ => decide (t ∈ tl.gtTree.toList) || decide (some t ∈ tl.ix.U.toList.take 4)
  | .mask _ => false

/-- The digits' and the planes' arrays are not among the arrays whose cells are early. -/
def lateTest : Bool :=
  !(decide (tl.ix.ZZ ∈ tl.gtTree.toList) || decide (some tl.ix.ZZ ∈ tl.ix.U.toList.take 4)) &&
    !(decide (tl.ix.BZ ∈ tl.gtTree.toList) || decide (some tl.ix.BZ ∈ tl.ix.U.toList.take 4))

theorem early_zz (h : lateTest tl = true) (r c : ℕ) : early tl (.cell tl.ix.ZZ r c) = false := by
  unfold lateTest at h
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
  exact h.1

theorem early_bz (h : lateTest tl = true) (r c : ℕ) : early tl (.cell tl.ix.BZ r c) = false := by
  unfold lateTest at h
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at h
  exact h.2

/-- The early entries; the others. -/
abbrev JE : Type := {j : J // early tl (Y.addr j) = true}
abbrev JL : Type := {j : J // early tl (Y.addr j) = false}

/-- The early entries and the others together. -/
def glue (m : JE Y tl → K) (u : JL Y tl → K) : J → K := fun j =>
  if h : early tl (Y.addr j) = true then m ⟨j, h⟩ else u ⟨j, Bool.eq_false_iff.2 h⟩

/-- An early cell does not hang on the other entries. -/
theorem cellAt_glue (m : JE Y tl → K) (u u' : JL Y tl → K) (t r c : ℕ)
    (ht : early tl (.cell t r c) = true) :
    Y.cellAt (glue Y tl m u) t r c = Y.cellAt (glue Y tl m u') t r c := by
  unfold Lay.cellAt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : Y.addr i = .cell t r c
  · have he : early tl (Y.addr i) = true := by rw [h]; exact ht
    rw [if_pos h, if_pos h]
    unfold glue
    rw [dif_pos he, dif_pos he]
  · rw [if_neg h, if_neg h]

/-- The symbol (matrix, row of symbols, column). -/
def symAt (m : JE Y tl → K) (μ i' c : ℕ) : K :=
  Y.cellAt (glue Y tl m fun _ => 0) (tl.gtTree.getD μ 0) i' c

/-- An entry of the vector of reads. -/
def u3At (iU3 K3 : ℕ) (m : JE Y tl → K) (pos : ℕ) : K :=
  Y.cellAt (glue Y tl m fun _ => 0) iU3 (pos / K3) (pos % K3)

/-- A weight of a table. -/
def phiAt (n j : ℕ) : K := ρ.val ((tl.funs.getD n default).phi.getD j zeroE)

/-- The letters of the typed smallness test at the record and the lay. -/
def thetaAt (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop) :
    TLetters K (sizeOf tl) where
  X := X
  M := JE Y tl → K
  E := Ex
  W := Dig K (sizeOf tl).size × W₀
  phi := fun _ => phiAt ρ tl
  sym := symAt Y tl
  u3 := u3At Y tl iU3 K3
  dig := Prod.fst
  ride := ride

section
variable (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec) (W₀ : Type)
  (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop)

local notation "Th" => thetaAt ρ Y tl iU3 K3 X Ex W₀ ride

/-- The block's soundness property at these letters. -/
theorem knowAt_at :
    TWhole.KnowAt (R (Th).letters) (A (Th).letters) (B (Th).letters) (fun _ _ _ wp => wp)
      (eps (Th).letters) :=
  knowAt_tables (Th) (sizeOf_ok tl)

end

/-- What `tabAt` says where it names an entry. -/
theorem tabAt_some {Fn : HFun} {c sg pos : ℕ} (h : tl.tabAt Fn c sg = some pos) :
    Fn.mat < tl.NM ∧ c < (tl.mats.getD Fn.mat {}).k ∧
      sg < (tl.mats.getD Fn.mat {}).m / Fn.len ∧
      pos = Fn.start + c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg := by
  unfold HTailF2.tabAt at h
  split at h
  · rename_i h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    dsimp only at h
    split at h
    · rename_i h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨h1.1, h2.1, h2.2, (Option.some.inj h).symm⟩
    · cases h
  · cases h

/-- Before the round, in the words of the record's own tables. -/
theorem reads_at (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop) {x : X}
    {msg : JE Y tl → K}
    (h : relIn (thetaAt ρ Y tl iU3 K3 X Ex W₀ ride).letters x msg) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          symAt Y tl msg μ i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              K)) ∧
      (∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
        u3At Y tl iU3 K3 msg pos =
          ∑ j ∈ Finset.range Fn.len,
            ρ.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : K)) := by
  obtain ⟨b, h1, h2, h3⟩ := reads_of_relIn (thetaAt ρ Y tl iU3 K3 X Ex W₀ ride) h
  refine ⟨fun μ i c => b μ c i, fun μ hμ c hc i hi => h1 μ hμ c hc i hi,
    fun μ hμ c hc i' hi' => h2 μ hμ c hc i' hi', fun n Fn hn c sg pos hp => ?_⟩
  obtain ⟨g1, g2, g3, rfl⟩ := tabAt_some tl hp
  have hT : (sizeOf tl).tabs[n]? = some ⟨Fn.mat, Fn.len, Fn.start⟩ := by
    show (tl.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))[n]? = _
    rw [List.getElem?_map, Array.getElem?_toList, hn]
    rfl
  have hφ : ∀ j, phiAt ρ tl n j = ρ.val (Fn.phi.getD j zeroE) := by
    intro j
    unfold phiAt
    have e : tl.funs.getD n default = Fn := by
      rw [Array.getD_eq_getD_getElem?, hn]
      rfl
    rw [e]
  have h4 := h3 n ⟨Fn.mat, Fn.len, Fn.start⟩ hT g1 c g2 sg g3
  refine h4.trans (Finset.sum_congr rfl fun j _ => ?_)
  show phiAt ρ tl n j * _ = _
  rw [hφ j]

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.early_zz
#print axioms OnBytes.Tie.Pv.Tail.cellAt_glue
#print axioms OnBytes.Tie.Pv.Tail.knowAt_at
#print axioms OnBytes.Tie.Pv.Tail.reads_at
