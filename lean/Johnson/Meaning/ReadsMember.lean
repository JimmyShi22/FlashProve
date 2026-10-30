-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsMember.lean: the premises of Johnson/Meaning/ReadsLaw.lean's and
Johnson/Meaning/ReadsCells.lean's
theorems can be met together, at any small cells.

`readsAll_of_relIn` and `readsAll_cells` take the relation in front of the draw of the smallness
test's matrix and two premises on the letters. A theorem whose premises cannot hold together says
nothing. Here a member is built: for any small integers a, any record, and any tables with the
shapes of the record's that do not overlap, there are letters over the record's sizes, and entries
of virtual rows, at which all three hold, the committed symbols being the packing of a.

Main names (namespace `Meaning.Reads`).
  `madeLetters`: the letters: the weights are the tables'; the symbols are the packing of
      a; the vector of reads is what the law of the reads asks (`madeRead`,
      Johnson/Meaning/PlanesLaw.lean).
  `dec_some`: what the library's numbering of reads says where it names a table's segment.
  `made_relIn`: the relation in front of the draw holds at these letters.
  `reads_member`: the three premises together, with entries of virtual rows.
  `mats_bound`: some number lies above the matrix of every table of a list.

Limits. A made member: an honest prover's messages in the letters' terms, no file, no run, nothing
committed. Nothing on soundness.
-/
import Johnson.Meaning.ReadsCells
import Johnson.Meaning.PlanesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open Finset
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open Meaning.Planes

variable {K : Type} [CommRing K]

/-- Letters made from tables funs and given integers a (matrix, column, row), over the sizes of a
record tl. -/
noncomputable def madeLetters (ρ : Reading K) (tl : HTailF2) (funs : Array HFun)
    (a : ℕ → ℕ → ℕ → ℤ) :
    TLetters K (Tie.Pv.Tail.sizeOf tl) where
  X := Unit
  M := Unit
  E := ⟨Unit, Empty, Unit, fun _ e => e.elim⟩
  W := Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size
  phi := fun _ n j => ρ.val ((funs.getD n default).phi.getD j zeroE)
  sym := fun _ μ i' c =>
    ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ c i) i' : ℤ) : K)
  u3 := fun _ pos => madeRead ρ tl.mats funs (fun μ r c => ((a μ c r : ℤ) : K)) pos
  dig := id
  ride := fun _ _ _ => True

/-- What the numbering of reads says where it names a table's segment. -/
theorem dec_some {t : TSize} {μ r n sg : ℕ} {T : Tab} (h : t.dec μ r = some (n, T, sg)) :
    t.tabs[n]? = some T ∧ T.mat = μ ∧ sg < t.m μ / T.len := by
  unfold TSize.dec at h
  split at h
  · rename_i T' hT
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hT, hc.1, hc.2⟩
    · cases h
  · cases h

/-- **The relation in front of the draw holds at the made letters**, if a is small and no entry of
the vector of reads lies in two tables. -/
theorem made_relIn (ρ : Reading K) (tl : HTailF2) (funs : Array HFun)
    (hsh : (Tie.Pv.Tail.sizeOf tl).tabs =
      funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
    (a : ℕ → ℕ → ℕ → ℤ) (small : ∀ μ c i, |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ))
    (apart : ∀ f ∈ funs.toList, ∀ f' ∈ funs.toList, ∀ col < entriesOf tl.mats f,
      ∀ col' < entriesOf tl.mats f', f.start + col = f'.start + col' → f = f') :
    relIn (madeLetters ρ tl funs a).letters () () := by
  refine relIn_of_cells (madeLetters ρ tl funs a).letters
    (a := fun μ c i => a μ c i) ⟨fun μ c i => small _ _ _, fun μ c i' => rfl, fun μ c r => ?_⟩
  show tabOf (Tie.Pv.Tail.sizeOf tl) ((madeLetters ρ tl funs a).u3 ()) μ r c =
    ∑ i : Fin (tl.mats.getD μ {}).m,
      wOf (Tie.Pv.Tail.sizeOf tl) ((madeLetters ρ tl funs a).phi ()) μ r i * ((a μ c i : ℤ) : K)
  cases hd : (Tie.Pv.Tail.sizeOf tl).dec μ r with
  | none =>
    unfold tabOf wOf
    rw [hd]
    simp
  | some z =>
    obtain ⟨n, T, sg⟩ := z
    obtain ⟨hT, hm, hs⟩ := dec_some hd
    have hT' := hT
    rw [hsh, List.getElem?_map] at hT'
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hT'
    have hm' : f.mat = (μ : ℕ) := hm
    have hs' : sg < (tl.mats.getD f.mat {}).m / f.len := by rw [hm']; exact hs
    have hmem : f ∈ funs.toList := List.mem_of_getElem? hf
    have hck : (c : ℕ) < (tl.mats.getD f.mat {}).k := by rw [hm']; exact c.2
    have hlen0 : 0 < f.len := by
      rcases Nat.eq_zero_or_pos f.len with h | h
      · rw [h, Nat.div_zero] at hs'
        exact absurd hs' (Nat.not_lt_zero _)
      · exact h
    have hlen : sg * f.len + f.len ≤ (tl.mats.getD μ {}).m := by
      have h5 := (Nat.le_div_iff_mul_le hlen0).1 (Nat.succ_le_of_lt hs')
      rw [Nat.succ_mul, hm'] at h5
      exact h5
    have hcol : (c : ℕ) * ((tl.mats.getD f.mat {}).m / f.len) + sg < entriesOf tl.mats f := by
      unfold entriesOf stretches
      calc (c : ℕ) * ((tl.mats.getD f.mat {}).m / f.len) + sg
          < (c : ℕ) * ((tl.mats.getD f.mat {}).m / f.len) + (tl.mats.getD f.mat {}).m / f.len :=
            Nat.add_lt_add_left hs' _
        _ = ((c : ℕ) + 1) * ((tl.mats.getD f.mat {}).m / f.len) := by rw [Nat.succ_mul]
        _ ≤ (tl.mats.getD f.mat {}).k * ((tl.mats.getD f.mat {}).m / f.len) :=
            Nat.mul_le_mul_right _ hck
    have eT : tabOf (Tie.Pv.Tail.sizeOf tl) ((madeLetters ρ tl funs a).u3 ()) μ r c =
        madeRead ρ tl.mats funs (fun μ r c => ((a μ c r : ℤ) : K))
          (f.start + ((c : ℕ) * ((tl.mats.getD f.mat {}).m / f.len) + sg)) := by
      unfold tabOf
      rw [hd]
      show madeRead ρ tl.mats funs _
        (f.start + (c : ℕ) * ((tl.mats.getD μ {}).m / f.len) + sg) = _
      rw [hm', Nat.add_assoc]
    have eW : ∀ i : ℕ, wOf (Tie.Pv.Tail.sizeOf tl) ((madeLetters ρ tl funs a).phi ()) μ r i =
        if sg * f.len ≤ i ∧ i < sg * f.len + f.len then
          ρ.val (f.phi.getD (i - sg * f.len) zeroE) else 0 := by
      intro i
      unfold wOf
      rw [hd]
      have e : funs.getD n default = f := by
        rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hf]
        rfl
      show (if sg * f.len ≤ i ∧ i < sg * f.len + f.len then
        ρ.val ((funs.getD n default).phi.getD (i - sg * f.len) zeroE) else 0) = _
      rw [e]
    rw [eT, madeRead_at apart _ hmem hcol]
    unfold readOf stretches
    have hq : 0 < (tl.mats.getD f.mat {}).m / f.len := Nat.lt_of_le_of_lt (Nat.zero_le _) hs'
    rw [Nat.mul_comm (c : ℕ), Nat.mul_add_mod, Nat.mod_eq_of_lt hs', Nat.mul_add_div hq,
      Nat.div_eq_of_lt hs', Nat.add_zero]
    show ∑ row ∈ range f.len, ρ.val (f.phi.getD row zeroE) *
      ((a f.mat c (sg * f.len + row) : ℤ) : K) = _
    rw [hm']
    have e5 := sum_stretch (tl.mats.getD μ {}).m (sg * f.len) f.len hlen
      (fun j => ρ.val (f.phi.getD j zeroE)) (fun i => ((a μ c i : ℤ) : K))
    rw [← e5]
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [eW]

/-- **The three premises of `readsAll_of_relIn` hold together**, at the made letters and made
entries.
-/
theorem reads_member (ρ : Reading K) (tl : HTailF2) (funs : Array HFun)
    (hsh : (Tie.Pv.Tail.sizeOf tl).tabs =
      funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
    (a : ℕ → ℕ → ℕ → ℤ) (small : ∀ μ c i, |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ))
    (apart : ∀ f ∈ funs.toList, ∀ f' ∈ funs.toList, ∀ col < entriesOf tl.mats f,
      ∀ col' < entriesOf tl.mats f', f.start + col = f'.start + col' → f = f') (iU3 K3 : ℕ) :
    relIn (madeLetters ρ tl funs a).letters () () ∧
      (∀ n Fn, funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
        (madeLetters ρ tl funs a).phi () n j = ρ.val (Fn.phi.getD j zeroE)) ∧
      ∃ entry : ℕ → ℕ → ℕ → K,
        ∀ pos, (madeLetters ρ tl funs a).u3 () pos = u3Val entry iU3 K3 pos := by
  refine ⟨made_relIn ρ tl funs hsh a small apart, fun n Fn hn j _ => ?_,
    fun _ r x => madeRead ρ tl.mats funs (fun μ r c => ((a μ c r : ℤ) : K)) (r * K3 + x),
    fun pos => ?_⟩
  · have e : funs.getD n default = Fn := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hn]
      rfl
    show ρ.val ((funs.getD n default).phi.getD j zeroE) = _
    rw [e]
  · unfold u3Val
    show _ = madeRead ρ tl.mats funs _ (pos / K3 * K3 + pos % K3)
    rw [Nat.div_add_mod']
    rfl

/-- Some number lies above the matrix of every table of a list. -/
theorem mats_bound : ∀ l : List HFun, ∃ N, ∀ f ∈ l, f.mat < N
  | [] => ⟨0, fun _ h => by cases h⟩
  | x :: l => by
    obtain ⟨N, hN⟩ := mats_bound l
    refine ⟨max N (x.mat + 1), fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    · exact lt_of_lt_of_le (hN f hf) (le_max_left _ _)

#print axioms made_relIn
#print axioms reads_member

end Meaning.Reads
