-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Join.lean: THE JOIN FROM THE TABLES, once for all kinds: where each part of a
declared read has its table in the smallness test's list, with the declared weights, the read is
joined (Joined, Reads/DeclRow.lean). ALL OF THIS FILE IS A TOOL: for all sizes, lists and
declarations; it names no description.

WHAT A KIND SHOWS, of its own declaration alone:
  PartsLaid t phi val d: for each table to which d unfolds (ReadDecl.tabs: one for each part) there
    is a number n at which the list has a table with these three numbers (matrix, run's length,
    first entry), and whose weights below the run's length are the declared ones. It says nothing
    of the other tables of the list, of their order, or of n. The vector's number is dropped: t.tabs
    has none. At the row's sizes (sizeU3, Reads/Stated.lean) the list holds the third vector's
    tables alone, so nothing follows; at sizes with all tables one of the first vector can answer.
  PartsFit t d: the parts lie in the record: mat + parts is at most the number of matrices; and each
    part has the rows and the columns of the first.
  ReadDecl.Whole (Reads/Decl.lean): the run is not empty, count is room, the make fits.
WHAT FOLLOWS:
  joined_of_parts: PartsLaid, PartsFit and Whole give Joined.
  parts_of_tables: the equation on a whole link's list (TablesAre) gives PartsLaid for each of its
    declarations. joined_of_tables: the two together.
STEPS: split3, split_block: arithmetic. cells_fit: where the make fits, all four makes give one
  address: row (i mod (m / len)) len + j of column (i / (m / len)) mod k of part i / (m / len) / k.
  same_of_parts: SameIndex at one entry. at_map: a list's item under a map.
split_block is block_split of Johnson/Road/HeadReads.lean, with its proof, said again here so that
a tool for all kinds does not import the output head's files.

Without "mat + parts is at most the number of matrices" it is false: a record that counts no matrix
meets all else, and the join asks a matrix inside the record (join_tooth_record,
Reads/DeclTeeth.lean [not in this library]). Whether each other premise is needed is not shown. Not
said: that any list
is as declared.

-/
import Johnson.Desc.Reads.DeclRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail
open OnBytes (E)

variable {K : Type}

/-- **Part by part, the declared read's tables are laid**, with the declared weights. -/
def PartsLaid (t : TSize) (phi : ℕ → ℕ → K) (val : E → K) (d : ReadDecl E) : Prop :=
  ∀ x ∈ d.tabs (t.m d.mat) (t.k d.mat),
    ∃ n, t.tabs[n]? = some x.tab ∧ ∀ j, j < d.len → phi n j = val (d.w j)

/-- The parts lie in the record, and have the rows and the columns of the first. -/
def PartsFit (t : TSize) (d : ReadDecl E) : Prop :=
  d.mat + d.parts ≤ t.NM ∧
    ∀ q, q < d.parts → t.m (d.mat + q) = t.m d.mat ∧ t.k (d.mat + q) = t.k d.mat

/-- A number i in three digits: i mod R, then (i / R) mod k, then i / R / k. -/
theorem split3 (i R k : ℕ) : i / R / k * (k * R) + i / R % k * R + i % R = i := by
  have e1 := Nat.div_add_mod (i / R) k
  have e2 := Nat.div_add_mod i R
  calc i / R / k * (k * R) + i / R % k * R + i % R
      = R * (k * (i / R / k) + i / R % k) + i % R := by ring
    _ = R * (i / R) + i % R := by rw [e1]
    _ = i := e2

/-- The feature e S + r, r < S, where a column holds n S features: its column is that of block e
among blocks of which a column holds n, and its place in the column is (e mod n) S + r. -/
theorem split_block {S n e r : ℕ} (hr : r < S) :
    (e * S + r) / (n * S) = e / n ∧ (e * S + r) % (n * S) = e % n * S + r := by
  have hS : 0 < S := by omega
  have d1 : (e * S + r) / S = e := by
    rw [Nat.mul_comm, Nat.mul_add_div hS, Nat.div_eq_of_lt hr, Nat.add_zero]
  have d2 : (e * S + r) % S = r := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  constructor
  · rw [Nat.mul_comm n S, ← Nat.div_div_eq_div_mul, d1]
  · rw [Nat.mul_comm n S, Nat.mod_mul, d1, d2]
    ring

/-- **Where the make fits, all four makes give one address.** -/
theorem cells_fit {F : Type} (d : ReadDecl F) {m k i j : ℕ} (hL : 0 < d.len)
    (hfit : d.make.Fits d.len m) (hj : j < d.len) :
    d.cells m k i j =
      (d.mat + i / (m / d.len) / k, i / (m / d.len) % k, i % (m / d.len) * d.len + j) := by
  obtain ⟨name, mat, parts, make, len, count, start, w⟩ := d
  have hL' : 0 < len := hL
  have hj' : j < len := hj
  cases make with
  | short => rfl
  | part => rfl
  | column =>
    have h : len = m := hfit
    subst h
    have h1 : len / len = 1 := Nat.div_self hL'
    show (mat + i / k, i % k, j) =
      (mat + i / (len / len) / k, i / (len / len) % k, i % (len / len) * len + j)
    rw [h1, Nat.div_one, Nat.mod_one, Nat.zero_mul, Nat.zero_add]
  | long block =>
    obtain ⟨h1, h2⟩ : block * (len / block) = len ∧ m / (len / block) = m / len * block := hfit
    have hT : 0 < len / block := by
      rcases Nat.eq_zero_or_pos (len / block) with h | h
      · rw [h, Nat.mul_zero] at h1
        omega
      · exact h
    have hr : j / (len / block) < block :=
      (Nat.div_lt_iff_lt_mul hT).2 (by rw [h1]; exact hj')
    obtain ⟨s1, s2⟩ := split_block (n := m / len) (e := i) hr
    have e : (i % (m / len) * block + j / (len / block)) * (len / block) + j % (len / block) =
        i % (m / len) * len + j := by
      have e1 := Nat.div_add_mod j (len / block)
      calc (i % (m / len) * block + j / (len / block)) * (len / block) + j % (len / block)
          = i % (m / len) * (block * (len / block)) +
              (len / block * (j / (len / block)) + j % (len / block)) := by ring
        _ = i % (m / len) * len + j := by rw [h1, e1]
    show (mat + (block * i + j / (len / block)) / (m / (len / block)) / k,
        (block * i + j / (len / block)) / (m / (len / block)) % k,
        (block * i + j / (len / block)) % (m / (len / block)) * (len / block) +
          j % (len / block)) =
      (mat + i / (m / len) / k, i / (m / len) % k, i % (m / len) * len + j)
    rw [h2, Nat.mul_comm block i, s1, s2, e]

/-- SameIndex at entry i of a declared read, for cells at the one address. -/
theorem same_of_parts {t : TSize} {phi : ℕ → ℕ → K} {val : E → K} {d : ReadDecl E}
    (hP : PartsLaid t phi val d) (hF : PartsFit t d)
    (hc : d.count = d.room (t.m d.mat) (t.k d.mat)) {i : ℕ} (hi : i < d.count)
    (cell : ℕ → ℕ × ℕ × ℕ)
    (hcell : ∀ j, j < d.len → cell j =
      (d.mat + i / (t.m d.mat / d.len) / t.k d.mat, i / (t.m d.mat / d.len) % t.k d.mat,
        i % (t.m d.mat / d.len) * d.len + j)) :
    SameIndex t phi ⟨d.start + i, d.len, cell, fun j => val (d.w j)⟩ := by
  have hi' : i < d.parts * (t.k d.mat * (t.m d.mat / d.len)) := by
    rw [hc] at hi
    exact hi
  have hkR : 0 < t.k d.mat * (t.m d.mat / d.len) := by
    rcases Nat.eq_zero_or_pos (t.k d.mat * (t.m d.mat / d.len)) with h | h
    · rw [h, Nat.mul_zero] at hi'
      exact absurd hi' (Nat.not_lt_zero _)
    · exact h
  have hk : 0 < t.k d.mat := by
    rcases Nat.eq_zero_or_pos (t.k d.mat) with h | h
    · rw [h, Nat.zero_mul] at hkR
      exact absurd hkR (Nat.lt_irrefl 0)
    · exact h
  have hR : 0 < t.m d.mat / d.len := by
    rcases Nat.eq_zero_or_pos (t.m d.mat / d.len) with h | h
    · rw [h, Nat.mul_zero] at hkR
      exact absurd hkR (Nat.lt_irrefl 0)
    · exact h
  have hq : i / (t.m d.mat / d.len) / t.k d.mat < d.parts := by
    rw [Nat.div_div_eq_div_mul]
    refine (Nat.div_lt_iff_lt_mul (Nat.mul_pos hR hk)).2 ?_
    rw [Nat.mul_comm _ (t.k d.mat)]
    exact hi'
  obtain ⟨n, hn, hw⟩ := hP _ (List.mem_map.2 ⟨_, List.mem_range.2 hq, rfl⟩)
  obtain ⟨hm, hk'⟩ := hF.2 _ hq
  have h3 := split3 i (t.m d.mat / d.len) (t.k d.mat)
  refine ⟨n, _, i / (t.m d.mat / d.len) % t.k d.mat, i % (t.m d.mat / d.len), hn, ?_, ?_, ?_, ?_,
    rfl, fun j hj => ⟨hcell j hj, hw j hj⟩⟩
  · show d.mat + i / (t.m d.mat / d.len) / t.k d.mat < t.NM
    have := hF.1
    omega
  · show i / (t.m d.mat / d.len) % t.k d.mat < t.k (d.mat + i / (t.m d.mat / d.len) / t.k d.mat)
    rw [hk']
    exact Nat.mod_lt _ hk
  · show i % (t.m d.mat / d.len) < t.m (d.mat + i / (t.m d.mat / d.len) / t.k d.mat) / d.len
    rw [hm]
    exact Nat.mod_lt _ hR
  · show d.start + i =
      d.start + i / (t.m d.mat / d.len) / t.k d.mat * (t.k d.mat * (t.m d.mat / d.len)) +
        i / (t.m d.mat / d.len) % t.k d.mat *
          (t.m (d.mat + i / (t.m d.mat / d.len) / t.k d.mat) / d.len) +
        i % (t.m d.mat / d.len)
    rw [hm]
    omega

/-- **The join from the tables.** -/
theorem joined_of_parts {t : TSize} {phi : ℕ → ℕ → K} {val : E → K} {d : ReadDecl E}
    (hP : PartsLaid t phi val d) (hF : PartsFit t d)
    (hW : d.Whole (t.m d.mat) (t.k d.mat)) : Joined t phi val d := by
  intro i hi
  exact same_of_parts hP hF hW.2.1 hi _ fun j hj => cells_fit d hW.1 hW.2.2 hj

/-- An item of a list, under a map. -/
theorem at_map {α β : Type} {f : α → β} {l : List α} {n : ℕ} {a : α} (h : l[n]? = some a) :
    (l.map f)[n]? = some (f a) := by
  rw [List.getElem?_map, h, Option.map_some]

/-- The equation on a whole link's list gives each declaration its tables. -/
theorem parts_of_tables {t : TSize} {phi : ℕ → ℕ → K} {val : E → K} {ds : List (ReadDecl E)}
    (h : TablesAre t phi val ds) {d : ReadDecl E} (hd : d ∈ ds) : PartsLaid t phi val d := by
  intro x hx
  have hlen : x.len = d.len := by
    have hx' := hx
    unfold ReadDecl.tabs at hx'
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx'
    rfl
  have hmem : (x, d.w) ∈ tablesOf t ds :=
    List.mem_flatMap.2 ⟨d, hd, List.mem_map.2 ⟨x, hx, rfl⟩⟩
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hmem
  refine ⟨n, ?_, fun j hj => h.2 n (x, d.w) hn j ?_⟩
  · rw [h.1]
    exact at_map hn
  · show j < x.len
    rw [hlen]
    exact hj

/-- The two together. -/
theorem joined_of_tables {t : TSize} {phi : ℕ → ℕ → K} {val : E → K} {ds : List (ReadDecl E)}
    (h : TablesAre t phi val ds) {d : ReadDecl E} (hd : d ∈ ds) (hF : PartsFit t d)
    (hW : d.Whole (t.m d.mat) (t.k d.mat)) : Joined t phi val d :=
  joined_of_parts (parts_of_tables h hd) hF hW

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.split3
#print axioms VerifiableInference.Reads.split_block
#print axioms VerifiableInference.Reads.cells_fit
#print axioms VerifiableInference.Reads.same_of_parts
#print axioms VerifiableInference.Reads.joined_of_parts
#print axioms VerifiableInference.Reads.at_map
#print axioms VerifiableInference.Reads.parts_of_tables
#print axioms VerifiableInference.Reads.joined_of_tables
