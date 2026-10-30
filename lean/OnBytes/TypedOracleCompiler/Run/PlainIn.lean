-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlainIn.lean: the plain part of a WRITTEN round of the protocol in three stretches
as a plain part of the whole shape; and the ties between three texts that each say "the round at the
typed round i": the recursion of `PlainAt.rcG`, the arithmetic of `KeyRanges.rdAt`, and
`KeyRanges.Three.on`, `idx`.

OnBytes/TypedOracleCompiler/Run/PlainAt.lean has ways in and out for the four seams' plain parts, and the code
`rcG G i` of (roots, plain part) at the typed round i, by recursion. OnBytes/TypedOracleCompiler/Run/KeyRanges.lean
reads the written round at a typed round off the three lists by arithmetic (`rdAt`), for the word of
kind and work, and says by arithmetic which typed rounds are rounds of a chain (`Three.on`) and with
which index. A slip of one in any of these would give a lawful code that no chain asks. This file
ties them. The sibling is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `PlainD d`: the type of a written round's plain part; `inAt C t ds k z`: the plain part z of
   round k of written rounds ds before a shape t; `inLast C ds k z`: the same with nothing behind;
 - `rcApp_at`: at round k and that plain part `rcApp` writes what the round's own code `PQ.pRound`
   writes; `rcApp_past`: at round (length of ds) + j and a plain part of t carried in, what `rt j`
   writes; `rcL_at`;
 - `inR₁`, `inR₂`, `inR₃`: the plain part of round k of G's first, second, third stretch as a plain
   part of G.sh;
 - `rcG_at₁`, `rcG_at₂`, `rcG_at₃`: at the typed rounds k + 1, n₁ + 3 + k, n₁ + n₂ + 4 + k and these
   plain parts, `rcG` writes what the round's own code writes;
 - `rdAt₁`, `rdAt₂`, `rdAt₃`: at these typed rounds `rdAt` is that round; `rdAt_seam`: at the typed
   rounds 0, `at1`, `at2`, `at3` it is none;
 - `on_iff`: `Three.on` at G's lengths is true exactly where `rdAt` is some round; `lab_idx₁`,
   `lab_idx₂`, `lab_idx₃`: the stretch's label and the index k + 1 at these typed rounds.

Main definitions: `inAt`, `inLast`, `inR₁`, `inR₂`, `inR₃`.
Main theorems: `rcG_at₁`, `rcG_at₂`, `rcG_at₃`, `rdAt₁`, `rdAt₂`, `rdAt₃`, `rdAt_seam`, `on_iff`.

Not claimed. That a chain of the compiled verifier writes, at the typed round i, these plain parts:
its text puts a round's plain part under as many right injections as rounds stand before it, and so
do these by their recursion; no theorem here names the verifier. That `PQ.pRound`'s bits are a
message's bytes of the format. Nothing ties G to a key file. Nothing on soundness.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.KeyRanges

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PlainIn
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PlainAt TypedOracleCompiler.Run.KeyRanges
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The type of a written round's plain part. -/
abbrev PlainD (d : PQ.RD) : Type := GPlain ℕ d.entry.work (PlainOf d.items)

/-! ## Written rounds before a shape -/

section
variable (C : PQ.CK) (t : Shape)

/-- The plain part z of round k of written rounds ds before a shape t. -/
def inAt : (ds : List PQ.RD) → (k : Fin ds.length) → PlainD (ds.get k) → PBa (PQ.uL C ds ++ t)
  | _ :: _, ⟨0, _⟩, z => .inl (.inr z)
  | _ :: ds, ⟨k + 1, h⟩, z => .inr (inAt ds ⟨k, Nat.lt_of_succ_lt_succ h⟩ z)

/-- At round k and that plain part the code writes what the round's own code writes. -/
theorem rcApp_at (rt : ℕ → PCode (List (Dig 256) × PBa t)) :
    ∀ (ds : List PQ.RD) (k : Fin ds.length) (r : List (Dig 256)) (z : PlainD (ds.get k)),
      (rcApp C t rt ds k.val).put (r, inAt C t ds k z) =
        (PQ.pRound (ds.get k).entry.work (ds.get k).items).put (r, z)
  | _ :: _, ⟨0, _⟩, _, _ => rfl
  | _ :: ds, ⟨k + 1, h⟩, r, z => rcApp_at rt ds ⟨k, Nat.lt_of_succ_lt_succ h⟩ r z

/-- Behind the written rounds the code writes what rt writes, at a plain part of t carried
in. -/
theorem rcApp_past (rt : ℕ → PCode (List (Dig 256) × PBa t)) :
    ∀ (ds : List PQ.RD) (j : ℕ) (r : List (Dig 256)) (y : PBa t),
      (rcApp C t rt ds (ds.length + j)).put (r, appIn C t ds y) = (rt j).put (r, y)
  | [], j, r, y => by
      show (rt (0 + j)).put (r, y) = _
      rw [Nat.zero_add]
  | _ :: ds, j, r, y => by
      show (rcApp C t rt (_ :: ds) (ds.length + 1 + j)).put _ = _
      rw [Nat.add_right_comm]
      exact rcApp_past rt ds j r y

end

/-- The plain part z of round k of written rounds ds, with nothing behind. -/
def inLast (C : PQ.CK) : (ds : List PQ.RD) → (k : Fin ds.length) → PlainD (ds.get k) → PQ.PBL C ds
  | _ :: _, ⟨0, _⟩, z => .inl (.inr z)
  | _ :: ds, ⟨k + 1, h⟩, z => .inr (inLast C ds ⟨k, Nat.lt_of_succ_lt_succ h⟩ z)

/-- At round k and that plain part the sibling's code writes what the round's own code writes. -/
theorem rcL_at (C : PQ.CK) :
    ∀ (ds : List PQ.RD) (k : Fin ds.length) (r : List (Dig 256)) (z : PlainD (ds.get k)),
      (PQ.rcL C ds k.val).put (r, inLast C ds k z) =
        (PQ.pRound (ds.get k).entry.work (ds.get k).items).put (r, z)
  | _ :: _, ⟨0, _⟩, _, _ => rfl
  | _ :: ds, ⟨k + 1, h⟩, r, z => rcL_at C ds ⟨k, Nat.lt_of_succ_lt_succ h⟩ r z

/-! ## The three stretches -/

variable (G : Stretches)

/-- The plain part of round k of the first stretch, as a plain part of the whole shape. -/
def inR₁ (k : Fin G.ds₁.length) (z : PlainD (G.ds₁.get k)) : PBa G.sh :=
  .inr (inAt G.C G.sh₂ G.ds₁ k z)

/-- The plain part of round k of the second stretch. -/
def inR₂ (k : Fin G.ds₂.length) (z : PlainD (G.ds₂.get k)) : PBa G.sh :=
  .inr (appIn G.C G.sh₂ G.ds₁ (.inr (.inr (inAt G.C G.sh₃ G.ds₂ k z))))

/-- The plain part of round k of the third stretch. -/
def inR₃ (k : Fin G.ds₃.length) (z : PlainD (G.ds₃.get k)) : PBa G.sh :=
  .inr (appIn G.C G.sh₂ G.ds₁ (.inr (.inr (appIn G.C G.sh₃ G.ds₂ (.inr (inLast G.C G.ds₃ k z))))))

/-- At the typed round k + 1 `rcG` writes the message of round k of the first stretch. -/
theorem rcG_at₁ (k : Fin G.ds₁.length) (r : List (Dig 256)) (z : PlainD (G.ds₁.get k)) :
    (rcG G (k.val + 1)).put (r, inR₁ G k z) =
      (PQ.pRound (G.ds₁.get k).entry.work (G.ds₁.get k).items).put (r, z) :=
  rcApp_at G.C G.sh₂ (rc₂ G) G.ds₁ k r z

/-- At the typed round n₁ + 3 + k `rcG` writes the message of round k of the second stretch. -/
theorem rcG_at₂ (k : Fin G.ds₂.length) (r : List (Dig 256)) (z : PlainD (G.ds₂.get k)) :
    (rcG G (G.ds₁.length + (k.val + 2) + 1)).put (r, inR₂ G k z) =
      (PQ.pRound (G.ds₂.get k).entry.work (G.ds₂.get k).items).put (r, z) :=
  (rcApp_past G.C G.sh₂ (rc₂ G) G.ds₁ (k.val + 2) r _).trans
    (rcApp_at G.C G.sh₃ (rc₃ G) G.ds₂ k r z)

/-- At the typed round n₁ + n₂ + 4 + k `rcG` writes the message of round k of the third
stretch. -/
theorem rcG_at₃ (k : Fin G.ds₃.length) (r : List (Dig 256)) (z : PlainD (G.ds₃.get k)) :
    (rcG G (G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1)).put (r, inR₃ G k z) =
      (PQ.pRound (G.ds₃.get k).entry.work (G.ds₃.get k).items).put (r, z) :=
  (rcApp_past G.C G.sh₂ (rc₂ G) G.ds₁ (G.ds₂.length + (k.val + 1) + 2) r _).trans
    ((rcApp_past G.C G.sh₃ (rc₃ G) G.ds₂ (k.val + 1) r _).trans (rcL_at G.C G.ds₃ k r z))

/-! ## The arithmetic -/

/-- At the typed round k + 1 `rdAt` is round k of the first stretch. -/
theorem rdAt₁ (k : Fin G.ds₁.length) : rdAt G (k.val + 1) = some (G.ds₁.get k) := by
  unfold rdAt
  rw [if_pos (by have := k.isLt; omega), if_neg (by omega), Nat.add_sub_cancel]
  exact List.getElem?_eq_getElem k.isLt

/-- At the typed round n₁ + 3 + k it is round k of the second stretch. -/
theorem rdAt₂ (k : Fin G.ds₂.length) :
    rdAt G (G.ds₁.length + (k.val + 2) + 1) = some (G.ds₂.get k) := by
  unfold rdAt
  rw [if_neg (by omega), if_pos (by have := k.isLt; omega), if_neg (by omega),
    show G.ds₁.length + (k.val + 2) + 1 - (G.ds₁.length + 3) = k.val by omega]
  exact List.getElem?_eq_getElem k.isLt

/-- At the typed round n₁ + n₂ + 4 + k it is round k of the third stretch. -/
theorem rdAt₃ (k : Fin G.ds₃.length) :
    rdAt G (G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1) = some (G.ds₃.get k) := by
  unfold rdAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1 -
      (G.ds₁.length + G.ds₂.length + 4) = k.val by omega]
  exact List.getElem?_eq_getElem k.isLt

/-- At the four seams' typed rounds there is no written round. -/
theorem rdAt_seam : rdAt G 0 = none ∧ rdAt G (at1 G) = none ∧ rdAt G (at2 G) = none ∧
    rdAt G (at3 G) = none := by
  unfold rdAt at1 at2 at3 n₁ n₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [if_pos (Nat.zero_le _), if_pos rfl]
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- A typed round is on exactly if a written round stands there. -/
theorem on_iff (l₁ l₂ l₃ i : ℕ) :
    (threeOf G l₁ l₂ l₃).on i = (rdAt G i).isSome := by
  unfold Three.on threeOf rdAt
  dsimp only
  by_cases h1 : i ≤ G.ds₁.length
  · rw [if_pos h1]
    by_cases h0 : i = 0
    · rw [if_pos h0]
      exact decide_eq_false (by omega)
    · rw [if_neg h0, List.getElem?_eq_getElem (by omega)]
      exact decide_eq_true (by omega)
  · rw [if_neg h1]
    by_cases h2 : i ≤ G.ds₁.length + 2 + G.ds₂.length
    · rw [if_pos h2]
      by_cases h3 : i ≤ G.ds₁.length + 2
      · rw [if_pos h3]
        exact decide_eq_false (by omega)
      · rw [if_neg h3, List.getElem?_eq_getElem (by omega)]
        exact decide_eq_true (by omega)
    · rw [if_neg h2]
      by_cases h4 : i = G.ds₁.length + G.ds₂.length + 3
      · rw [if_pos h4]
        exact decide_eq_false (by omega)
      · rw [if_neg h4]
        by_cases h5 : i - (G.ds₁.length + G.ds₂.length + 4) < G.ds₃.length
        · rw [List.getElem?_eq_getElem h5]
          exact decide_eq_true (by omega)
        · rw [List.getElem?_eq_none (by omega)]
          exact decide_eq_false (by omega)

/-- Label and index at a round of the first stretch. -/
theorem lab_idx₁ (l₁ l₂ l₃ : ℕ) (k : Fin G.ds₁.length) :
    (threeOf G l₁ l₂ l₃).lab (k.val + 1) = l₁ ∧
      (threeOf G l₁ l₂ l₃).idx (k.val + 1) = k.val + 1 := by
  have hk : k.val + 1 ≤ (threeOf G l₁ l₂ l₃).n₁ := k.isLt
  unfold Three.lab Three.idx
  rw [if_pos hk, if_pos hk]
  exact ⟨rfl, rfl⟩

/-- Label and index at a round of the second stretch. -/
theorem lab_idx₂ (l₁ l₂ l₃ : ℕ) (k : Fin G.ds₂.length) :
    (threeOf G l₁ l₂ l₃).lab (G.ds₁.length + (k.val + 2) + 1) = l₂ ∧
      (threeOf G l₁ l₂ l₃).idx (G.ds₁.length + (k.val + 2) + 1) = k.val + 1 := by
  have h1 : ¬ G.ds₁.length + (k.val + 2) + 1 ≤ (threeOf G l₁ l₂ l₃).n₁ := by
    show ¬ _ ≤ G.ds₁.length
    omega
  have h2 : G.ds₁.length + (k.val + 2) + 1 ≤
      (threeOf G l₁ l₂ l₃).n₁ + 2 + (threeOf G l₁ l₂ l₃).n₂ := by
    show _ ≤ G.ds₁.length + 2 + G.ds₂.length
    have := k.isLt
    omega
  unfold Three.lab Three.idx
  rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
  refine ⟨rfl, ?_⟩
  show G.ds₁.length + (k.val + 2) + 1 - (G.ds₁.length + 2) = k.val + 1
  omega

/-- Label and index at a round of the third stretch. -/
theorem lab_idx₃ (l₁ l₂ l₃ : ℕ) (k : Fin G.ds₃.length) :
    (threeOf G l₁ l₂ l₃).lab (G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1) = l₃ ∧
      (threeOf G l₁ l₂ l₃).idx (G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1) =
        k.val + 1 := by
  have h1 : ¬ G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1 ≤
      (threeOf G l₁ l₂ l₃).n₁ := by
    show ¬ _ ≤ G.ds₁.length
    omega
  have h2 : ¬ G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1 ≤
      (threeOf G l₁ l₂ l₃).n₁ + 2 + (threeOf G l₁ l₂ l₃).n₂ := by
    show ¬ _ ≤ G.ds₁.length + 2 + G.ds₂.length
    omega
  unfold Three.lab Three.idx
  rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
  refine ⟨rfl, ?_⟩
  show G.ds₁.length + (G.ds₂.length + (k.val + 1) + 2) + 1 -
    (G.ds₁.length + G.ds₂.length + 3) = k.val + 1
  omega

end TypedOracleCompiler.Run.PlainIn
