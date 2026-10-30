-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsBounds.lean: the conditions of OnBytes/TypedOracleCompiler/StringsWhole.lean and
OnBytes/TypedOracleCompiler/StringsRead.lean on all positions and symbols, from conditions on the trees and the
salt.

These two files show that a symbol's body passes the tests on bodies, and that the reader reads its
leaf's spelling from it, under three conditions: no tree is deeper than 63; every tree's word begins
with the 16 bits of the leaves' number (a test by program); both words of every leaf's label are
below 2 ^ 64 (a condition on all positions and symbols). This file shows that the second holds at
ALL trees (`tagsT_all`, `tagsL_all`, `Stretches.tags_all`; of the library's own test, `tagsOK_all`):
a word is taken modulo 2 ^ 64, which 65536 divides. And that the third follows from conditions on
the trees and the salt (`SmallT`: a tree's number below 2 ^ 16, its width below 2 ^ 24, its depth at
most 63; the salt's words, salt / 8 rounded down, below 2 ^ 8): `inWordsL_of` in one list of rounds,
`Stretches.inWords_of` at three stretches.

So the statements stand with conditions on the trees and the salt alone: none on positions or
symbols, and no test by program: `rdOk_embTail_of_small`, `embTail_okRd_of_small` in one list of
rounds; `Stretches.rdOk_embS_of_small`, `Stretches.embS_okRd_of_small` at three stretches. THESE ARE
THE FORMS TO USE.

Main definitions: `SmallT`, `SmallL`, `Stretches.Small`.
Main theorems: `low16`, `tagsT_all`, `tagsOK_all`, `tagsL_all`, `SmallT.of_le`, `inWordsT`,
`inWordsL_of`, `rdOk_embTail_of_small`, `embTail_okRd_of_small`, `Stretches.tags_all`,
`Stretches.inWords_of`, `Stretches.rdOk_embS_of_small`, `Stretches.embS_okRd_of_small`.

Not claimed. That a description gives these conditions is not shown HERE:
OnBytes/TypedOracleCompiler/StringsMeet.lean has them from the sibling's test `ok` on a description, by the
sibling's `small_of` and `salt_of` (OnBytes/TypedOracleCompiler/Run/SmallTrees.lean). `SmallT` is the library's
`SmallTrees` in another spelling. The conditions are shown besides at one made-up list
(a test that is not in this library). What the heads of the two files say is not claimed is not
claimed here either.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsRead

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop (Shape OPos OSym)
open _root_.Run (t164 bytesToBits bitsL bitsOfByte length_bitsOfByte)
open _root_.Run.PQ (leafWord)
open TypedOracleCompiler.Run TypedOracleCompiler.Strings

/-! ## The test on the trees' words holds at all trees -/

theorem take16_bitsL (a b : UInt8) (l : List UInt8) :
    (bitsL (a :: b :: l)).take 16 = bitsOfByte a ++ bitsOfByte b := by
  have h : bitsL (a :: b :: l) = (bitsOfByte a ++ bitsOfByte b) ++ bitsL l := by
    simp [bitsL, List.flatMap_cons, List.append_assoc]
  rw [h]
  exact List.take_left' (by rw [List.length_append, length_bitsOfByte, length_bitsOfByte])

/-- The first 16 bits of the word 164 + 65536 n are those of 164, for every n. -/
theorem low16 (n : ℕ) : (bytesToBits (_root_.Fmt.u64n (164 + 65536 * n))).take 16 = t164 := by
  have h0 : (UInt64.ofNat (164 + 65536 * n)).toUInt8 = (UInt64.ofNat 164).toUInt8 := by
    apply UInt8.toNat_inj.1
    rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    omega
  have h1 : ((UInt64.ofNat (164 + 65536 * n)) >>> 8).toUInt8 =
      ((UInt64.ofNat 164) >>> 8).toUInt8 := by
    apply UInt8.toNat_inj.1
    rw [UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
      UInt64.toNat_shiftRight, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    simp only [Nat.shiftRight_eq_div_pow]
    have e8 : (8 : UInt64).toNat % 64 = 8 := by decide
    rw [e8]
    omega
  unfold t164
  show (bitsL (_ :: _ :: _)).take 16 = (bitsL (_ :: _ :: _)).take 16
  rw [take16_bitsL, take16_bitsL, h0, h1]

variable (salt : ℕ)

theorem tagsT_all : ∀ ts : List _root_.Fmt.Shape, tagsT salt ts = true
  | [] => rfl
  | s :: ts => by
      show (decide ((leafWord (some s) salt).take 16 = t164) && tagsT salt ts) = true
      rw [tagsT_all ts, Bool.and_true, decide_eq_true_iff]
      exact low16 _

/-- The library's own test on the trees' words (one tree a round) holds at every list of rounds too.
-/
theorem tagsOK_all : ∀ ds : List _root_.Run.PQ.RD, _root_.Run.PQ.tagsOK salt ds = true
  | [] => rfl
  | d :: ds => by
      show (decide ((leafWord d.tree salt).take 16 = t164) && _root_.Run.PQ.tagsOK salt ds) = true
      rw [tagsOK_all ds, Bool.and_true, decide_eq_true_iff]
      exact low16 _

/-- The test on the trees' words holds at every list of rounds. -/
theorem tagsL_all (ds : List PQ.RD) : tagsL salt ds = true :=
  List.all_eq_true.2 fun d _ => tagsT_all salt d.trees

/-! ## Both words of a label, from conditions on the trees -/

/-- Conditions on a round's trees: number below 2 ^ 16, width below 2 ^ 24, depth at most 63. -/
def SmallT (ts : List _root_.Fmt.Shape) : Prop :=
  ∀ s ∈ ts, s.tree < 2 ^ 16 ∧ s.W < 2 ^ 24 ∧ 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64

/-- The same from "depth at most 63" in so many words. -/
theorem SmallT.of_le {ts : List _root_.Fmt.Shape}
    (h : ∀ s ∈ ts, s.tree < 2 ^ 16 ∧ s.W < 2 ^ 24 ∧ s.a ≤ 63) : SmallT ts := fun s hs => by
  obtain ⟨h1, h2, h3⟩ := h s hs
  have h4 : 2 ^ s.a ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) h3
  exact ⟨h1, h2, by omega⟩

/-- The same on a list of rounds. -/
def SmallL (ds : List PQ.RD) : Prop := ∀ d ∈ ds, SmallT d.trees

theorem SmallL.shallow {ds : List PQ.RD} (h : SmallL ds) :
    ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64 := fun d hd s hs => (h d hd s hs).2.2

/-- What it is for a spelling of leaves to have both words below 2 ^ 64. -/
def InW {t : Shape} (lt : (p : OPos t) → OSym t p → ℕ × ℕ × ByteArray) : Prop :=
  ∀ p a, 164 + 65536 * (lt p a).1 < 2 ^ 64 ∧ (lt p a).2.1 < 2 ^ 64

/-- In a round whose trees meet `SmallT`, with the salt's words below 2 ^ 8: both words of every
leaf's label are below 2 ^ 64. -/
theorem inWordsT (h8 : salt / 8 < 2 ^ 8) : ∀ ts : List _root_.Fmt.Shape, SmallT ts →
    ∀ (p : PQ.PosT ts) (a : PQ.SymT ts p),
      164 + 65536 * (StringsList.leafT salt ts p a).1 < 2 ^ 64 ∧
        (StringsList.leafT salt ts p a).2.1 < 2 ^ 64
  | s :: _, h, .inl x, _ => by
      obtain ⟨h1, h2, h3⟩ := h s (List.mem_cons_self ..)
      have hp := _root_.Fmt.leafPlace_lt s.tree s.W (salt / 8) h1 h2 h8
      have hx : x.val < 2 ^ s.a := x.isLt
      refine ⟨?_, ?_⟩
      · show 164 + 65536 * _root_.Fmt.leafPlace s.tree s.W (salt / 8) < 2 ^ 64
        omega
      · show 2 ^ s.a + x.val < 2 ^ 64
        omega
  | _ :: ts, h, .inr p, a => inWordsT h8 ts (fun s hs => h s (List.mem_cons_of_mem _ hs)) p a

variable (C : PQ.CK)

theorem inW_tail (h8 : salt / 8 < 2 ^ 8) : ∀ ds : List PQ.RD, SmallL ds →
    InW fun (p : OPos (PQ.uL C ds)) a => StringsList.leafSL salt C ds ⟨p, a⟩
  | [], _, p, _ => p.elim
  | d :: _, h, .inl p, a => inWordsT salt h8 d.trees (h d (List.mem_cons_self ..)) p a
  | _ :: ds, h, .inr q, a => inW_tail h8 ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

theorem inW_app (h8 : salt / 8 < 2 ^ 8) (t : Shape)
    (lt : (p : OPos t) → OSym t p → ℕ × ℕ × ByteArray) (ht : InW lt) :
    ∀ ds : List PQ.RD, SmallL ds → InW (leafApp salt C t lt ds)
  | [], _, p, a => ht p a
  | d :: _, h, .inl p, a => inWordsT salt h8 d.trees (h d (List.mem_cons_self ..)) p a
  | _ :: ds, h, .inr q, a =>
      inW_app h8 t lt ht ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

theorem inW_seam (s : Seam) (t : Shape) (lt : (p : OPos t) → OSym t p → ℕ × ℕ × ByteArray)
    (ht : InW lt) : InW (leafSeam s t lt)
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => ht q a

/-- In one list of rounds the condition on all positions and symbols follows from the conditions
on the trees and the salt. -/
theorem inWordsL_of (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds) :
    InWordsL salt C ds := fun y => by
  rw [← leafSL_eq salt C ds y]
  exact inW_tail salt C h8 ds h y.1 y.2

/-- A symbol's body passes `okRd`, in one list of rounds, under the conditions on the trees and the
salt. -/
theorem embTail_okRd_of_small (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds)
    (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) : okRd (embTail salt C ds p a) = true :=
  embTail_okRd salt C ds h.shallow (tagsL_all salt ds) (inWordsL_of salt C h8 ds h) p a

/-- From a symbol's body the reader behind the test reads the sibling's own spelling of its
leaf, in one list of rounds, under the conditions on the trees and the salt. -/
theorem rdOk_embTail_of_small (h8 : salt / 8 < 2 ^ 8) (ds : List PQ.RD) (h : SmallL ds)
    (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p) :
    rdOk (embTail salt C ds p a) = some (PQ.leafSL C salt ds ⟨p, a⟩) :=
  rdOk_embTail salt C ds h.shallow (tagsL_all salt ds) (inWordsL_of salt C h8 ds h) p a

namespace Stretches
variable (G : Stretches)

/-- The conditions on the trees of all three stretches. -/
def Small : Prop := SmallL G.ds₁ ∧ SmallL G.ds₂ ∧ SmallL G.ds₃

theorem Small.shallow {G : Stretches} (h : G.Small) : G.Shallow :=
  ⟨h.1.shallow, h.2.1.shallow, h.2.2.shallow⟩

theorem tags_all : G.Tags salt := ⟨tagsL_all salt _, tagsL_all salt _, tagsL_all salt _⟩

/-- At three stretches the condition on all positions and symbols follows from the conditions on
the trees and the salt. -/
theorem inWords_of (h8 : salt / 8 < 2 ^ 8) (h : G.Small) : G.InWords salt :=
  inW_seam G.s0 _ _ (inW_app salt G.C h8 G.sh₂ _
    (inW_seam G.s1 _ _ (inW_seam G.s2 _ _ (inW_app salt G.C h8 G.sh₃ _
      (inW_seam G.s3 _ _ (inW_tail salt G.C h8 G.ds₃ h.2.2)) G.ds₂ h.2.1))) G.ds₁ h.1)

/-- A symbol's body passes `okRd`, under the conditions on the trees and the salt. -/
theorem embS_okRd_of_small (h8 : salt / 8 < 2 ^ 8) (h : G.Small) (p : OPos G.sh) (a : OSym G.sh p) :
    okRd (G.embS salt p a) = true :=
  G.embS_okRd salt h.shallow (G.tags_all salt) (G.inWords_of salt h8 h) p a

/-- The reader behind the test reads from a symbol's body the spelling of its leaf in its own tree,
under the conditions on the trees and the salt. -/
theorem rdOk_embS_of_small (h8 : salt / 8 < 2 ^ 8) (h : G.Small) (p : OPos G.sh) (a : OSym G.sh p) :
    rdOk (G.embS salt p a) = some (G.leafS salt p a) :=
  G.rdOk_embS salt h.shallow (G.tags_all salt) (G.inWords_of salt h8 h) p a

end Stretches

end TypedOracleCompiler.Slice
