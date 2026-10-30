-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTie.lean: the key vectors of the eight calls of a feed-forward segment
against the library's glued families of keys.

The library speaks of the keys of a feed-forward segment in two numberings. Inst/Model/FF/ lays
them in the key vectors of eight calls (keyVec in Inst/Model/FF/Trace.lean): the key with the name
(family s, layer l, entry x, position i) stands at the place (l | the column of x | i) of the
vector of the call of s. Cm/ makes a family of conditions (Cb.Fam) for each of the 34 families of
keys, with that key at the vertex (l | x | i), and glues the families that share a table into one
(SegSpec.glued in Cb/Req/ReqGlue.lean); the glued segments are the segments of the partition over
which the library's theorems on a request stand (Cm/TargetPart.lean). No theorem of the library
names both numberings. This file ties them: as sets of keys; and, for the families before gluing,
place by place.

What is compared with what. The library with itself. No definition or function of OnBytes/ stands
in a statement but KeysHold and InT, which abbreviate texts of the library, and rows_call and
pad_call of Johnson/Road/FormsKeysPass.lean in one proof (pad_InT).

Main definitions: KeysHold (the second clause of SegSpec.Holds), InT (the images of a table's
entries). Main theorems.
 - holds_iff: a segment's conditions are its identities' half and its keys' half.
 - keys_glued: gluing keeps the keys' half.
 - vecs_iff_keys: the entries of the eight key vectors below their lengths lie in given sets
   exactly if the keys by name do.
 - keys_ffSpec: the keys' half of the library's feed-forward segment, before gluing, in keys by
   name.
 - vecs_glued: the tie: the keys' half of segment 2 g of the model in glued form says that the
   entries of the group's eight key vectors lie in their calls' tables. As sets: eight calls
   against five glued families (calls 0, 1, 2, 7 share a table); no call has a glued family of its
   own; nothing at a point.
 - key_place: for each of the 34 families before gluing (kfAll): its value at the vertex of (l, x,
   i) is the entry of the key vector of the call of s at the place of (l, x, i). Into the glued
   families place by place: not shown.

Who reads the targets. (Cm.Seg.TS.segM s k).glued is the segment number k of the library's partition
targetPart; the partition's Cond asks its Holds of every segment, at the partition's own format,
where the statements here stand at fmtRef: the two formats have the same rows and column variables,
and the library crosses from one to the other (Cb/Part/LdPartIdxFmt.lean). The laws admit and force
read Cond whole: all 25 segments, the identities' half too, and a bound on the cells: so nothing
here reaches the relation. The keys' half alone is read by the library's theorem on the lookup's
claim before the shift (ldPartKeys_holds in Cb/Part/LdPartLkpFam.lean), which the front of a segment
and the law on the multiplicities' bits use; no file of this library joins it with vecs_glued. Of
key_place the left side is read by the proofs of the library's KeyOK alone, the right side by
nobody.

At which sizes. keys_glued: every segment. vecs_iff_keys: every ring, all sizes, every trace. The
others: the library's reference sizes DF, its format fmtRef; vecs_glued at the reference tables and
the fields Cb.Gl.F and Cb.Gl.E, where the library defines its model's segments.

The hypotheses, and that they can be met. g < nGr, the number of groups, 12. The ranges are those
of the names of keys and of the key vectors. keys_glued asks that the segment be well formed,
keys_ffSpec that each family have the library's KeyOK: for the model's segment both are theorems of
the library (ffSeg_wf, kfAll_ok in Cm/TargetSegFFAllProofs.lean), used in vecs_glued. vecs_iff_keys
asks that each set hold its table's padding value: pad_InT.

What is not claimed. That the entries lie in the tables. Anything on the identities, on attention,
on the head, on the cells' size. Anything on the verifier: its cells stand in another dictionary
than the library's tA, and its key vectors under another table of scales (see
Johnson/Road/FormsKeysScl.lean). key_place says that two values at two places are one; that the map
between the places is one to one or onto is not stated, and it is no map of cubes: nothing follows
on an extension at a point. The program does not import this file.
-/
import Johnson.Road.FormsKeysPass
import Cm.TargetSegModel
import Cm.TargetSegFFAllProofs
import Cb.Req.ReqGlueProofsSeg
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Scl Tables ppref)
open Inst.Model.All (DF SFK nGr)
open Inst.Model.FFSeg (Dim Cell Fam LW key keyVec lut call len present famAt lJ aC pos keyIdx)

/-! ## The keys' half of a segment's conditions -/

section Half

variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- The keys' half of the conditions of a segment: every key of every family, on the family's cube,
is the image of an element of the family's table. It is the second of the two clauses of the
library's SegSpec.Holds (Cb/Req/ReqSpec.lean). -/
def KeysHold (S : Cb.SegSpec X F E) (Φ : Cb.IdxFmt F) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) : Prop :=
  ∀ k ∈ S.keys, ∀ b < 2 ^ k.1.v, ∃ u ∈ k.2.set, k.1.val Φ x W A b = algebraMap F E u

/-- The conditions of a segment are its identities' half and its keys' half. -/
theorem holds_iff (S : Cb.SegSpec X F E) (Φ : Cb.IdxFmt F) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) :
    S.Holds Φ x W A ↔
      (∀ f ∈ S.idn, ∀ b < 2 ^ f.v, f.val Φ x W A b = 0) ∧ KeysHold S Φ x W A :=
  Iff.rfl

/-- Gluing keeps the keys' half. The library has this for the two halves together
(glued_holds_iff in Cb/Req/ReqGlueProofsSeg.lean); the proof is the second half of that one. -/
theorem keys_glued {S : Cb.SegSpec X F E} {Φ : Cb.IdxFmt F} (h : S.WF Φ) (x : X)
    (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) :
    KeysHold S.glued Φ x W A ↔ KeysHold S Φ x W A := by
  constructor
  · intro hg k hk
    have h1 := hg (Cb.Fam.glue (algebraMap F E (k.2.t 0)) (Cb.group S k.2), k.2)
      ((Cb.mem_glued_keys S _).2 ⟨⟨k.1, hk⟩, rfl⟩)
    exact (Cb.glue_key_iff X F E (Cb.group S k.2) k.2 Φ x W A (Cb.group_wf h k.2)).1
      h1 k.1 ((Cb.mem_group S k.2 k.1).2 hk)
  · intro hs k hk
    obtain ⟨-, h2⟩ := (Cb.mem_glued_keys S k).1 hk
    rw [h2]
    exact (Cb.glue_key_iff X F E (Cb.group S k.2) k.2 Φ x W A (Cb.group_wf h k.2)).2
      fun f hf => hs (f, k.2) ((Cb.mem_group S k.2 f).1 hf)

end Half

/-! ## Key vectors and keys by name -/

/-- All entries of the eight key vectors below the vectors' lengths lie in sets S c exactly if all
keys, by their names, lie in the sets of their calls. Asked: each set holds the padding value of its
call's table. For every ring, all sizes, every trace. -/
theorem vecs_iff_keys [scl : Scl] {R : Type} [CommRing R] (D : Dim) (t : Cell → R) (tb : Tables)
    (L0 : ℕ) (w : ℕ → LW R) (S : Fin 8 → Set R) (hp : ∀ c, (((lut tb c).pad : ℤ) : R) ∈ S c) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC D c → keyVec D t tb L0 w c X ∈ S c) ↔
      ∀ s : Fam, ∀ l, l < D.nl → present s l = true → ∀ x, x < len D s → ∀ i, i < D.T →
        key D t tb L0 w s l x i ∈ S (call s) := by
  constructor
  · intro H s l hl hs x hx i hi
    have hX : keyIdx D (call s) l (pos D s x) i < 2 ^ aC D (call s) := by
      have e : 2 ^ aC D (call s) = D.nl * 2 ^ lJ D (call s) * D.T := by
        show 2 ^ (D.lL + lJ D (call s) + D.lT) = 2 ^ D.lL * 2 ^ lJ D (call s) * 2 ^ D.lT
        rw [pow_add, pow_add]
      rw [e]
      exact Inst.Model.FFSeg.IndexFacts.mr_lt
        (Inst.Model.FFSeg.IndexFacts.mr_lt hl (Inst.Model.FFSeg.IndexFacts.pos_lt D hx)) hi
    have h1 := H (call s) _ hX
    rwa [Inst.Model.FFSeg.IndexFacts.keyVecAt R D t tb L0 w s l x i hx hi hs] at h1
  · intro H c X hX
    have hT : 0 < D.T := Nat.two_pow_pos _
    have hi : X % D.T < D.T := Nat.mod_lt _ hT
    have hl : X / D.T / 2 ^ lJ D c < D.nl := by
      have e : 2 ^ aC D c = D.nl * 2 ^ lJ D c * D.T := by
        show 2 ^ (D.lL + lJ D c + D.lT) = 2 ^ D.lL * 2 ^ lJ D c * 2 ^ D.lT
        rw [pow_add, pow_add]
      rw [e] at hX
      rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hT (Nat.two_pow_pos _))]
      calc X < D.nl * 2 ^ lJ D c * D.T := hX
        _ = D.nl * (D.T * 2 ^ lJ D c) := by ring
    unfold keyVec
    cases hfa : famAt D c (X / D.T % 2 ^ lJ D c) with
    | none => exact hp c
    | some sx =>
      obtain ⟨s, x⟩ := sx
      obtain ⟨hc, hx, -⟩ := (Inst.Model.FFSeg.IndexFacts.famAtPos D c _ s x).mp hfa
      by_cases hs : present s (X / D.T / 2 ^ lJ D c) = true
      · subst hc
        have h2 := H s _ hl hs x hx _ hi
        simpa only [if_pos hs] using h2
      · simpa only [if_neg hs] using hp c

/-! ## The library's segment, before gluing -/

section Seg

variable [scl : Scl] {X E : Type} [Field E] [Algebra Cb.Gl.F E]

/-- The images, in the larger field, of the entries of a call's table. -/
def InT (tb : Tables) (c : Fin 8) : Set E :=
  {e | ∃ u ∈ (Cm.Seg.tabOf (lut tb c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
    e = algebraMap Cb.Gl.F E u}

/-- The padding value of a call's table is among them. -/
theorem pad_InT (tb : Tables) (c : Fin 8) : (((lut tb c).pad : ℤ) : E) ∈ InT (E := E) tb c :=
  ⟨_, (Cm.Seg.mem_tabOf (rows_call tb c) _).2 (pad_call tb c), (map_intCast _ _).symm⟩

/-- The keys' half of the conditions of the library's feed-forward segment of group g, before
gluing, says that all keys, by their names, at the matrices read as a trace and the weights read in
the index matrix, lie in their tables. For all index matrices over the prime field and all matrices
of cells. The library has this inside the proof of ffSpec_holds_iff (Cm/TargetSegFF.lean), which is
stated for the two halves together, at casts of integers. -/
theorem keys_ffSpec {Φ : Cb.IdxFmt Cb.Gl.F} {g : ℕ} {tb : Tables} {kf : Fam → Cb.Fam X E}
    (idf : List (Cb.Fam X E)) (hk : ∀ s, Cm.Seg.TS.KeyOK Φ g tb s (kf s)) (x₀ : X)
    (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → E) :
    KeysHold (Cm.Seg.TS.ffSpec tb kf idf) Φ x₀ W A ↔
      ∀ s : Fam, ∀ l, l < DF.nl → present s l = true → ∀ x, x < len DF s → ∀ i, i < DF.T →
        key DF (Cm.Seg.tA g A) tb (4 * g) (Cm.Seg.wOf g W) s l x i ∈ InT (E := E) tb (call s) := by
  have hS : ∀ s, ((Cm.Seg.padOf tb s : ℤ) : E) ∈ InT (E := E) tb (call s) :=
    fun s => pad_InT tb (call s)
  constructor
  · intro h s l hl hp x hx i hi
    exact ((hk s).iff x₀ W A _ (hS s)).1
      (h (kf s, _) (List.mem_map_of_mem (Cm.Seg.TS.mem_allFams s))) l hl hp x hx i hi
  · intro h k hkm
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hkm
    exact ((hk s).iff x₀ W A _ (hS s)).2 fun l hl hp x hx i hi => h s l hl hp x hx i hi

end Seg

/-! ## The tie -/

/-- Segment number 2 g of the library's model is the feed-forward segment of group g. -/
theorem segM_even (s : Cm.Scales) {g : ℕ} (hg : g < nGr) :
    Cm.Seg.TS.segM s (2 * g) = Cm.Seg.TS.ffSeg s.kap s.nf g Cm.Seg.tokX := by
  have hg' : g < 12 := hg
  unfold Cm.Seg.TS.segM Cm.Seg.TS.segOf
  rw [if_neg (by omega), if_pos (by omega), Nat.mul_div_cancel_left g (by norm_num)]

/-- The tie, as sets. The keys' half of the conditions of segment 2 g of the library's model in its
glued form, which is the segment of the library's partition, says that all entries of the eight key
vectors of the group, below the vectors' lengths, at the matrices read as a trace and the weights
read in the index matrix, lie in their calls' tables. Eight calls stand against five glued families
(calls 0, 1, 2, 7 share a table): one conjunction against another; nothing at a point. For all
index matrices over the prime field and all matrices of cells. -/
theorem vecs_glued (s : Cm.Scales) {g : ℕ} (hg : g < nGr) (x : Cm.Seg.XI)
    (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    KeysHold (Cm.Seg.TS.segM s (2 * g)).glued Cm.Seg.TS.fmtRef x W A ↔
      ∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
        keyVec (scl := SFK s.kap s.nf g) DF (Cm.Seg.tA g A) Inst.Model.tbRef (4 * g)
          (Cm.Seg.wOf g W) c X ∈ InT (E := Cb.Gl.E) Inst.Model.tbRef c := by
  rw [segM_even s hg, keys_glued (Cm.Seg.TS.ffSeg_wf _ s.kap s.nf g Cm.Seg.tokX hg)]
  unfold Cm.Seg.TS.ffSeg
  rw [keys_ffSpec (scl := SFK s.kap s.nf g) _
    (fun f => @Cm.Seg.TS.kfAll_ok (SFK s.kap s.nf g) _ g Inst.Model.tbRef f hg)]
  exact (vecs_iff_keys (scl := SFK s.kap s.nf g) DF _ Inst.Model.tbRef (4 * g) _ _
    (pad_InT (scl := SFK s.kap s.nf g) Inst.Model.tbRef)).symm

/-! ## Place by place -/

/-- Place by place, for each of the 34 families before gluing (kfAll). The key with the name (s, l,
x, i) stands at the vertex (l | x | i) of the library's family of s and at the place (l | the
column of x | i) of the key vector of the call of s: the two values are one. Of a vertex of a glued
family nothing is said. That the vertex lies on the family's cube is not stated here (the library
has enc3_lt in Cm/SegAlg.lean). For all index matrices over the prime field and all matrices of
cells. -/
theorem key_place [scl : Scl] {X : Type} {g : ℕ} (hg : g < nGr) (tb : Tables) {s : Fam}
    {l x i : ℕ} (hl : l < DF.nl) (hs : present s l = true) (hx : x < len DF s) (hi : i < DF.T)
    (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    (Cm.Seg.TS.kfAll (X := X) g tb s).val Cm.Seg.TS.fmtRef x₀ W A
        (Cm.Seg.enc3 (Cm.Seg.vxOf s) l x i) =
      keyVec DF (Cm.Seg.tA g A) tb (4 * g) (Cm.Seg.wOf g W) (call s)
        (keyIdx DF (call s) l (pos DF s x) i) := by
  rw [Inst.Model.FFSeg.IndexFacts.keyVecAt _ DF _ tb (4 * g) _ s l x i hx hi hs]
  unfold Cm.Seg.TS.kfAll
  by_cases h1 : Cm.Seg.isAff s = true
  · rw [if_pos h1]
    exact Cm.Seg.affKey_live g tb Cm.Seg.TS.fmtRef x₀ W A (4 * g) (Cm.Seg.wOf g W) h1 hs hx hi
  · rw [if_neg h1]
    by_cases h2 : Cm.Seg.isQuad s = true
    · rw [if_pos h2]
      exact Cm.Seg.quadKey_live g tb Cm.Seg.TS.fmtRef x₀ W A (4 * g) (Cm.Seg.wOf g W) h2 hs hx hi
    · rw [if_neg h2]
      refine Cm.Seg.TS.matKey_live X g tb s hg ?_ x₀ W A l x i hl hs hx hi
      cases s <;> first
        | rfl
        | exact absurd rfl h1
        | exact absurd rfl h2

#print axioms holds_iff
#print axioms keys_glued
#print axioms vecs_iff_keys
#print axioms pad_InT
#print axioms keys_ffSpec
#print axioms segM_even
#print axioms vecs_glued
#print axioms key_place

end OnBytes.Road
