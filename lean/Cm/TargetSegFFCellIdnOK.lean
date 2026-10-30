-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFCellIdnOK.lean: the identity (J11) on the embedding of the tokens, and all identities
of a feed-forward segment together, as families (`Fam`) of Cb/Req/ReqSpec.lean over
p = 2^64 - 2^32 + 1.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex b < 2^v of a cube; a
vertex beyond the index set is called dead.

Main names:
  `j11Fam g tok`: in the first segment, (J11) "the stream starts with the embedding of the token":
    "x_0[j] at position i is Emb[tok_i][j]". Vertices b = j · 2^10 + i, 13 bits for the channel.
    Emb[tok_i][j] is a sum atom over the 18 bits of a token t: the index atom `aEmb`
    (Cm/TargetSegIdxModel.lean) under the public coefficient table
    [t = tok_x(i), t < 202,048, j < d], a function of the instance. So the atom's dead vertices
    (tokens from 202,048 on: the head of Cm/TargetSegIdxModel.lean, Limits) have the coefficient 0;
    at a dead channel the family is 0. The inner vertex b · 2^18 + t has 41 variables:
    channel 0 .. 12, position 13 .. 22, token 23 .. 40.
  `j11_val`: at a vertex b < 2^23 its value is the identity of Inst/Model/FF/Trace.lean at a live
    channel, 0 at a dead one.
  `idnFams g tok`: the 17 families of the identities (J1) to (J9) of the ledger of a normalisation
    (`jnFam`), (J10) "the selection bits of a layer with experts add up to 1" (`j10Fam`; both:
    Cm/SegFFCellIdn.lean), and in the first segment (J11).
  `idn_ok`: that list has `IdnOK`, which the theorems on `ffSpec` (Cm/TargetSegFF.lean) require:
    for all matrices A and index matrices W, all vanish on their cubes if and only if all valid
    identities (`FFSeg.Idn.Valid`) of Inst/Model/FF/Trace.lean vanish at the trace `tA g A`; well
    formed; they read only places of valid cells that the segment reads, own or borrowed (`IsFF`).

`σT`, `σJ`, `enc2`, `enc2_lt` are Cm/SegFFCellIdnOK.lean's.
The fields are `Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).


Limits: what is not said of the segment's
families: Cm/TargetSegFFAll.lean, the head, Limits.



Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFCellIdnOK
import Cm.TargetSegAll
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegIdxModel
noncomputable section -- Lean tags what it cannot compile


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl] {X : Type} (g : ℕ) (tok : X → ℕ → ℕ)

/-- the public coefficient: 1 if the token t of the inner vertex is the token of the position,
t < 202,048 and the channel is below d; else 0 -/
def κ11 (x : X) (b' : ℕ) : Cb.Gl.E :=
  if b' % 2 ^ 18 = tok x (b' / 2 ^ 18 % 2 ^ 10) ∧
      b' % 2 ^ 18 < 202048 ∧
      b' / 2 ^ 18 / 2 ^ 10 < DF.d then 1
  else 0

def j11Inner : Poly0 X Cb.Gl.E :=
  ⟨41, 1, fun _ => .idx (aEmb σT σJ), [⟨κ11 tok, [0]⟩]⟩

/-- the stream's first place, 0 at a dead channel -/
def a11 (b : ℕ) : CForm Cb.Gl.E :=
  if b / 2 ^ 10 < DF.d then cXS g 0 (b / 2 ^ 10) (b % 2 ^ 10) else cK 0

/-- (J11). -/
def j11Fam : Cb.Fam X Cb.Gl.E :=
  fam 23 [.base (.cell (a11 g)), .sum 18 (j11Inner tok)] [⟨fun _ _ => 1, [0]⟩, ⟨fun _ _ => -1, [1]⟩]

variable (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E)

theorem j11_raw (b : ℕ) :
    (j11Fam g tok).val fmtRef x₀ W A b =
      (a11 g b).val A -
        ∑ t ∈ range (2 ^ 18),
          κ11 tok x₀ (b * 2 ^ 18 + t) * (aEmb σT σJ).at fmtRef W (vtx 41 (b * 2 ^ 18 + t)) := by
  simp [j11Fam, fam, Fam.val, Term.val, Atom.val, Atom0.val, Poly0.val, j11Inner]
  ring

/-- the index atom at the inner vertex of (j, i, t) -/
theorem emb_at {b t : ℕ} (hb : b < 2 ^ 23) (ht : t < 202048) :
    (aEmb σT σJ).at fmtRef W (vtx 41 (b * 2 ^ 18 + t)) = embOf W t (b / 2 ^ 10) := by
  have n1 : Src.num σT 41 (b * 2 ^ 18 + t) = t := by
    unfold σT
    rw [num_run 23 18 (by norm_num)]
    norm_num
    omega
  have n2 : Src.num σJ 41 (b * 2 ^ 18 + t) = b / 2 ^ 10 := by
    unfold σJ
    rw [num_run 0 13 (by norm_num)]
    norm_num at hb ⊢
    omega
  have h := emb_vtx 41 σT σJ (run_length _ _)
    (by rw [show σJ.length = 13 from run_length _ _]; norm_num) W
    (b * 2 ^ 18 + t) (by rw [n1]; exact ht)
  rw [n1, n2] at h
  exact h

/-- the value of (J11) at a vertex b < 2^23, at a live channel and at a dead one -/
theorem j11_val {b : ℕ} (hb : b < 2 ^ 23) :
    (j11Fam g tok).val fmtRef x₀ W A b =
      if b / 2 ^ 10 < DF.d then
        FFSeg.idnVal DF (tA g A) (embOf W) (tok x₀) (.j11 (b / 2 ^ 10) (b % 2 ^ 10))
      else 0 := by
  rw [j11_raw]
  have hterm : ∀ t ∈ range (2 ^ 18), κ11 tok x₀ (b * 2 ^ 18 + t) *
        (aEmb σT σJ).at fmtRef W (vtx 41 (b * 2 ^ 18 + t)) =
      if t = tok x₀ (b % 2 ^ 10) then
        (if t < 202048 ∧ b / 2 ^ 10 < DF.d then embOf W t (b / 2 ^ 10) else 0)
      else 0 := by
    intro t ht
    have ht' : t < 2 ^ 18 := mem_range.mp ht
    have e1 : (b * 2 ^ 18 + t) % 2 ^ 18 = t := by omega
    have e2 : (b * 2 ^ 18 + t) / 2 ^ 18 = b := by omega
    unfold κ11
    rw [e1, e2]
    by_cases h1 : t = tok x₀ (b % 2 ^ 10)
    · by_cases h2 : t < 202048 ∧ b / 2 ^ 10 < DF.d
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, one_mul, emb_at W hb h2.1]
      · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2, zero_mul]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]
  rw [sum_congr rfl hterm, sum_ite_eq' (range (2 ^ 18)) (tok x₀ (b % 2 ^ 10))]
  unfold a11
  by_cases hd : b / 2 ^ 10 < DF.d
  · rw [if_pos hd, if_pos hd, val_cXS]
    show _ =
      FFSeg.xS DF (tA g A) 0 (b / 2 ^ 10) (b % 2 ^ 10) - embOf W (tok x₀ (b % 2 ^ 10)) (b / 2 ^ 10)
    refine congrArg (fun z => FFSeg.xS DF (tA g A) 0 (b / 2 ^ 10) (b % 2 ^ 10) - z) ?_
    by_cases hV : tok x₀ (b % 2 ^ 10) < 202048
    · rw [if_pos (mem_range.mpr (lt_trans hV (by norm_num))), if_pos ⟨hV, hd⟩]
    · have hz : embOf (E := Cb.Gl.E) W (tok x₀ (b % 2 ^ 10)) (b / 2 ^ 10) = 0 := by
        unfold embOf FFSeg.embR FFSeg.matR
        rw [if_neg (fun h => hV h.1), map_zero]
      rw [hz]
      split_ifs with h1 h2
      · exact absurd h2.1 hV
      · rfl
      · rfl
  · rw [if_neg hd, if_neg hd, val_cK]
    split_ifs with h1 h2
    · exact absurd h2.2 hd
    · simp
    · simp

theorem j11_wf : (j11Fam g tok).WF fmtRef := by
  refine ⟨fun t ht j hj => ?_, fun j hj => ?_⟩
  · show j < 2
    rcases List.mem_cons.1 ht with rfl | ht
    · obtain rfl : j = 0 := by simpa using hj
      norm_num
    · obtain rfl : t = ⟨fun _ _ => -1, [1]⟩ := by simpa using ht
      obtain rfl : j = 1 := by simpa using hj
      norm_num
  · have hj : j < 2 := hj
    interval_cases j
    · exact trivial
    · refine ⟨rfl, fun t ht i hi => ?_, fun _ _ => ?_⟩
      · obtain rfl : t = ⟨κ11 tok, [0]⟩ := by simpa [j11Inner] using ht
        obtain rfl : i = 0 := by simpa using hi
        exact Nat.one_pos
      · exact (tok_ok 41 σT σJ (run_length _ _)
          (by rw [show σJ.length = 13 from run_length _ _]; norm_num)
          (ok_append (ok_run (by norm_num)) (ok_run (by norm_num)) fun u hu u' hu' => by
            have := mem_vars_run.1 hu
            have := mem_vars_run.1 hu'
            omega)).1

theorem j11_places : ∀ p ∈ (j11Fam g tok).places, IsFF g p := by
  rintro p ⟨j, hj, hp⟩
  have hj : j < 2 := hj
  interval_cases j
  · obtain ⟨b, hb, t, ht, rfl⟩ := hp
    have hb : b < 2 ^ (13 + 10) := hb
    have : InFF g (a11 g b) :=
      AllPl.ite (fun hd => inFF_cXS g (Nat.zero_le _) hd (dec2_lt hb).2) fun _ => AllPl.cK _
    exact this _ (List.mem_map_of_mem ht)
  · obtain ⟨i, _, hp⟩ := hp
    exact hp.elim

/-- All identities of the feed-forward segment of group g. -/
def idnFams : List (Cb.Fam X Cb.Gl.E) :=
  (List.range 17).map (fun k => jnFam g k) ++ [j10Fam g] ++ (if g = 0 then [j11Fam g tok] else [])

theorem mem_idnFams (f : Cb.Fam X Cb.Gl.E) :
    f ∈ idnFams g tok ↔ (∃ k < 17, f = jnFam g k) ∨ f = j10Fam g ∨ (g = 0 ∧ f = j11Fam g tok) := by
  unfold idnFams
  rw [List.mem_append, List.mem_append, List.mem_map, List.mem_singleton, or_assoc]
  refine or_congr
    ⟨fun ⟨k, hk, e⟩ => ⟨k, List.mem_range.1 hk, e.symm⟩,
      fun ⟨k, hk, e⟩ => ⟨k, List.mem_range.2 hk, e.symm⟩⟩
    (or_congr Iff.rfl ?_)
  split_ifs with h0
  · simp [h0]
  · simp [h0]

/-- The identities have what the theorems on `ffSpec` require (`IdnOK`). -/
theorem idn_ok : IdnOK fmtRef g (decide (g = 0)) tok (idnFams g tok) where
  iff := fun x₀ W A => by
    constructor
    · intro h j hj
      cases j with
      | jn k ν i =>
        obtain ⟨hk, hν, hi⟩ : k < 17 ∧ ν < DF.nNu ∧ i < DF.T := hj
        have h1 := h (jnFam g k) ((mem_idnFams g tok _).2 (Or.inl ⟨k, hk, rfl⟩))
          (ν * 2 ^ 10 + i) (enc2_lt (n := 3) hν hi)
        rwa [jn_val g fmtRef x₀ W A (embOf W) (tok x₀) hk, (enc2 hi).1, (enc2 hi).2] at h1
      | j10 l' i =>
        obtain ⟨hl, hi⟩ : l' < DF.ne ∧ i < DF.T := hj
        have h1 := h (j10Fam g) ((mem_idnFams g tok _).2 (Or.inr (Or.inl rfl)))
          (l' * 2 ^ 10 + i) (enc2_lt (n := 1) hl hi)
        rwa [j10_val g fmtRef x₀ W A (embOf W) (tok x₀), (enc2 hi).1, (enc2 hi).2] at h1
      | j11 j i =>
        obtain ⟨h0, hjd, hi⟩ : decide (g = 0) = true ∧ j < DF.d ∧ i < DF.T := hj
        have hj13 : j < 2 ^ 13 := lt_trans hjd (by decide)
        have h1 := h (j11Fam g tok)
          ((mem_idnFams g tok _).2 (Or.inr (Or.inr ⟨of_decide_eq_true h0, rfl⟩)))
          (j * 2 ^ 10 + i) (enc2_lt (n := 13) hj13 hi)
        rwa [j11_val g tok x₀ W A (enc2_lt (n := 13) hj13 hi), (enc2 hi).1,
          (enc2 hi).2, if_pos hjd] at h1
    · intro h f hf b hb
      rcases (mem_idnFams g tok f).1 hf with ⟨k, hk, rfl⟩ | rfl | ⟨h0, rfl⟩
      · have hb : b < 2 ^ (3 + 10) := hb
        rw [jn_val g fmtRef x₀ W A (embOf W) (tok x₀) hk]
        exact h _ ⟨hk, (dec2_lt hb).1, (dec2_lt hb).2⟩
      · have hb : b < 2 ^ (1 + 10) := hb
        rw [j10_val g fmtRef x₀ W A (embOf W) (tok x₀)]
        exact h _ ⟨(dec2_lt hb).1, (dec2_lt hb).2⟩
      · have hb : b < 2 ^ (13 + 10) := hb
        rw [j11_val g tok x₀ W A hb]
        split_ifs with hd
        · exact h _ ⟨decide_eq_true h0, hd, (dec2_lt hb).2⟩
        · rfl
  wf := fun f hf => by
    rcases (mem_idnFams g tok f).1 hf with ⟨k, _, rfl⟩ | rfl | ⟨_, rfl⟩
    · exact jn_wf g fmtRef k
    · exact j10_wf g fmtRef
    · exact j11_wf g tok
  places := fun f hf => by
    rcases (mem_idnFams g tok f).1 hf with ⟨k, _, rfl⟩ | rfl | ⟨_, rfl⟩
    · exact jn_places g k
    · exact j10_places g
    · exact j11_places g tok

end Cm.Seg.TS
