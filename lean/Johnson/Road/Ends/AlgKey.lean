-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgKey.lean: the library's key vector of a call, beside G.lean's kvG.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (vec_kvOf_any) AlgKv.lean's vec_kvOf for ANY two functions that agree family by family, on
the entries below a family's length.
(keyVec_kvG) **THE LIBRARY's KEY VECTOR OF A CALL IS G.lean's kvG**, at every index below 2^(a_c):
with AlgGam.lean's key_segG and AlgCongr.lean's key_congr_w | key_congr_tb. The library's weights w
need agree with G.lean's (wOfG) INSIDE THE MATRICES' RANGES ALONE (AgreeW): the library's layerR is
0 outside them, wOfG is not; likewise the rotary tables (AgreeT).
(ext_keyVec_kvG) so their extensions at any point are one.
Under: TiesG; TiesW at the verifier's own rotary tables tbG P and at w := wOfG (AlgWit.lean's
tiesW_of_laid concludes it); AgreeW D w wOfG (AlgW.lean's agreeW_layerR concludes it for the
library's layerR); AgreeT D tb (tbG P) L0: the library's rotary tables are the verifier's inside
their ranges; f = 2 fe; a head has a width; what Johnson/Road/FormsKeysKF.lean asks of the call
(CallFits, SegFits); cd is P's call q; as many tokens; G.lean's padding key tauN is the library's.
Does not say: what a form of the verifier's is worth; that a key lies in its table.
-/
import Johnson.Road.Ends.AlgKv
import Johnson.Road.Ends.AlgGam
import Johnson.Road.Ends.AlgCongr
import Johnson.Road.Ends.AlgWit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open OnBytes.Ends
open OnBytes.Model (Reading World Aff Seg CallD)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW key len call pos lJ aC famAt fams present isExp lut keyVec)
open Inst.Model.FFSeg.IndexFacts (mem_fams_iff famAtPos)

section Kv

variable {K : Type} [Field K] [scl : Scl] {v : Env} {D : Dim} {t : Cell → K}
  {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K}

omit scl in
/-- **The two vectors are one**, for any two functions that agree family by family. -/
theorem vec_kvOf_any (tb : Tables) (Fk : Fam → ℕ → ℕ → ℕ → K) (f : String → ℕ → ℕ → ℕ → K)
    (hF : ∀ (s : Fam) (lam x i : ℕ), lam < D.nl → present s lam = true → x < len D s → i < D.T →
      Fk s lam x i = f (segName s) lam x i) {q : ℕ}
    {cd : CallD} {weighed : Array Bool} {cc : Fin 8} {fam : Seg → Fam}
    (C : CallFits v D cd weighed cc fam) (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    (hpad : ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K) = (((lut tb cc).pad : ℤ) : K))
    (X : ℕ) (hX : X < 2 ^ aC D cc) :
    vecF D tb Fk cc X = G.kvOf P f q X := by
  have h1 : X < D.T * (2 ^ lJ D cc * 2 ^ D.lL) := by
    calc X < 2 ^ (D.lL + lJ D cc + D.lT) := hX
      _ = D.T * (2 ^ lJ D cc * 2 ^ D.lL) := by
        unfold Dim.T
        ring
  have hlam : X / D.T / 2 ^ lJ D cc < D.nl := Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul h1)
  rw [kvOf_eq, hT, hcd, C.lJ]
  unfold vecF
  generalize X / D.T / 2 ^ lJ D cc = lam at hlam ⊢
  generalize X / D.T % 2 ^ lJ D cc = j
  have hiT : X % D.T < D.T := Nat.mod_lt X (Inst.Model.FFSeg.IndexFacts.T_pos D)
  generalize X % D.T = i at hiT ⊢
  cases hc : G.colG P.y q j with
  | none =>
    have hf : famAt D cc j = none := by
      cases hf : famAt D cc j with
      | none => rfl
      | some a =>
        exfalso
        obtain ⟨s', x⟩ := a
        obtain ⟨e1, e2, e3⟩ := (famAtPos D cc j s' x).mp hf
        have hm : s' ∈ fams cc := mem_fams_iff.mpr e1
        rw [← C.fams] at hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
        have S := HS s hs
        unfold G.colG at hc
        rw [hcd] at hc
        have h4 := List.findSome?_eq_none_iff.mp hc s hs
        have h5 : s.pos.findIdx? (· == j) = none := by
          cases h : s.pos.findIdx? (· == j) with
          | none => rfl
          | some a =>
            rw [h] at h4
            cases h4
        have hx : x < s.pos.size := by
          rw [S.size, S.n]
          exact e2
        have h6 := Array.findIdx?_eq_none_iff.1 h5 s.pos[x] (Array.getElem_mem hx)
        have h7 : s.pos.getD x 0 = j := by
          rw [C.pos s hs x e2]
          exact e3
        have h8 : s.pos[x] = j := by simpa [Array.getD, hx] using h7
        simp [h8] at h6
    rw [hf]
    exact hpad.symm
  | some a =>
    obtain ⟨s, x⟩ := a
    unfold G.colG at hc
    rw [hcd] at hc
    obtain ⟨s0, hs, h0⟩ := List.exists_of_findSome?_eq_some hc
    cases hx0 : s0.pos.findIdx? (· == j) with
    | none =>
      rw [hx0] at h0
      cases h0
    | some x0 =>
      rw [hx0] at h0
      have e : (s0, x0) = (s, x) := Option.some.inj h0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨hi, hp0, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx0
      have S := HS s0 hs
      have hxl : x0 < len D (fam s0) := by
        rw [← S.n, ← S.size]
        exact hi
      have hpos : pos D (fam s0) x0 = j := by
        rw [← C.pos s0 hs x0 hxl]
        simpa [Array.getD, hi] using hp0
      have hcall : call (fam s0) = cc :=
        mem_fams_iff.mp (by rw [← C.fams]; exact List.mem_map_of_mem hs)
      have hf : famAt D cc j = some (fam s0, x0) := (famAtPos D cc j _ _).mpr ⟨hcall, hxl, hpos⟩
      rw [hf]
      show (if present (fam s0) lam = true then Fk (fam s0) lam x0 i
          else (((lut tb cc).pad : ℤ) : K)) =
        if (s0.moe && lam % 2 == 0) = true then ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K)
        else f s0.name lam x0 i
      rw [S.moe, moe_present]
      by_cases hp : present (fam s0) lam = true
      · rw [if_pos hp, hp, if_neg (by decide), S.name]
        exact hF (fam s0) lam x0 i hlam hp hxl hiT
      · have hp' : present (fam s0) lam = false := by simpa using hp
        rw [if_neg hp, hp', if_pos (by decide)]
        exact hpad.symm

/-- **The library's key vector of a call is G.lean's kvG.** -/
theorem keyVec_kvG {tb : Tables} {L0 : ℕ} {w : ℕ → LW K} (T : TiesG P g cell D t)
    (Wt : TiesW P g cell D t (tbG P) L0 (wOfG P g cell)) (A : AgreeW D w (wOfG P g cell))
    (B : AgreeT D tb (tbG P) L0) (hffe : D.f = D.fe + D.fe) (hch : 0 < D.P.ch) {q : ℕ}
    {cd : CallD} {weighed : Array Bool} {cc : Fin 8}
    {fam : Seg → Fam} (C : CallFits v D cd weighed cc fam)
    (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    (hpad : ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K) = (((lut tb cc).pad : ℤ) : K))
    (X : ℕ) (hX : X < 2 ^ aC D cc) :
    keyVec D t tb L0 w cc X = G.kvG P g cell q X :=
  vec_kvOf_any tb (key D t tb L0 w) (G.segG P g cell)
    (fun s lam x i hl hp hx hi => ((key_congr_w t A hffe Wt.even tb L0 s hl hp hx i).trans
      (key_congr_tb t B Wt.even hch _ s hl hi x)).trans (Wt.key_segG T s lam x i hl hp))
    C HS hcd hT hpad X hX

/-- Their extensions at any point are one. -/
theorem ext_keyVec_kvG {tb : Tables} {L0 : ℕ} {w : ℕ → LW K} (T : TiesG P g cell D t)
    (Wt : TiesW P g cell D t (tbG P) L0 (wOfG P g cell)) (A : AgreeW D w (wOfG P g cell))
    (B : AgreeT D tb (tbG P) L0) (hffe : D.f = D.fe + D.fe) (hch : 0 < D.P.ch) {q : ℕ}
    {cd : CallD} {weighed : Array Bool} {cc : Fin 8}
    {fam : Seg → Fam} (C : CallFits v D cd weighed cc fam)
    (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    (hpad : ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K) = (((lut tb cc).pad : ℤ) : K))
    (ζ : ℕ → K) :
    Blocks.ext (aC D cc) (keyVec D t tb L0 w cc) ζ = Blocks.ext (aC D cc) (G.kvG P g cell q) ζ :=
  Blocks.ext_congr (fun X hX => keyVec_kvG T Wt A B hffe hch C HS hcd hT hpad X hX) ζ

end Kv

#print axioms vec_kvOf_any
#print axioms keyVec_kvG
#print axioms ext_keyVec_kvG

end OnBytes.Road.Alg
