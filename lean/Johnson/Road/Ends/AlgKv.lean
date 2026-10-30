-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgKv.lean: one call's factor in the layers' join, with the products left out,
beside G.lean's terms.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (vec_kvOf) the library's vector of a call with the affine parts of its keys (vecF at lin,
Johnson/Road/Ends/AlgVec.lean) is G.lean's key vector of that call with the products left out, kvOf
P (affG ..) q, at every index below 2^(a_c).
(alg_call) **The call's factor with the products left out, over G.lean's terms**: under the record
Fits (every read that the forms name has its rule value at this world; and public numbers), TiesG
(Johnson/Road/Ends/AlgLin.lean), what Johnson/Road/FormsKeysKF.lean asks of the call (CallFits,
SegFits; four clauses on the call's point), and four public clauses more (cd is P's call q; as many
tokens; the verifier's padding key, read by ρ and as the tauN of
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean, is the library's): the form that the verifier's Env.joinPart
returns for call q is worth alpha - q theta - the extension of kvOf P (affG P g cell) q at the
call's own point zk[q].
Does not say: anything on the products in the keys; that a run's reads have their rule values; that
a layout's calls meet CallFits and SegFits (callFits_of_layout, Johnson/Road/FormsKeysKV.lean).
Mind: CallFits holds cd.lJ = lJ D cc, which needs the premise hfl (the verifier's least number of
columns passes the library's for no call). By the head of Johnson/Road/FormsKeysWhole.lean hfl fails
at the small example's shape for four calls: to those four calls vec_kvOf and alg_call do not apply
there. At the full-size example's shape and the library's reference sizes hfl is a theorem (hfl_ref,
Johnson/Road/FormsKeysRef.lean).
-/
import Johnson.Road.Ends.AlgVec
import Johnson.Road.Ends.AlgLin

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
open Inst.Model.FFSeg (Dim Cell Fam LW lin len call pos lJ aC famAt fams present isExp lut)
open Inst.Model.FFSeg.IndexFacts (mem_fams_iff famAtPos)

/-- G.lean's vector of a call, its lets written out. -/
theorem kvOf_eq {R : Type} [CommRing R] (P : Model.Layer.Pub) (f : String → ℕ → ℕ → ℕ → R)
    (q X : ℕ) :
    G.kvOf P f q X =
      match G.colG P.y q (X / P.y.T % 2 ^ (P.y.calls.getD q default).lJ) with
      | some (s, x) =>
        if (s.moe && X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ % 2 == 0) = true then
          (tauN P.y.fo q (t0N P.y.fo q) : R)
        else f s.name (X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ) x (X % P.y.T)
      | none => (tauN P.y.fo q (t0N P.y.fo q) : R) := rfl

/-- A family that exists on layers with experts alone is absent exactly on the even layers. -/
theorem moe_present (s : Fam) (lam : ℕ) : (isExp s && lam % 2 == 0) = !present s lam := by
  unfold present Inst.Model.FFSeg.isExpL
  rcases Nat.mod_two_eq_zero_or_one lam with h | h <;> cases isExp s <;> simp [h]

section Kv

variable {K : Type} [Field K] [scl : Scl] {v : Env} {D : Dim} {t : Cell → K}
  {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K}

/-- **The two vectors are one.** -/
theorem vec_kvOf (T : TiesG P g cell D t) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {q : ℕ}
    {cd : CallD} {weighed : Array Bool} {cc : Fin 8} {fam : Seg → Fam}
    (C : CallFits v D cd weighed cc fam) (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    (hpad : ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K) = (((lut tb cc).pad : ℤ) : K))
    (X : ℕ) (hX : X < 2 ^ aC D cc) :
    vecF D tb (lin D t tb L0 w) cc X = G.kvOf P (G.affG P g cell) q X := by
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
  generalize X % D.T = i
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
      show (if present (fam s0) lam = true then lin D t tb L0 w (fam s0) lam x0 i
          else (((lut tb cc).pad : ℤ) : K)) =
        if (s0.moe && lam % 2 == 0) = true then ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K)
        else G.affG P g cell s0.name lam x0 i
      rw [S.moe, moe_present]
      by_cases hp : present (fam s0) lam = true
      · rw [if_pos hp, hp, if_neg (by decide), S.name]
        exact T.lin_affG tb L0 w (fam s0) lam x0 i hlam hp
      · have hp' : present (fam s0) lam = false := by simpa using hp
        rw [if_neg hp, hp', if_pos (by decide)]
        exact hpad.symm

end Kv

section Call

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K} {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K}

/-- **The call's factor with the products left out, over G.lean's terms.** -/
theorem alg_call (F : Fits ρ W v D c t low u) (T : TiesG P g cell D t) (tb : Tables)
    (alpha theta : E) (q : ℕ) (cd : CallD) (weighed : Array Bool) (cc : Fin 8) (fam : Seg → Fam)
    (C : CallFits v D cd weighed cc fam) (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) (hls : v.y.ls ≤ cd.lJ)
    (hlow : ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    (hu : ∀ j, j < D.lT → u j = pt ρ (v.zk.getD q #[]) (D.lL + lJ D cc + j))
    (hpad : ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) =
      (((lut tb cc).pad : ℤ) : K))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    (hpadG : ((tauN P.y.fo q (t0N P.y.fo q) : ℕ) : K) = (((lut tb cc).pad : ℤ) : K))
    {f : Aff} (h : v.joinPart alpha theta q cd weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      Blocks.ext (aC D cc) (G.kvOf P (G.affG P g cell) q) (pt ρ (v.zk.getD q #[])) := by
  rw [joinPart_linVec F tb 0
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩)
    alpha theta q cd weighed cc fam C HS hzk hls hlow hu hpad h]
  congr 1
  exact Blocks.ext_congr (fun X hX => vec_kvOf T tb _ _ C HS hcd hT hpadG X hX) _

end Call

#print axioms vec_kvOf
#print axioms alg_call

end OnBytes.Road.Alg
