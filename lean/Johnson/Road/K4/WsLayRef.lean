-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WsLayRef.lean: TWO NUMBERS OF THE COMMITTED TABLE's LAYOUT ARE THE REFERENCE ONES:
its number of column bits is kRef and its number of rows is hRef (Inst/Model/Layout.lean), wherever
the structure RefPub (Johnson/Road/K4/RefPub.lean) holds of the public parameters X at a group g
that has an entry in X.G.

  `lk_ref`: kRef = X.layers.wsLay.lk. Premises: B : RefPub X g · hg : X.G[g]? = some hp (RefPub's
    field lines speaks under that fence alone).
  `wsRef D`: the shape of the committed table at the nine reference sizes, D a letter.
  `wsLayOf_ref`: at a shape with these nine sizes wsLayOf is wsLayOf at wsRef of the shape's own D:
    the three other fields are written over before they are read.
  `rowsRefB D`: a closed test: wsLayOf returns at wsRef D and kRef, with hRef rows.
  **`rowsRef_2048`**, **`rowsRef_32`**: BY LEAN's KERNEL: true at both values of D that
    WsLay.build lets pass. `rowsRef_fewer`: A NEGATIVE TEST: with two layers fewer wsLayOf still
    RETURNS a layout, and its number of rows is another (a refusal would not pass for it).
  `rows_ref`: where wsLayOf returns lay at a shape with the nine sizes and kRef: hRef = lay.m0.
  **`m0_ref`**: hRef = X.layers.wsLay.m0. Premises: as lk_ref's.
No new argument: wsLayOf_units (Johnson/Road/FormsKeysWLay.lean) has the column bits and "D is 2048
or 32"; the rows are an evaluation.
Limits. RefPub is a premise (a theorem in the goals' scope has it elsewhere). The reference sizes
alone. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.RefPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model (WsShape WsLay wsLayOf wsSetMoe)
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Verify (Public)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (Dim)

/-- The shape of the committed table at the nine reference sizes. -/
def wsRef (D : ℕ) : WsShape :=
  { D := D, L := Dim.ref.P.layers, d := Dim.ref.P.d, dh := Dim.ref.P.ch,
    dkv := Dim.ref.P.nkv * Dim.ref.P.ch, dq := Dim.ref.P.nq * Dim.ref.P.ch, f := Dim.ref.P.f,
    fe := Dim.ref.P.fe, NE := Dim.ref.P.nexp, V := Dim.ref.P.V }

/-- At a shape with the nine sizes wsLayOf is wsLayOf at wsRef. -/
theorem wsLayOf_ref {s : WsShape} (Zw : SizedW s Dim.ref.P) (k : ℕ) :
    wsLayOf s true k = wsLayOf (wsRef s.D) true k := by
  obtain ⟨D, L, d, dh, dkv, dq, f, fe, NE, V, eh, MOE, moe⟩ := s
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Zw
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  rfl

/-- A closed test: wsLayOf returns at wsRef D and kRef, with hRef rows. -/
def rowsRefB (D : ℕ) : Bool :=
  match wsLayOf (wsRef D) true kRef with
  | .ok lay => lay.m0 == hRef
  | .error _ => false

set_option maxRecDepth 1000000 in
theorem rowsRef_2048 : rowsRefB 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rowsRef_32 : rowsRefB 32 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: with two layers fewer a layout is returned, and its rows are other. -/
theorem rowsRef_fewer :
    (match wsLayOf { wsRef 2048 with L := Dim.ref.P.layers - 2 } true kRef with
      | .ok lay => lay.m0 != hRef
      | .error _ => false) = true := by
  decide +kernel

/-- Where wsLayOf returns at a shape with the nine sizes and kRef, the rows are hRef. -/
theorem rows_ref {s : WsShape} {lay : WsLay} (Zw : SizedW s Dim.ref.P)
    (h : wsLayOf s true kRef = .ok lay) : hRef = lay.m0 := by
  have hD : s.D = 2048 ∨ s.D = 32 := (wsLayOf_units h).2.2.2.D
  rw [wsLayOf_ref Zw] at h
  rcases hD with e | e
  · rw [e] at h
    have t := rowsRef_2048
    unfold rowsRefB at t
    rw [h] at t
    exact (beq_iff_eq.1 t).symm
  · rw [e] at h
    have t := rowsRef_32
    unfold rowsRefB at t
    rw [h] at t
    exact (beq_iff_eq.1 t).symm

variable {X : Public} {g : ℕ} {hp : HPlan2}

/-- **The column bits are the reference's.** -/
theorem lk_ref (B : RefPub X g) (hg : X.G[g]? = some hp) : kRef = X.layers.wsLay.lk := by
  obtain ⟨_, H, _⟩ := B.lines hp hg
  exact (wsLayOf_units (H #[]).hlw).1.symm

/-- **The rows are the reference's.** -/
theorem m0_ref (B : RefPub X g) (hg : X.G[g]? = some hp) : hRef = X.layers.wsLay.m0 := by
  obtain ⟨_, H, _⟩ := B.lines hp hg
  exact rows_ref (H #[]).Zw (H #[]).hlw

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.wsLayOf_ref
#print axioms OnBytes.Road.K4.rowsRef_2048
#print axioms OnBytes.Road.K4.rowsRef_32
#print axioms OnBytes.Road.K4.rowsRef_fewer
#print axioms OnBytes.Road.K4.rows_ref
#print axioms OnBytes.Road.K4.lk_ref
#print axioms OnBytes.Road.K4.m0_ref
