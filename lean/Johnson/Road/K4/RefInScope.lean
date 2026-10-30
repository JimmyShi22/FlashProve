-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefInScope.lean: THE RECORD `RefPub X g` (Johnson/Road/K4/RefPub.lean) HOLDS AT ALL
PUBLIC FILES IN THE GOALS' SCOPE, FOR EVERY GROUP BELOW 12, WITH NO BOOLEAN TEST AS A PREMISE: from
VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp and publicOf Z.pol Z.KL lay = .ok X. So the
premise `RefPub` of the statements on K4's block at the reference value (`refP_meets`,
`refP_valueIs`, `refP_hk`, `refP_lines_pub`, `refP_rope`) is a theorem there; their other premises
stay (the place holds the record's layers and the group's plan; in the first two: the group is not
the first; in the second and third: the section's table of scales is `sclX X g`). The lines and the
rotary tables' fit are `Meaning.P34.pub34_all` (Johnson/Goal/Meaning/Pub34All.lean),
field for field. NEW HERE: that K4's text covers the record.

  `readsOf_tsc`: the list of calls with terms in the second token sumcheck, as `readsOf` makes it.
  `zipFilter_ne`: a list zipped with its image, filtered on the image's members that are not empty,
    is not empty where some member of the image is not empty.
  `covers_of_lines`: `covers P` (OnBytes/Desc/First/K4/Rounds.lean: five limbs; routed experts;
    ll > 1; lNI ≠ 0; the second token sumcheck is not empty) from the layout's and the reads'
    returns, `Switches`, 1 < ll and "the eight lines of calls are the library's" (`LinesAre`). The
    fifth clause is an evaluation of the library's eight lines by Lean's kernel.
  `refPub_in_scope`: the record.
  `scope_lt`: a group that has a plan is below 12. `scope_la`: the shape's number la is 16 (the
    premise hla of the first group's `refF_meets`, Johnson/Road/K4/RefValueFirst.lean).
    `scope_cap`: the reference cap is the shape's lidb.

Limits. THE PUBLIC SIDE ALONE. Not claimed: that the three facts hold together at any files (the
heads of Johnson/Goal/Meaning/); that `recordB` or `tablesB` says true in the scope: no statement
of this library concludes that: in its code the two names stand in definitions, premises and a
run's text alone; one clause of `recordB` (that `layTables` returns at the group's own list of
matrices) is not shown of any files here. No soundness is concluded.
-/
import Johnson.Road.K4.RefPub
import Johnson.Goal.Meaning.HearPremises
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Lay Pub Reads HPlan2 layout readsOf readsR)
open OnBytes.Model.Verify (Public publicOf layerShape)
open Inst.Model (tbRef)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim fams)
open OnBytes.Desc.First.K4 (covers)

/-! ### K4's text covers a record with the library's lines -/

/-- The calls with terms in the second token sumcheck, as `readsOf` makes the list. -/
theorem readsOf_tsc {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    rd.tscCalls = ((y.calls.toList.zip
      (y.calls.toList.map fun c => c.segs.flatMap fun s => readsR y.h.p3 s.name)).filter
        fun x => !x.2.isEmpty).map (·.1.name) := by
  unfold Layer.readsOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    rfl

/-- Where some member of the image is not empty, the filtered list is not empty. -/
theorem zipFilter_ne {α β γ : Type} (f : α → List β) (g : α × List β → γ) :
    ∀ l : List α, ((l.map f).any fun r => !r.isEmpty) = true →
      (((l.zip (l.map f)).filter fun x => !x.2.isEmpty).map g).isEmpty = false
  | [], h => by simp at h
  | a :: l, h => by
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true] at h
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons]
    cases hfa : (f a).isEmpty with
    | false => simp
    | true =>
      simp only [hfa, Bool.not_true, Bool.false_eq_true, if_false, false_or] at h ⊢
      exact zipFilter_ne f g l h

/-- **K4's text covers a public record with the library's eight lines of calls.** -/
theorem covers_of_lines {hS : Layer.Shape} {pc : List (List String)} {P : Pub}
    (hy : layout hS pc = .ok P.y) (S : Switches hS) (hll : 1 < hS.ll)
    (hrd : readsOf P.y = .ok P.rd) (hN : LinesAre P.y) : covers P = true := by
  have L := laySizes_of_layout hy
  have two : 2 * 2 ^ hS.ll = 2 ^ (hS.ll + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have eN : P.rd.lNI = hS.ll + 1 := by
    rw [Model.Fit.readsOf_lNI hrd, L.NI, two, ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide)]
  have eR : (P.y.calls.toList.map fun c => c.segs.flatMap fun s => readsR P.y.h.p3 s.name) =
      (P.y.calls.toList.map fun cd => cd.segs.map (·.name)).map
        fun ns => ns.flatMap (readsR P.y.h.p3) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    simp only [Function.comp, List.flatMap_map]
  have eT : P.rd.tscCalls.isEmpty = false := by
    rw [readsOf_tsc hrd]
    apply zipFilter_ne
    rw [eR, hN, L.shape, S.p3]
    rfl
  unfold covers
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [L.shape, S.xl]
    rfl
  · rw [L.shape]
    exact S.p3
  · rw [L.shape]
    exact decide_eq_true hll
  · rw [eN]
    simp
  · rw [eT]
    rfl

/-! ### The goals' scope -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- **THE DOOR WITH NO TEST: `RefPub` at all public files in the goals' scope**, for every group
below 12. -/
theorem refPub_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) : RefPub X g := by
  obtain ⟨⟨hy, S, hs, hrd, Zd, hc, hN, hfl, Zw, hsL, hlw, h4⟩, hN12, ⟨s0, pub, hs0, efo⟩, hT, hM,
    hpad, R⟩ := Meaning.P34.pub34_all hZ hR h gl_numerals
  exact {
    lines := fun hp hG => ⟨s0, fun _ =>
      { hy := hy
        S := S
        hs := hs
        hg := by
          show g < X.y.NGr
          rw [hN12]
          exact hg
        hrd := hrd
        hmats := hM g
        hρ := gl_numerals
        Z := Zd
        hc := hc
        hN := hN
        hfl := hfl
        hs0 := hs0
        Zw := Zw
        hsL := hsL
        hlw := hlw
        h4 := h4
        htm := (hT g hp hG).1
        hNM := (hT g hp hG).2
        hpad := hpad }, pub, efo⟩
    rope := fun v vy vsc vg rs rt lam hl => by
      have y := R { v := v, wsLay := X.layers.wsLay, rope := X.layers.rope, rs := rs, rt := rt }
        vy vsc rfl (by show v.g < 12; rw [vg]; exact hg) lam
        (by show lam < v.y.Lam; rw [vy]; exact hl)
      have e : v.g * v.y.Lam = g * X.layers.y.Lam := by rw [vg, vy]
      have y' : RopeFits Reading.gl
          { v := v, wsLay := X.layers.wsLay, rope := X.layers.rope, rs := rs, rt := rt } Dim.ref
          tbRef (v.g * v.y.Lam) lam := y
      rw [e] at y'
      exact y'
    covers := covers_of_lines (P := X.layers) hy S
      (Nat.lt_of_lt_of_eq (by decide : 1 < Dim.ref.lL) Zd.lL) hrd hN }

/-- A group that has a plan is below 12, in the goals' scope. -/
theorem scope_lt (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} {hp : HPlan2} (hG : X.G[g]? = some hp) :
    g < 12 := by
  have e : X.y.NGr = 12 := (Meaning.P34.pub34_all hZ hR h gl_numerals).2.1
  have l : g < X.y.NGr := _root_.Fo.PlaneMatG.public_G_lt h hG
  rw [e] at l
  exact l

/-- The shape's number la is 16, in the goals' scope. -/
theorem scope_la (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : (layerShape X.P).la = 16 :=
  (Hd.core_of_scope hZ hR h).num 12

/-- The reference cap is the shape's lidb, in the goals' scope. -/
theorem scope_cap (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Dim.ref.cap = (layerShape X.P).lidb :=
  (Meaning.P34.pub34_all hZ hR h gl_numerals).1.2.2.2.2.2.1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.covers_of_lines
#print axioms OnBytes.Road.K4.refPub_in_scope
#print axioms OnBytes.Road.K4.scope_lt
#print axioms OnBytes.Road.K4.scope_la
#print axioms OnBytes.Road.K4.scope_cap
