-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Gated.lean: CONDITIONAL.

Not shown here. THE TWO LAYERS' OWN CLAIMS ARE PREMISES (r1, r2). The four end values' slots are
asked to hold the extensions of the library's maps at the layers' points; EndGround
(Johnson/Road/Rows/GatedEnds.lean) at each layer's point, that the public record's layout is the
environment's (hy), and seven equations and two inequalities between public numbers, powers of two
among them, are premises. gated2_start asks three equations and one inequality between public
numbers besides. No example is known. That an honest run leaves such a world is not shown.

THE CLAIMS OF THE TWO PRODUCT LAYERS OF THE GATED PRODUCTS ARE WORTH 0 (the format's groups 8 and
9; OnBytes/Desc/First/K4/Claims.lean), and the second layer's start form is worth the sum on which
the layer runs. At a free reading and a free world.

  endsForms_open   the two end claims of a product layer, opened.
  gated_zero       the field gated of FrontWorth (Johnson/Road/K4/WorthGroups.lean).
  gated2_start     the second layer's start form, where each routed layer's slot holds the honest
                   never-sent vector under the batched sumcheck's weights.

No property is claimed.
-/
import Johnson.Road.K4.WorthGroups
import Johnson.Road.Rows.GatedEndsProofs
import Johnson.Road.Rows.GatedStartsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Pub Ten downFrom)
open Inst.Model.FFSeg (Dim Cell lF lFe slV upV slV' upV')
open OnBytes.Road.Rows (EndGround endForm start2 hvOf)
open Blocks (ext)
open OnBytes.Desc.First.K4 (gatedForms endsForms)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  {D : Dim}

/-- The two end claims of a product layer, opened. -/
theorem endsForms_open {o : Level} {e : Array E} {tb rows blocks stride : ℕ} {lamOf : ℕ → ℕ}
    {first : ℕ} {l : List Aff} (h : endsForms v o e tb rows blocks stride lamOf first = some l) :
    ∃ ts tu aS aU, v.y.T_ "s" = some ts ∧ v.y.T_ "u" = some tu ∧
      endForm v tb ts e rows blocks stride lamOf first = some aS ∧
      endForm v tb tu e rows blocks stride lamOf first = some aU ∧
      l = [Aff.slot o.sL + aS, Aff.slot o.sR + aU] := by
  unfold endsForms at h
  obtain ⟨ts, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tu, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aS, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aU, a4, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨ts, tu, aS, aU, a1, a2, a3, a4, (Option.some.inj h).symm⟩

/-- **The claims of the two product layers.** hd, o2: the layers as they were heard. r1, r2: their
own claims. a1 to b2: what the four end values' slots hold. -/
theorem gated_zero {P : Pub} (hy : P.y = v.y) {hd o2 : Level} {hd2 : Option Level}
    (h2 : hd2 = some o2) {ts tu : Ten} {tbA tbB : ℕ}
    (hts : v.y.T_ "s" = some ts) (htu : v.y.T_ "u" = some tu)
    (hA : v.tabAt "af@Z_a" = some tbA) (hB : v.tabAt "af@Z_b" = some tbB)
    (GA : EndGround ρ W v D c t hd.r (D.lL + lF D - v.y.ls) tbA ts tu)
    (GB : EndGround ρ W v D c t o2.r (D.lL - 1 + lFe D - v.y.ls) tbB ts tu)
    (hla : v.y.h.la = v.y.ls + D.lT) (hls : v.y.ls ≤ lF D) (hls' : v.y.ls ≤ lFe D)
    (hLam : v.y.Lam = 2 ^ D.lL) (hf : v.y.h.f = 2 ^ lF D) (hPf : v.y.Pf = 2 ^ lF D)
    (hLamM : v.y.LamM = 2 ^ (D.lL - 1)) (hfe : v.y.h.fe = 2 ^ lFe D) (hDfe : D.fe = 2 ^ lFe D)
    (r1 : hd.row.value ρ W = 0) (r2 : o2.row.value ρ W = 0)
    (a1 : W.slot hd.sL = ext (D.lL + lF D + D.lT) (slV D t) (pt ρ hd.r))
    (a2 : W.slot hd.sR = ext (D.lL + lF D + D.lT) (upV D t) (pt ρ hd.r))
    (b1 : W.slot o2.sL = ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt ρ o2.r))
    (b2 : W.slot o2.sR = ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt ρ o2.r)) :
    ∀ l, gatedForms P v hd hd2 = some l → ∀ f ∈ l, f.value ρ W = 0 := by
  intro l h f hm
  subst h2
  unfold gatedForms at h
  obtain ⟨e, c1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tA, c2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, c3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, c4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, c5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB, c6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, c7, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : hd.row :: a ++ o.row :: b = l := Option.some.inj h
  obtain rfl : o2 = o := Option.some.inj c4
  obtain rfl : tbA = tA := Option.some.inj (hA.symm.trans c2)
  obtain rfl : tbB = tB := Option.some.inj (hB.symm.trans c6)
  rw [hy] at c1 c3 c5 c7
  obtain ⟨ts1, tu1, aS, aU, d1, d2, d3, d4, rfl⟩ := endsForms_open c3
  obtain ⟨ts2, tu2, bS, bU, d5, d6, d7, d8, rfl⟩ := endsForms_open c7
  obtain rfl : ts = ts1 := Option.some.inj (hts.symm.trans d1)
  obtain rfl : tu = tu1 := Option.some.inj (htu.symm.trans d2)
  obtain rfl : ts = ts2 := Option.some.inj (hts.symm.trans d5)
  obtain rfl : tu = tu2 := Option.some.inj (htu.symm.trans d6)
  obtain ⟨x1, x2⟩ := Rows.gatedFirstOut K ρ W v D c t hd tbA ts tu e aS aU GA hla hls hLam hf hPf
    (ok_of_toOption c1) d3 d4
  obtain ⟨y1, y2⟩ := Rows.gatedSecondOut K ρ W v D c t o2 tbB ts tu e2 bS bU GB hla hls' hLamM hfe
    hDfe (ok_of_toOption c5) d7 d8
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact r1
  · rw [x1, a1, sub_self]
  · rw [x2, a2, sub_self]
  · exact r2
  · rw [y1, b1, sub_self]
  · rw [y2, b2, sub_self]

/-- **The second product layer's start form** is worth the sum on which the layer runs. rs: the
batched sumcheck's challenges; rt: the second token sumcheck's end point; rhoM: the fresh point. -/
theorem gated2_start {rs rt rhoM : Array E} {u : ℕ → K} {sH1 LamM lfe : ℕ} (hlfe : lfe = lFe D)
    (hle : lfe ≤ rs.size) (hrho : rhoM.size = D.lL - 1) (hLam : LamM = 2 ^ (D.lL - 1))
    (hS : ∀ lm, lm < LamM → W.slot (sH1 + 1 + lm) =
      ∑ yv ∈ range (2 ^ lfe), eqR ρ rs 0 lfe yv * hvOf D t u (pt ρ rt) (1 + lm) yv) :
    (start2 LamM sH1 rhoM).value ρ W =
      ext (D.lL - 1 + lFe D + D.lT) (fun X => slV' D t X * upV' D t X)
        (pt ρ (rhoM ++ downFrom rs lfe ++ rt)) := by
  have e := Rows.gatedSecondIn K ρ W D t rs rt rhoM u sH1 LamM lfe hlfe hle hrho hLam
  rw [Finset.sum_eq_zero fun lm hlm => by
    rw [hS lm (Finset.mem_range.mp hlm), sub_self, mul_zero]] at e
  exact sub_eq_zero.mp e

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.endsForms_open
#print axioms OnBytes.Road.K4.W.gated_zero
#print axioms OnBytes.Road.K4.W.gated2_start
