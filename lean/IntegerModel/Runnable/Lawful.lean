-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/Lawful.lean: the array program's check "lawful" compared with the library's
Lawful
(Inst/Model/Scales.lean).
The library's Lawful also bounds the three numbers of the acceptance policy, which are not part of
the model and which the program does not have; this file's lawful_iff lists them separately.
-/
import IntegerModel.Runnable.Defs
import Inst.Model.Scales

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

theorem norm_lawful_iff (n : NormPar) : (normOf n).lawful = true ↔ n.OK ∧ n.K ≤ n.M := by
  simp only [ArrayProgram.Norm.lawful, normOf, NormPar.OK, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem scales_lawful_iff (s : LayerScale) :
    (scalesOf s).lawful = true ↔
    FFSeg.Ranges s ∧ (4 ≤ s.sh ∧ s.sh ≤ 12) ∧ s.n1.K ≤ s.n1.M ∧ s.n2.K ≤ s.n2.M := by
  have h1 := norm_lawful_iff s.n1
  have h2 := norm_lawful_iff s.n2
  constructor
  · intro h
    simp only [ArrayProgram.LayerScales.lawful, scalesOf, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩,
                                a13⟩,
                              a14⟩,
                            a15⟩,
                          a16⟩,
                        a17⟩,
                      a18⟩,
                    a19⟩,
                  a20⟩,
                a21⟩,
              b1⟩,
            b2⟩,
          c1⟩,
        c2⟩ := h
    exact ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩, a5, ⟨a6, a7⟩, ⟨a8, a9⟩, ⟨a10, a11⟩, ⟨a12, a13⟩, ⟨a14, a15⟩,
        ⟨a16, a17⟩, ⟨a18, a19⟩, ⟨a20, a21⟩, (h1.1 b1).1, (h2.1 b2).1⟩,
      ⟨c1, c2⟩, (h1.1 b1).2, (h2.1 b2).2⟩
  · rintro ⟨r, ⟨c1, c2⟩, k1, k2⟩
    simp only [ArrayProgram.LayerScales.lawful, scalesOf, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨r.kq.1, r.kq.2⟩, r.kk.1⟩, r.kk.2⟩, r.qk⟩, r.kv.1⟩, r.kv.2⟩,
                                        r.ko.1⟩,
                                      r.ko.2⟩,
                                    r.kg.1⟩,
                                  r.kg.2⟩,
                                r.kg'.1⟩,
                              r.kg'.2⟩,
                            r.ku.1⟩,
                          r.ku.2⟩,
                        r.ku'.1⟩,
                      r.ku'.2⟩,
                    r.kd.1⟩,
                  r.kd.2⟩,
                r.kr.1⟩,
              r.kr.2⟩,
            h1.2 ⟨r.n1, k1⟩⟩,
          h2.2 ⟨r.n2, k2⟩⟩,
        c1⟩,
      c2⟩

theorem kap_lt (s : ScalesAndPolicy) {L : ℕ} (h : L < 48) : s.kap L = (s.w ⟨L, h⟩).scale := dif_pos h

/-- At modelShape, on the renamed settings of a table s: the program's test is the library's Lawful
but for the policy's three numbers -/
theorem lawful_iff (s : ScalesAndPolicy) :
    Lawful s ↔
    ArrayProgram.lawful ArrayProgram.modelShape (settingsOf s.kap s.nf) = true ∧
    (s.pol.C < 2 ^ 32 ∧ s.pol.theta ≤ s.pol.C ∧ s.pol.cap ≤ 1024) := by
  have e : ArrayProgram.lawful ArrayProgram.modelShape (settingsOf s.kap s.nf) = true ↔
      (∀ L < 48, (scalesOf (s.kap L)).lawful = true ∧ (s.kap L).sh = (s.kap (4 * (L / 4))).sh) ∧
      (normOf s.nf).lawful = true := by
    simp only [ArrayProgram.lawful, ArrayProgram.modelShape, settingsOf, scalesOf, Bool.and_eq_true,
      List.all_eq_true, List.mem_range, beq_iff_eq]
  rw [e]
  constructor
  · intro h
    refine ⟨⟨fun L hL => ⟨(scales_lawful_iff _).2 ?_, ?_⟩, (norm_lawful_iff _).2 ⟨h.nf, h.km.2⟩⟩,
      h.pol⟩
    · rw [kap_lt s hL]
      exact ⟨h.ff ⟨L, hL⟩, h.sh ⟨L, hL⟩, h.km.1 ⟨L, hL⟩⟩
    · have := h.one ⟨L / 4, by omega⟩ ⟨L % 4, by omega⟩
      simp only at this
      rwa [Nat.div_add_mod] at this
  · rintro ⟨⟨a, b⟩, p⟩
    have hw : ∀ L : Fin 48,
        FFSeg.Ranges (s.w L).scale ∧
        (4 ≤ (s.w L).scale.sh ∧ (s.w L).scale.sh ≤ 12) ∧
        (s.w L).scale.n1.K ≤ (s.w L).scale.n1.M ∧
        (s.w L).scale.n2.K ≤ (s.w L).scale.n2.M := fun L => by
      have := (scales_lawful_iff _).1 (a L.val L.isLt).1
      rwa [kap_lt s L.isLt] at this
    refine ⟨⟨fun L => (hw L).1, fun L => (hw L).2.1, fun g l => ?_, ((norm_lawful_iff _).1 b).1, p⟩,
      fun L => (hw L).2.2,
      ((norm_lawful_iff _).1 b).2⟩
    have := (a (4 * g.val + l.val) (by omega)).2
    rwa [show (4 * g.val + l.val) / 4 = g.val by omega] at this

end IntegerModel.Runnable
