-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartHeadProofs.lean: the statement of Cb/Part/LdPartHead.lean, proved
(`ldPartHead_step`): an unfolding of the request's relation at the builder's configuration
`P.cfB K Bt`.

Main names:
  `ldPartHead_matU`: under `P.Props p` and `Cf.ModelOK`, the matrix read off the message that holds
    the index i, whatever the pads, is i's (the partition's clause `idx`; an index's body holds
    it).
  `ldPartHead_world`: under `P.Props p`, the ties and `O'.pkR m`, the relaxed world of segment 0
    and the cells unpacked from the data with layer 0 overwritten agree at every place that a
    segment j < P.n reads (`(P.seg j).places`).

Limits: what the head of Cb/Part/LdPartHead.lean lists as not said is not said here either.
-/
import Cb.Part.LdPartHead
import Cb.Part.LdPartNextProofs

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)

theorem ldPartHead_matU {p : ℕ} (hP : P.Props p) (hM : Cf.ModelOK) (i : Cf.I) (η : Cf.conf.Pad) :
    P.matU (Cf.conf.hold i η) = P.matI i :=
  hP.idx _ i (hM.held i)

theorem ldPartHead_hold (K : LdPartPk) (Bt : LdPartBits P) (i : Cf.I) (η : Cf.Pad) :
    (P.cfB K Bt).conf.hold i η = Cf.conf.hold i η := by
  funext n
  show (P.cfB K Bt).hold i η n = Cf.hold i η n
  unfold LdCf.hold
  rcases n with ⟨r, j | q⟩ <;> rfl

theorem ldPartHead_held {p : ℕ} (hP : P.Props p) (U : Cf.conf.Msg)
    (i : Cf.I) (h : Cf.conf.held U = some i) : P.matU U = P.matI i := hP.idx _ i h

variable {K : LdPartPk} {p : ℕ} {S' : Sig E} {O' : LdPartOut E S'}
  {ov : S'.Msg → LdPartW E → LdPartW E} {St' : Type} {x' : St' → Cf.Xm}
  {bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop}
  {vld : St' → Cf.conf.Msg × S'.Msg → Prop}

theorem ldPartHead_world (hP : P.Props p) (hT : LdPartTie0 P K O' ov x' bitX vld) (m : S'.Msg)
    (w : LdPartW E) (hm : O'.pkR m) {j : ℕ} (hj : j < P.n) :
    ∀ q ∈ (P.seg j).places,
      P.world K 0 O' m w q.1 q.2.1 q.2.2 = P.cellsW K (ov m w) q.1 q.2.1 q.2.2 := by
  intro q hq
  have hr := (hP.reads j hj q hq).2
  unfold LdPartD.world
  by_cases h1 : q.1 ≤ 0
  · have e : q.1 = 0 := Nat.le_zero.1 h1
    rw [if_pos h1, e]
    rw [LdPartD.InShape, e] at hr
    exact hT.rdOwn m w hm q.2.1 q.2.2 hr.2.1 hr.2.2
  · rw [if_neg h1, ldPartNext_cellsW P K (hT.ovPk m w q.1 (by omega))]

end

theorem ldPartHead_step : Spec.ldPartHead_step := by
  intro F E _ _ _ _ Cf P K Bt p S' O' ov St' x' rc' f vld hP hM hT hx hrc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `fw`
    rintro ⟨x, rec⟩ y ⟨m, pi, w, g⟩ ⟨hE, i, η, hU, hF, hB, hL, hb, hC⟩
    have hW : P.matU pi.1.1 = P.matI i := by
      have e : pi.1.1 = Cf.conf.hold i η := hU.trans (ldPartHead_hold P K Bt i η)
      rw [e]
      exact ldPartHead_matU P hP hM i η
    have hX : O'.pkX m g := hT.pkX m w g (hL 0 hP.pos)
    refine ⟨by rw [hrc]; exact hE,
      ⟨⟨i, η, hU.trans (ldPartHead_hold P K Bt i η)⟩, hX, hB, fun j h1 h2 => ?_,
        fun j h1 h2 => ?_, fun j _ h2 => ?_⟩,
      ?_, ?_⟩
    · have := hL j h2
      rwa [ldPartNext_layW P K (hT.ovPk m w j (by omega))] at this
    · have := hb j h2
      rw [hT.ovBit m w j (by omega)] at this
      rw [hx]
      show Bt.ok j x (P.matU pi.1.1) g (w.bit j)
      rw [hW]
      exact this
    · rw [hx]
      show (P.seg j).Holds P.fmt x (P.matU pi.1.1) _
      rw [hW]
      exact hC j h2
    · rw [hx]
      show (P.seg 0).Holds P.fmt x (P.matU pi.1.1) _
      rw [hW]
      exact ldPartCf_holds _ _ _ _ _ _ (hP.wf 0 hP.pos)
        (fun q hq => (hT.rdX m g hX q hq).symm) (hC 0 hP.pos)
    · refine hT.bits (f (x, rec)) _ m w g hX ?_
      rw [hx]
      show Bt.ok 0 x (P.matU pi.1.1) g _
      rw [hW]
      exact hb 0 hP.pos
  · -- the test passes on the relation
    rintro ⟨x, rec⟩ y ⟨m, pi, w, g⟩ ⟨_, i, η, _, hF, _⟩
    exact hF
  · -- the condition
    rintro ⟨x, rec⟩ y h0 hF
    have h0' : (Cf.conf.D y rec).isSome := h0
    refine ⟨?_, by rw [hrc]; exact h0', by rw [hx]; exact hF⟩
    rw [hrc]
    intro hc
    unfold ConfigurationWithOutOfDomainSample.D at h0'
    rw [if_pos hc] at h0'
    cases h0'
  · intro st w
    rfl
  · -- `bw`
    rintro ⟨x, rec⟩ y ⟨m, pi, w, g⟩ h0 hF ⟨U, hU, ⟨hm, hL, hC⟩, hO⟩
    rw [hrc] at hU
    rw [hx] at hC hO
    have h0' : (Cf.conf.D y rec).isSome := h0
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h0'
    have hh : Cf.conf.held U = some i := by
      have h1 := hi
      unfold ConfigurationWithOutOfDomainSample.D at h1
      split_ifs at h1
      rw [hU] at h1
      exact h1
    have hW : P.matU U = P.matI i := ldPartHead_held P hP U i hh
    rw [hW] at hC hO
    refine ⟨i, hi, hF, fun j hj => ?_, fun j hj => ?_⟩
    · by_cases e : j = 0
      · subst e
        exact hT.pkR m w hm
      · rw [ldPartNext_layW P K (hT.ovPk m w j e)]
        exact hL j (Nat.pos_of_ne_zero e) hj
    · by_cases e : j = 0
      · subst e
        refine ldPartCf_holds _ _ _ _ _ _ (hP.wf 0 hj) (fun q hq => ?_) hO
        have := ldPartHead_world P hP hT m w hm hj q hq
        rw [← this]
        unfold LdPartD.world
        rw [if_pos (hP.reads 0 hj q hq).1]
      · exact ldPartCf_holds _ _ _ _ _ _ (hP.wf j hj)
          (ldPartHead_world P hP hT m w hm hj) (hC j (Nat.pos_of_ne_zero e) hj)

end Cb
