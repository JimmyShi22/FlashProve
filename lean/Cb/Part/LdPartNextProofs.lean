-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartNextProofs.lean: the statement of Cb/Part/LdPartNext.lean, proved: the reduction step
without interaction from the end of segment k to the start of segment k + 1 is in order (`StepWOK`,
Cb/Ld/LdStepW.lean) for every partition with its laws, under the hypotheses of
`Spec.ldPartNext_step`. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

Main names:
  `ldPartNext_step`: proves `Spec.ldPartNext_step` (Cb/Part/LdPartNext.lean), forth and back, clause
    by clause.
  `ldPartNext_layW`, `ldPartNext_cellsW`: a layer, and what is unpacked from it, read the field `pk`
    at that layer alone.
  `ldPartNext_world`: told in its docstring.

Notation:
  `P : LdPartD Cf`: a partition, `P.Props p`: its laws (Cb/Part/LdPartDef.lean);
  `LdPartTie`: the ties: clauses that link how messages are read before and after a closing
    (Cb/Part/LdPartNext.lean);
  `P.layW K w j`: layer j of the further witness;
  `P.cellsW K w j`: the cells unpacked from layer j;
  `P.world K k O m w`: the relaxed world's cells while segment k runs: `O.A m s` at segments s ≤ k,
    `P.cellsW K w s` at later ones (all three: Cb/Part/LdPartRide.lean).

Limits: what the head of Cb/Part/LdPartNext.lean lists as not said is not said here either.
Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartNext
import Cb.Part.LdPartCfProofs

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

omit [Fintype F] in
theorem ldPartNext_layW {w w' : LdPartW E} {j : ℕ} (h : w.pk j = w'.pk j) :
    P.layW K w j = P.layW K w' j := by
  funext i c
  show w.pk j i.val c.val = w'.pk j i.val c.val
  rw [h]

omit [Fintype F] in
theorem ldPartNext_cellsW {w w' : LdPartW E} {j : ℕ} (h : w.pk j = w'.pk j) :
    P.cellsW K w j = P.cellsW K w' j := by
  funext r c
  unfold LdPartD.cellsW
  rw [ldPartNext_layW P K h]

variable {K} {k p : ℕ} {Sk S' : Sig E} {Ok : LdPartOut E Sk} {O' : LdPartOut E S'}
  {kept : S'.Msg → Sk.Msg} {ov : S'.Msg → LdPartW E → LdPartW E} {St' : Type} {x' : St' → Cf.Xm}
  {bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop}
  {vld : St' → Cf.conf.Msg × S'.Msg → Prop}

/-- Under `P.Props p`, the ties and `O'.pkR m`, the relaxed world of segment k (kept messages; the
further witness with layer k + 1 overwritten) and that of segment k + 1 (open messages; the further
witness) agree at every place that a segment j, k < j < P.n, reads: rows of segments ≤ k are kept
(`keeps`); segment k + 1 is read off the layer just sent; later layers are not touched. -/
theorem ldPartNext_world (hP : P.Props p) (hT : LdPartTie P K k Ok O' kept ov x' bitX vld)
    (m : S'.Msg) (w : LdPartW E) (hm : O'.pkR m) {j : ℕ} (hkj : k < j) (hj : j < P.n) :
    ∀ q ∈ (P.seg j).places, P.world K (k + 1) O' m w q.1 q.2.1 q.2.2 =
      P.world K k Ok (kept m) (ov m w) q.1 q.2.1 q.2.2 := by
  intro q hq
  have hr := hP.reads j hj q hq
  unfold LdPartD.world
  by_cases h1 : q.1 ≤ k
  · rw [if_pos (Nat.le_succ_of_le h1), if_pos h1]
    exact hT.rdKept m hm (q.1, q.2.1) (hP.keeps j hj q hq k h1 hkj) q.2.2
  · rw [if_neg h1]
    by_cases h2 : q.1 ≤ k + 1
    · have e : q.1 = k + 1 := by omega
      rw [if_pos h2, e]
      have h3 := hr.2
      rw [LdPartD.InShape, e] at h3
      exact hT.rdOwn m w hm q.2.1 q.2.2 h3.2.1 h3.2.2
    · rw [if_neg h2, ldPartNext_cellsW P K (hT.ovPk m w q.1 (by omega))]

end

theorem ldPartNext_step : Spec.ldPartNext_step := by
  intro F E _ _ _ _ Cf P K p k Sk S' Ok O' kept ov St St' x rc x' rc' f bitX vld hP hk hT hx hrc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- forth
    rintro st y ⟨m, pi, w, g⟩ ⟨hE, hH, hpk, hB, hL, hb, hC⟩
    have hX : O'.pkX m g := hT.pkX m w g hpk (hL (k + 1) (Nat.lt_succ_self k) hk)
    refine ⟨by rw [hrc]; exact hE,
      ⟨hH, hX, hB, fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩, ?_, ?_⟩
    · have := hL j (by omega) h2
      rwa [ldPartNext_layW P K (hT.ovPk m w j (by omega))] at this
    · have := hb j (by omega) h2
      rw [hT.ovBit m w j (by omega)] at this
      rw [hx]
      exact this
    · rw [hx]
      exact hC j (by omega) h2
    · rw [hx]
      exact ldPartCf_holds _ _ _ _ _ _ (hP.wf (k + 1) hk)
        (fun q hq => (hT.rdX m g hX q hq).symm) (hC (k + 1) (Nat.lt_succ_self k) hk)
    · refine hT.bits (f st) _ m w g hX ?_
      rw [hx]
      exact hb (k + 1) (Nat.lt_succ_self k) hk
  · -- the condition
    rintro st y ⟨h1, h2, h3⟩
    exact ⟨by rw [hrc]; exact h1, by rw [hrc]; exact h2, by rw [hx]; exact h3⟩
  · intro st w
    rfl
  · -- back
    rintro st y ⟨m, pi, w, g⟩ _ ⟨U, hU, ⟨hm, hL, hC⟩, hO⟩
    rw [hrc] at hU
    rw [hx] at hC hO
    refine ⟨U, hU, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
    · by_cases e : j = k + 1
      · subst e
        exact hT.pkR m w hm
      · rw [ldPartNext_layW P K (hT.ovPk m w j e)]
        exact hL j (by omega) h2
    · by_cases e : j = k + 1
      · subst e
        refine ldPartCf_holds _ _ _ _ _ _ (hP.wf (k + 1) hk) (fun q hq => ?_) hO
        have := ldPartNext_world P hP hT m w hm h1 h2 q hq
        rw [← this]
        unfold LdPartD.world
        rw [if_pos (hP.reads (k + 1) hk q hq).1]
      · exact ldPartCf_holds _ _ _ _ _ _ (hP.wf j h2)
          (ldPartNext_world P hP hT m w hm h1 h2) (hC j (by omega) h2)

end Cb
