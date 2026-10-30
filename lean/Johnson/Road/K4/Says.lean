-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Says.lean: what three groups of claims of the layers' own rounds say, in a world in
which the reads are true.

K4's claims are plain lists of forms (OnBytes/Desc/First/K4/Claims.lean).
Johnson/Road/K4/ListsTie.lean ties four of them to the library's lists, and
Johnson/Road/FormsKeysIdnW.lean and FormsKeysIdnL.lean say what the library's forms are worth where
the verifier's layout fits the library's sizes (Fits) and the entries of the reads are the true
values of the tables (TrueAt3). Here the two are put together:
IF EVERY FORM OF THE GROUP IS WORTH 0, THEN …

  `hot_says` (group 10): for each routed layer the identity (J10), extended over the positions,
      vanishes at the lookup's token point.
  `norms_says` (group 2): the squares' product layer's own claim is worth 0; its two end values are
      one hidden value; and that value is the sum, under the verifier's weights, of the limbs of the
      library's stream, extended over features and positions at the point Z_V.
  `embedding_says` (group 12, first group): the hidden value of the embedding is the sum, under the
      equality weights of tkh, of the library's stream at place 0, extended at the point Z_E.

Limits. IDENTITIES IN A WORLD, AT ONE POINT EACH: nothing here goes from a point to all positions
(that is a draw's matter), from the field to the integers, or from a transcript to a world. Fits and
TrueAt3 are premises: no theorem here concludes them, AND NOTHING HERE SHOWS THAT THEY CAN HOLD AT
THE LAYOUT OF A SHIPPED EXAMPLE: a theorem under a premise that nothing meets says nothing. No
theorem on a run of the program `verify-on-bytes` is called.
-/
import Johnson.Road.K4.ListsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell idnVal bS xS)
open Blocks (ext)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- Group 10. -/
theorem hot_says (F : Fits ρ W v D c t low u) (hp : v.y.h.p3 = true) {l : List Aff}
    (h : Desc.First.K4.oneHotForms v = some l) (hz : ∀ f ∈ l, f.value ρ W = 0)
    {lm : ℕ} (hlm : lm < v.y.LamM) (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) :
    ext D.lT (fun i => idnVal D t emb tok (.j10 lm i)) u = 0 := by
  rw [oneHotForms_oneHotL v hp] at h
  obtain ⟨s, hs, hm⟩ := mem_oneHotL h hp hlm
  have e := F.hot lm hs emb tok
  rw [hz _ hm] at e
  exact e.symm

/-- Group 2. -/
theorem norms_says (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) {P : Pub} (hy : P.y = v.y) {H : Heard}
    (hNI : v.y.NI = D.nNu) {l : List Aff} (h : Desc.First.K4.normsForms P v H = some l)
    (hz : ∀ f ∈ l, f.value ρ W = 0) :
    H.wpl.row.value ρ W = 0 ∧ W.slot H.wpl.sL = W.slot H.wpl.sR ∧
      ∃ e, (hiTab H.wpl.r v.y.h.la (P.rd.lNI + v.y.lPd - v.y.ls)).toOption = some e ∧
        W.slot H.wpl.sL =
          ∑ x ∈ range (v.y.NI * (v.y.h.d / v.y.S2) * v.y.xb.nl),
            ρ.val (e.getD (x / v.y.xb.nl / (v.y.h.d / v.y.S2) * v.y.Pd / v.y.S2 +
              x / v.y.xb.nl % (v.y.h.d / v.y.S2)) zeroE) *
                ρ.val (H.gp.getD (x % v.y.xb.nl) zeroE) *
            ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
              ext D.lT (fun p => bS D t (x / v.y.xb.nl / (v.y.h.d / v.y.S2)) (x % v.y.xb.nl)
                (x / v.y.xb.nl % (v.y.h.d / v.y.S2) * 2 ^ v.y.ls + r) p) uV := by
  obtain ⟨m1, m2, txs, tI, tA, e, sum, a1, a2, a3, a4, a5, m3⟩ :=
    mem_normsL (normsForms_normsL h)
  rw [hy] at a1 a4 a5
  have e2 := hz _ m2
  rw [Aff.value_sub, Aff.value_slot, Aff.value_slot] at e2
  have e3 := F.normsEnd T3 a2 a3 a1 hNI e H.gp H.wpl.sL a5
  rw [hz _ m3] at e3
  exact ⟨hz _ m1, sub_eq_zero.mp e2, e, a4, (sub_eq_zero.mp e3.symm)⟩

/-- Group 12, in the first group. -/
theorem embedding_says (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (h0 : v.g = 0) {H : Heard} {sVE : ℕ}
    {f : Aff} (h : Desc.First.K4.embeddingForm v H sVE = some f) (hz : f.value ρ W = 0) :
    W.slot sVE =
      ∑ kh ∈ range (v.y.h.d / v.y.S2), ρ.val ((eqTab H.tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowE r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ v.y.ls + r) p) uE := by
  have e := embeddingForm_embL v H sVE
  rw [h] at e
  unfold embL at e
  obtain ⟨tb, hb, e⟩ := Option.bind_eq_some_iff.mp e.symm
  obtain ⟨s, hs, e⟩ := Option.bind_eq_some_iff.mp e
  have ef : f = (Aff.slot sVE).scale (negE oneE) + s := by
    have := Option.some.inj e
    simpa using this.symm
  have w := F.embedding T3 h0 hb H.tkh sVE hs
  rw [← ef, hz] at w
  exact (sub_eq_zero.mp w.symm).symm

end OnBytes.Road.K4
