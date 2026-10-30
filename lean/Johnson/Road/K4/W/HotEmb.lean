-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/HotEmb.lean: CONDITIONAL but for hotCube_iff.

Not shown here. THE LIBRARY's IDENTITY (J10) IS A NAMED PREMISE, IN TWO FORMS: HotCube, at every
routed layer and position, and HotPoint, its extension at the lookup's token point alone. That
either is in hand in front of the sub-protocol K4 is not shown. HotPoint says in the library's terms
what the selector's claims say: the law restates it. The embedding's law asks that the slot holds
the library's sum at the cells: where the slot is laid as the weight claim's sum on the committed
matrix, that is the library's identity (J11) summed at the embedding's point, not at every feature
and position, and under the premise EmbWeight (Johnson/Road/Rows/EmbEnds.lean). That it follows from
(J11) is not shown here. Fits and TrueAt3 are premises. So is that the group is the first (h0). That
the list, or the form, is there is a premise. No example that meets the premises is known. That an
honest run leaves such a world is not shown.

THE SELECTOR's CLAIMS AND THE EMBEDDING's CLAIM OF THE SUB-PROTOCOL K4 ARE WORTH 0 (the format's
groups 10 and 12; OnBytes/Desc/First/K4/Claims.lean), at a free reading and a free world in which
the tables of the reads are true of the cells (Fits, TrueAt3: Johnson/Road/).

  HotCube          (J10) at every routed layer and every position below 2 ^ D.lT.
  hotCube_iff      it is the library's idnVal at the names j10, whatever embedding and tokens.
  HotPoint, hotPoint_of_cube   the identity's extension at a point; it follows from HotCube.
  hot_zero', hot_zero   the field hot of FrontWorth (Johnson/Road/K4/WorthGroups.lean), from the
                   point; from the cube.
  embedding_zero   the field emb of FrontWorth.

No property is claimed.
-/
import Johnson.Road.K4.WorthGroups
import Johnson.Road.K4.HotIs
import Johnson.Road.K4.ListsTie
import Johnson.Road.K4.Says3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell idnVal d10 xS)
open Blocks (ext)
open OnBytes.Desc.First.K4 (oneHotForms embeddingForm)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}
  [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- **(J10) at every routed layer and every position**: the selector's entries sum to 1. This
defines a hypothesis; the definition claims nothing. -/
def HotCube (D : Dim) (t : Cell → K) : Prop :=
  ∀ lm, lm < D.ne → ∀ i, i < 2 ^ D.lT → d10 D t lm i = 0

/-- It is the library's identity at the names j10, whatever embedding and tokens. -/
theorem hotCube_iff (D : Dim) (t : Cell → K) (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) :
    HotCube D t ↔ ∀ lm, lm < D.ne → ∀ i, i < 2 ^ D.lT → idnVal D t emb tok (.j10 lm i) = 0 :=
  Iff.rfl

/-- **(J10) at the point alone**: for every routed layer the extension of the identity's array over
the positions is 0 at u. It is what the claims ask, no more (hot_zero_iff,
Johnson/Road/K4/HotIs.lean). This defines a hypothesis; the definition claims nothing. -/
def HotPoint (D : Dim) (t : Cell → K) (u : ℕ → K) : Prop :=
  ∀ lm, lm < D.ne → ext D.lT (fun i => d10 D t lm i) u = 0

omit scl in
/-- The identity at every position gives it at every point. -/
theorem hotPoint_of_cube {D : Dim} {t : Cell → K} (h : HotCube D t) (u : ℕ → K) :
    HotPoint D t u :=
  fun lm hlm => Blocks.ext_zero_of_forall (h lm hlm) u

/-- **The selector's claims, from the point alone.** -/
theorem hot_zero' (F : Fits ρ W v D c t low u) (hJ : HotPoint D t u) :
    ∀ l, oneHotForms v = some l → ∀ f ∈ l, f.value ρ W = 0 :=
  fun _ h => (Road.K4.hot_zero_iff F h).2 hJ

/-- **The selector's claims.** -/
theorem hot_zero (F : Fits ρ W v D c t low u) (hJ : HotCube D t) :
    ∀ l, oneHotForms v = some l → ∀ f ∈ l, f.value ρ W = 0 :=
  fun _ h => Road.K4.hot_forms_zero_of_cube F h hJ

/-- **The embedding's claim**, in the first group, is worth 0 where the slot holds the library's sum
over the blocks of features of the stream that comes in, at the embedding's point. -/
theorem embedding_zero (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (h0 : v.g = 0) {H : Heard} {sVE : ℕ}
    (hV : W.slot sVE =
      ∑ kh ∈ range (v.y.h.d / v.y.S2), ρ.val ((eqTab H.tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowE r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ v.y.ls + r) p) uE) :
    ∀ f, embeddingForm v H sVE = some f → f.value ρ W = 0 := by
  intro f h
  have e := Road.K4.embeddingForm_embL v H sVE
  rw [h] at e
  unfold embL at e
  obtain ⟨tb, hb, e⟩ := Option.bind_eq_some_iff.mp e.symm
  obtain ⟨s, hs, e⟩ := Option.bind_eq_some_iff.mp e
  have ef : f = (Aff.slot sVE).scale (negE oneE) + s := by
    have := Option.some.inj e
    simpa using this.symm
  have w := F.embedding T3 h0 hb H.tkh sVE hs
  rw [ef, w, hV, sub_self]

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.hotCube_iff
#print axioms OnBytes.Road.K4.W.hotPoint_of_cube
#print axioms OnBytes.Road.K4.W.hot_zero'
#print axioms OnBytes.Road.K4.W.hot_zero
#print axioms OnBytes.Road.K4.W.embedding_zero
