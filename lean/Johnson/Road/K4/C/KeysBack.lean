-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/KeysBack.lean: CONDITIONAL.

What is here. THE LOOKUP's ITEM ON THE KEYS, READ BACKWARDS. The library goes from the lookup's join
in its own key vectors to the lookup's item "keys at points" (`K3OutKeys`,
Johnson/Top/H/K3RowOut.lean): `k3KeysHanded` (Johnson/Top/H/K3OutPaid.lean), `join_of_keys`
(Johnson/Road/K4/K4PinsKeys.lean). Each step of these two is an equation. Here they are read from
right to left: where the item holds and what was heard stands for some rounds, the lookup's own part
of the start form of the batched sumcheck of the feed-forward layers' own rounds (sub-protocol K4)
is worth 0, in the text in which the laws on the honest side ask it: the sum over the eight calls of
the heard weight times alpha less the call's number times theta less the extension of the call's key
vector at the call's heard point; plus the public number for the padding trees; less what the
lookup's end form is worth at a later ledger. No new argument: the library's lemmas, called.

  `join_of_outKeys`   the join's value at what was heard is 0, from the item and one list of rounds.
  `ext_at_heard`   the extension at a heard point, as a list, is the library's at that point.
  `part_of_join`   the sum in the text above is 0, from the join's value.
  `part_of_outKeys`   **the sum is 0, from the item.**

Not shown here. That the item holds anywhere; that what was heard stands for any rounds (hI);
`HeardFits` (the sizes of the lookup's two points, its calls' points and weights); `TreesFit`; that
there are eight calls; THAT THE ITEM's KEY VECTORS ARE THE LIBRARY's `keyVec` AT ANY CELLS, TABLES
AND WEIGHTS (hKv): hypotheses, each by name; no example is known of all together. The world's mask
row is the reading's (fun j => ν (.mask j)); nothing is said of another mask row. By a walk
of import lines that stops, unopened, at modules under Johnson/Goal/, Johnson/D/, Johnson/Bridge/,
Cb/Bridge and ThirdParty/: it stopped at one module, under Johnson/Bridge/; what lies behind it is
not counted. Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.K4PinsKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

/- the names of the lookup's item are read as in the library's own file -/
namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin Cb.Fo.PlaneClaims

/-- **The join's value at what was heard is 0, from the item and one list of rounds.** The converse
of k3KeysHanded. CONDITIONAL: on hI, hL and hK. -/
theorem _root_.OnBytes.Road.K4.C.join_of_outKeys {K : Type} [CommRing K]
    (ρ : OnBytes.Model.Reading K) {lm : ℕ} {g : Forest.Heard} {F0 H : Fork} {first : ℕ}
    {ν : _root_.Fo.Pl → K} (entry : ℕ → ℕ → ℕ → K) {Kv : ℕ → ℕ → K} {rs : Rounds K}
    (hI : HeardIs ρ g F0 (endsOf g.shape lm first rs)) (hL : _root_.Fo.Later F0 H)
    (hK : K3OutKeys g.shape lm first ν Kv ρ g F0) :
    AffK.val (joinK g.shape (ρ.val g.theta) (ρ.val g.alpha) (eK g.shape (rdA ρ g.zy))
      (rdA ρ g.zy) (fun c => AffK.ofConst (extL (Kv c) (rdA ρ (g.zk.getD c #[]))))
      (AffK.ofConst (g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)))) ν = 0 := by
  have h0 : claimJoin g.shape lm first rs ν (keysAt g.shape lm first Kv rs) = 0 := hK rs hI
  unfold claimJoin at h0
  rw [val_joinK] at h0 ⊢
  simp only [AffK.val_ofConst] at h0 ⊢
  rw [← cEnd_worth ρ g F0 H lm first rs hI hL ν entry, ← hI.theta, ← hI.alpha, ← hI.zy] at h0
  have hk : ∀ c, keysAt g.shape lm first Kv rs c = extL (Kv c) (rdA ρ (g.zk.getD c #[])) := by
    intro c
    unfold keysAt
    rw [← hI.zk, zk_getD]
  simp only [hk] at h0
  exact h0

end VerifiableInference.OnPublicFiles

noncomputable section

/- the names of the library's road are read as in its own file -/
namespace OnBytes.Road.K4
open Finset
open OnBytes.Model (Fork Reading Forest.Heard)
open VerifiableInference.OnPublicFiles (K3OutKeys)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim aC keyVec LW)

/-- **The extension at a heard point, as a list, is the library's extension at that point.**
CONDITIONAL: on H, T and h8. -/
theorem C.ext_at_heard {g : Forest.Heard} (H : HeardFits g) {D : Dim} (T : TreesFit g.shape D)
    (h8 : g.shape.NC = 8) (f : ℕ → Cb.Gl.E) (c : Fin 8) :
    _root_.Fo.extL f (_root_.Fo.rdA Reading.gl (g.zk.getD c.val #[])) =
      Blocks.ext (aC D c) f (pt Reading.gl (g.zk.getD c.val #[])) := by
  have ek : g.zk.getD c.val #[] = ((Array.range g.shape.NC).map fun c =>
      g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx).getD c.val #[] := by
    rw [range_map_getD' _ _ _ (by rw [h8]; exact c.isLt)]
    exact H.points c.val (by rw [h8]; exact c.isLt)
  rw [key_at H T h8 f c]
  refine ext_congr_pt _ _ fun j hj => ?_
  have hz := zc_of_look (ρ := Reading.gl) T h8 H.zx H.zy rfl c j hj
  rw [← ek] at hz
  exact hz.symm

/-- **The lookup's own part of the start form is worth 0, from the join's value.** The converse of
join_of_keys, in the heard letters. CONDITIONAL: on every hypothesis named. All letters free: cells
t, tables tb, first layer L0, weights wts, key vectors Kv, reading nu, the end form's worth cE. -/
theorem C.part_of_join [scl : Scl] {g : Forest.Heard} (H : HeardFits g) {D : Dim}
    (T : TreesFit g.shape D) (h8 : g.shape.NC = 8) (t : Inst.Model.FFSeg.Cell → Cb.Gl.E)
    (tb : Tables) (L0 : ℕ) (wts : ℕ → LW Cb.Gl.E) (Kv : ℕ → ℕ → Cb.Gl.E)
    (hKv : ∀ c : Fin 8, Kv c.val = keyVec D t tb L0 wts c) (nu : _root_.Fo.Pl → Cb.Gl.E)
    (cE : Cb.Gl.E)
    (hz : _root_.Fo.AffK.val (_root_.Fo.joinK g.shape (Reading.gl.val g.theta)
      (Reading.gl.val g.alpha) (_root_.Fo.eK g.shape (_root_.Fo.rdA Reading.gl g.zy))
      (_root_.Fo.rdA Reading.gl g.zy)
      (fun c => _root_.Fo.AffK.ofConst
        (_root_.Fo.extL (Kv c) (_root_.Fo.rdA Reading.gl (g.zk.getD c #[]))))
      (_root_.Fo.AffK.ofConst cE)) nu = 0) :
    (∑ q : Fin 8, Reading.gl.val (g.e.getD q.val zeroE) *
        (Reading.gl.val g.alpha - (q.val : Cb.Gl.E) * Reading.gl.val g.theta -
          Blocks.ext (aC D q) (keyVec D t tb L0 wts q)
            (pt Reading.gl (g.zk.getD q.val #[])))) +
      Reading.gl.val (padFo g) - cE = 0 := by
  rw [_root_.Fo.val_joinK] at hz
  simp only [_root_.Fo.AffK.val_ofConst] at hz
  rw [← pad_at g, h8, Finset.sum_range] at hz
  have e : ∀ c : Fin 8, _root_.Fo.eK g.shape (_root_.Fo.rdA Reading.gl g.zy) c.val *
        (Reading.gl.val g.alpha - ((c.val : ℕ) : Cb.Gl.E) * Reading.gl.val g.theta -
          _root_.Fo.extL (Kv c.val) (_root_.Fo.rdA Reading.gl (g.zk.getD c.val #[]))) =
      Reading.gl.val (g.e.getD c.val zeroE) *
        (Reading.gl.val g.alpha - ((c.val : ℕ) : Cb.Gl.E) * Reading.gl.val g.theta -
          Blocks.ext (aC D c) (keyVec D t tb L0 wts c)
            (pt Reading.gl (g.zk.getD c.val #[]))) := fun c => by
    rw [← e_eK H h8 c, C.ext_at_heard H T h8 _ c, hKv c]
  rw [sum_congr rfl fun c _ => e c] at hz
  exact hz

/-- **THE LOOKUP's OWN PART OF THE START FORM IS WORTH 0, FROM THE LOOKUP's ITEM ON THE KEYS.**
CONDITIONAL: on every hypothesis named. -/
theorem C.part_of_outKeys [scl : Scl] {g : Forest.Heard} (H : HeardFits g) {D : Dim}
    (T : TreesFit g.shape D) (h8 : g.shape.NC = 8) (t : Inst.Model.FFSeg.Cell → Cb.Gl.E)
    (tb : Tables) (L0 : ℕ) (wts : ℕ → LW Cb.Gl.E) {Kv : ℕ → ℕ → Cb.Gl.E}
    (hKv : ∀ c : Fin 8, Kv c.val = keyVec D t tb L0 wts c) {lm first : ℕ} {F0 F : Fork}
    {nu : _root_.Fo.Pl → Cb.Gl.E} (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {rs : TwV.Rounds Cb.Gl.E}
    (hI : _root_.Fo.HeardIs Reading.gl g F0 (_root_.Fo.endsOf g.shape lm first rs))
    (hL : _root_.Fo.Later F0 F) (hK : K3OutKeys g.shape lm first nu Kv Reading.gl g F0) :
    (∑ q : Fin 8, Reading.gl.val (g.e.getD q.val zeroE) *
        (Reading.gl.val g.alpha - (q.val : Cb.Gl.E) * Reading.gl.val g.theta -
          Blocks.ext (aC D q) (keyVec D t tb L0 wts q)
            (pt Reading.gl (g.zk.getD q.val #[])))) +
      Reading.gl.val (padFo g) - g.cEnd.value Reading.gl
        (F.worldOf Reading.gl (fun j => nu (.mask j)) entry) = 0 :=
  C.part_of_join H T h8 t tb L0 wts Kv hKv nu _ (C.join_of_outKeys Reading.gl entry hI hL hK)

end OnBytes.Road.K4

end

#print axioms OnBytes.Road.K4.C.join_of_outKeys
#print axioms OnBytes.Road.K4.C.ext_at_heard
#print axioms OnBytes.Road.K4.C.part_of_join
#print axioms OnBytes.Road.K4.C.part_of_outKeys
