-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPassedPlaces.lean.
From a passing result of the whole call to the run of each sub-proof's routine: which link stands at
the place.

`passed_all` (OnBytes/Tie/Pv/Lookup/Ends/FoPassedAll.lean) names, for each group's layers and for
each group's attention, a
place i of the links at which the routine has run, and ties i to the group through the run alone.

 * `passed_places`: `passed_all`, word for word, with one clause more at each of the three kinds:
   the link at that place of `Verify.linksOf C.X cov` is the one that is made of the group's plan
   for its layers, of the group's plan for its attention, of the head's plan, with its name, its
   identifier, its kind and its group.

Not said: the number of the place at which a group's link stands.

The clause on a group's attention stands under `C.X.p4 = true`: where the public record does not
cover attention, nothing is said of attention.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPassedAll

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Verify OnBytes.Model.Stages

theorem passed_places {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) :
    ∃ (r : Read) (ent : ByteArray) (p : Planned) (C : Common) (table further : Params.TableName)
      (so : Head.StOwn) (cov : Head.Covered) (item : ByteArray) (links : Array LinkH)
      (rd : Proof.ProofRead) (x : Proof.LinksResult × Ctx) (check check2 : ChainCheck)
      (c1 c2 : Ctx),
      PassedRan o f k entry r ent p C table further so cov item links rd x check check2 c1 c2 ∧
      publicOf r.pol r.KL r.layout = .ok C.X ∧
      (∀ (g : Nat) (hp : Layer.HPlan2), C.X.G[g]? = some hp →
        ∃ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size) (q' : ChainCheck)
          (d1 d2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) i hb hi q' d1 d2 D F ∧
          links[i] = (layersPlanOf C.X cov.tokv g hp).link ("G" ++ toString g) (1 + g) 0 g true ∧
          Layer.runForkHidG2 { C.X.layers with tokv := cov.tokv } hp g
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := hp.Tp }
            hp.Fp d1 = .ok (((w, D), F), d2)) ∧
      (C.X.p4 = true → ∀ (g : Nat) (hp : Layer.HPlan2) (a : Attention.Plan),
        C.X.G[g]? = some hp → C.X.A[g]? = some a →
        ∃ (i : Nat) (hb : i < C.built.links.size) (hi : i < links.size) (q' : ChainCheck)
          (d1 d2 : Ctx) (D : LinkCtx) (F : Fork),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) i hb hi q' d1 d2 D F ∧
          links[i] = (attentionPlanOf a).link ("A" ++ toString g) (2 + C.X.NGr + g) 1 g false ∧
          Attention.run a
            { check := q', link := i, arrayOf := (C.built.links[i]).arrayOf, list := a.seam.Tp }
            a.seam.Fp d1 = .ok ((((), D), F), d2)) ∧
      (∃ (hb : links.size - 1 < C.built.links.size) (hi : links.size - 1 < links.size)
          (q' : ChainCheck) (d1 d2 : Ctx) (D : LinkCtx) (F : Fork) (w : WsForkOut),
          CutAt C.X cov links C.built.links p.chains.proof.first C.X.layers.wsLay check c1
            ((check2, x.1), c2) (links.size - 1) hb hi q' d1 d2 D F ∧
          links[links.size - 1] = (headPlanOf C.X cov).link "H" (1 + C.X.NGr) 2 0 true ∧
          Head.runForkHidH2 C.X.hS C.X.HLy (borderOf C.X.y) C.X.H C.X.owner cov C.X.layers.wsLay
            { check := q', link := links.size - 1,
              arrayOf := (C.built.links[links.size - 1]).arrayOf, list := C.X.H.Tp }
            C.X.H.Fp d1 = .ok (((w, D), F), d2)) := by
  obtain ⟨r, ent, p, C, table, further, a1, b1, b2, a2, a3, b3, b4, b5,
    ⟨so, cov, item, links, a4, a5, b6, a6, hacc⟩, _⟩ := wholeCall_passed hk h
  obtain ⟨rd, x, check, check2, c1, c2, a7, a8, a9, a10⟩ :=
    accepted_ran C.X cov links C.built.links a6 _ _ _ _ _ _ _ _ hacc
  obtain ⟨hX, hB⟩ := common_public a3
  have sb := built_bare hB a6
  have cut := cut_at C.X cov links C.built.links a6 sb p.chains.proof.first C.X.layers.wsLay
    check c1 ((check2, x.1), c2) a9
  refine ⟨r, ent, p, C, table, further, so, cov, item, links, rd, x, check, check2, c1, c2,
    ⟨a1, b1, b2, a2, a3, b3, b4, b5, b6, a4, a5, a6, a7, a8, a9, a10⟩, hX, ?_, ?_, ?_⟩
  · intro g hp hg
    obtain ⟨i, hi, ei⟩ := layer_place C.X cov links a6 g hp hg
    have hb : i < C.built.links.size := by
      rw [sb.size]
      exact hi
    obtain ⟨q', d1, d2, D, F, hc⟩ := cut i hb hi
    have hc' := hc
    obtain ⟨_, _, _, _, _, _, hr, _, _⟩ := hc'
    rw [ei] at hr
    obtain ⟨w, hw⟩ := ranAt_layer C.X cov g hp hg _ _ _ _ _ _ _ _ _ hr
    exact ⟨i, hb, hi, q', d1, d2, D, F, w, hc, ei, hw⟩
  · intro h4 g hp a hg ha
    obtain ⟨i, hi, ei⟩ := att_place C.X cov links a6 h4 g hp hg a ha
    have hb : i < C.built.links.size := by
      rw [sb.size]
      exact hi
    obtain ⟨q', d1, d2, D, F, hc⟩ := cut i hb hi
    have hc' := hc
    obtain ⟨_, _, _, _, _, _, hr, _, _⟩ := hc'
    rw [ei] at hr
    exact ⟨i, hb, hi, q', d1, d2, D, F, hc, ei, ranAt_att C.X cov g a ha _ _ _ _ _ _ _ _ _ hr⟩
  · obtain ⟨hi, ei⟩ := linksOf_last C.X cov links a6
    have hb : links.size - 1 < C.built.links.size := by
      rw [sb.size]
      exact hi
    obtain ⟨q', d1, d2, D, F, hc⟩ := cut (links.size - 1) hb hi
    have hc' := hc
    obtain ⟨_, _, _, _, _, _, hr, _, _⟩ := hc'
    rw [ei] at hr
    obtain ⟨w, hw⟩ := ranAt_head C.X cov _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨hb, hi, q', d1, d2, D, F, w, hc, ei, hw⟩

end Fo
