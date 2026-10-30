-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWireDrawOK.lean: the wire records built over any challenge samplers are well-formed, if the
verifiers open no more positions than announced and there are 2^depthReq slots
(`Iop.Spec.wireBDOK`); and for good samplers, under the hypotheses of its statement, the record of
protocols keeps its properties, with the bias in the numbers (`Iop.Spec.drawsPropsB`). Both are
stated in Iop/BatchWireDraw.lean. The second is `Iop.pullPropsB` at the samplers, with
`Iop.drawsGood`. Many statements of this library are written twice: a definition in the namespace
`Spec` states a proposition, and a theorem of the same name outside that namespace proves it
(lean/GLOSSARY.md). (Words of this library: lean/GLOSSARY.md.)
-/
import Iop.BatchWireDraw
import Iop.BatchWireOK
import Iop.BatchPullProofs
import Iop.DrawProofs

namespace Iop
open Prob

namespace BatchWireDrawOK

theorem ofPoint_ok (lam K : ℕ) (r : Round) (a : RAnn r) (pt : r.IsPoint) (bs : BS lam r.Chal)
    (n0 : {p : r.Pos // a.own p = false} ≃ Fin (a.card0 pt))
    (nJ : {p : r.Pos // a.own p = true} ≃ Fin (a.cardJ pt)) (hK : bs.b ≤ K) :
    (WireRB.ofDraw lam K r a pt bs n0 nJ).OK where
  place_lt0 := fun p hp' => by
    have hp : a.own p = false := hp'
    have hn : ¬ a.own p = true := by rw [hp]; simp
    show (if h : a.own p = true then (nJ ⟨p, h⟩).val
        else (n0 ⟨p, Bool.eq_false_of_not_eq_true h⟩).val) <
      2 ^ Nat.clog 2 (a.card0 pt)
    rw [dif_neg hn]
    exact lt_of_lt_of_le (n0 _).isLt (Nat.le_pow_clog (by norm_num) _)
  place_ltJ := fun p hp' => by
    have hp : a.own p = true := hp'
    show (if h : a.own p = true then (nJ ⟨p, h⟩).val
        else (n0 ⟨p, Bool.eq_false_of_not_eq_true h⟩).val) <
      2 ^ Nat.clog 2 (a.cardJ pt)
    rw [dif_pos hp]
    exact lt_of_lt_of_le (nJ _).isLt (Nat.le_pow_clog (by norm_num) _)
  posAt0_place := fun p hp' => by
    have hp : a.own p = false := hp'
    have hn : ¬ a.own p = true := by rw [hp]; simp
    have e : (WireRB.ofDraw lam K r a pt bs n0 nJ).place p = (n0 ⟨p, hp⟩).val := dif_neg hn
    rw [e]
    show (if h : (n0 ⟨p, hp⟩).val < a.card0 pt then some (n0.symm ⟨(n0 ⟨p, hp⟩).val, h⟩).1
        else none) = some p
    rw [dif_pos (n0 ⟨p, hp⟩).isLt]
    exact congrArg (fun q : {p : r.Pos // a.own p = false} => some q.1)
      (n0.symm_apply_apply ⟨p, hp⟩)
  posAtJ_place := fun p hp' => by
    have hp : a.own p = true := hp'
    have e : (WireRB.ofDraw lam K r a pt bs n0 nJ).place p = (nJ ⟨p, hp⟩).val := dif_pos hp
    rw [e]
    show (if h : (nJ ⟨p, hp⟩).val < a.cardJ pt then some (nJ.symm ⟨(nJ ⟨p, hp⟩).val, h⟩).1
        else none) = some p
    rw [dif_pos (nJ ⟨p, hp⟩).isLt]
    exact congrArg (fun q : {p : r.Pos // a.own p = true} => some q.1) (nJ.symm_apply_apply ⟨p, hp⟩)
  place_posAt0 := fun j p h => by
    have h' : (if hj : j < a.card0 pt then some (n0.symm ⟨j, hj⟩).1 else none) = some p := h
    by_cases hj : j < a.card0 pt
    · rw [dif_pos hj] at h'
      have hp : (n0.symm ⟨j, hj⟩).1 = p := Option.some.inj h'
      have ho : a.own p = false := hp ▸ (n0.symm ⟨j, hj⟩).2
      refine ⟨ho, ?_⟩
      have hn : ¬ a.own p = true := by rw [ho]; simp
      have e : (WireRB.ofDraw lam K r a pt bs n0 nJ).place p = (n0 ⟨p, ho⟩).val := dif_neg hn
      rw [e]
      have : (⟨p, ho⟩ : {p : r.Pos // a.own p = false}) = n0.symm ⟨j, hj⟩ := Subtype.ext hp.symm
      rw [this, Equiv.apply_symm_apply]
    · rw [dif_neg hj] at h'
      cases h'
  place_posAtJ := fun j p h => by
    have h' : (if hj : j < a.cardJ pt then some (nJ.symm ⟨j, hj⟩).1 else none) = some p := h
    by_cases hj : j < a.cardJ pt
    · rw [dif_pos hj] at h'
      have hp : (nJ.symm ⟨j, hj⟩).1 = p := Option.some.inj h'
      have ho : a.own p = true := hp ▸ (nJ.symm ⟨j, hj⟩).2
      refine ⟨ho, ?_⟩
      have e : (WireRB.ofDraw lam K r a pt bs n0 nJ).place p = (nJ ⟨p, ho⟩).val := dif_pos ho
      rw [e]
      have : (⟨p, ho⟩ : {p : r.Pos // a.own p = true}) = nJ.symm ⟨j, hj⟩ := Subtype.ext hp.symm
      rw [this, Equiv.apply_symm_apply]
    · rw [dif_neg hj] at h'
      cases h'
  no0 := fun h j => by
    have h0 : ¬ 0 < a.card0 pt := of_decide_eq_false h
    exact dif_neg fun hj => h0 (lt_of_le_of_lt (Nat.zero_le j) hj)
  noJ := fun h j => by
    have h0 : ¬ 0 < a.cardJ pt := of_decide_eq_false h
    exact dif_neg fun hj => h0 (lt_of_le_of_lt (Nat.zero_le j) hj)
  chal_unif := map_firstBlocks_unif (Dig lam) (fun _ => false) (bs.b) K hK
  gr0_none := rfl
  grJ_none := rfl

theorem ofLocal_ok (lam K : ℕ) (r : Round) (pt : r.IsPoint) (bs : BS lam r.Chal)
    (np : r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)) (hK : bs.b ≤ K) :
    (WireRB.ofLocalD lam K r pt bs np).OK := by
  letI : Fintype r.Pos := pt.finPos
  exact
  { place_lt0 := fun p hp => Bool.noConfusion hp
    place_ltJ := fun p _ => lt_of_lt_of_le (np p).isLt (Nat.le_pow_clog (by norm_num) _)
    posAt0_place := fun p hp => Bool.noConfusion hp
    posAtJ_place := fun p _ => by
      show (if h : (np p).val < Fintype.card r.Pos then some (np.symm ⟨(np p).val, h⟩) else none) =
        some p
      rw [dif_pos (np p).isLt]
      exact congrArg some (np.symm_apply_apply p)
    place_posAt0 := fun j p h => by
      have h' : (none : Option r.Pos) = some p := h
      cases h'
    place_posAtJ := fun j p h => by
      have h' : (if hj : j < Fintype.card r.Pos then some (np.symm ⟨j, hj⟩) else none) = some p := h
      refine ⟨rfl, ?_⟩
      show (np p).val = j
      by_cases hj : j < Fintype.card r.Pos
      · rw [dif_pos hj] at h'
        rw [← Option.some.inj h', Equiv.apply_symm_apply]
      · rw [dif_neg hj] at h'
        cases h'
    no0 := fun _ _ => rfl
    noJ := fun h j => by
      have h0 : ¬ 0 < Fintype.card r.Pos := of_decide_eq_false h
      exact dif_neg fun hj => h0 (lt_of_le_of_lt (Nat.zero_le j) hj)
    chal_unif := map_firstBlocks_unif (Dig lam) (fun _ => false) (bs.b) K hK
    gr0_none := rfl
    grJ_none := rfl }

theorem sb_ofPoint_ok (lam K : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPosB A pts),
      Shape.Draws.maxB s ds ≤ K → RoundsQueryLayout.OK _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps)
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), (pt, pts), (bs, ds), (n0, nJ, nps), h =>
      ⟨ofPoint_ok lam K r a pt bs n0 nJ (le_trans (le_max_left _ _) h),
        sb_ofPoint_ok lam K s A pts ds nps (le_trans (le_max_right _ _) h)⟩

theorem sb_ofLocal_ok (lam K : ℕ) :
    ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts),
      Shape.Draws.maxB s ds ≤ K → RoundsQueryLayout.OK _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps)
  | [], _, _, _, _ => trivial
  | r :: s, (pt, pts), (bs, ds), (np, nps), h =>
      ⟨ofLocal_ok lam K r pt bs np (le_trans (le_max_left _ _) h),
        sb_ofLocal_ok lam K s pts ds nps (le_trans (le_max_right _ _) h)⟩

open BatchWireOK (depthLe_of_maxDepth_le enumUnit_ok)

variable {X : Type} {E : ExtSpec}

theorem qb_ofPoint_ok (lam K : ℕ) (Q : BatchInteractiveOracleProof X E) (pt : Q.loc.shape.IsPoint)
    (ds : Q.loc.shape.Draws lam) (nps : Q.loc.shape.NumPosB Q.ann pt) (we : WireE E) (nOpen d : ℕ)
    (hK : Shape.Draws.maxB _ ds ≤ K) (hwe : we.OK)
    (hop : ∀ x ρ pl, (Q.loc.reads x ρ pl).card + (Q.loc.extReads x ρ).card ≤ nOpen) :
    (ProtocolQueryLayout.ofDraws lam K Q pt ds nps we nOpen d).OK where
  sh := sb_ofPoint_ok lam K Q.loc.shape Q.ann pt ds nps hK
  ext := hwe
  opens := fun x ρ pl => by
    show ((Q.loc.reads x (Rho.push _ ρ) (Plains.push _ pl)).map
          (OPos.pushEquiv _).symm.toEmbedding).card +
        (Q.loc.extReads x (Rho.push _ ρ)).card ≤ nOpen
    rw [Finset.card_map]
    exact hop _ _ _
  depth := depthLe_of_maxDepth_le _ _ _ _ (le_max_right _ _)

theorem qb_ofLocal_ok (lam K : ℕ) (Q : InteractiveOracleProof X E) (pt : Q.shape.IsPoint) (ds : Q.shape.Draws lam)
    (nps : Q.shape.NumPos pt) (we : WireE E) (nOpen d : ℕ) (hK : Shape.Draws.maxB _ ds ≤ K)
    (hwe : we.OK) (hop : ∀ x ρ pl, (Q.reads x ρ pl).card + (Q.extReads x ρ).card ≤ nOpen) :
    (ProtocolQueryLayout.ofLocalD lam K Q pt ds nps we nOpen d).OK where
  sh := sb_ofLocal_ok lam K Q.shape pt ds nps hK
  ext := hwe
  opens := fun x ρ pl => by
    show ((Q.reads x (Rho.push _ ρ) (Plains.push _ pl)).map
          (OPos.pushEquiv _).symm.toEmbedding).card +
        (Q.extReads x (Rho.push _ ρ)).card ≤ nOpen
    rw [Finset.card_map]
    exact hop _ _ _
  depth := depthLe_of_maxDepth_le _ _ _ _ (le_max_right _ _)

end BatchWireDrawOK

open BatchWireDrawOK BatchWireOK in
/-- `QueryLayout.ofDraws` and `WireBP.ofDraws` are well-formed (`QueryLayout.OK`, `WireBP.OK`), under the
hypotheses of `Spec.wireBDOK` (Iop/BatchWireDraw.lean: `L.Opens no`; `L.maxBatchSize = 2 ^ ax.depthReq`). -/
theorem wireBDOK : Spec.wireBDOK := by
  intro I X lam L pT pL pB z no dr ax hno hN
  refine ⟨?_, ?_⟩
  · exact
      { T := qb_ofLocal_ok lam (dr.K) L.offline pT dr.T ax.posT _ no.T _ (le_max_left _ _)
          (WireE.one_ok _ _ _) hno.opT
        Lk := qb_ofLocal_ok lam (dr.K) L.link pL dr.Lk ax.posL _ no.L _
          (le_trans (le_max_left _ _) (le_max_right _ _)) (WireE.two_ok _ _ _) hno.opL
        B := qb_ofPoint_ok lam (dr.K) L.onlineBatch pB dr.B ax.posB _ no.O _
          (le_trans (le_max_right _ _) (le_max_right _ _)) (WireE.one_ok _ _ _) hno.opB
        fits := Nat.le_pow_clog (by norm_num) L.wordLength
        slots := hN
        extDepth := ⟨rfl, rfl, rfl⟩
        depthT := le_max_left _ _
        depthL := le_max_left _ _
        depthB := le_max_left _ _
        extT := fun _ => ⟨rfl, rfl⟩
        extB := fun _ => ⟨rfl, rfl⟩
        extL := ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩ }
  · exact
      { T := ⟨enumUnit_ok, Enum.ofNum_ok _ _⟩
        Lk := ⟨enumUnit_ok, Enum.ofNum_ok _ _⟩
        B := ⟨Enum.ofNum_ok _ _, Enum.ofNum_ok _ _⟩
        ri := Enum.ofNum_ok _ _
        perm := Enum.ofNum_ok _ _ }

/-- `BatchProtocol.Props` is preserved, with the hypotheses and numbers of `Spec.drawsPropsB`
(Iop/BatchWireDraw.lean: `1 ≤ κ₀`, `dr.Good κ₀`, `dr.TotLe n`, `L.Props Ryes Rno M`; the numbers
`M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize`). -/
theorem drawsPropsB : Spec.drawsPropsB := by
  intro I X L Ryes Rno M lam n dr κ₀ h1 hg hn h
  exact pullPropsB I X L Ryes Rno M _ _ _ _ _
    (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K n (le_max_left _ _) hn.1)
    (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K n
      (le_trans (le_max_left _ _) (le_max_right _ _)) hn.2.1)
    (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K n
      (le_trans (le_max_right _ _) (le_max_right _ _)) hn.2.2) h

end Iop
