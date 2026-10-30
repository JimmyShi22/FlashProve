-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysTabs.lean: kind K5: the table clauses of LinPub (LinTabs,
Johnson/Desc/First/Att/Claims/KeysPubAll.lean) out of TabsAt
(Johnson/Desc/First/Att/Claims/TablesAt.lean), which holds of what tablesP itself makes (tabs_at).
TabsAt has every table. What lies between the two records is no table's matter but equalities of
arrays: a plane claim's point is a tail of zx, so its last coordinates are those of zx; the points
of the list wh are the same stretches of zx as those of the list wl.

Main names:
  `inner_arr`: the kind's inner point of a unit IS the tail of zx, as an array.
  `last_tail`: the last n coordinates of a tail of at least n coordinates are those of the whole.
  `wh_is_wl`: ziH = ziW and zcH = zcW.
  `linTabs_of`: TabsAt tl (oldOf S gL i) zx, and the two units' tables stand beside the units in the
    record's lists ⟹ LinTabs.
Used: TabsAt; PointsTie.lean, PointsCut.lean, KeysPub.lean, KeysPubAll.lean.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.KeysPubAll
import Johnson.Desc.First.Att.Claims.TablesAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Pts ScoreP RemP UnitG geoOf)

/-- **The kind's inner point of a unit is the tail of zx, as an array.** -/
theorem inner_arr {key zx : Array E} (hk : EndsIn key zx) (u : UnitG) (hb : u.bits ≤ zx.size) :
    P.inner u key = zx.extract (zx.size - u.bits) zx.size := by
  obtain ⟨pre, rfl⟩ := hk
  unfold P.inner
  have hs : (pre ++ zx).size = pre.size + zx.size := Array.size_append
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_extract, Array.getElem?_extract, hs]
  by_cases hj : j < u.bits
  · rw [if_pos (by omega), if_pos (by omega), Array.getElem?_append_right (by omega)]
    congr 1
    omega
  · rw [if_neg (by omega), if_neg (by omega)]

/-- A cut of a tail is a cut of the whole. -/
theorem cut_tail (z : Array E) {n a b : ℕ} (hn : n ≤ z.size) (hb : b ≤ n) :
    (z.extract (z.size - n) z.size).extract a b = z.extract (z.size - n + a) (z.size - n + b) := by
  rw [Array.extract_extract]
  congr 1
  omega

/-- The last coordinates of a tail are those of the whole. -/
theorem last_tail (z : Array E) {n m : ℕ} (hn : n ≤ z.size) (hm : m ≤ n) :
    lastCoords (z.extract (z.size - n) z.size) m = lastCoords z m := by
  unfold lastCoords
  have hs : (z.extract (z.size - n) z.size).size = n := by
    rw [Array.size_extract]
    omega
  rw [hs, cut_tail z hn (Nat.le_refl n)]
  congr 1 <;> omega

/-- The equality weights of a plane claim's last coordinates are those of zx's. -/
theorem plane_last {g : Geo} {zk : Array (Array E)} {pc : RemP} {zx : Array E} {m : ℕ}
    (H : PlaneCut g zk pc) (hk : EndsIn (zk.getD pc.call #[]) zx)
    (hb : g.keyBits (if pc.isD then .rd else .rm) ≤ zx.size)
    (hm : m ≤ g.keyBits (if pc.isD then .rd else .rm)) : lastN pc.z m = lastN zx m := by
  obtain ⟨u, hu, ez, _⟩ := H
  unfold lastN
  rw [ez, inner_arr hk u (by rw [hu]; exact hb), last_tail zx (by rw [hu]; exact hb)
    (by rw [hu]; exact hm)]

/-- **The points of the list wh are those of the list wl.** -/
theorem wh_is_wl {g : Geo} {zk : Array (Array E)} {p : Pts} {zx : Array E} (H : Cut5 g zk p)
    (hE : ∀ u : UnitG, (∃ k, g.single k = some u) → EndsIn (zk.getD u.call #[]) zx)
    (hb : 1 + g.lgk + g.lt + g.ldh ≤ zx.size) : p.d.ziH = p.d.ziW ∧ p.d.zcH = p.d.zcW := by
  obtain ⟨uW, uX, uH, hW, hX, hH, _, _, _, _, _, e2, e3, _, _, _, e7, e8⟩ := H.at'
  have bW : uW.bits = 1 + g.lgk + g.lt + g.ldh := single_bits hW
  have bH : uH.bits = g.lgk + g.lt + g.ldh := single_bits hH
  have aW := inner_arr (hE uW ⟨_, hW⟩) uW (by omega)
  have aH := inner_arr (hE uH ⟨_, hH⟩) uH (by omega)
  rw [e2, e3, e7, e8, aW, aH, cut_tail zx (by omega) (by omega), cut_tail zx (by omega) (by omega),
    cut_tail zx (by omega) (by omega), cut_tail zx (by omega) (by omega)]
  constructor <;> congr 1 <;> omega

theorem forall₂_at {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ {n : ℕ} {a : α} {b : β}, l[n]? = some a → l'[n]? = some b → R a b
  | _, _, .nil, n, a, b, h, _ => by simp at h
  | _, _, .cons h t, 0, a, b, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    exact h
  | _, _, .cons h t, n + 1, a, b, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    exact forall₂_at t h1 h2

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {lid : ℕ} {cf : Cfg} {S : Attention.Shape}
  {fs : Model.Forest.Shape} {zx zy : Array E} {zk : Array (Array E)}
  {p : Inst.Model.AttSeg.Pub Kf} {gL : Forest.Heard} {i : P.Runs.In} {tl : HTailF2}

/-- **The table clauses of LinPub out of TabsAt.** nM, nD: the units' numbers in the record's
list. -/
theorem linTabs_of (G : Ground ρ lid cf S fs zx zy zk p) {hh : P.Heard} {L' : P.Left}
    (hp : P.pointsOf (geoOf S) zk hh L' = some i.p) (TA : TabsAt tl (oldOf S gL i) zx)
    {pM pD cM cD : RemP} {kM kD : ScoreP} {tM tD : ScoreTables} {nM nD : ℕ}
    (mM : pM ∈ i.p.planes.toList) (mD : pD ∈ i.p.planes.toList)
    (mcM : cM ∈ i.p.planes.toList) (mcD : cD ∈ i.p.planes.toList)
    (sM : i.p.scores[nM]? = some kM) (tsM : (oldOf S gL i).t.score[nM]? = some tM)
    (sD : i.p.scores[nD]? = some kD) (tsD : (oldOf S gL i).t.score[nD]? = some tD) :
    LinTabs tl (oldOf S gL i) pM pD cM cD kM kD tM tD := by
  have Fo := L5.four_of_hid G.hid G.usual
  have N := norm_of_hid G.hid
  have Z := sizes_of_hid G.hid
  have L := look_of G.look
  have CU := cutU_of hp
  have hM : (geoOf S).keyBits .rm ≤ zx.size := by rw [bitsM N]; exact fam_le G.fit L .m1
  have hD : (geoOf S).keyBits .rd ≤ zx.size := by rw [bitsD N]; exact fam_le G.fit L .d1
  have lD : S.cf.lmS ≤ (geoOf S).keyBits .rd := by
    rw [bitsD N]
    have h1 := Z.lmS
    rw [N.nD] at h1
    exact h1
  have lM : S.cf.lmS ≤ (geoOf S).keyBits .rm := by
    refine le_trans lD ?_
    rw [bitsM N, bitsD N]
    show S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB ≤
      S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB
    omega
  have last : ∀ pc ∈ i.p.planes.toList, lastN pc.z S.cf.lmS = lastN zx S.cf.lmS := by
    intro pc hpc
    have A := CU.planes pc hpc
    have hk : EndsIn (zk.getD pc.call #[]) zx := by
      rcases plane_old Fo A with ⟨_, a, _⟩ | ⟨_, a, _⟩
      · rw [a]; exact endsIn_of (G.keys 0)
      · rw [a]; exact endsIn_of (G.keys 1)
    cases hf : pc.isD
    · exact plane_last A.cut hk (by rw [hf]; exact hM) (by rw [hf]; exact lM)
    · exact plane_last A.cut hk (by rw [hf]; exact hD) (by rw [hf]; exact lD)
  have hW : 1 + (geoOf S).lgk + (geoOf S).lt + (geoOf S).ldh ≤ zx.size := by
    have h1 := fam_le G.fit L .w3
    have h2 : Inst.Model.AttSeg.Fam.l (L5.dimOf S) .w3 =
        1 + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh := rfl
    rw [h2, ← N.lt] at h1
    exact h1
  obtain ⟨eI, eC⟩ := wh_is_wl (cut5_of hp) (ends_single G) hW
  have gM := forall₂_at TA.score (n := nM) (a := scoreBack kM) (b := tM)
    (by
      show (i.p.scores.map scoreBack).toList[nM]? = _
      rw [Array.toList_map, List.getElem?_map, Array.getElem?_toList, sM]
      rfl)
    (by rw [Array.getElem?_toList]; exact tsM)
  have gD := forall₂_at TA.score (n := nD) (a := scoreBack kD) (b := tD)
    (by
      show (i.p.scores.map scoreBack).toList[nD]? = _
      rw [Array.toList_map, List.getElem?_map, Array.getElem?_toList, sD]
      rfl)
    (by rw [Array.getElem?_toList]; exact tsD)
  refine ⟨?_, ?_, ?_, ?_, gM.1, gD.1, TA.hW, TA.hX, TA.tO, ?_⟩
  · show AsAt _ _ (lastN pM.z S.cf.lmS)
    rw [last pM mM]; exact TA.tA
  · show AsAt _ _ (lastN pD.z S.cf.lmS)
    rw [last pD mD]; exact TA.tA
  · show AsAt _ _ (lastN cM.z S.cf.lmS)
    rw [last cM mcM]; exact TA.tA
  · show AsAt _ _ (lastN cD.z S.cf.lmS)
    rw [last cD mcD]; exact TA.tA
  · show TabAt tl _ _ _ _ (blockRows (lowOf S i.p.d.zcH) (eqTab i.p.d.ziH))
    rw [eI, eC]
    exact TA.tO

end K5Law

#print axioms K5Law.linTabs_of
