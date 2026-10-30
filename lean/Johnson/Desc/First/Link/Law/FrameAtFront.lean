-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrameAtFront.lean: `FrameAtLink` (FrameFindsOf.lean) AT EVERY CUT OF A
LINK BEHIND ITS SECOND LATER SENDING AND IN FRONT OF ITS CLOSING; AND SO AT THE BATCHING's FRONT.
`frame_behind` and `frameAtLink_behind` (FrameAtBehind.lean), general in the cut. Theorems. It
changes no other file.

  `entryCut l`: the cut behind the sub-protocol that opens link l: 14 l + 3; at the head's link 340.
  `frame_late`: at the cut entryCut l + k, 5 ≤ k ≤ 9: a link is open with the number l and the frame
    laterF (laterF f n₃) n₅, with f's seven facts as in `frame_behind`.
  `frameAtLink_late`: **FrameAtLink Z.first l Xl a at every part a that the batching's lens reads at
    a state reached there**, where the link has at most three moments.
  `front_cut`: the batching's entry's number 14 l + nAt l + 2 is entryCut l + 6 (the head: + 7).
  `frameAtLink_front`, `frameFinds_front`: **at the batching's front.**
Limits. Those of FrameAtBehind.lean. In scope, at secondHashFunction alone. No member. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HtinPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (ReqShape ReqLink)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open Meaning.K2 (laterF seqF Opn frontOf fold_cut fold_back)
open VerifiableInference.Desc.First.K2 (targetAt frameAtLink)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (nAt)
open ProofFile (Cl)

/-- The cut behind the sub-protocol that opens link l. -/
def entryCut (l : ℕ) : ℕ := if l = 24 then 340 else 14 * l + 3

theorem seqF_late (f : ReqFrame) (n₃ n₅ : ℕ) {k : ℕ} (hk : 5 ≤ k) :
    seqF f n₃ n₅ k = laterF (laterF f n₃) n₅ := by
  unfold Meaning.K2.seqF
  rw [if_neg (by omega), if_neg (by omega)]

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE OPEN LINK's FRAME BEHIND THE SECOND LATER SENDING.** -/
theorem frame_late (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {k : ℕ} (h5 : 5 ≤ k) (h9 : k ≤ 9) {p : ProofFile.InstPub} {R r : List Fmt.RoundView} {C q : List OpenedColumn}
    {t : S}
    (g : foldBlocks 0 (c.blocksInOrder.take (entryCut l + k)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (f : ReqFrame) (n₃ n₅ : ℕ), Opn l (laterF (laterF f n₃) n₅) t ∧ f.moment = 1 ∧
      f.link = l ∧ f.next = .laterOrClose ∧ f.shape = Z.first.shape ∧
      f.keptBefore.size = (targetAt Z.first.shape l).kept.size ∧
      f.own.size = ((frameAtLink Z.first.shape l).atMoment 0).length := by
  have hfl := Meaning.Carry.front_len hS hR O
  by_cases h24 : l < 24
  · have e : entryCut l = 14 * l + 3 := by
      unfold entryCut
      rw [if_neg (by omega)]
    rw [e] at g
    obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * l + 3 + 4) (k - 4)
      (by rw [show 14 * l + 3 + 4 + (k - 4) = 14 * l + 3 + k by omega]; exact g)
    obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 3 + 2) 2 f₅
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
    have walk : ∀ {f : ReqFrame}, Opn l f t₁ →
        Opn l (laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size) t := fun {f} H => by
      have w := (Meaning.K2.frame_walk_link hS hR O h24
        (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₃.symm.trans h))).1])
        (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₅.symm.trans h))).1])
        f₁ H).1 k h9 t r q g
      rwa [seqF_late _ _ _ h5] at w
    by_cases h0 : l = 0
    · subst h0
      obtain ⟨f, a1, _, mo, lk, _, nx, sh, kb, ow⟩ := Meaning.K2.entry_at_zero hS hR O f₁
      have e0s := Meaning.K2.laid_is_start hS hR O f₀
      obtain ⟨-, hk⟩ := Meaning.K2.laid_at hS hR O (by omega : 0 < 25) f₀
      have Rr : Meaning.K2.RecAll Z.first.codes Z.first.shape t₀ :=
        Meaning.K2.open_recAll hS hR O (by omega) (by omega) f₀
      refine ⟨f, _, _, walk a1.opn, mo, lk, nx, by rw [sh, ← e0s]; exact Rr.walk.shape, ?_, ?_⟩
      · rw [kb, target_zero]
        rfl
      · rw [ow, Array.size_map, Array.size_range, ← e0s, First.K2.atMoment_pub Rr.walk hk 0]
    · obtain ⟨x, f, hx, a1, _, mo, lk, _, nx, sh, kb, ow⟩ :=
        Meaning.K2.entry_at hS hR O (by omega) h24 f₀ f₁
      obtain ⟨eT, eo, es⟩ := Meaning.K2.front_words hS hR O h24 f₀ hx
      refine ⟨f, _, _, walk a1.opn, mo, lk, nx, sh.trans es, ?_, ?_⟩
      · rw [kb, Array.size_map, Array.size_range, eT]
      · rw [ow, Array.size_map, Array.size_range, eo]
  · obtain rfl : l = 24 := by omega
    have e : entryCut 24 = 340 := rfl
    rw [e] at g
    obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 340 + 4) (k - 4)
      (by rw [show 340 + 4 + (k - 4) = 340 + k by omega]; exact g)
    obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 340 + 2) 2 f₅
    obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) 2 f₃
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
    obtain ⟨G, f, hG, hk, H1, mo, lk, _, nx, sh, kb, ow⟩ :=
      Meaning.K2.entry_head_frame hS hR O f₁ f₂
    have Rr : Meaning.K2.RecAll Z.first.codes Z.first.shape t₁ :=
      Meaning.K2.open_recAll hS hR O (by decide) (by omega) f₁
    have w := (Meaning.K2.frame_walk_head hS hR O
      (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₃.symm.trans h))).1])
      (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₅.symm.trans h))).1])
      f₂ H1).1 k (by omega) t r q g
    rw [seqF_late _ _ _ h5] at w
    refine ⟨f, t₃.st.oracles.size, t₅.st.oracles.size, w, mo, lk, nx, sh.trans Rr.walk.shape,
      ?_, ?_⟩
    · rw [Rr.walk.groups] at hG
      rw [kb, Array.size_map, Array.size_range]
      unfold First.K2.targetAt
      rw [Array.getD_eq_getD_getElem?, hG]
      rfl
    · rw [ow, Array.size_map, Array.size_range, First.K2.atMoment_pub Rr.walk hk 0]

/-- **FrameAtLink AT EVERY PART READ THERE.** -/
theorem frameAtLink_late (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {k : ℕ} (h5 : 5 ≤ k) (h9 : k ≤ 9) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (h3 : ∀ L, Z.first.shape.link[l]? = some L → reqMoments L ≤ 3) {y : ProofFile.InstPub × S}
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (entryCut l + k) y) {a : K9.Part}
    (ha : atS.get? y.2 = some a) : FrameAtLink Z.first l Xl a := by
  obtain ⟨_, rs, cols, g⟩ := hr.fold
  have hfl := Meaning.Carry.front_len hS hR O
  have hk : entryCut l + k ≤ (frontOf c).length := by
    rw [hfl]
    unfold entryCut
    split <;> omega
  have h2 : 2 ≤ entryCut l + k := by omega
  have hL : y.2.link? = some a.L := (part_reads y.2 a ha).1
  obtain ⟨f, n₃, n₅, ⟨L', hL', eF, eN⟩, mo, lk, nx, sh, kb, ow⟩ :=
    frame_late hS hR O hl h5 h9 g
  obtain rfl : a.L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨g1, g2, g3, g4, g5⟩ := grown mo n₃ n₅
  have I := Meaning.K2.own_at_cut hS hR O h2 hk g
  obtain ⟨m, hm, hc⟩ := Meaning.K2.ctx_open hL
  obtain ⟨i1, i2⟩ := I.2 _ hc
  have Rr : Meaning.K2.RecAll Z.first.codes Z.first.shape y.2 :=
    Meaning.K2.open_recAll hS hR O h2 hk g
  have hlive := Rr.live
  rw [Meaning.K2.live_open hL] at hlive
  refine ⟨?_, i1, by rw [eF, g1]; exact nx, by rw [eF, g2]; exact lk, hlive.shape, hlive.groups,
    by rw [eF, g4]; exact kb, fun L hLk => ?_⟩
  · rw [Meaning.K2.built_arr O.blank e3, ← eN]
    exact i2 hm
  · have hok : reqMomentsOk 0 L.messages = true := by
      have h1 := Rr.ok
      unfold reqOk at h1
      simp only [Bool.and_eq_true] at h1
      have h2 : reqShapeOk Z.first.shape = true := by tauto
      have h4 := Meaning.K2.links_ok h2 L (List.mem_of_getElem? hLk)
      unfold reqLinkOk at h4
      simp only [Bool.and_eq_true] at h4
      exact h4.1.2
    rw [eF, g5, ow, atMoment_is hLk rfl rfl 0, atMoment_is hLk sh lk 1, atMoment_is hLk sh lk 2]
    exact count_link hok (h3 L hLk)

/-- The batching's entry's number, from the link's entry's cut. -/
theorem front_cut (l : ℕ) : 14 * l + nAt l + 2 = entryCut l + (if l = 24 then 7 else 6) := by
  unfold nAt entryCut
  split <;> omega

/-- **AT THE BATCHING's FRONT.** -/
theorem frameAtLink_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (h3 : ∀ L, Z.first.shape.link[l]? = some L → reqMoments L ≤ 3) {y : ProofFile.InstPub × S}
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 2) y) {a : K9.Part}
    (ha : atS.get? y.2 = some a) : FrameAtLink Z.first l Xl a :=
  frameAtLink_late hS hR O hl (k := if l = 24 then 7 else 6) (by split <;> omega)
    (by split <;> omega) e3 h3 (by rw [← front_cut]; exact hr) ha

theorem frameFinds_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) (hP : LinkPlanFits Z l Xl)
    {y : ProofFile.InstPub × S} (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 2) y)
    {a : K9.Part} (ha : atS.get? y.2 = some a) : FrameFinds a Xl.Fp.trees.size := by
  obtain ⟨L, hL, hM⟩ := hP.mask
  exact frameFinds_of (frameAtLink_front hS hR O hl e3 hP.three hr ha)
    (named_at_blank O.pub O.blank e3) hP.names hL hM

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frame_late
#print axioms VerifiableInference.Desc.LinkJoin.frameAtLink_late
#print axioms VerifiableInference.Desc.LinkJoin.frameAtLink_front
#print axioms VerifiableInference.Desc.LinkJoin.frameFinds_front
