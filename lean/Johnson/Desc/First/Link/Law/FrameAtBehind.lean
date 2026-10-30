-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrameAtBehind.lean: `FrameAtLink` (FrameFindsOf.lean) AT EVERY PART THAT
THE BATCHING's LENS READS AT A STATE REACHED BEHIND A LINK's BATCHING's ENTRY, AT ALL 25 LINKS OF
THE PROOF FILE's FIRST CHAIN; AND SO `FrameFinds` THERE. A joining of the
laws on the running frame in Johnson/IMR/. Theorems.

  `grown`: the frame behind the two later sendings, from a frame of moment 1: next, link, shape and
    the kept list stay; «own» grows by the messages of the moments 1 and 2.
  `frame_behind`: at the cut 14 l + nAt l + 3: a link is open with the number l and the frame
    laterF (laterF f n₃) n₅, f of moment 1, link l, a link under way, the public shape, as many kept
    as the group's target has, as many own as the link has messages of moment 0. By `entry_at`,
    `entry_at_zero`, `front_words`, `frame_walk_link`; `entry_head_frame`, `frame_walk_head`
    (Johnson/IMR/FrameEntry.lean, FlagsAt.lean, FrameAll.lean), as `own_size_draw` | `own_size_head`
    (IMR/OwnSize.lean) spend them two cuts earlier.
  `frameAtLink_behind`: **FrameAtLink Z.first x.1 Xl p**, where the link has at most three moments.
    Names and layout: `own_at_cut`, `ctx_open`, `built_arr` (IMR/ArraysOpen.lean); groups:
    `open_recAll` (IMR/ListsEnds.lean); the count: MomentsCount.lean, off reqOk in `RecAll`.
  `frameFinds_behind`: **FrameFinds p n** there, from: the built link's entries are `NamedHeld` ·
    n ≤ their number · at most three moments · a message with mask rows.
Limits. «At most three moments», «a message with mask rows» and «n ≤ the number of entries» are
premises on the public part: closed facts at a given plan. In scope, at secondHashFunction alone. No member.
Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.FrameFindsOf
import Johnson.Desc.First.Link.Law.MomentsCount
import Johnson.Desc.First.Link.Law.HtinLeft
import Johnson.IMR.OwnSize
import Johnson.IMR.ArraysOpen
import Johnson.Goal.Meaning.KeptRowsPos

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

/-- The frame behind the two later sendings. -/
theorem grown {f : ReqFrame} (hm : f.moment = 1) (n₃ n₅ : ℕ) :
    (laterF (laterF f n₃) n₅).next = f.next ∧ (laterF (laterF f n₃) n₅).link = f.link ∧
      (laterF (laterF f n₃) n₅).shape = f.shape ∧
      (laterF (laterF f n₃) n₅).keptBefore = f.keptBefore ∧
      (laterF (laterF f n₃) n₅).own.size =
        f.own.size + (f.atMoment 1).length + (f.atMoment 2).length := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  show ((f.own ++ (Array.range (f.atMoment f.moment).length).map (· + n₃)) ++
    (Array.range (f.atMoment (f.moment + 1)).length).map (· + n₅)).size = _
  rw [hm]
  simp only [Array.size_append, Array.size_map, Array.size_range]

theorem atMoment_is {sh : ReqShape} {l : ℕ} {L : ReqLink} (hL : sh.link[l]? = some L)
    {f : ReqFrame} (hs : f.shape = sh) (hl : f.link = l) (m : ℕ) :
    f.atMoment m = L.messages.filter fun x => x.moment == m := by
  unfold ReqFrame.atMoment
  rw [hs, hl, hL]
  rfl

theorem target_zero (sh : ReqShape) : (targetAt sh 0).kept.size = 0 := by
  unfold First.K2.targetAt
  rw [groups_get sh (Nat.zero_le _)]
  rfl

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE OPEN LINK's FRAME BEHIND THE BATCHING's ENTRY.** -/
theorem frame_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {p : ProofFile.InstPub} {R r : List Fmt.RoundView} {C q : List OpenedColumn} {t : S}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + nAt l + 3)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (f : ReqFrame) (n₃ n₅ : ℕ), Opn l (laterF (laterF f n₃) n₅) t ∧ f.moment = 1 ∧
      f.link = l ∧ f.next = .laterOrClose ∧ f.shape = Z.first.shape ∧
      f.keptBefore.size = (targetAt Z.first.shape l).kept.size ∧
      f.own.size = ((frameAtLink Z.first.shape l).atMoment 0).length := by
  have hfl := Meaning.Carry.front_len hS hR O
  by_cases h24 : l < 24
  · have e : 14 * l + nAt l + 3 = 14 * l + 3 + 7 := by
      unfold nAt
      rw [if_neg (by omega)]
    rw [e] at g
    obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * l + 3 + 4) 3 g
    obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 3 + 2) 2 f₅
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
    have walk : ∀ {f : ReqFrame}, Opn l f t₁ →
        Opn l (laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size) t := fun H =>
      (Meaning.K2.frame_walk_link hS hR O h24
        (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₃.symm.trans h))).1])
        (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₅.symm.trans h))).1])
        f₁ H).1 7 (by omega) t r q g
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
    have e : 14 * 24 + nAt 24 + 3 = 340 + 8 := by decide
    rw [e] at g
    obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 340 + 4) 4 g
    obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 340 + 2) 2 f₅
    obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) 2 f₃
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
    obtain ⟨G, f, hG, hk, H1, mo, lk, _, nx, sh, kb, ow⟩ :=
      Meaning.K2.entry_head_frame hS hR O f₁ f₂
    have Rr : Meaning.K2.RecAll Z.first.codes Z.first.shape t₁ :=
      Meaning.K2.open_recAll hS hR O (by decide) (by omega) f₁
    refine ⟨f, t₃.st.oracles.size, t₅.st.oracles.size,
      (Meaning.K2.frame_walk_head hS hR O
        (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₃.symm.trans h))).1])
        (fun t' r' q' h => by rw [← (Prod.mk.inj (Except.ok.inj (f₅.symm.trans h))).1])
        f₂ H1).1 8 (by omega) t r q g, mo, lk, nx, sh.trans Rr.walk.shape, ?_, ?_⟩
    · rw [Rr.walk.groups] at hG
      rw [kb, Array.size_map, Array.size_range]
      unfold First.K2.targetAt
      rw [Array.getD_eq_getD_getElem?, hG]
      rfl
    · rw [ow, Array.size_map, Array.size_range, First.K2.atMoment_pub Rr.walk hk 0]

/-- **FrameAtLink AT EVERY PART READ BEHIND THE BATCHING's ENTRY.** -/
theorem frameAtLink_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (h3 : ∀ L, Z.first.shape.link[l]? = some L → reqMoments L ≤ 3) {y : ProofFile.InstPub × S}
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 3) y) {a : K9.Part}
    (ha : atS.get? y.2 = some a) : FrameAtLink Z.first l Xl a := by
  obtain ⟨_, rs, cols, g⟩ := hr.fold
  have hfl := Meaning.Carry.front_len hS hR O
  have hk : 14 * l + nAt l + 3 ≤ (frontOf c).length := by
    rw [hfl]
    unfold nAt
    split <;> omega
  have hL : y.2.link? = some a.L := (part_reads y.2 a ha).1
  obtain ⟨f, n₃, n₅, ⟨L', hL', eF, eN⟩, mo, lk, nx, sh, kb, ow⟩ := frame_behind hS hR O hl g
  obtain rfl : a.L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨g1, g2, g3, g4, g5⟩ := grown mo n₃ n₅
  have I := Meaning.K2.own_at_cut hS hR O (by omega) hk g
  obtain ⟨m, hm, hc⟩ := Meaning.K2.ctx_open hL
  obtain ⟨i1, i2⟩ := I.2 _ hc
  have Rr : Meaning.K2.RecAll Z.first.codes Z.first.shape y.2 :=
    Meaning.K2.open_recAll hS hR O (by omega) hk g
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

/-- **FrameFinds BEHIND THE BATCHING's ENTRY.** -/
theorem frameFinds_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (hQ : ∀ (τ born : ℕ) (name : String), Xl.arrayOf[τ]? = some (born, name) →
      NamedHeld Z.first l Xl τ born name)
    {n : ℕ} (hC : n ≤ Xl.arrayOf.size) {L : ReqLink} (hL : Z.first.shape.link[l]? = some L)
    (h3 : reqMoments L ≤ 3) (hM : (L.messages.any fun x => x.shape.maskRows != 0) = true)
    {y : ProofFile.InstPub × S} (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 3) y)
    {a : K9.Part} (ha : atS.get? y.2 = some a) : FrameFinds a n :=
  frameFinds_of (frameAtLink_behind hS hR O hl e3
    (fun L' h => by rw [Option.some.inj (h.symm.trans hL)]; exact h3) hr ha) hQ hC hL hM

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.grown
#print axioms VerifiableInference.Desc.LinkJoin.frame_behind
#print axioms VerifiableInference.Desc.LinkJoin.frameAtLink_behind
#print axioms VerifiableInference.Desc.LinkJoin.frameFinds_behind
