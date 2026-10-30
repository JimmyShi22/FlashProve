-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HeadFill.lean: THE MEMBERS AND FLAGS OF THE HEAD's LINK's GROUP
BEHIND "H:2" (the cut 340): at the proof file's seat, in the goals' scope, from the fold's return
alone.
  gain_bounds: the numbers of kind K2's two lists stand below the number of messages behind
    the sending, and none stands twice: for a front that announces one notice more than the link
    has messages of moment 0.
  head_gains: with fx the front that K2.frontAt makes at the cut 339: over "H:2" the statement's
    group number 24 gains just switchGain fx ++ ownGain fx and every other group stays (kind K2's
    GainsAt, by head_place_groups and Johnson/IMR/HeadFront.lean's front_nums_head: the group is
      fresh); the
    number of messages behind.
  head_holds: THE TOP: so behind "H:2" that group holds just these (Johnson/IMR/GroupFill.lean's
    Holds).
NOT HERE: the head's link's later sendings; its closing; the finish.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.HeadFront
import Johnson.IMR.FrameEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

theorem gain_bounds (x : _root_.Tw.K2.Front) (ho : x.others.size = x.own.length + 1) :
    (∀ o ∈ (K2.switchGain x ++ K2.ownGain x).map (·.1),
      o < x.st.oracles.size + (_root_.Tw.K2.switchNotices x.T x.others).size) ∧
      ((K2.switchGain x ++ K2.ownGain x).map (·.1)).Nodup := by
  have hN : (_root_.Tw.K2.switchNotices x.T x.others).size =
      1 + x.T.kept.size + x.others.size := by
    simp [_root_.Tw.K2.switchNotices]
    omega
  rw [gain_fst]
  refine ⟨fun o ho' => ?_, ?_⟩
  · rw [hN, ho]
    rcases List.mem_append.1 ho' with k | k
    · rcases List.mem_cons.1 k with rfl | k
      · omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 k
        have := List.mem_range.1 hi
        omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 k
      have := List.mem_range.1 hi
      omega
  · have hP : (x.st.oracles.size ::
        (List.range x.T.kept.size).map (· + (x.st.oracles.size + 1)) ++
        (List.range x.own.length).map
          (· + (x.st.oracles.size + (1 + x.T.kept.size)))).Pairwise (· < ·) := by
      rw [List.cons_append, List.pairwise_cons, List.pairwise_append]
      refine ⟨fun o ho' => ?_, K2.rising_range _ _, K2.rising_range _ _, fun o h1 o' h2 => ?_⟩
      · rcases List.mem_append.1 ho' with k | k <;> obtain ⟨i, -, rfl⟩ := List.mem_map.1 k <;>
          omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 h2
        have := List.mem_range.1 hi
        omega
    exact hP.imp fun k => Nat.ne_of_lt k

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **OVER "H:2"**: what the statement's group number 24 gains, and the number of messages
behind. -/
theorem head_gains (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) :
    K2.GainsAt 24 (K2.switchGain fx ++ K2.ownGain fx) t₀.st t₁.st ∧
      t₁.st.oracles.size =
        fx.st.oracles.size + (_root_.Tw.K2.switchNotices fx.T fx.others).size ∧
      fx.others.size = fx.own.length + 1 ∧ fx.st = t₀.st := by
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨eg, -, -, G, hG, -, gm, gk⟩ := front_nums_head hS hR O fm f₀ hq h
  obtain ⟨Lk, b1, x, eL, e1, -, la1, hx⟩ := IM.k2_head_of hS hR O
  have i1 : c.blocksInOrder[339]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 1).trans (by omega : _ = 339)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i1 f₀ f₁
  have dx : x.decide t₀ rs gs = .ok t₁ :=
    ((IM.yes_alone la1 (by intro k; cases k) t₀ t₁ rs gs).1 d).1
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
  · obtain ⟨er, he⟩ := hm t₀ rs gs
    rw [he] at dx
    cases dx
  · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases hn
    · rw [ex] at dx
      obtain ⟨m, a1, a2⟩ := andThen_yes (n := x.name) dx
      have h₁ : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n) t₀ _ _
          = .ok m := a1
      have h₂ : K2.headOpenQ HP m = .ok t₁ := a2
      obtain ⟨a, G₀, ha, hG₀, hgain⟩ := K2.head_place_groups rfl h₁ h₂
      have efx : fx = K2.headFrontOf t₀ a G₀.target := by
        unfold K2.frontAt at h
        rw [hq, ha, hG₀] at h
        exact (Option.some.inj h).symm
      subst efx
      have hga := hgain G hG gm gk
      have eg' : a.fr.group = 24 := eg
      rw [eg'] at hga
      obtain ⟨x', hf, -, -, hs, -⟩ := K2.yes_size h₁
      have ex' : x' = K2.headFrontOf t₀ a G₀.target := by
        rcases hf with ⟨k, -⟩ | ⟨-, a', G'', ha', hG'', e⟩ | ⟨k, -⟩
        · cases k
        · rw [ha] at ha'
          injection ha' with ea
          rw [hG₀] at hG''
          rw [e, ← ea, ← Option.some.inj hG'']
        · cases k
      rw [ex'] at hs
      exact ⟨hga, by rw [K2.headOpenQ_size h₂, hs], by simp [K2.headFrontOf, ReqFrame.notices],
        rfl⟩
    · rw [ex] at dx
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lq⟩ :=
        K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl dx
      unfold K2.frontAt at h
      rw [hq, Lq.hHere] at h
      cases h

/-- **BEHIND "H:2".** -/
theorem head_holds (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) :
    Holds 24 ((K2.switchGain fx ++ K2.ownGain fx).map (·.1))
      ((K2.switchGain fx ++ K2.ownGain fx).map (·.2)) t₁ := by
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨eg, -, -, G, hG, -, gm, gk⟩ := front_nums_head hS hR O fm f₀ hq h
  obtain ⟨⟨-, -, Ga, G', hGa, hG', am, ak⟩, hs, ho, est⟩ := head_gains hS hR O f₀ f₁ hq h
  rw [eg, est] at hG
  obtain rfl : Ga = G := Option.some.inj (hGa.symm.trans hG)
  obtain ⟨b1', b2'⟩ := gain_bounds fx ho
  refine ⟨G', hG', by rw [am, gm]; simp, by rw [ak, gk]; simp, by simp, fun o ho' => ?_, b2'⟩
  rw [hs]
  exact b1' o ho'

end

#print axioms gain_bounds
#print axioms head_gains
#print axioms head_holds

end Meaning.K2
