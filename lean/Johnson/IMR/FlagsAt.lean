-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlagsAt.lean: THE FLAGS "kept" OF A LINK's GROUP, IN THE WORDS OF
THE PUBLIC SHAPE, from behind the link's second later sending to in front of its closing (the cuts
14 l + 8 + n, n ≤ 4), 1 ≤ l < 24: at the proof file's seat, in the goals' scope, from the fold's
return alone.
  gain_snd: the flags of kind K2's files' two lists, written out.
  atMoment_of: a frame's messages of a moment are a function of its shape and its link.
  front_words: the front x that the text makes of the state in front of link l's code switching, in
    the shape's words: x.T = K2.targetAt sh l; x.own = (K2.frameAtLink sh l).atMoment 0.
  frames_at: the open link's frame in front of the two later sendings (the cuts 14 l + 5 and
    14 l + 7): shape sh, link l, moment 1 and 2.
  flags_at: THE TOP: G.kept.toList = false :: the target's "kept again" ++ "life > 0" of the link's
    messages of moment 0 ++ of moment 1 ++ of moment 2; with it: the open link, its frame's group,
    the members as the frame's two lists behind one number, no number twice.
sh := Z.first.shape.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FrameEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

theorem gain_snd (x : _root_.Tw.K2.Front) :
    (K2.switchGain x ++ K2.ownGain x).map (·.2) =
      false :: x.T.kept.toList.map (·.keptAgain) ++ x.own.map fun m => decide (0 < m.life) := by
  have hm1 : (K2.switchGain x).map (·.2) = false :: x.T.kept.toList.map (·.keptAgain) := by
    unfold K2.switchGain
    rw [List.map_cons, List.map_map]
    congr 1
    have e : ((fun p : Nat × Bool => p.2) ∘ fun p : Nat × KeptTarget => (p.1, p.2.keptAgain)) =
        (fun k : KeptTarget => k.keptAgain) ∘ Prod.snd := rfl
    rw [e, ← List.map_map, List.map_snd_zip (by simp)]
  have hm2 : (K2.ownGain x).map (·.2) = x.own.map fun m => decide (0 < m.life) := by
    unfold K2.ownGain
    rw [List.map_map]
    have e : ((fun p : Nat × Bool => p.2) ∘
        fun y : OnBytes.Params.ReqMessage × Nat => (y.2, decide (0 < y.1.life))) =
        (fun m : OnBytes.Params.ReqMessage => decide (0 < m.life)) ∘ Prod.fst := rfl
    rw [e, ← List.map_map, List.map_fst_zip (by simp)]
  rw [List.map_append, hm1, hm2]

theorem atMoment_of {sh : ReqShape} {f : ReqFrame} {l : Nat} (hs : f.shape = sh) (hl : f.link = l)
    (m : Nat) : f.atMoment m = (K2.frameAtLink sh l).atMoment m := by
  unfold ReqFrame.atMoment K2.frameAtLink
  rw [hs, hl]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The front at link l's code switching, in the shape's words. -/
theorem front_words (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {x : _root_.Tw.K2.Front} (hx : _root_.Tw.K2.firstFront t₀.st t₀.check.frame = .ok x) :
    x.T = K2.targetAt Z.first.shape l ∧ x.own = (K2.frameAtLink Z.first.shape l).atMoment 0 ∧
      t₀.check.frame.shape = Z.first.shape := by
  obtain ⟨hB, hk⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega)
    (by have k := draw_in_front hS hR O (l := l) (i := 0) (by omega) (by decide); omega) f₀
  obtain ⟨n1, -, -⟩ := K2.link_notices hx Rr.walk hk
  obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  refine ⟨n1, ?_, Rr.walk.shape⟩
  rw [a.out]
  exact K2.atMoment_pub Rr.walk hk 0

/-- **THE OPEN LINK's FRAME IN FRONT OF THE TWO LATER SENDINGS, 1 ≤ l < 24.** -/
theorem frames_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₃ R₅ : List Fmt.RoundView}
    {C C₃ C₅ : List VerifiableInference.Desc.OpenedColumn} {t₃ t₅ : S}
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅)) :
    ∃ L₃ L₅, t₃.link? = some L₃ ∧ t₅.link? = some L₅ ∧
      L₃.check.frame.shape = Z.first.shape ∧ L₃.check.frame.link = l ∧
      L₃.check.frame.moment = 1 ∧
      L₅.check.frame.shape = Z.first.shape ∧ L₅.check.frame.link = l ∧
      L₅.check.frame.moment = 2 := by
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  obtain ⟨x, f, hx, a1, a2, mo, lk, hg, -, sh, -, -⟩ := entry_at hS hR O h1 h24 f₀ f₁
  obtain ⟨-, -, es⟩ := front_words hS hR O h24 f₀ hx
  obtain ⟨L₃, hL₃, e3, -⟩ := (walk_a hS hR O h24 f₁ a1 a2 2 (by omega) t₃ R₃ C₃ f₃).1.link
  obtain ⟨L₅, hL₅, e5, -⟩ := (walk_b hS hR O h24 f₁ f₃ hg a1 a2 1 (by omega) t₅ R₅ C₅ f₅).1.link
  refine ⟨L₃, L₅, hL₃, hL₅, by rw [e3, sh, es], by rw [e3, lk], by rw [e3, mo], ?_, ?_, ?_⟩
  · rw [e5]
    exact sh.trans es
  · rw [e5]
    exact lk
  · rw [e5]
    show f.moment + 1 = 2
    rw [mo]

/-- **THE GROUP's FLAGS IN THE SHAPE's WORDS, AT THE CUTS 14 l + 8 + n, n ≤ 4, 1 ≤ l < 24** (n = 4:
in front of the closing). -/
theorem flags_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 4) {t : S} {r : List Fmt.RoundView}
    {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group) (n₀ : Nat), t.link? = some L ∧ L.link = l ∧
      L.check.frame.group = l ∧ t.st.groups[l]? = some G ∧
      G.members = #[n₀] ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
      G.members.toList.Nodup ∧
      G.kept.toList = false :: (K2.targetAt Z.first.shape l).kept.toList.map (·.keptAgain) ++
        (((K2.frameAtLink Z.first.shape l).atMoment 0).map fun m => decide (0 < m.life)) ++
        (((K2.frameAtLink Z.first.shape l).atMoment 1).map fun m => decide (0 < m.life)) ++
        (((K2.frameAtLink Z.first.shape l).atMoment 2).map fun m => decide (0 < m.life)) := by
  obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * l + 7) (n + 1)
    (by rw [show 14 * l + 7 + (n + 1) = 14 * l + 8 + n by omega]; exact g)
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 5) 2 f₅
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  obtain ⟨x, f, hx, a1, a2, mo, lk, hg, -, sh, -, -⟩ := entry_at hS hR O h1 h24 f₀ f₁
  obtain ⟨eT, eo, es⟩ := front_words hS hR O h24 f₀ hx
  obtain ⟨L, G, hL, e2, e1, hG, em, ek, -, hnd⟩ :=
    (walk_c hS hR O h24 f₁ f₃ f₅ hg a1 a2 n hn t r q g).members
  refine ⟨L, G, t₀.st.oracles.size, hL, e2, by rw [e1]; exact hg, hG, em, hnd, ?_⟩
  have s1 : f.shape = Z.first.shape := sh.trans es
  have k1 : K1.flagsAt f =
      ((K2.frameAtLink Z.first.shape l).atMoment 1).map fun m => decide (0 < m.life) := by
    unfold K1.flagsAt
    rw [mo, atMoment_of s1 lk]
  have k2 : K1.flagsAt (laterF f t₃.st.oracles.size) =
      ((K2.frameAtLink Z.first.shape l).atMoment 2).map fun m => decide (0 < m.life) := by
    unfold K1.flagsAt
    have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    rw [m2, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk]
  rw [ek, k1, k2, gain_snd, eT, eo]

end

#print axioms gain_snd
#print axioms front_words
#print axioms frames_at
#print axioms flags_at

end Meaning.K2
