-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/OwnSize.lean: IN FRONT OF KIND K8's DRAW THE LINK's THIRD SENDING
HAS NOT BEEN: the open link's frame's list "own" has just as many entries as the public shape gives
the link messages of the moments 0 and 1: at all 25 links: at the proof file's seat, in the goals'
scope, from the fold's return alone.
  msgsAt sh l m: the number of the link's messages of a moment, of the shape.
  own_size_draw: l < 24: at the cuts 14 l + 6 and 14 l + 7 (in front of kind K8's draw; in front of
    the second later sending): a link L is open, L.link = l; its frame has the public shape, the
    link l, the moment 2, and own.size = msgsAt sh l 0 + msgsAt sh l 1.
  own_size_head: the like at the head's link, at the cuts 343 and 344.
sh := Z.first.shape.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K8's and K9's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FlagsAt
import Johnson.IMR.FrameAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

/-- The number of link l's messages of moment m. -/
def msgsAt (sh : ReqShape) (l m : Nat) : Nat := ((K2.frameAtLink sh l).atMoment m).length

/-- The frame behind one later sending, from a frame of moment 1. -/
theorem later_size {sh : ReqShape} {f : ReqFrame} {l k n : Nat} (hs : f.shape = sh)
    (hl : f.link = l) (hm : f.moment = 1) (ho : f.own.size = k) :
    (laterF f n).own.size = k + msgsAt sh l 1 ∧ (laterF f n).shape = sh ∧
      (laterF f n).link = l ∧ (laterF f n).moment = 2 := by
  refine ⟨?_, hs, hl, ?_⟩
  · show (f.own ++ (Array.range (f.atMoment f.moment).length).map (· + n)).size = _
    rw [Array.size_append, Array.size_map, Array.size_range, ho, hm, atMoment_of hs hl]
    rfl
  · show f.moment + 1 = 2
    rw [hm]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF KIND K8's DRAW, l < 24** (n = 0), and in front of the second later sending
(n = 1). -/
theorem own_size_draw (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat}
    (hn : n ≤ 1) {t : S} {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 6 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ L, t.link? = some L ∧ L.link = l ∧
      L.check.frame.own.size = msgsAt Z.first.shape l 0 + msgsAt Z.first.shape l 1 ∧
      L.check.frame.shape = Z.first.shape ∧ L.check.frame.link = l ∧
      L.check.frame.moment = 2 := by
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 5) (n + 1)
    (by rw [show 14 * l + 5 + (n + 1) = 14 * l + 6 + n by omega]; exact g)
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  have fin : ∀ {pre : Array Nat} {fl : List Bool} {f : ReqFrame}, At l pre fl f t₁ → Below l t₁ →
      f.group = l → f.shape = Z.first.shape → f.link = l → f.moment = 1 →
      f.own.size = msgsAt Z.first.shape l 0 →
      ∃ L, t.link? = some L ∧ L.link = l ∧
        L.check.frame.own.size = msgsAt Z.first.shape l 0 + msgsAt Z.first.shape l 1 ∧
        L.check.frame.shape = Z.first.shape ∧ L.check.frame.link = l ∧
        L.check.frame.moment = 2 := by
    intro pre fl f a1 a2 hg hs hl hm ho
    obtain ⟨L, hL, e1, e2⟩ := (walk_b hS hR O h24 f₁ f₃ hg a1 a2 n hn t r q g).1.link
    obtain ⟨k1, k2, k3, k4⟩ := later_size (n := t₃.st.oracles.size) hs hl hm ho
    exact ⟨L, hL, e2, by rw [e1]; exact k1, by rw [e1]; exact k2, by rw [e1]; exact k3,
      by rw [e1]; exact k4⟩
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨f, a1, a2, mo, lk, hg, -, sh, -, ow⟩ := entry_at_zero hS hR O f₁
    have e0s := laid_is_start hS hR O f₀
    obtain ⟨-, hk⟩ := laid_at hS hR O (by omega : 0 < 25) f₀
    have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega)
      (by have k := draw_in_front hS hR O (l := 0) (i := 0) (by omega) (by decide); omega) f₀
    refine fin a1 a2 hg (by rw [sh, ← e0s]; exact Rr.walk.shape) lk mo ?_
    rw [ow, Array.size_map, Array.size_range, ← e0s, K2.atMoment_pub Rr.walk hk 0]
    rfl
  · obtain ⟨x, f, hx, a1, a2, mo, lk, hg, -, sh, -, ow⟩ := entry_at hS hR O (by omega) h24 f₀ f₁
    obtain ⟨-, eo, es⟩ := front_words hS hR O h24 f₀ hx
    refine fin a1 a2 hg (sh.trans es) lk mo ?_
    rw [ow, Array.size_map, Array.size_range, eo]
    rfl

/-- **IN FRONT OF KIND K8's DRAW AT THE HEAD's LINK** (the cut 343), and in front of the second
later sending (344). -/
theorem own_size_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat}
    (hn : n ≤ 1) {t : S} {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (343 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ L, t.link? = some L ∧ L.link = 24 ∧
      L.check.frame.own.size = msgsAt Z.first.shape 24 0 + msgsAt Z.first.shape 24 1 ∧
      L.check.frame.shape = Z.first.shape ∧ L.check.frame.link = 24 ∧
      L.check.frame.moment = 2 := by
  have cut : ∀ k ≤ 4, ∃ t' r' q',
      foldBlocks 0 (c.blocksInOrder.take (339 + k)) (ProofFile.startS Z p) R C = .ok (t', r', q') := by
    intro k hk
    exact fold_cut (k := 339 + k) (n + 4 - k)
      (by rw [show 339 + k + (n + 4 - k) = 343 + n by omega]; exact g)
  obtain ⟨t₀, r0, q0, g0⟩ := cut 0 (by omega)
  obtain ⟨t₁, r1, q1, g1⟩ := cut 1 (by omega)
  obtain ⟨t₂, r2, q2, g2⟩ := cut 2 (by omega)
  obtain ⟨t₃, r3, q3, g3⟩ := cut 3 (by omega)
  obtain ⟨t₄, r4, q4, g4⟩ := cut 4 (by omega)
  obtain ⟨G, f, -, hk, H1, mo, lk, -, -, sh, -, ow⟩ := entry_head_frame hS hR O g0 g1
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by decide)
    (by have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide); omega) g0
  have H3 := opn_quiet (step_quiet24 hS hR O (j := 3) (by omega) g2 g3)
    (opn_quiet (step_quiet24 hS hR O (j := 2) (by omega) g1 g2) H1)
  have H4 := step_commit24 hS hR O (j := 4) (Or.inl rfl) g3 g4 H3
  have ho : f.own.size = msgsAt Z.first.shape 24 0 := by
    rw [ow, Array.size_map, Array.size_range, K2.atMoment_pub Rr.walk hk 0]
    rfl
  obtain ⟨k1, k2, k3, k4⟩ := later_size (n := t₃.st.oracles.size) (sh.trans Rr.walk.shape) lk mo ho
  have fin : ∀ {t' : S}, Opn 24 (laterF f t₃.st.oracles.size) t' → t' = t →
      ∃ L, t.link? = some L ∧ L.link = 24 ∧
        L.check.frame.own.size = msgsAt Z.first.shape 24 0 + msgsAt Z.first.shape 24 1 ∧
        L.check.frame.shape = Z.first.shape ∧ L.check.frame.link = 24 ∧
        L.check.frame.moment = 2 := by
    intro t' H e
    subst e
    obtain ⟨L, hL, e1, e2⟩ := H
    exact ⟨L, hL, e2, by rw [e1]; exact k1, by rw [e1]; exact k2, by rw [e1]; exact k3,
      by rw [e1]; exact k4⟩
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact fin H4 (congrArg Prod.fst (Except.ok.inj (g4.symm.trans g)))
  · exact fin (opn_quiet (step_quiet24 hS hR O (j := 5) (by omega) g4 g) H4) rfl

end

#print axioms own_size_draw
#print axioms own_size_head

end Meaning.K2
