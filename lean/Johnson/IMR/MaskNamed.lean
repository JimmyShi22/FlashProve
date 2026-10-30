-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MaskNamed.lean: THE OPEN LINK's FRAME's FIELD mask ("the fresh mask of the present
link's closing") AS A NUMBER: the oracle message right behind the link's own messages of moment 0:
at the links 1 to 23, at every cut 14 l + 3 + n, n ≤ 9 (from behind the code switch to in front of
the closing): at the proof file's seat, in the goals' scope, from the fold's return alone.
Theorems, proved.

Compiled with the whole library.

  others_get       the numbers of a sending, cut: entry number k.
  yes_link_mask    ON THE TEXT: behind an accept of the code switch at a link: the frame's mask is
    some (x.st.oracles.size + (1 + x.T.kept.size) + x.own.length), x the front that the text makes
    of the state in front. By BehindAsks.theMask (Johnson/Top/H0/Tw/K2C/Asks.lean) and
    switch_numbers (LinkNumbers.lean).
  entry_mask       AT THE SEAT: behind the first sub-protocol of link l, 1 ≤ l < 24: in the public
    shape's words. ITS DESCENT TO THE TEXT's ACCEPT IS entry_at's OWN (Johnson/IMR/FrameEntry.lean),
      LINE FOR
    LINE, copied by program.
  seqF_mask        a later sending leaves the field.
  **mask_named**   at every cut 14 l + 3 + n, n ≤ 9: by frame_walk_link (Johnson/IMR/FrameAll.lean).
sh := Z.first.shape.

OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files. LETTERS: none.

What is not claimed. Anything at link 0 or at the head's link. The count at 14 l + 2 as a closed
number (n0_at_link_paid, Johnson/IMR/ToldPaid.lean; in the table's words: size_at_table,
Johnson/IMR/FlagsNamed.lean).
That a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FlagsNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- Entry number k of the numbers of a sending, cut from a on. -/
theorem others_get (n0 N a k : Nat) (h : a + k < N) :
    ((K2.sentIds n0 N).extract a N)[k]? = some (n0 + a + k) := by
  unfold K2.sentIds
  rw [Array.getElem?_eq_getElem (by simp; omega)]
  simp
  omega

/-- **ON THE TEXT: the frame's mask behind the code switch at a link.** -/
theorem yes_link_mask {p : K2.P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S} (hp : p.stands = .link)
    (h : K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, _root_.Tw.K2.firstFront s.st s.check.frame = .ok x ∧
      s'.check.frame.mask = some (x.st.oracles.size + (1 + x.T.kept.size) + x.own.length) := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := K2.link_inv hp h
  obtain ⟨lay, -, -, -, e3⟩ := K2.switch_numbers k.hSwitch
  obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.hFront
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  have ho : x.others.size = x.own.length + 1 := by
    rw [a.out]
    simp [ReqFrame.notices]
  have hN : (_root_.Tw.K2.switchNotices x.T x.others).size =
      1 + x.T.kept.size + x.others.size := by
    simp [_root_.Tw.K2.switchNotices]
    omega
  have hm := bA.theMask
  rw [e3, others_get _ _ _ _ (by omega)] at hm
  refine ⟨x, k.hFront, ?_⟩
  rw [k.hOut]
  show f.mask = _
  rw [bA.frame]
  exact congrArg some (Option.some.inj hm).symm

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE SEAT: BEHIND THE FIRST SUB-PROTOCOL OF LINK l, 1 ≤ l < 24.** -/
theorem entry_mask (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView}
    {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ L : LinkCtx, t₁.link? = some L ∧ L.link = l ∧
      L.check.frame.mask = some (t₀.st.oracles.size +
        (1 + (K2.targetAt Z.first.shape l).kept.size) + msgsAt Z.first.shape l 0) := by
  obtain ⟨hB, hlk0⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have hc := count_at hS hR O l (by omega) t₀ R₀ C₀ f₀
  obtain ⟨L, hL, eLn, eLg⟩ := entry_group hS hR O h24 f₀ f₁
  obtain ⟨Lk, b, x0, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l h1 h24
  have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
      (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y1' : x0.decide t₀ rs' gs' = .ok m := y1
  have mB := switch_between hx y1' hB
  have mo := switch_moment hx y1' hB
  have v := ((framesOf_live hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
  have eLc : L.check = m.check := by rw [← live_open hL, v, live_between mB]
  have st1 : t₁.st = m.st := framesOf_st hfs fr (List.mem_of_getElem? hf) m t₁ y3
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
  · obtain ⟨er, he⟩ := hm t₀ rs' gs'
    rw [he] at y1'
    cases y1'
  · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases hn
    · rw [ex] at y1'
      obtain ⟨w, a1, -⟩ := andThen_yes (n := x0.name) y1'
      obtain ⟨r₁, r₂, a, G', w', roots, -, H⟩ := K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [ex] at y1'
      have h' : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x0.name .link n) t₀
          rs' gs' = .ok m := y1'
      obtain ⟨x, hxf, hmk⟩ := yes_link_mask rfl h'
      obtain ⟨x₃, hx₃, e0s, -⟩ := K2.yes_link_groups rfl h'
      obtain rfl : x₃ = x := Except.ok.inj (hx₃.symm.trans hxf)
      obtain ⟨eT, eo, -⟩ := front_words hS hR O h24 f₀ hxf
      refine ⟨L, hL, eLn, ?_⟩
      rw [eLc, hmk, e0s, eT, eo]
      rfl

/-- A later sending leaves the field. -/
theorem seqF_mask (f : ReqFrame) (n₃ n₅ i : Nat) : (seqF f n₃ n₅ i).mask = f.mask := by
  unfold seqF
  split
  · rfl
  · split <;> rfl

/-- **THE FRAME's MASK AT EVERY CUT 14 l + 3 + n, n ≤ 9, OF A LINK 1 ≤ l < 24.** -/
theorem mask_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 9) {t : S} {r : List Fmt.RoundView}
    {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₀ : S) (R₀ : List Fmt.RoundView) (C₀ : List VerifiableInference.Desc.OpenedColumn) (L : LinkCtx),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      t.link? = some L ∧ L.link = l ∧
      L.check.frame.mask = some (t₀.st.oracles.size +
        (1 + (K2.targetAt Z.first.shape l).kept.size) + msgsAt Z.first.shape l 0) := by
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) n g
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  obtain ⟨L₁, hL₁, eN₁, hm₁⟩ := entry_mask hS hR O h1 h24 f₀ f₁
  obtain ⟨L, hL, eF, eN⟩ := (frame_walk_link hS hR O h24
    (n₃ := match foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + 2)) (ProofFile.startS Z p) R C with
      | .ok x => x.1.st.oracles.size
      | .error _ => 0)
    (n₅ := match foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + 4)) (ProofFile.startS Z p) R C with
      | .ok x => x.1.st.oracles.size
      | .error _ => 0)
    (fun _ _ _ h => by rw [h]) (fun _ _ _ h => by rw [h]) f₁
    (⟨L₁, hL₁, rfl, eN₁⟩ : Opn l L₁.check.frame t₁)).1 n hn t r q g
  exact ⟨t₀, R₀, C₀, L, f₀, hL, eN, by rw [eF, seqF_mask]; exact hm₁⟩

end

#print axioms others_get
#print axioms yes_link_mask
#print axioms entry_mask
#print axioms seqF_mask
#print axioms mask_named

end Meaning.K2
