-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MaskZeroNamed.lean: mask_named (Johnson/IMR/MaskNamed.lean) AT LINK 0: the open link's
frame's field mask as a number, at every cut 3 + n, n ≤ 9 (from behind the link's opening to in
front of its closing): at the proof file's seat, in the goals' scope, from the fold's return alone.
Theorems, proved.

Compiled with the whole library.

  firstOwn_mask    ON THE TEXT: behind an accept of kind K1's opening's decision: the frame's mask
    is some (d.st.oracles.size + (c.frame.atMoment 0).length). THE FRONT OF ITS PROOF IS
    firstOwn_frame''s OWN (Johnson/Desc/K1/Law/FrameAtFirst.lean, which says "there is a mask"),
    copied by program.
  firstAtS_mask    the block at the verifier's state.
  entry_mask_zero  AT THE SEAT: behind link 0's first sub-protocol (the cut 3): some
    (msgsAt sh 0 0): the first state has no message (start_msgs, Johnson/IMR/KeptJoin.lean). ITS
      DESCENT IS entry_at_zero's OWN (FrameEntry.lean),
    copied by program.
  **mask_zero_named**   at every cut 3 + n, n ≤ 9: by frame_walk_link at l = 0.
sh := Z.first.shape.

OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files. LETTERS: none.

What is not claimed. That a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.MaskNamed
import Johnson.IMR.KeptJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM.K1Mask

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.K1
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **ON THE TEXT: the frame's mask behind the opening's decision.** -/
theorem firstOwn_mask (P : K1.Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) :
    c'.frame.mask = some (d.st.oracles.size + (c.frame.atMoment 0).length) := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨mask, hmask, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, hfin⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, hids, _⟩ := (decideSend_iff P owed d₁ d₂ r₁ r₂ ids).1 h2
  have hn := (newGroupP_book _ _ _ _ _ ((named_ok _ _ _).1 h1)).2
  have hf : f₂ = _ := joinOwnP_frame _ _ _ _ _ _ ((named_ok _ _ _).1 h3)
  have hI : ids = idsOf P d.st.oracles.size := by rw [hids, hn]; rfl
  have hlt : (c.frame.atMoment 0).length < ids.size := by
    have hm := (named_ok _ _ _).1 hmask
    by_contra hx
    rw [Array.getElem?_eq_none (by omega)] at hm
    cases hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hfin)
  subst hI
  have hm := (named_ok _ _ _).1 hmask
  rw [idsOf_get P d.st.oracles.size _ (by rw [idsOf_size] at hlt; exact hlt)] at hm
  show ({ f₂ with next := .laterOrClose } : ReqFrame).mask = _
  rw [hf]
  exact hm.symm

/-- The block at the verifier's state. -/
theorem firstAtS_mask (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.check.frame.mask = some (s.st.oracles.size + (s.check.frame.atMoment 0).length) := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact firstOwn_mask _ _ _ c _ d' r₁ r₂ h2

end IM.K1Mask

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE SEAT: BEHIND THE FIRST SUB-PROTOCOL OF LINK 0.** -/
theorem entry_mask_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ L : LinkCtx, t₁.link? = some L ∧ L.link = 0 ∧
      L.check.frame.mask = some (msgsAt Z.first.shape 0 0) := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * 0 + 2) f₁
  have e0s := laid_is_start hS hR O f₀
  obtain ⟨Hh, -⟩ := entry_zero hS hR O f₁
  obtain ⟨L, hL, eLn, eLg⟩ := entry_group hS hR O (by omega : 0 < 24) f₀ f₁
  obtain ⟨hB, hlk0⟩ := laid_at hS hR O (by omega : 0 < 25) f₀
  obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
  have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
      (by omega : 14 * 0 + 0 + 2 = 14 * 0 + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs' gs' = .ok m := y1
  obtain ⟨r₁, r₂, er⟩ := firstAtS_two y'
  rw [er] at y'
  obtain ⟨g', mask, e, -, lt⟩ := K1.firstAtS_frame _ _ t₀ m r₁ r₂ _ y'
  have hR0 : t₀.roots = t₀.book.trees.size := by
    rw [e0s, (start_empty O.pub p).1, (start_empty O.pub p).2]
    rfl
  have hK : t₀.check.frame.keptBefore = #[] := by
    rw [e0s]
    exact start_kept O.pub p
  obtain ⟨-, mB⟩ := opening_lists y' hB hR0 hK
  have v := ((framesOf_live hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
  have eLc : L.check = m.check := by rw [← live_open hL, v, live_between mB]
  have hmk := IM.K1Mask.firstAtS_mask _ _ t₀ m r₁ r₂ _ y'
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega)
    (by have k := draw_in_front hS hR O (l := 0) (i := 0) (by omega) (by decide); omega) f₀
  have ea : t₀.check.frame.atMoment 0 = (K2.frameAtLink Z.first.shape 0).atMoment 0 :=
    K2.atMoment_pub Rr.walk hlk0 0
  have e0 : t₀.st.oracles.size = 0 := by
    rw [e0s, start_msgs O.pub p]
    rfl
  refine ⟨L, hL, eLn, ?_⟩
  rw [eLc, hmk, e0, ea, Nat.zero_add]
  rfl

/-- **THE FRAME's MASK AT EVERY CUT 3 + n, n ≤ 9, OF LINK 0.** -/
theorem mask_zero_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 9) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ L : LinkCtx, t.link? = some L ∧ L.link = 0 ∧
      L.check.frame.mask = some (msgsAt Z.first.shape 0 0) := by
  have g' : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    rw [show 14 * 0 + 3 + n = 3 + n by omega]
    exact g
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * 0 + 3) n g'
  obtain ⟨L₁, hL₁, eN₁, hm₁⟩ := entry_mask_zero hS hR O f₁
  obtain ⟨L, hL, eF, eN⟩ := (frame_walk_link hS hR O (by omega : 0 < 24)
    (n₃ := match foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3 + 2)) (ProofFile.startS Z p) R C with
      | .ok x => x.1.st.oracles.size
      | .error _ => 0)
    (n₅ := match foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3 + 4)) (ProofFile.startS Z p) R C with
      | .ok x => x.1.st.oracles.size
      | .error _ => 0)
    (fun _ _ _ h => by rw [h]) (fun _ _ _ h => by rw [h]) f₁
    (⟨L₁, hL₁, rfl, eN₁⟩ : Opn 0 L₁.check.frame t₁)).1 n hn t r q g'
  exact ⟨L, hL, eN, by rw [eF, seqF_mask]; exact hm₁⟩

end

end Meaning.K2

#print axioms IM.K1Mask.firstOwn_mask
#print axioms IM.K1Mask.firstAtS_mask
#print axioms Meaning.K2.entry_mask_zero
#print axioms Meaning.K2.mask_zero_named
