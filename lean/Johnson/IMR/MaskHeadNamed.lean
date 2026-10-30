-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MaskHeadNamed.lean: mask_named (Johnson/IMR/MaskNamed.lean) AT THE HEAD's LINK: the open
link's frame's field mask as a number, at every cut 340 + n, n ≤ 10 (from behind "H:2" to in front
of the closing): at the proof file's seat, in the goals' scope, from the fold's return alone.
Theorems, proved.

Compiled with the whole library.

  h2_place_mask    ON THE TEXT: behind an accept of the code switch with the quiet step behind it
    (the place "H:2"): the open link's frame's mask is some (s.st.oracles.size +
    (1 + G.target.kept.size) + (s.check.frame.atMoment 0).length). THE FRONT OF ITS PROOF IS
    h2_place_frame's OWN (Johnson/IMR/FrameAll.lean), copied by program.
  h2_mask          the same at the seat's arm: h2_frame's own case split, copied by program.
  entry_mask_head  AT THE SEAT: behind "H:2" (the cut 340). ITS DESCENT IS entry_head_frame's OWN,
    copied by program.
  **mask_head_named**   at every cut 340 + n, n ≤ 10: by frame_walk_head; in the public shape's
    words, as flags_head_named (Johnson/IMR/FlagsHeadNamed.lean) turns them: front_pin_head,
      K2.atMoment_pub.
sh := Z.first.shape.

OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files. LETTERS: none.

What is not claimed. The count at 339 as a closed number (n0_at_head_paid,
Johnson/IMR/ToldPaid.lean; in the
table's words: size_at_table). That a fold returns is shown of no proof here. No soundness.

-/
import Johnson.IMR.MaskNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- **ON THE TEXT: the open link's frame's mask behind the place "H:2".** -/
theorem h2_place_mask {p : K2.P2} {n : String} {HP : K2.HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((K2.codeSwitchKind p : Block S Unit).andThen n (K2.headOpened n p.place HP)).decide s rs gs =
      .ok s') :
    ∃ (a : HeadOwn) (G : ReqGroup) (L : LinkCtx), s.here = .head a ∧
      s.check.frame.groups[s.check.frame.link]? = some G ∧ s'.link? = some L ∧
      L.check.frame.mask = some (s.st.oracles.size + (1 + G.target.kept.size) +
        (s.check.frame.atMoment 0).length) := by
  have hp := K2.placeH2_stands h
  obtain ⟨m, h₁, h₂⟩ := andThen_yes h
  have h₁' : K2.decideWith _root_.Tw.K2.sendByL8 p s _ _ = .ok m := h₁
  have h₂' : K2.headOpenQ HP m = .ok s' := h₂
  obtain ⟨r₁, r₂, a, G, w, roots, -, k⟩ := K2.head_inv hp h₁'
  obtain ⟨lay, -, -, e2, e3⟩ := K2.switch_numbers k.hSwitch
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (K2.headOpenQ_iff HP m s').1 h₂'
  obtain ⟨-, ⟨b', hb', ho⟩, -⟩ := K2.headOpenOpens HP m s' h₂'
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hmc : m.check = s.check := by rw [k.hOut]
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  obtain ⟨-, -, hL, -⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := HP.X.Fp.trees }) HP.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hx : (K2.headFrontOf s a G.target).others.size =
      (K2.headFrontOf s a G.target).own.length + 1 := by
    simp [K2.headFrontOf, ReqFrame.notices]
  have hN : (_root_.Tw.K2.switchNotices (K2.headFrontOf s a G.target).T
      (K2.headFrontOf s a G.target).others).size =
      1 + G.target.kept.size + (K2.headFrontOf s a G.target).others.size := by
    simp [_root_.Tw.K2.switchNotices, K2.headFrontOf]
    omega
  have hx' : (K2.headFrontOf s a G.target).others.size =
      (s.check.frame.atMoment 0).length + 1 := hx
  have hm : w.out.others[(s.check.frame.atMoment 0).length]? = some mask := by
    have e : a2.ids[(m.check.frame.atMoment 0).length]? = some mask := bA.theMask
    rw [ha2, hmc] at e
    exact e
  have key : w.out.others[(s.check.frame.atMoment 0).length]? =
      some (s.st.oracles.size + (1 + G.target.kept.size) +
        (s.check.frame.atMoment 0).length) := by
    rw [e3]
    exact others_get s.st.oracles.size _ (1 + G.target.kept.size)
      (s.check.frame.atMoment 0).length (by omega)
  refine ⟨a, G, L, k.hHere, k.hGroup, ?_, ?_⟩
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [hL]
    show f.mask = _
    rw [bA.frame]
    exact hm.symm.trans key

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The place "H:2" at its seat: the arm read off the accept. -/
theorem h2_mask {G₀ : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ (G : ReqGroup) (L : LinkCtx),
      s.check.frame.groups[s.check.frame.link]? = some G ∧ t.link? = some L ∧
      L.check.frame.mask = some (s.st.oracles.size + (1 + G.target.kept.size) +
        (s.check.frame.atMoment 0).length) := by
  rcases hx with ⟨-, hm⟩ | ⟨P', n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      have h' : ((K2.codeSwitchKind (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name
                      .head n) : Block S Unit).andThen x.name (K2.headOpened x.name
                      (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n).place
                      HP)).decide s rs gs = .ok t := h
      obtain ⟨a', G, L, ha', k⟩ := h2_place_mask h'
      obtain rfl : a' = a := by
        rw [ha] at ha'
        injection ha' with e'
        exact e'.symm
      exact ⟨G, L, k⟩
    · rw [e] at h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ :=
        K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl h
      rw [Lk.hHere] at ha
      cases ha

/-- **AT THE SEAT: BEHIND THE PLACE "H:2".** t₁: the state in front of "H:2". -/
theorem entry_mask_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₁ R₂ : List Fmt.RoundView} {C C₁ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₁ t₂ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (G : ReqGroup) (L : LinkCtx), t₁.check.frame.groups[24]? = some G ∧ t₂.link? = some L ∧
      L.link = 24 ∧
      L.check.frame.mask = some (t₁.st.oracles.size + (1 + G.target.kept.size) +
        (t₁.check.frame.atMoment 0).length) := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f₁
  obtain ⟨L, hL, eN, eG⟩ := entry_head hS hR O f₀ f₁ f₂
  obtain ⟨-, hk0⟩ := laid_at hS hR O (l := 24) (by omega) f₀
  obtain ⟨Lk, b0, eL, e0, J, -⟩ := IM.k7_sits hS hR O
  obtain ⟨Lk', b1, x, eL', e1, -, la, hx⟩ := IM.k2_head_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have q := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 0] at q
  have i1 : c.blocksInOrder[339]? = some b1 := by
    have q := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1] at q
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  obtain ⟨a, ha, o1, o2, o3, o4, o5⟩ := h1_fr (IM.k7_sits_yes hS hR O J d0).1
  have hk1 : t₁.check.frame.link = 24 := by rw [o5]; exact hk0
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
  obtain ⟨G, L', g1, hL', hmk⟩ :=
    h2_mask hx ((IM.yes_alone la (by intro k; cases k) _ _ rs1 gs1).1 d1).1 ha
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  rw [hk1] at g1
  exact ⟨G, L, g1, hL, eN, hmk⟩

/-- **THE FRAME's MASK AT EVERY CUT 340 + n, n ≤ 10.** -/
theorem mask_head_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₀ : S) (R₀ : List Fmt.RoundView) (C₀ : List VerifiableInference.Desc.OpenedColumn) (L : LinkCtx),
      foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      t.link? = some L ∧ L.link = 24 ∧
      L.check.frame.mask = some (t₀.st.oracles.size +
        (1 + (K2.targetAt Z.first.shape 24).kept.size) + msgsAt Z.first.shape 24 0) := by
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) n g
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 339) f₂
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨Gr, L₂, hGr, hL₂, eN₂, hm₂⟩ := entry_mask_head hS hR O f₀ f₂
  obtain ⟨L, hL, eF, eN⟩ := (frame_walk_head hS hR O
    (n₃ := match foldBlocks 0 (c.blocksInOrder.take (340 + 2)) (ProofFile.startS Z p) R C with
      | .ok x => x.1.st.oracles.size
      | .error _ => 0)
    (n₅ := match foldBlocks 0 (c.blocksInOrder.take (340 + 4)) (ProofFile.startS Z p) R C with
      | .ok x => x.1.st.oracles.size
      | .error _ => 0)
    (fun _ _ _ h => by rw [h]) (fun _ _ _ h => by rw [h]) f₂
    (⟨L₂, hL₂, rfl, eN₂⟩ : Opn 24 L₂.check.frame t₂)).1 n hn t r q g
  -- the words of the public shape
  obtain ⟨-, hk0⟩ := laid_at hS hR O (l := 24) (by omega) fm
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 0).trans (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  obtain ⟨x, a, hx, ha, -, -, hck⟩ := h1_front (IM.k7_sits_yes hS hR O hj d0).1
  have hk : t₀.check.frame.link = 24 := by rw [hck]; exact hk0
  have hfx : K2.frontAt headQ t₀ = some (K2.headFrontOf t₀ a Gr.target) := by
    unfold K2.frontAt
    rw [show headQ.stands = .head from rfl, ha, hk, hGr]
    rfl
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by decide)
    (by have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide); omega) f₀
  obtain ⟨-, -, eT, -⟩ := front_pin_head hS hR O f₀ rfl hfx
  have eT' : Gr.target = K2.targetAt Z.first.shape 24 := eT
  refine ⟨t₀, R₀, C₀, L, f₀, hL, eN, ?_⟩
  rw [eF, seqF_mask, hm₂, eT', K2.atMoment_pub Rr.walk hk 0]
  rfl

end

#print axioms h2_place_mask
#print axioms h2_mask
#print axioms entry_mask_head
#print axioms mask_head_named

end Meaning.K2
