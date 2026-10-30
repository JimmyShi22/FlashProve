-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameAll.lean: THE OPEN LINK's FRAME, WRITTEN OUT, AT EVERY CUT OF
EVERY ONE OF THE 25 LINKS AT WHICH A LINK IS OPEN: at the proof file's seat, in the goals' scope,
from the fold's return alone. THE FRAME ALONE: nothing on the link's group's members (for these, at
l < 24: Johnson/IMR/FrameAt.lean's At). "The state": the verifier's state, the value that the fold
of the IOP
as written in Lean carries from sub-protocol to sub-protocol. "The cut k": the state behind the flat
list's first k entries.
  Opn l f t: at t a link is open with the number l and the frame f (the first half of At).
  closedF f rows: the frame behind the closing: rows, no mask, the link's number raised by 1, next =
    first; every other field f's (closeFrame_lays' term, Johnson/Desc/First/Close/Law/Lays.lean).
  opn_quiet, opn_gby, opn_commit: over a Quiet step; over a step that leaves the open link's frame;
    over kind K1's later sending: laterF f n, n the number of messages in front of it.
  h2_place_frame, h2_frame, h1_fr, entry_head_frame: THE ENTRY AT THE HEAD's LINK: behind the place
    "H:2" (the cut 340): moment 1, link 24, group 24, next = later or close, the shape of the walk's
    frame; keptBefore = n₀ + 1 + i (i < K); own = n₀ + 1 + K + j (j < the number of the link's
    messages of moment 0); n₀: the number of messages at the cut 339; K: the number of old messages
    that the group's target keeps. (Johnson/IMR/FrameEntry.lean's entry_at's letters.)
  hear_flat24: the head's link's nine hearing sub-protocols by number in the flat list.
  hear_commitQ24, hear_quiet24, step_quiet24, step_commit24, step_commit_opn: over one of them.
  rest_front_of_runs: A TOOL, l < 25: the batching, what runs behind it and the one equation keep a
    relation, given the hearing sub-protocols' runs. closing_opn, shutting_opn: l < 25.
  seqF f n₃ n₅ i: the frame at the i-th cut behind the entry: f (i ≤ 2), laterF f n₃ (i ≤ 4),
    laterF (laterF f n₃) n₅ (from 5 on). KeepAt, GrowAt, walk_steps, keep_rest, closed_cuts.
  frame_walk_link (l < 24; the entry's cut e = 14 l + 3), frame_walk_head (e = 340): THE TOPS: from
    Opn l f at e: at e + k, up to in front of the closing (k ≤ 9; at the head's link k ≤ 10):
    Opn l (seqF f n₃ n₅ k); behind the closing and behind the shutting: for some rows:
    Opn l (closedF (laterF (laterF f n₃) n₅) rows). n₃, n₅: letters, under the premises that they
    are the numbers of messages at the cuts e + 2 and e + 4 of the same fold (in front of the two
    later sendings: hearing numbers 3 and 5; at the head's link 4 and 6).
NOT HERE: f's fields at l < 24 (Johnson/IMR/FrameEntry.lean); the numbers n₀, n₃, n₅ and K as terms
of the
list of rounds and of the shape (Johnson/IMR/FrameField.lean takes them as named premises).
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: the list of facts along the fold
(field "frameIs"); whoever walks the head's link by place.
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.FrameEntry
import Johnson.IMR.GroupHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- At t a link is open with the number l and the frame f. -/
def Opn (l : Nat) (f : ReqFrame) (t : S) : Prop :=
  ∃ L, t.link? = some L ∧ L.check.frame = f ∧ L.link = l

/-- The frame behind the closing (closeFrame_lays' term, Johnson/Desc/First/Close/Law/Lays.lean). -/
def closedF (f : ReqFrame) (rows : SingleRows) : ReqFrame :=
  { f with rows := rows, mask := none, link := f.link + 1, next := .first }

theorem At.opn {l : Nat} {pre : Array Nat} {fl : List Bool} {f : ReqFrame} {t : S}
    (H : At l pre fl f t) : Opn l f t := H.link

theorem opn_quiet {l : Nat} {f : ReqFrame} {s t : S} (q : Quiet s t) (H : Opn l f s) :
    Opn l f t := by
  obtain ⟨L, hL, e1, e2⟩ := H
  obtain ⟨L', a, c, -, n⟩ := quiet_fwd q hL
  exact ⟨L', a, by rw [c]; exact e1, n.trans e2⟩

theorem opn_gby {l : Nat} {f : ReqFrame} {s t : S} (q : GBy (fun f : ReqFrame => f) s t)
    (H : Opn l f s) : Opn l f t := by
  obtain ⟨L, hL, e1, e2⟩ := H
  obtain ⟨L', a, c, n⟩ := q L hL
  exact ⟨L', a, c.trans e1, n.trans e2⟩

/-- **Kind K1's later sending**: the frame alone (FrameAt.lean's at_commit without the group). -/
theorem opn_commit {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v)
    {l : Nat} {f : ReqFrame} (H : Opn l f s) : Opn l (laterF f s.st.oracles.size) v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨L, hL, e1, e2⟩ := H
  obtain ⟨L₀, L', a1, a2, e, -⟩ := K1.commitAtS_frame Q link moment arrays s v r₁ r₂ gs h
  obtain rfl : L₀ = L := Option.some.inj (a1.symm.trans hL)
  obtain ⟨M, M', b1, b2, -, m2, -⟩ := K1.commitAtS_moments Q link moment arrays s v _ gs h
  obtain rfl : M = L₀ := Option.some.inj (b1.symm.trans hL)
  obtain rfl : M' = L' := Option.some.inj (b2.symm.trans a2)
  have hlen := commit_len h hL
  rw [e1] at hlen e
  have hk : Q.sent.size = (f.atMoment f.moment).length := by
    simpa [K1.idsOf, K1.flagsAt] using hlen
  have hid : K1.idsOf Q s.st.oracles.size =
      (Array.range (f.atMoment f.moment).length).map (· + s.st.oracles.size) := by
    unfold K1.idsOf
    rw [hk]
  exact ⟨M', a2, by rw [e, hid]; rfl, m2.trans e2⟩

/-- **An accept of the whole place "H:2": the open link's frame, field by field**: a the head's own
part of the state in front, G the group of the walk's frame's link. -/
theorem h2_place_frame {p : K2.P2} {n : String} {HP : K2.HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((K2.codeSwitchKind p : Block S Unit).andThen n (K2.headOpened n p.place HP)).decide s rs gs =
      .ok s') :
    ∃ (a : HeadOwn) (G : ReqGroup) (L : LinkCtx), s.here = .head a ∧
      s.check.frame.groups[s.check.frame.link]? = some G ∧ s'.link? = some L ∧
      L.check.frame.moment = a.fr.moment ∧ L.check.frame.link = a.fr.link ∧
      L.check.frame.next = .laterOrClose ∧ L.check.frame.shape = a.fr.shape ∧
      L.check.frame.keptBefore =
        (Array.range G.target.kept.size).map (· + (s.st.oracles.size + 1)) ∧
      L.check.frame.own = a.fr.own ++ (Array.range (s.check.frame.atMoment 0).length).map
        (· + (s.st.oracles.size + (1 + G.target.kept.size))) := by
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
  refine ⟨a, G, L, k.hHere, k.hGroup, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [hL]
    show f.moment = _
    rw [bA.frame]
    show a2.fr.moment = _
    rw [ha2]
  · rw [hL]
    show f.link = _
    rw [bA.frame]
    show a2.fr.link = _
    rw [ha2]
  · rw [hL]
    show f.next = _
    rw [bA.frame]
  · rw [hL]
    show f.shape = _
    rw [bA.frame]
    show a2.fr.shape = _
    rw [ha2]
  · rw [hL]
    show f.keptBefore = _
    rw [bA.frame]
    show a2.kept = _
    rw [ha2]
    show w.out.kept = _
    rw [e2]
    exact K2.ids_cut _ _ 1 G.target.kept.size (by omega)
  · rw [hL]
    show f.own = _
    rw [bA.frame]
    show a2.fr.own ++ mine = _
    rw [bA.theOwn, ha2]
    show a.fr.own ++ w.out.others.extract 0 (m.check.frame.atMoment 0).length = _
    rw [hmc]
    exact congrArg (a.fr.own ++ ·) (K2.mine_is e3 hx)

/-- Behind the place "H:1": the head's own copy of the frame. -/
theorem h1_fr {W : Verify.Public} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block W 24).decide s rs gs = .ok t) :
    ∃ a, t.here = .head a ∧ a.fr.own = #[] ∧ a.fr.shape = t.check.frame.shape ∧
      a.fr.link = t.check.frame.link ∧ a.fr.moment = 1 ∧ t.check = s.check := by
  obtain ⟨m, a1, a2⟩ := andThen_yes h
  have hq : K2.headFrontQ W.H.tl s = .ok m :=
    ((guarded_yes _ (fun _ => false) _ rfl s _ _ m).1 a1).1
  obtain ⟨a, ha, f1, f2, -, f4, f5, f6⟩ := K2.headFrontQ_fr hq
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 W.hS.V a2
  exact ⟨a, ha, f5, f1, f2, f4, f6⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The place "H:2" at its seat**: h2_place_frame, the arm read off the accept. -/
theorem h2_frame {G₀ : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) :
    ∃ (G : ReqGroup) (L : LinkCtx),
      s.check.frame.groups[s.check.frame.link]? = some G ∧ t.link? = some L ∧
      L.check.frame.moment = a.fr.moment ∧ L.check.frame.link = a.fr.link ∧
      L.check.frame.next = .laterOrClose ∧ L.check.frame.shape = a.fr.shape ∧
      L.check.frame.keptBefore =
        (Array.range G.target.kept.size).map (· + (s.st.oracles.size + 1)) ∧
      L.check.frame.own = a.fr.own ++ (Array.range (s.check.frame.atMoment 0).length).map
        (· + (s.st.oracles.size + (1 + G.target.kept.size))) := by
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
      obtain ⟨a', G, L, ha', k⟩ := h2_place_frame h'
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

/-- **BEHIND THE PLACE "H:2": THE OPEN LINK's FRAME** (FrameEntry.lean's entry_at's letters, with
G.target in the place of x.T): t₁: the state in front of "H:2". -/
theorem entry_head_frame (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₁ R₂ : List Fmt.RoundView} {C C₁ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₁ t₂ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (G : ReqGroup) (f : ReqFrame), t₁.check.frame.groups[24]? = some G ∧
      t₁.check.frame.link = 24 ∧ Opn 24 f t₂ ∧
      f.moment = 1 ∧ f.link = 24 ∧ f.group = 24 ∧ f.next = .laterOrClose ∧
      f.shape = t₁.check.frame.shape ∧
      f.keptBefore = (Array.range G.target.kept.size).map (· + (t₁.st.oracles.size + 1)) ∧
      f.own = (Array.range (t₁.check.frame.atMoment 0).length).map
        (· + (t₁.st.oracles.size + (1 + G.target.kept.size))) := by
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
  obtain ⟨G, L', g1, hL', m1, m2, m3, m4, m5, m6⟩ :=
    h2_frame hx ((IM.yes_alone la (by intro k; cases k) _ _ rs1 gs1).1 d1).1 ha
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  rw [hk1] at g1
  refine ⟨G, L.check.frame, g1, hk1, ⟨L, hL, rfl, eN⟩, m1.trans o4, (m2.trans o3).trans hk1, eG,
    m3, m4.trans o2, m5, ?_⟩
  rw [m6, o1, Array.empty_append]

/-- The hearing sub-protocols of the head's link, by number in the flat list. -/
theorem hear_flat24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ Lk, c.links[24]? = some Lk ∧ Lk.hear.length = 9 ∧
      ∀ j < 9, ∃ b, Lk.hear[j]? = some b ∧ c.blocksInOrder[338 + j]? = some b := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  refine ⟨Lk, eL, hlen, fun j hj => ?_⟩
  obtain ⟨b, e⟩ : ∃ b, Lk.hear[j]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : j < Lk.hear.length)⟩
  refine ⟨b, e, ?_⟩
  have q := IM.hear_at_flat eL e
  rwa [(IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) j).trans
    (by omega : 14 * 24 + j + 2 = 338 + j)] at q

/-- Hearing sub-protocols number 4 and 6 of the head's link: kind K1's later sending, then a Quiet
step (FrameAt.lean's hear_commitQ at l = 24). -/
theorem hear_commitQ24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {j : Nat} (hj : j = 4 ∨ j = 6) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[24]? = some Lk) (e : Lk.hear[j]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok t) :
    ∃ (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (v : S) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))),
      (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs' gs' = .ok v ∧
        Quiet v t := by
  have hk : (kindsBeforeBatching (IM.subAt 24) (24 == 0))[j]? = some KindName.K1 := by
    rcases hj with rfl | rfl <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O 24 (IM.subAt 24) (IM.subs_scope hS hR O 24 (by omega)) j hk
      (by rcases hj with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · have h' : (IM.k1Reads Z Bs.G₀ 24 Xl pr reads).decide s rs gs = .ok t :=
      ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
    obtain ⟨v, a1, a2⟩ := andThen_yes h'
    exact ⟨_, _, _, _, v, _, _, a1, (orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2⟩
  · exact ⟨_, _, _, _, t, rs, gs, ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1,
      quiet_refl t⟩

/-- Hearing sub-protocols number 2, 3, 5, 7 and 8 of the head's link are Quiet. -/
theorem hear_quiet24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {j : Nat} (hj : j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 8) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[24]? = some Lk) (e : Lk.hear[j]? = some b) : Decides Quiet b := by
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact (head_k3 hS hR O eL false e).decides fun _ _ q => q
  · exact (head_k6 hS hR O eL e).decides fun _ _ q => q
  · exact (head_k8 hS hR O eL e).decides fun _ _ q => q
  · exact (head_k3 hS hR O eL true e).decides fun _ _ q => q
  · exact (head_k11 hS hR O eL e).decides fun _ _ q => q

/-- Over a Quiet hearing sub-protocol of the head's link. -/
theorem step_quiet24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 8) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (338 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (338 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q')) :
    Quiet s s' := by
  obtain ⟨Lk, eL, -, hA⟩ := hear_flat24 hS hR O
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  exact hear_quiet24 hS hR O hj eL e s rs' gs' s' d'

/-- Over a later sending's sub-protocol of the head's link. -/
theorem step_commit24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 4 ∨ j = 6) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (338 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (338 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q'))
    {l : Nat} {f : ReqFrame} (H : Opn l f s) : Opn l (laterF f s.st.oracles.size) s' := by
  obtain ⟨Lk, eL, -, hA⟩ := hear_flat24 hS hR O
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ24 hS hR O hj eL e d'
  exact opn_quiet qv (opn_commit cm H)

/-- Over a later sending's sub-protocol of a link l < 24: the frame alone. -/
theorem step_commit_opn (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 3 ∨ j = 5) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q'))
    {m : Nat} {f : ReqFrame} (H : Opn m f s) : Opn m (laterF f s.st.oracles.size) s' := by
  obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ hS hR O h24 hj eL e d'
  exact opn_quiet qv (opn_commit cm H)

/-- **A TOOL, AT EVERY LINK l < 25: the batching, what runs behind it and the one equation**
(numbers 14 l + (the number of hearing sub-protocols) + 2 + n, n ≤ 2, of the flat list) keep Rl:
reflexive, transitive, kept by the batching's maker where the gathered claims keep it and by the
one equation's maker; given that the hearing sub-protocols' runs keep it. (FrameAt.lean's
rest_front says the like at l < 24.) -/
theorem rest_front_of_runs {Rl : S → S → Prop} (hr : ∀ s, Rl s s)
    (ht : ∀ a b c, Rl a b → Rl b c → Rl a c)
    (hBat : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl Rl claims →
      Decides Rl (K9.batch K9.atS p claims))
    (hEq : ∀ p : K9.Where, Decides Rl (K9.oneEquation (Cl := Unit) K9.atS p))
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk) (hruns : ∀ b ∈ Lk.hear, RunsKeep Rl b)
    {n : Nat} (hn : n ≤ 2) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + Lk.hear.length + 2 + n]? = some b) : Decides Rl b := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', f, bL, bB, bC, eL', -, -, -, -, -, -, -, -, -, iB, -, dB, -⟩ := hfr l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · obtain ⟨Lk', p, w, T, eL', -, -, -, -, -, hal, ifl, -⟩ := (IM.k9_of hS hR O).2 l hl
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl := Option.some.inj (ifl.symm.trans hb)
    intro s rs gs t h
    exact hBat p (link_claims_runs hr ht Lk hruns) s rs gs t
      ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro k; cases k) s t rs gs).1 h).1
  · rw [show 14 * l + Lk.hear.length + 2 + 1 = 14 * l + Lk.hear.length + 3 by omega] at hb
    obtain rfl := Option.some.inj (iB.symm.trans hb)
    intro s rs gs t h
    rw [dB] at h
    exact link_behind_runs hr ht Lk hruns s t h
  · obtain ⟨Lk', p, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l hl
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain ⟨b', x, e1, e2, la⟩ := hall 0 .K9 rfl
    have ib := IM.close_numbers hS hR O hl eL e1
    rw [show 14 * l + Lk.hear.length + 4 + 0 = 14 * l + Lk.hear.length + 2 + 2 by omega] at ib
    obtain rfl := Option.some.inj (ib.symm.trans hb)
    intro s rs gs t h
    have dx : x.retype.decide s rs gs = .ok t :=
      ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
    obtain rfl : ({ K9.oneEquation K9.atS p with planOk := K9.fits p Q } : Block S Unit) = x :=
      Option.some.inj e2
    exact hEq p s rs gs t dx

/-- **The closing, at every link l < 25**: number 14 l + (the number of hearing sub-protocols) + 5
of the flat list: the frame behind it is closedF of the frame in front. -/
theorem closing_opn (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + Lk.hear.length + 5]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok t) {m : Nat} {f : ReqFrame}
    (H : Opn m f s) : ∃ rows, Opn m (closedF f rows) t := by
  obtain ⟨L, hL, rfl, eN⟩ := H
  obtain ⟨Lk', p, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O hl eL e1
  rw [show 14 * l + Lk.hear.length + 4 + 1 = 14 * l + Lk.hear.length + 5 by omega] at ib
  obtain rfl := Option.some.inj (ib.symm.trans hb)
  have dx : x.retype.decide s rs gs = .ok t :=
    ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
  obtain rfl : K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy', hl4, -⟩ := closing_yes (C := Unit) dx hL
  obtain ⟨Gc, rows, -, -, ey⟩ := Close.closeFrame_lays (f' := y.1) (S' := y.2) hy'
  exact ⟨rows, _, hl4, ey, eN⟩

/-- **The shutting, at every link l < 25**: number 14 l + (the number of hearing sub-protocols) + 6
of the flat list: it leaves the open link's frame. -/
theorem shutting_opn (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + Lk.hear.length + 6]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok t) {m : Nat} {f : ReqFrame}
    (H : Opn m f s) : Opn m f t := by
  obtain ⟨Lk', p, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b', x, e1, e2, la⟩ := hall 2 .K9 rfl
  have ib := IM.close_numbers hS hR O hl eL e1
  rw [show 14 * l + Lk.hear.length + 4 + 2 = 14 * l + Lk.hear.length + 6 by omega] at ib
  obtain rfl := Option.some.inj (ib.symm.trans hb)
  have dx : x.retype.decide s rs gs = .ok t :=
    ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
  obtain rfl : K9.shut p (Q.piece + 1) = x := Option.some.inj e2
  exact opn_gby (shut_gby (fun f => f) (C := Unit) p (Q.piece + 1) s rs gs t dx) H

/-- The frame at the cut e + i of a link, e the cut behind the sub-protocol that opens it: f the
frame at e; n₃, n₅: the numbers of messages in front of the two later sendings. -/
def seqF (f : ReqFrame) (n₃ n₅ i : Nat) : ReqFrame :=
  if i ≤ 2 then f else if i ≤ 4 then laterF f n₃ else laterF (laterF f n₃) n₅

theorem seqF_keep (f : ReqFrame) (n₃ n₅ : Nat) {k : Nat} (h2 : k ≠ 2) (h4 : k ≠ 4) :
    seqF f n₃ n₅ (k + 1) = seqF f n₃ n₅ k := by
  unfold seqF
  rcases (by omega : k ≤ 1 ∨ k = 3 ∨ 5 ≤ k) with h | rfl | h
  · rw [if_pos (by omega : k + 1 ≤ 2), if_pos (by omega : k ≤ 2)]
  · rfl
  · rw [if_neg (by omega : ¬ k + 1 ≤ 2), if_neg (by omega : ¬ k + 1 ≤ 4),
      if_neg (by omega : ¬ k ≤ 2), if_neg (by omega : ¬ k ≤ 4)]

/-- The sub-protocol number k of the flat list leaves the open link's number and frame, along the
fold from the first state at p, R, C. -/
def KeepAt (c : Chain S Cl) (Z : ProofFile.Pub) (p : ProofFile.InstPub) (R : List Fmt.RoundView)
    (C : List VerifiableInference.Desc.OpenedColumn) (k : Nat) : Prop :=
  ∀ (s s' : S) (r r' : List Fmt.RoundView) (q q' : List VerifiableInference.Desc.OpenedColumn),
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (s, r, q) →
    foldBlocks 0 (c.blocksInOrder.take (k + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q') →
    ∀ (m : Nat) (f : ReqFrame), Opn m f s → Opn m f s'

/-- The sub-protocol number k of the flat list is a later sending. -/
def GrowAt (c : Chain S Cl) (Z : ProofFile.Pub) (p : ProofFile.InstPub) (R : List Fmt.RoundView)
    (C : List VerifiableInference.Desc.OpenedColumn) (k : Nat) : Prop :=
  ∀ (s s' : S) (r r' : List Fmt.RoundView) (q q' : List VerifiableInference.Desc.OpenedColumn),
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (s, r, q) →
    foldBlocks 0 (c.blocksInOrder.take (k + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q') →
    ∀ (m : Nat) (f : ReqFrame), Opn m f s → Opn m (laterF f s.st.oracles.size) s'

/-- **The walk, from the steps**: K steps from the cut e, of which number 2 and number 4 are later
sendings and the others leave the frame. -/
theorem walk_steps {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn}
    {e K : Nat} (hk : ∀ i < K, i ≠ 2 → i ≠ 4 → KeepAt c Z p R C (e + i))
    (h2 : GrowAt c Z p R C (e + 2)) (h4 : GrowAt c Z p R C (e + 4)) {n₃ n₅ : Nat}
    (h₃ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (e + 2)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      t.st.oracles.size = n₃)
    (h₅ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (e + 4)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      t.st.oracles.size = n₅)
    {te : S} {Re : List Fmt.RoundView} {Ce : List VerifiableInference.Desc.OpenedColumn}
    (fe : foldBlocks 0 (c.blocksInOrder.take e) (ProofFile.startS Z p) R C = .ok (te, Re, Ce))
    {m : Nat} {f : ReqFrame} (H : Opn m f te) :
    ∀ k ≤ K, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (e + k)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      Opn m (seqF f n₃ n₅ k) t
  | 0, _, t, r, q, g => by
    obtain rfl : te = t := congrArg Prod.fst (Except.ok.inj (fe.symm.trans g))
    exact H
  | k + 1, hK, t, r, q, g => by
    obtain ⟨u, ru, qu, gu⟩ := fold_back (k := e + k) g
    have a := walk_steps hk h2 h4 h₃ h₅ fe H k (by omega) u ru qu gu
    by_cases e2 : k = 2
    · subst e2
      have b := h2 u t ru r qu q gu g m _ a
      rw [h₃ u ru qu gu] at b
      exact b
    · by_cases e4 : k = 4
      · subst e4
        have b := h4 u t ru r qu q gu g m _ a
        rw [h₅ u ru qu gu] at b
        exact b
      · rw [seqF_keep f n₃ n₅ e2 e4]
        exact hk k (by omega) e2 e4 u t ru r qu q gu g m _ a

/-- The batching, what runs behind it and the one equation leave the open link's number and
frame. -/
theorem keep_rest (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk)
    (hruns : ∀ b ∈ Lk.hear, RunsKeep (GBy fun f : ReqFrame => f) b)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn)
    {n : Nat} (hn : n ≤ 2) : KeepAt c Z p R C (14 * l + Lk.hear.length + 2 + n) := by
  intro s s' r r' q q' g g' m f H
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, bC, eL', -, -, -, -, -, -, -, -, -, -, -, -, iC, -⟩ := hfr l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[14 * l + Lk.hear.length + 2 + n]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 iC).1
      omega)⟩
  obtain ⟨rs, gs, d⟩ := fold_next ib g g'
  exact opn_gby (rest_front_of_runs (gby_refl _) (gby_trans _) (fun p _ hcl => batch_gby _ p hcl)
    (fun p => oneEquation_gby _ (C := Unit) p) hS hR O hl eL hruns hn ib s rs gs s' d) H

/-- **BEHIND THE CLOSING AND BEHIND THE SHUTTING, AT EVERY LINK l < 25**: from the frame f in front
of the closing (the cut 14 l + (the number of hearing sub-protocols) + 5). -/
theorem closed_cuts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk)
    {p : ProofFile.InstPub} {R Ru : List Fmt.RoundView} {C Cu : List VerifiableInference.Desc.OpenedColumn} {u : S}
    (fu : foldBlocks 0 (c.blocksInOrder.take (14 * l + Lk.hear.length + 5)) (ProofFile.startS Z p) R C =
      .ok (u, Ru, Cu)) {m : Nat} {f : ReqFrame} (H : Opn m f u) :
    ∀ n ≤ 1, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + Lk.hear.length + 6 + n)) (ProofFile.startS Z p) R C =
        .ok (t, r, q) → ∃ rows, Opn m (closedF f rows) t := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, bC, eL', -, -, -, -, -, -, -, -, -, -, -, -, iC, -⟩ := hfr l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  have blk : ∀ i ≤ 7, ∃ b, c.blocksInOrder[14 * l + Lk.hear.length + i]? = some b := fun i hi =>
    ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 iC).1
      omega)⟩
  have z : ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + Lk.hear.length + 6)) (ProofFile.startS Z p) R C =
        .ok (t, r, q) → ∃ rows, Opn m (closedF f rows) t := by
    intro t r q g
    obtain ⟨b, ib⟩ := blk 5 (by omega)
    obtain ⟨rs, gs, d⟩ := fold_next ib fu g
    exact closing_opn hS hR O hl eL ib d H
  intro n hn t r q g
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact z t r q g
  · obtain ⟨v, rv, qv, gv⟩ := fold_back (k := 14 * l + Lk.hear.length + 6) g
    obtain ⟨rows, Hv⟩ := z v rv qv gv
    obtain ⟨b, ib⟩ := blk 6 (by omega)
    obtain ⟨rs, gs, d⟩ := fold_next ib gv g
    exact ⟨rows, shutting_opn hS hR O hl eL ib d Hv⟩

/-- **THE OPEN LINK's FRAME AT EVERY CUT OF A LINK l < 24 AT WHICH A LINK IS OPEN**: from the frame
f at the cut 14 l + 3. -/
theorem frame_walk_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n₃ n₅ : Nat}
    (h₃ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + 2)) (ProofFile.startS Z p) R C =
      .ok (t, r, q) → t.st.oracles.size = n₃)
    (h₅ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + 4)) (ProofFile.startS Z p) R C =
      .ok (t, r, q) → t.st.oracles.size = n₅)
    {t₁ : S} {R₁ : List Fmt.RoundView} {C₁ : List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    {f : ReqFrame} (H : Opn l f t₁) :
    (∀ k ≤ 9, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + k)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      Opn l (seqF f n₃ n₅ k) t) ∧
    ∀ n ≤ 1, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + 10 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      ∃ rows, Opn l (closedF (laterF (laterF f n₃) n₅) rows) t := by
  obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, -, eL', hlen, -⟩ := hfr l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  have hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
    intro b₀ e0
    obtain ⟨b₀', e0', i0⟩ := hA 0 (by omega)
    obtain rfl : b₀ = b₀' := Option.some.inj (e0.symm.trans e0')
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
    obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
    exact ⟨_, _, _, _, d0⟩
  have hruns := hear_runs (gby_refl fun f : ReqFrame => f) (gby_trans _)
    (fun _ _ => gby_of_quiet _) hS hR O h24 eL hy
  have hk : ∀ i < 9, i ≠ 2 → i ≠ 4 → KeepAt c Z p R C (14 * l + 3 + i) := by
    intro i hi i2 i4
    by_cases h6 : i < 6
    · intro s s' r r' q q' g g' m f' H'
      exact opn_quiet (step_quiet hS hR O h24 (j := i + 1) (by omega)
        (by rw [show 14 * l + 2 + (i + 1) = 14 * l + 3 + i by omega]; exact g)
        (by rw [show 14 * l + 2 + (i + 1) + 1 = 14 * l + 3 + i + 1 by omega]; exact g')) H'
    · have k := keep_rest hS hR O (by omega : l < 25) eL hruns p R C (n := i - 6) (by omega)
      rwa [hlen, show 14 * l + 7 + 2 + (i - 6) = 14 * l + 3 + i by omega] at k
  have hg : ∀ j, j = 3 ∨ j = 5 → GrowAt c Z p R C (14 * l + 2 + j) :=
    fun j hj s s' r r' q q' g g' m f' H' => step_commit_opn hS hR O h24 hj g g' H'
  have W := walk_steps (K := 9) hk (hg 3 (Or.inl rfl)) (hg 5 (Or.inr rfl)) h₃ h₅ f₁ H
  refine ⟨W, fun n hn t r q g => ?_⟩
  obtain ⟨u, ru, qu, gu⟩ := fold_cut (k := 14 * l + 3 + 9) (n + 1)
    (by rw [show 14 * l + 3 + 9 + (n + 1) = 14 * l + 3 + 10 + n by omega]; exact g)
  exact closed_cuts hS hR O (by omega : l < 25) eL
    (by rw [hlen, show 14 * l + 7 + 5 = 14 * l + 3 + 9 by omega]; exact gu)
    (W 9 (by omega) u ru qu gu) n hn t r q
    (by rw [hlen, show 14 * l + 7 + 6 + n = 14 * l + 3 + 10 + n by omega]; exact g)

/-- **THE OPEN LINK's FRAME AT EVERY CUT OF THE HEAD's LINK AT WHICH A LINK IS OPEN**: from the
frame f at the cut 340. -/
theorem frame_walk_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n₃ n₅ : Nat}
    (h₃ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (340 + 2)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      t.st.oracles.size = n₃)
    (h₅ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (340 + 4)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      t.st.oracles.size = n₅)
    {t₂ : S} {R₂ : List Fmt.RoundView} {C₂ : List VerifiableInference.Desc.OpenedColumn}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    {f : ReqFrame} (H : Opn 24 f t₂) :
    (∀ k ≤ 10, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (340 + k)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      Opn 24 (seqF f n₃ n₅ k) t) ∧
    ∀ n ≤ 1, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (340 + 11 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      ∃ rows, Opn 24 (closedF (laterF (laterF f n₃) n₅) rows) t := by
  obtain ⟨Lk, eL, hlen, hA⟩ := hear_flat24 hS hR O
  have hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t := by
    intro b₁ e1
    obtain ⟨b₁', e1', i1⟩ := hA 1 (by omega)
    obtain rfl : b₁ = b₁' := Option.some.inj (e1.symm.trans e1')
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
    obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
    exact ⟨_, _, _, _, d1⟩
  have hruns := hear_runs24 (gby_refl fun f : ReqFrame => f) (gby_trans _)
    (fun _ _ => gby_of_quiet _) hS hR O eL hy
  have hk : ∀ i < 10, i ≠ 2 → i ≠ 4 → KeepAt c Z p R C (340 + i) := by
    intro i hi i2 i4
    by_cases h7 : i < 7
    · intro s s' r r' q q' g g' m f' H'
      exact opn_quiet (step_quiet24 hS hR O (j := i + 2) (by omega)
        (by rw [show 338 + (i + 2) = 340 + i by omega]; exact g)
        (by rw [show 338 + (i + 2) + 1 = 340 + i + 1 by omega]; exact g')) H'
    · have k := keep_rest hS hR O (by omega : 24 < 25) eL hruns p R C (n := i - 7) (by omega)
      rwa [hlen, show 14 * 24 + 9 + 2 + (i - 7) = 340 + i by omega] at k
  have hg : ∀ j, j = 4 ∨ j = 6 → GrowAt c Z p R C (338 + j) :=
    fun j hj s s' r r' q q' g g' m f' H' => step_commit24 hS hR O hj g g' H'
  have W := walk_steps (K := 10) hk (hg 4 (Or.inl rfl)) (hg 6 (Or.inr rfl)) h₃ h₅ f₂ H
  refine ⟨W, fun n hn t r q g => ?_⟩
  obtain ⟨u, ru, qu, gu⟩ := fold_cut (k := 340 + 10) (n + 1)
    (by rw [show 340 + 10 + (n + 1) = 340 + 11 + n by omega]; exact g)
  exact closed_cuts hS hR O (by omega : 24 < 25) eL
    (by rw [hlen]; exact gu) (W 10 (by omega) u ru qu gu) n hn t r q
    (by rw [hlen, show 14 * 24 + 9 + 6 + n = 340 + 11 + n by omega]; exact g)

end

#print axioms opn_commit
#print axioms h2_place_frame
#print axioms entry_head_frame
#print axioms hear_commitQ24
#print axioms rest_front_of_runs
#print axioms closing_opn
#print axioms shutting_opn
#print axioms walk_steps
#print axioms closed_cuts
#print axioms frame_walk_link
#print axioms frame_walk_head

end Meaning.K2
