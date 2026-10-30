-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupTail.lean: FROM IN FRONT OF A LINK's BATCHING TO IN FRONT OF
THE NEXT LINK's FIRST SUB-PROTOCOL (the cuts 14 l + 9 and 14 (l + 1) + 2, l < 24): WHAT THE CODE
SWITCHING WILL READ OF THE CLOSED GROUP IS WHAT THE OPEN GROUP HELD.
  GBy φ s t: where a link is open at s one is open at t, with the same number, and φ reads the same
    of its frame. Reflexive, transitive. gby_of_quiet, gby_set, batch_gby, oneEquation_gby,
    closing_gby (for a φ that does not read the four fields that the closing writes), shut_gby,
    closeOf_gby: as Gk's in Johnson/IMR/GroupRest.lean, general in φ.
  listsOfFrame f: the frame's kept messages of earlier links, its own messages, its group.
  Tl: GS on the statement (Calm) and GBy listsOfFrame together.
  closing_calm, closeOf_calm: Calm at "what closes a link": kind K10's closeFrame_groups.
  tail_rows: THE TOP: with L the link open in front of the batching and G the statement's group at
    its frame's number: in front of the next link's first sub-protocol the walk's frame's carried
    rows' layout has G's members and flags; the frame's two lists are L's; the statement's groups
    have kept their number, members and flags.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K2's files (the kept old
messages); kind K10's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupRest
import Johnson.Desc.First.Close.Law.GroupsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open ProofFile (Cl)

section By
variable {α : Type} (φ : ReqFrame → α)

/-- Where a link is open at s one is open at t, with the same number; φ reads the same of its
frame. -/
def GBy (s t : S) : Prop :=
  ∀ L, s.link? = some L → ∃ L', t.link? = some L' ∧ φ L'.check.frame = φ L.check.frame ∧
    L'.link = L.link

theorem gby_refl (s : S) : GBy φ s s := fun L h => ⟨L, h, rfl, rfl⟩

theorem gby_trans (a b c : S) (h : GBy φ a b) (k : GBy φ b c) : GBy φ a c := fun L hL => by
  obtain ⟨L₁, h1, e1, e2⟩ := h L hL
  obtain ⟨L₂, h2, f1, f2⟩ := k L₁ h1
  exact ⟨L₂, h2, f1.trans e1, f2.trans e2⟩

theorem gby_of_quiet {s t : S} (q : Quiet s t) : GBy φ s t := fun L hL => by
  obtain ⟨L', a, c, -, n⟩ := quiet_fwd q hL
  exact ⟨L', a, by rw [c], n⟩

theorem gby_set {s : S} {L : LinkCtx} (h : s.link? = some L) (p : K9.Part)
    (e1 : p.L.check.frame = L.check.frame) (e2 : p.L.link = L.link) :
    GBy φ s (atS.set s p) := fun L₀ h₀ => by
  obtain rfl : L = L₀ := Option.some.inj (h.symm.trans h₀)
  refine ⟨p.L, ?_, by rw [e1], e2⟩
  show ((s.putLink p.L).putFork p.F).link? = _
  rw [link_putFork, link_putLink h]

theorem batch_gby (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (GBy φ) claims) : Decides (GBy φ) (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : GBy φ s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      exact gby_set φ (atS_get (there_some hq)).1 _
        (by show o.L.check.frame = _; rw [drawn_L ho]) (drawn_link ho)
    · cases h1
  have a2 : GBy φ t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact gby_trans φ _ _ _ (hcl t₁ x hx) (gby_set φ (atS_get (there_some hq)).1 _ rfl rfl)
  exact gby_trans φ _ _ _ a1 a2

theorem oneEquation_gby {C : Type} (p : Where) :
    Decides (GBy φ) (oneEquation (Cl := C) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  obtain ⟨d1, -⟩ := door_keeps ho
  exact gby_set φ (atS_get (there_some hq)).1 _ (by show o.L.check.frame = _; rw [d1])
    (by show o.L.link = _; rw [d1])

/-- What a yes of the closing lays: the open link's frame behind is closeFrame's. -/
theorem closing_yes {C : Type} {P : Close.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K9.closing (Cl := C) P).decide s rs gs = .ok s')
    {L : LinkCtx} (hL : s.link? = some L) :
    ∃ x : ReqFrame × Statement,
      Close.closeFrame (K9.recOf s).owed L.check.frame s.st (Close.entries P) rs = .ok x ∧
      s'.link? = some { L with check := { L.check with frame := x.1 } } ∧ s'.st = x.2 := by
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  have hx' : Close.closeFrame (K9.recOf s).owed s.live.frame s.st (Close.entries P) rs = .ok x := hx
  rw [live_open hL] at hx'
  refine ⟨x, hx', ?_, rfl⟩
  show (s.putLive { s.live with frame := x.1 }).link? = _
  unfold S.putLive
  rw [hL, live_open hL]
  exact link_putLink hL _

theorem closing_gby {C : Type}
    (hφ : ∀ (f : ReqFrame) (rows : SingleRows) (l : Nat),
      φ { f with rows := rows, mask := none, link := l, next := .first } = φ f)
    (P : Close.Par) : Decides (GBy φ) (K9.closing (Cl := C) P) := by
  intro s rs gs s' h L hL
  obtain ⟨x, hx, hl, -⟩ := closing_yes h hL
  obtain ⟨G, rows, -, -, e⟩ := Close.closeFrame_lays (f' := x.1) (S' := x.2) hx
  refine ⟨_, hl, ?_, rfl⟩
  show φ x.1 = _
  rw [e]
  exact hφ _ _ _

theorem shut_gby {C : Type} (p : Where) (piece : Nat) :
    Decides (GBy φ) (K9.shut (Cl := C) p piece) := by
  intro s rs gs s' h L hL
  obtain ⟨L₁, h1, h⟩ := bindE h
  cases h
  obtain rfl : L = L₁ := by
    rw [hL] at h1
    exact Except.ok.inj h1
  exact ⟨_, link_putLink hL _, rfl, rfl⟩

theorem closeOf_gby
    (hφ : ∀ (f : ReqFrame) (rows : SingleRows) (l : Nat),
      φ { f with rows := rows, mask := none, link := l, next := .first } = φ f)
    (p : Where) (P : Close.Par) : ∀ b ∈ closeOf (Cl := Unit) p P, Decides (GBy φ) b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact fun s rs gs t h => oneEquation_gby φ (C := Unit) p s rs gs t h
  · exact closing_gby φ hφ P
  · exact shut_gby φ p _

end By

/-- The frame's kept messages of earlier links, its own messages, its group. -/
def listsOfFrame (f : ReqFrame) : Array Nat × Array Nat × Nat := (f.keptBefore, f.own, f.group)

theorem closing_calm {C : Type} (Q : Close.Par) : Decides Calm (K9.closing (Cl := C) Q) := by
  intro s rs gs s' h
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact ⟨(Close.closeFrame_groups hx).1, (Close.closeFrame_groups hx).2.1⟩

theorem closeOf_calm (p : Where) (Q : Close.Par) :
    ∀ b ∈ closeOf (Cl := Unit) p Q, Decides Calm b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact fun s rs gs t h => oneEquation_calm (Cl := Unit) p s rs gs t h
  · exact closing_calm Q
  · exact fun s rs gs t h => calm_of_enters ((shut_still p _).1 s rs gs t h).1

/-- Calm, and the open link's frame's lists and group stay. -/
def Tl (s t : S) : Prop := Calm s t ∧ GBy listsOfFrame s t

theorem tl_refl (s : S) : Tl s s := ⟨calm_refl s, gby_refl _ s⟩

theorem tl_trans (a b c : S) (h : Tl a b) (k : Tl b c) : Tl a c :=
  ⟨calm_trans _ _ _ h.1 k.1, gby_trans _ _ _ _ h.2 k.2⟩

theorem tl_of_quiet {s t : S} (q : Quiet s t) : Tl s t := ⟨calm_of_quiet q, gby_of_quiet _ q⟩

theorem batch_tl (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl Tl claims) : Decides Tl (batch atS p claims) := fun s rs gs t h =>
  ⟨(batch_calm p fun a y k => (hcl a y k).1).1 s rs gs t h,
    batch_gby _ p (fun a y k => (hcl a y k).2) s rs gs t h⟩

theorem closeOf_tl (p : Where) (Q : Close.Par) :
    ∀ b ∈ closeOf (Cl := Unit) p Q, Decides Tl b := fun b hb s rs gs t h =>
  ⟨closeOf_calm p Q b hb s rs gs t h,
    closeOf_gby listsOfFrame (fun _ _ _ => rfl) p Q b hb s rs gs t h⟩

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- Every row's "cleared" lays the state of the calls in use as the walk's and leaves the groups. -/
theorem framesOf_clear {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, ∀ s t,
    f.clear s = .ok t → t.check = s.live ∧ t.st.groups = s.st.groups := by
  have clr : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
      (row : RowFn) (s t : S), clearWith X counts left row s = .ok t →
      t.check = s.live ∧ t.st.groups = s.st.groups := fun X counts left row s t k =>
    ⟨(Law.clear_carries k).2.2.2.2.2.2.1, (Law.clear_carries k).2.2.2.2.2.2.2.2.1⟩
  have th : ∀ (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (s t : S),
      Close.tailHead X lay lin s = .ok t → t.check = s.live ∧ t.st.groups = s.st.groups :=
    fun _ _ _ => clr _ _ _ _
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact th _ _ _
  · split at e
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
      · cases e
        exact clr _ _ _ _

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **FROM IN FRONT OF THE BATCHING OF LINK l < 24 TO IN FRONT OF THE NEXT LINK's FIRST
SUB-PROTOCOL.** -/
theorem tail_rows (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R Ru R₂ : List Fmt.RoundView} {C Cu C₂ : List VerifiableInference.Desc.OpenedColumn}
    {u t₂ : S}
    (fu : foldBlocks 0 (c.blocksInOrder.take (14 * l + 9)) (ProofFile.startS Z p) R C = .ok (u, Ru, Cu))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ L G, u.link? = some L ∧ L.link = l ∧ L.check.frame.group = l ∧
      u.st.groups[l]? = some G ∧
      t₂.check.frame.rows.layout.members = G.members ∧
      t₂.check.frame.rows.layout.kept = G.kept ∧
      t₂.check.frame.keptBefore = L.check.frame.keptBefore ∧
      t₂.check.frame.own = L.check.frame.own ∧ Calm u t₂ := by
  obtain ⟨L, hL, eLn, eLg⟩ := group_open hS hR O h24 6 (by omega) u Ru Cu fu
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen] at iC
  obtain ⟨Lk', f', bL', -, -, -, -, hf', -, efl', hLay', -, iL', -, dL', -⟩ :=
    hfr (l + 1) (by omega)
  have cut : ∀ n ≤ 7, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 9 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 14 * l + 9 + n) (7 - n)
      (by rw [show 14 * l + 9 + n + (7 - n) = 14 * (l + 1) + 2 by omega]; exact f₂)
  have hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
    intro b₀ e0
    have i0 : c.blocksInOrder[14 * l + 2]? = some b₀ := by
      have q := IM.hear_at_flat eL e0
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
        (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at q
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 6 fu
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
    obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
    exact ⟨_, _, _, _, d0⟩
  have blk : ∀ n ≤ 6, ∃ b, c.blocksInOrder[14 * l + 9 + n]? = some b := fun n hn =>
    ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 iL').1
      omega)⟩
  have step : ∀ n ≤ 4, ∀ t r q t' r' q',
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 9 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 9 + (n + 1))) (ProofFile.startS Z p) R C = .ok (t', r', q') →
      Tl t t' := by
    intro n hn t r q t' r' q' g g'
    obtain ⟨b, ib⟩ := blk n (by omega)
    obtain ⟨rs, gs, d⟩ := fold_next ib g g'
    exact rest_by tl_refl tl_trans (fun _ _ => tl_of_quiet) (fun p _ hcl => batch_tl p hcl)
      closeOf_tl hS hR O h24 eL hy hn ib t rs gs t' d
  obtain ⟨s1, r1, q1, g1⟩ := cut 1 (by omega)
  obtain ⟨s2, r2, q2, g2⟩ := cut 2 (by omega)
  obtain ⟨s3, r3, q3, g3⟩ := cut 3 (by omega)
  obtain ⟨s4, r4, q4, g4⟩ := cut 4 (by omega)
  obtain ⟨s5, r5, q5, g5⟩ := cut 5 (by omega)
  obtain ⟨s6, r6, q6, g6⟩ := cut 6 (by omega)
  have T03 : Tl u s3 := tl_trans _ _ _ (tl_trans _ _ _ (step 0 (by omega) u Ru Cu s1 r1 q1 fu g1)
    (step 1 (by omega) s1 r1 q1 s2 r2 q2 g1 g2)) (step 2 (by omega) s2 r2 q2 s3 r3 q3 g2 g3)
  have T34 : Tl s3 s4 := step 3 (by omega) s3 r3 q3 s4 r4 q4 g3 g4
  have T45 : Tl s4 s5 := step 4 (by omega) s4 r4 q4 s5 r5 q5 g4 g5
  -- the closing, by itself
  obtain ⟨L3, hL3, e3, n3⟩ := T03.2 L hL
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : l < 25) eL e1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 9 + 3 by omega] at ib
  obtain ⟨rs, gs, d⟩ := fold_next ib g3 g4
  have dx : x.retype.decide s3 rs gs = .ok s4 :=
    ((IM.yes_alone la (by intro k; cases k) s3 s4 rs gs).1 d).1
  obtain rfl : K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy', hl4, -⟩ := closing_yes (C := Unit) dx hL3
  obtain ⟨-, -, G3, hG3, m1, m2⟩ := Close.closeFrame_groups hy'
  -- the group in front of the batching
  have eg3 : L3.check.frame.group = l := by
    have := congrArg (fun z => z.2.2) e3
    exact this.trans eLg
  rw [eg3] at hG3
  have pr := T03.1.2 l
  rw [hG3] at pr
  obtain ⟨G, hG, eG⟩ := Option.map_eq_some_iff.1 pr.symm
  have eGm : G.members = G3.members := congrArg Prod.fst eG
  have eGk : G.kept = G3.kept := congrArg Prod.snd eG
  -- the shutting leaves the frame; "cleared" lays the open link's state of the calls as the walk's
  obtain ⟨b5, ib5⟩ := blk 4 (by omega)
  obtain ⟨rs5, gs5, d5⟩ := fold_next ib5 g4 g5
  obtain ⟨b5', x5, e15, e25, la5⟩ := hall 2 .K9 rfl
  have ib5' := IM.close_numbers hS hR O (by omega : l < 25) eL e15
  rw [hlen, show 14 * l + 7 + 4 + 2 = 14 * l + 9 + 4 by omega] at ib5'
  obtain rfl := Option.some.inj (ib5.symm.trans ib5')
  have dx5 : x5.retype.decide s4 rs5 gs5 = .ok s5 :=
    ((IM.yes_alone la5 (by intro k; cases k) s4 s5 rs5 gs5).1 d5).1
  obtain rfl : K9.shut pw (Q.piece + 1) = x5 := Option.some.inj e25
  obtain ⟨L5, hL5, e5, -⟩ := shut_gby (fun f => f) (C := Unit) pw (Q.piece + 1) s4 rs5 gs5 s5 dx5
    _ hl4
  have e5' : L5.check.frame = y.1 := e5
  have iC' : c.blocksInOrder[14 * l + 9 + 5]? = some bC := by
    rw [show 14 * l + 9 + 5 = 14 * l + 7 + 7 by omega]
    exact iC
  obtain ⟨rs6, gs6, d6⟩ := fold_next iC' g5 g6
  rw [dC] at d6
  have hc6 := ((hClear s5 s6).1 d6).1
  have k6 : s6.check = s5.live ∧ s6.st.groups = s5.st.groups := by
    exact framesOf_clear hfs f (List.mem_of_getElem? hf) s5 s6 hc6
  have iL2 : c.blocksInOrder[14 * l + 9 + 6]? = some bL' := by
    rw [show 14 * l + 9 + 6 = 14 * (l + 1) + 1 by omega]
    exact iL'
  have f₂' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 9 + (6 + 1))) (ProofFile.startS Z p) R C =
      .ok (t₂, R₂, C₂) := by
    rw [show 14 * l + 9 + (6 + 1) = 14 * (l + 1) + 2 by omega]
    exact f₂
  obtain ⟨rs7, gs7, d7⟩ := fold_next iL2 g6 f₂'
  rw [dL'] at d7
  have hl7 := ((hLay' s6 t₂).1 d7).1
  rw [efl'] at hl7
  have e7 : t₂ = s6 := (Johnson.Desc.First.Walk.Law.layFront_ok hl7).1
  have ef : t₂.check.frame = y.1 := by rw [e7, k6.1, live_open hL5, e5']
  obtain ⟨Gc, rows, -, -, ey⟩ := Close.closeFrame_lays (f' := y.1) (S' := y.2) hy'
  refine ⟨L, G, hL, eLn, eLg, hG, by rw [ef, m1, eGm], by rw [ef, m2, eGk], ?_, ?_, ?_⟩
  · rw [ef, ey]
    exact congrArg (fun z => z.1) e3
  · rw [ef, ey]
    exact congrArg (fun z => z.2.1) e3
  · refine calm_trans _ _ _ (calm_trans _ _ _ T03.1 (calm_trans _ _ _ T34.1 T45.1)) ?_
    rw [e7]
    exact ⟨by rw [k6.2], fun g => by rw [k6.2]⟩

end

#print axioms closeOf_gby
#print axioms closeOf_calm
#print axioms tail_rows

end Meaning.K2
