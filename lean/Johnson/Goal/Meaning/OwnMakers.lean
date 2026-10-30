-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/OwnMakers.lean: the invariant of Johnson/Goal/Meaning/OwnInv.lean is handed on
by the rows of the links' frames, by kind K1's blocks at the record, and by K9's and K10's.
Theorems, proved: each by the script of its like for RecAll (Johnson/Goal/Meaning/RecSeated.lean,
RecK1.lean, RecK9.lean, RecK10.lean).

  zeroAt_arr, frameAt_arr   the frame's letters at link l bear the built link's list of arrays, and
    the number l.
  framesOf_own   every row of framesOf built first W: lay, opened, clear: WHERE A IS THE BUILT
    LINKS' OWN: ∀ l X, built[l]? = some X → X.arrayOf = A l.
  laterOwn_rows, firstOwn_rows, commitStep_ctx   K1's decisions on the state of the calls leave the
    rows; a commitment leaves the link's number and list of arrays.
  commitAtS_ctx, firstAtS_ctx   Whole SameCtx of K1's two blocks.
  ctx_atS_set, drawn_ctx, oneEquation_ctx, closing_ctx   K9's lens, its draw, the one equation;
    K10's closing, which writes the live frame alone.
  closeOf_own, batch_own   the three blocks of a closing; the batching.

Object, letters. Object: the makers named above.
Letters: A, lay: free.

What is not claimed. Which maker stands at which place of a seated text. Nothing on soundness.

-/
import Johnson.Goal.Meaning.OwnInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K1
open VerifiableInference.Desc.K9 (atS drawAlone adds batch oneEquation Where door drawnClean drawn
  Out Drawn St RowsOwed)
open Johnson.Desc.First.Walk

variable {Cl : Type} {A : Nat → Array (Nat × String)} {lay : ReqLayout}

/-! ## The links' frames, link by link -/

open Johnson.Desc.First.Walk.Seat in
theorem zeroAt_arr {built : Array Stages.LinkH} {W : Verify.Public} {P : LayPar}
    (h : zeroAt built W = some P) : ∃ X, built[0]? = some X ∧ P.X.arrayOf = X.arrayOf := by
  unfold zeroAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨X, hX, ?_⟩
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hp, -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rfl

open Johnson.Desc.First.Walk.Seat in
theorem frameAt_arr {built : Array Stages.LinkH} {W : Verify.Public} {l : Nat} {p : Seat.Par}
    (h : Seat.frameAt built W l = some p) : ∃ X, built[l]? = some X ∧
      match p with
      | .att P _ => P.X.arrayOf = X.arrayOf ∧ P.l = l
      | .lay P => P.X.arrayOf = X.arrayOf ∧ P.l = l := by
  unfold Seat.frameAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨X, hX, ?_⟩
  split at h
  · cases h
  · split at h
    · obtain ⟨q, -, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      exact ⟨rfl, rfl⟩
    · split at h
      · obtain ⟨q, -, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        exact ⟨rfl, rfl⟩
      · cases h

theorem tailHead_own (X : LinkPub) (ws : WsLay) (lin : LinShape) :
    Fn (OwnRel A lay) (Close.tailHead X ws lin) := clearWith_own _ _ _ _

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link**, where A is the built links' own lists of arrays. -/
theorem framesOf_own {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (hA : ∀ l X, built[l]? = some X → X.arrayOf = A l)
    (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (OwnRel A lay) f.lay ∧ Fn (OwnRel A lay) f.opened ∧ Fn (OwnRel A lay) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_own (layFront_quiet l), fun s t k I => by cases k; exact I,
        tailHead_own _ _ _⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        obtain ⟨X, hX, e1⟩ := zeroAt_arr hP
        exact ⟨fn_own (layFront_quiet 0), openLayZero_own _ _ _ (e1.trans (hA 0 X hX)),
          clearWith_own _ _ _ _⟩
    · split at e
      · cases e
      · rename_i P n hP
        cases e
        obtain ⟨X, hX, e1, e2⟩ := frameAt_arr hP
        exact ⟨fn_own (layFront_quiet l), openAtt_own _ (by rw [e1, e2]; exact hA l X hX),
          clearWith_own _ _ _ _⟩
      · rename_i P hP
        cases e
        obtain ⟨X, hX, e1, e2⟩ := frameAt_arr hP
        exact ⟨fn_own (layFront_quiet l), openLay_own _ (by rw [e1, e2]; exact hA l X hX),
          clearWith_own _ _ _ _⟩

/-! ## K1 -/

theorem laterOwn_rows {P : K1.Par} {owed : Option Nat} {c c' : ChainCheck} {w w' : DState Unit}
    {rs : List Fmt.RoundView} (h : laterOwn P owed c w rs = .ok (c', w')) : c'.rows = c.rows := by
  unfold laterOwn at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · cases h
            rfl

theorem firstOwn_rows {P : K1.Par} {owed : Option Nat} {c c' : ChainCheck} {d d' : DState Unit}
    {rs : List Fmt.RoundView} (h : firstOwn P owed c d rs = .ok (c', d')) : c'.rows = c.rows := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨g, d₁⟩, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨ids, d₂⟩, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨mask, _, h⟩ := bindE h
  obtain ⟨⟨f₂, d₃⟩, hj, h⟩ := bindE h
  cases h
  rfl

theorem commitStep_ctx {P : K1.Par} {owed : Option Nat} {ts : List Nat}
    {x y : L3.St (DState Unit)} {rs : List Fmt.RoundView}
    (h : L3.commitStep (laterOwn P owed) ts x rs = .ok y) :
    y.L.check.rows = x.L.check.rows ∧ y.L.link = x.L.link ∧ y.L.arrayOf = x.L.arrayOf := by
  unfold L3.commitStep at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨check, w⟩, h1, h⟩ := bindE h
  obtain ⟨⟨L, F⟩, h2, h⟩ := bindE h
  cases h
  unfold L3.commitBehind at h2
  obtain ⟨F', _, h2⟩ := bindE h2
  split at h2
  · cases h2
    exact ⟨laterOwn_rows h1, rfl, rfl⟩
  · cases h2

theorem commitAtS_ctx (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole SameCtx (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    have hfr : y.held.L.check.rows = L.check.rows ∧ y.held.L.link = L.link ∧
        y.held.L.arrayOf = L.arrayOf := by
      simp only [commitOwn] at hy
      split at hy
      · split at hy
        · cases hy
        · obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hy
          exact commitStep_ctx hx
      · cases hy
    show ctxOf _ = ctxOf s
    rw [ctx_putFork, ctx_putLink (s := laid s y.held.w) (L := L) hL hfr.1 hfr.2.1 hfr.2.2]
    rfl
  · cases h

theorem firstAtS_ctx (q : Params.First) (gp : GPar) :
    Whole SameCtx (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [firstSegmentOpening] at h
  obtain ⟨_, hB, h⟩ := bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := bindE h
  cases h
  show ((c.rows, (ctxOf s).2) : _ × _) = ctxOf s
  rw [firstOwn_rows h1]
  rfl

/-! ## K9 and K10 -/

theorem ctx_atS_set {s : S} {L : LinkCtx} (h : s.link? = some L) (p : K9.Part)
    (e1 : p.L.check.rows = L.check.rows) (e2 : p.L.link = L.link)
    (e3 : p.L.arrayOf = L.arrayOf) : ctxOf (atS.set s p) = ctxOf s := by
  have e : ctxOf ((s.putLink p.L).putFork p.F) = ctxOf s :=
    (ctx_putFork _ _).trans (ctx_putLink h e1 e2 e3)
  exact e

theorem drawn_ctx {rows : Nat} {chi : E} {owed : RowsOwed} {used : Nat} {L : LinkCtx} {F : Fork}
    {o : Drawn} (h : drawnClean rows chi owed used L F = .ok o) :
    o.L.check = L.check ∧ o.L.link = L.link ∧ o.L.arrayOf = L.arrayOf := by
  unfold drawnClean at h
  obtain ⟨o', h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  unfold drawn at h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  cases h1
  exact ⟨rfl, rfl, rfl⟩

theorem oneEquation_ctx (p : Where) : Whole SameCtx (oneEquation (Cl := Cl) atS p) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  obtain ⟨g1, -⟩ := atS_get (there_some hq)
  obtain ⟨d1, -⟩ := door_keeps ho
  exact ctx_atS_set g1 _ (by show o.L.check.rows = _; rw [d1]) (by show o.L.link = _; rw [d1])
    (by show o.L.arrayOf = _; rw [d1])

theorem closing_ctx (P : Close.Par) : Whole SameCtx (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact ctx_putLive s (c := { s.live with frame := x.1 }) rfl

theorem closeOf_own (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (OwnRel A lay) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact whole_ownC (oneEquation_ctx p)
  · exact whole_ownC (closing_ctx P)
  · exact whole_ownC (whole_mono (fun _ _ q => q.2) (shut_still p _))

theorem batch_own (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (OwnRel A lay) claims) : Whole (OwnRel A lay) (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : OwnRel A lay s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      obtain ⟨g1, -⟩ := atS_get (there_some hq)
      obtain ⟨d1, d2, d3⟩ := drawn_ctx ho
      exact own_of_ctx (ctx_atS_set g1 _ (by show o.L.check.rows = _; rw [d1]) d2 d3)
    · cases h1
  have a2 : OwnRel A lay t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    obtain ⟨g1, -⟩ := atS_get (there_some hq)
    exact ownRel_trans _ _ _ (hcl t₁ x hx) (own_of_ctx (ctx_atS_set g1 _ rfl rfl rfl))
  exact ownRel_trans _ _ _ a1 a2

#print axioms framesOf_own
#print axioms commitAtS_ctx
#print axioms firstAtS_ctx
#print axioms closeOf_own
#print axioms batch_own

end Meaning.K2
