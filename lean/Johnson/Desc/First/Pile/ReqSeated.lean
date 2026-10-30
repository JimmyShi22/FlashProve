-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Pile/ReqSeated.lean: `ReqStays` (Johnson/Desc/First/Pile/ReqMakers.lean) AT THE
OTHER MAKERS OF THE REQUEST'S OWN CHAIN, THOSE BEHIND THE LAST LINK AMONG THEM. Statements with
their proofs; no definition.

Main names (namespace `Meaning.K2`).
  More writers of State.lean: `req_putLink`, `req_putLive`, `req_enterLay`, `req_enterAtt`,
    `req_enterHead`, `req_openHead`, `req_enterFin`.
  The links' frames: `layFront_req`, `openAtt_req`, `openLay_req`, `openLayZero_req`,
    `clearWith_req`, `tailHead_req`, **`framesOf_req`**. Kind K1: `firstAtS_req`, `laterAt_req`.
    Kinds K9 and K10: `closeOf_req`, `batch_req`. The quiet step behind the reads: `layers_req`,
    `headReads_req`, `readsAtO_req`. Kind K2's five: `k2_req` (by `K2.keeps`),
    `headFrontQ_req`, `headOpenQ_req`, `finishFrontQ_req`, `finishBehindQ_req`.
  Behind the last link: `atFinish_req` (kind K12: by `atFinish_leaves_req` and
    `_failed`), `atM3_req` (by `K13.Law.atM3_rec`), `atM4_req` (by `K1.sendAtS_here` and
    `K13.Law.rowsB_at`).

Limits. Frame laws. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Pile.ReqMakers
import Johnson.Goal.Meaning.OwnMakers
import Johnson.Goal.Meaning.GrowsSeated
import Johnson.Top.H0.Tw.K2C.LeavesOut
import Johnson.Desc.K12.SeatLeaves
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K1.Law.HereAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K1
open VerifiableInference.Desc.K9 (atS drawAlone adds batch oneEquation Where door drawnClean drawn
  Out Drawn St RowsOwed shut)
open Johnson.Desc.First.Walk

variable {Cl : Type}

/-! ## More writers of State.lean -/

/-- A tactic for a writer of State.lean that turns another field than the two, or marks. -/
local macro "calm" d:ident : tactic =>
  `(tactic| (unfold $d; repeat' split) <;> first
    | exact req_refl _
    | exact req_mark _ _
    | exact req_same rfl rfl)

theorem req_putLink (s : S) (L : LinkCtx) : ReqStays s (s.putLink L) := by calm S.putLink

theorem req_putLive (s : S) (c : ChainCheck) : ReqStays s (s.putLive c) := by
  unfold S.putLive
  split
  · exact req_putLink _ _
  · exact req_same rfl rfl

theorem req_enterLay (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    ReqStays s (s.enterLay L F tl) := by calm S.enterLay

theorem req_enterAtt (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    ReqStays s (s.enterAtt L F tl) := by calm S.enterAtt

theorem req_enterHead (s : S) (tl : HTailF2) : ReqStays s (s.enterHead tl) := by calm S.enterHead

theorem req_openHead (s : S) : ReqStays s s.openHead := by calm S.openHead

theorem req_enterFin (s : S) : ReqStays s s.enterFin := by calm S.enterFin

/-! ## The links' frames -/

theorem layFront_req (l : Nat) : Fn ReqStays (layFront l) := fun s t h => by
  rw [(Law.layFront_ok h).1]
  exact req_refl s

theorem openAtt_req (P : AttPar) : Fn ReqStays (openAtt P) := fun s t h => by
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  rw [unmarked_eq h]
  exact req_enterAtt ({ s with out := a.out } : S) _ _ _

theorem openLay_req (P : LayPar) : Fn ReqStays (openLay P) := fun s t h => by
  unfold openLay at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  rw [unmarked_eq h]
  exact req_enterLay ({ s with out := a.out } : S) _ _ _

theorem openLayZero_req (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn ReqStays (openLayZero P fvs kCol) := fun s t h => by
  unfold openLayZero at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  rw [unmarked_eq h]
  exact req_enterLay ({ s with out := a.out } : S) _ _ _

theorem clearWith_req (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) : Fn ReqStays (clearWith X counts left row) :=
  fun s t h => by
  obtain ⟨-, -, -, -, hf, hr, -⟩ := Law.clear_carries h
  exact req_same hr hf

theorem tailHead_req (X : LinkPub) (ws : WsLay) (lin : LinShape) :
    Fn ReqStays (Close.tailHead X ws lin) := clearWith_req _ _ _ _

open Johnson.Desc.First.Walk.Seat in
/-- Every row of the links' frames. -/
theorem framesOf_req {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn ReqStays f.lay ∧ Fn ReqStays f.opened ∧ Fn ReqStays f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨layFront_req l, fun s t k => by cases k; exact req_refl s, tailHead_req _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_req 0, openLayZero_req _ _ _, clearWith_req _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_req l, openAtt_req _, clearWith_req _ _ _ _⟩
      · cases e
        exact ⟨layFront_req l, openLay_req _, clearWith_req _ _ _ _⟩

/-! ## K1's two -/

theorem commitAtS_req (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole ReqStays (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [commitAtS] at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    exact req_trans _ _ _ (req_trans _ _ _
      (req_same (s' := laid s y.held.w) rfl rfl) (req_putLink _ _)) (req_putFork _ _)
  · cases h

theorem laterAt_req (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Whole ReqStays (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  commitAtS_req _ link moment arrays

theorem firstAtS_req (q : Params.First) (gp : GPar) :
    Whole ReqStays (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [firstSegmentOpening] at h
  obtain ⟨_, hB, h⟩ := bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := bindE h
  cases h
  exact req_same rfl rfl

/-! ## K9's and K10's -/

theorem req_atS_set (s : S) (p : K9.Part) : ReqStays s (atS.set s p) := by
  have e : ReqStays s ((s.putLink p.L).putFork p.F) :=
    req_trans _ _ _ (req_putLink s p.L) (req_putFork _ p.F)
  exact e

theorem oneEquation_req (p : Where) : Whole ReqStays (oneEquation (Cl := Cl) atS p) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  exact req_atS_set _ _

theorem closing_req (P : Close.Par) : Whole ReqStays (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact (req_putLive s { s.live with frame := x.1 } : ReqStays s _)

theorem shut_req (p : Where) (piece : Nat) : Whole ReqStays (shut (Cl := Cl) p piece) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨L, hL, h⟩ := bindE h
  cases h
  exact req_putLink _ _

theorem closeOf_req (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole ReqStays b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact oneEquation_req p
  · exact closing_req P
  · exact shut_req p _

theorem batch_req (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl ReqStays claims) : Whole ReqStays (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : ReqStays s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      exact req_atS_set _ _
    · cases h1
  have a2 : ReqStays t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact req_trans _ _ _ (hcl t₁ x hx) (req_atS_set _ _)
  exact req_trans _ _ _ a1 a2

/-! ## The quiet step behind the reads -/

theorem layers_req (P : K8.ReadsQuiet.PG) : Whole ReqStays (K8.ReadsQuiet.layers P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, own, tl', ha, -, -, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact req_same rfl rfl

theorem headReads_req (P : K8.ReadsQuiet.PH) : Whole ReqStays (K8.ReadsQuiet.head P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, cov, x, t, tl', ha, -, -, -, -, -, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact req_same rfl rfl

theorem readsAtSO_req (A : Attention.Plan) : Fn ReqStays (Att.readsAtSO A) := fun s s' h => by
  obtain ⟨a, t, tl, ha, rfl⟩ := readsAtSO_eq h
  exact req_same rfl rfl

theorem readsAtO_req {W : Verify.Public} {l g : Nat} {b : Block S Cl}
    (h : Att.readsAtO W l g = some b) : Whole ReqStays b := by
  unfold Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨fun s _ _ s' e => readsAtSO_req A s s' e, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

/-! ## Kind K2's five -/

theorem k2_req (p : K2.P2) : Whole ReqStays (K2.codeSwitchKind p : Block S Unit) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h : K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s' := h
  obtain ⟨hf, -, hr⟩ := K2.keeps _ _ _ _ _ _ h
  exact req_same hr hf

theorem headFrontQ_req (tl : HTailF2) : Fn ReqStays (K2.headFrontQ tl) := fun s s' h => by
  unfold K2.headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, _, h⟩ := K2.bindOk h
      obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
      cases K2.enterHeadQ h₁
      split at h
      · cases h
        exact req_trans _ _ _ (req_enterHead s tl) (req_same rfl rfl)
      · cases h

theorem finishFrontQ_req : Fn ReqStays K2.finishFrontQ := fun s s' h => by
  unfold K2.finishFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
        cases K2.enterFinQ h₁
        split at h
        · cases h
          exact req_trans _ _ _ (req_enterFin s) (req_same rfl rfl)
        · cases h
      · cases h
      · cases h

theorem finishBehindQ_req : Fn ReqStays K2.finishBehindQ := fun s s' h => by
  unfold K2.finishBehindQ at h
  split at h
  · rename_i a ha
    cases hb : _root_.Tw.K2.finishBehind a.sw with
    | error e => rw [hb] at h; cases h
    | ok m =>
      rw [hb] at h
      cases h
      exact req_same rfl rfl
  · cases h

theorem headOpenQ_req (P : K2.HeadPar) : Fn ReqStays (K2.headOpenQ P) := fun s s' h => by
  unfold K2.headOpenQ at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := K2.bindOk h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hf, h⟩ := K2.bindOk h
        dsimp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
                cases K2.openHeadQ h₁
                split at h
                · cases h
                  exact req_trans _ _ _ (req_openHead s) (req_same rfl rfl)
                · cases h
        · cases h
  · cases h

/-! ## The sub-protocols behind the last link -/

theorem atFinish_req (p : K12.P12) : Whole ReqStays (K12.atFinish p) :=
  ⟨fun s rs gs s' h => req_same (K12.Seat.atFinish_leaves_req p s rs gs s' h)
      (K12.Seat.atFinish_leaves_failed p s rs gs s' h),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem atM3_req (p : K13.Where) : Whole ReqStays (K13.atM3 (Cl := Cl) p) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨f, st', o, -, rfl⟩ := K13.Law.atM3_rec h
  exact req_same rfl rfl

theorem sendAtS_req (Q : K1.Par) : Decides ReqStays (K1.sendAtS Q : Block S Cl) := by
  intro s rs gs s' h
  obtain ⟨a, ids, -, -, -, -, -, hr, hf, -⟩ := K1.sendAtS_here Q s s' rs gs h
  exact req_same hr hf

theorem rowsB_req (p : K13.Where) : Decides ReqStays (K13.rowsB (Cl := Cl) K13.atS p) := by
  intro s rs gs s' h
  obtain ⟨m₀, l, o, owed, -, -, -, rfl⟩ := K13.Law.rowsB_at h
  exact req_same rfl rfl

theorem atM4_req (p : K13.Where) (Q : K1.Par) :
    Whole ReqStays (K13.atM4 (Cl := Cl) p (K1.sendAtS Q)) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' : ((K1.sendAtS Q : Block S Cl).decide s _ _).bind (fun m =>
      (K13.rowsB (Cl := Cl) K13.atS p).decide m _ _) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := Keeps.ebind_ok h'
  exact req_trans _ _ _ (sendAtS_req Q _ _ _ _ h1) (rowsB_req p _ _ _ _ h2)

#print axioms req_putLink
#print axioms req_putLive
#print axioms req_enterLay
#print axioms req_enterAtt
#print axioms req_enterHead
#print axioms req_openHead
#print axioms req_enterFin
#print axioms layFront_req
#print axioms openAtt_req
#print axioms openLay_req
#print axioms openLayZero_req
#print axioms clearWith_req
#print axioms tailHead_req
#print axioms framesOf_req
#print axioms commitAtS_req
#print axioms laterAt_req
#print axioms firstAtS_req
#print axioms req_atS_set
#print axioms oneEquation_req
#print axioms closing_req
#print axioms shut_req
#print axioms closeOf_req
#print axioms batch_req
#print axioms layers_req
#print axioms headReads_req
#print axioms readsAtSO_req
#print axioms readsAtO_req
#print axioms k2_req
#print axioms headFrontQ_req
#print axioms finishFrontQ_req
#print axioms finishBehindQ_req
#print axioms headOpenQ_req
#print axioms atFinish_req
#print axioms atM3_req
#print axioms sendAtS_req
#print axioms rowsB_req
#print axioms atM4_req

end Meaning.K2
