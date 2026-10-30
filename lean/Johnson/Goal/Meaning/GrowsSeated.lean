-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/GrowsSeated.lean: "the statement only grows" (Johnson/Desc/Grows.lean) at the
makers that Johnson/Goal/Meaning/RecGrows.lean had left: the closing of a link, the clearing of a
link, the rows of the links' frames, kind K1's blocks, and K9's closing as three blocks with the
batching. GR is the relation on records: GrowsBy fun s => s.st (Johnson/Desc/ChainEndCovered.lean).

  fold_grows, closingP_grows, closeFrame_grows: the closing's plain text
    (Johnson/Desc/First/Close/Closing.lean): its batching lays begun S g G (the library's
    bat_inv_layout; grows_begun), its fold spends one message as a mask (spendAsMaskP_grows).
  closing_grows: Whole GR (K9.closing P).
  clearWith_grows: the clearing (Johnson/Desc/First/Walk/Frame.lean: clearWith), FOR A ROW's
    FUNCTION THAT CHANGES ONE ORACLE MESSAGE AND GROWS IT (RowGrows). pendingRowO_rowGrows: the
    pending row's function is one (the library's pendingRowO_spec: it lays one message's ledger).
  tailHead_grows, framesOf_grows: so every row of Walk.Seat.framesOf: lay, opened, clear.
  firstAtS_grows, laterAt_grows: K1, by the library's Rel.firstAtS_keeps and commitAtS_keeps.
  closeOf_grows, batch_grows: K9's three blocks of a closing; its batching, for a function of claims
    that keeps GR.
OBJECT: the laid makers' blocks and steps that are named above. USER: Johnson/IMR/GrowsSeat.lean, which lies in this library.
Not claimed: anything on kind K2's texts.
-/
import Johnson.Goal.Meaning.RecGrows
import Johnson.Goal.Meaning.RecSeated
import Johnson.Desc.GrowsGround
import Johnson.Desc.ChainEndCovered
import Johnson.Desc.First.Close.Law.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundKeeps By groundKeeps_grows)
open VerifiableInference.Desc.First.Close (closeFrame ok_bind got_ok bat_inv_layout)

variable {Cl : Type}

/-- The statement, read off the first chain's record, grows. -/
abbrev GR : S → S → Prop := ChainEnd.GrowsBy fun s : S => s.st

theorem gr_refl (s : S) : GR s s := Grows.refl _

theorem gr_trans (a b c : S) (h : GR a b) (k : GR b c) : GR a c := Grows.trans h k

/-! ## The closing of a link -/

theorem fold_grows {T T' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : Close.fold T F row m es rs = .ok (out, T')) : Grows T T' := by
  unfold Close.fold at h
  obtain ⟨y, hD, e⟩ := Keeps.emap_ok h
  cases e
  unfold Close.foldD at hD
  split at hD
  · obtain ⟨_, -, hD⟩ := ok_bind hD
    obtain ⟨_, -, hD⟩ := ok_bind hD
    obtain ⟨_, -, hD⟩ := ok_bind hD
    obtain ⟨p, k2, hD⟩ := ok_bind hD
    simp only [pure, Except.pure, Except.ok.injEq] at k2
    subst k2
    obtain ⟨_, -, hD⟩ := ok_bind hD
    obtain ⟨_, -, hD⟩ := ok_bind hD
    obtain ⟨d2, k5, hD⟩ := ok_bind hD
    obtain ⟨z, -, hD⟩ := ok_bind hD
    split at hD
    · obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨w, -, hD⟩ := ok_bind hD
      simp only [pure, Except.pure, Except.ok.injEq] at hD
      subst hD
      exact Ground.spendAsMaskP_grows _ _ _ (got_ok k5)
    · exact absurd hD (by simp)
  · exact absurd hD (by simp)

theorem closingP_grows {P : Close.Plan} {T T' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : Close.closing P T g mask rs = .ok (out, T')) :
    Grows T T' := by
  unfold Close.closing at h
  split at h
  · obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨G, x, -, -, -, a4, -, -⟩ := bat_inv_layout (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    have g1 : Grows T p.2.2 := by
      rw [a4]
      exact grows_begun T g G
    exact g1.trans (fold_grows h)
  · exact absurd h (by simp)

theorem closeFrame_grows {owed : Option Nat} {f f' : ReqFrame} {T T' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f T es rs = .ok (f', T')) :
    Grows T T' := by
  unfold closeFrame at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨L, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨rows, S1⟩, hc, h⟩ := bindE h
  cases h
  exact closingP_grows hc

theorem closing_grows (P : Close.Par) : Whole GR (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact closeFrame_grows (f' := x.1) (T' := x.2) hx

/-! ## The clearing of a link -/

open Johnson.Desc.First.Walk

/-- A row's function changes one oracle message, and grows it. -/
def RowGrows (row : RowFn) : Prop :=
  ∀ im w n os r os', row im w n os = .ok (r, os') →
    ∃ (k : Nat) (f : OnBytes.Oracle → OnBytes.Oracle), (∀ x, OracleGrows x (f x)) ∧
      os' = os.modify k f

theorem pendingRowO_rowGrows (lay : WsLay) (lin : LinShape) :
    RowGrows fun im w n os => Pend.pendingRowO lay im w n lin os := by
  intro im w n os r os' h
  obtain ⟨l, c, l', -, -, -, hos⟩ := Law.pendingRowO_spec h
  exact ⟨im, fun x => { x with ledger := some l' }, fun x => ⟨rfl, id, fun _ k => k⟩, hos⟩

theorem leaveLink_st {s t : S} (h : s.leaveLink? = .ok t) : t.st = s.st := by
  unfold S.leaveLink? at h
  rw [unmarked_eq h]
  unfold S.leaveLink
  split
  · rfl
  · unfold S.mark
    split <;> rfl

theorem clearWith_grows (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) {row : RowFn} (hrow : RowGrows row) :
    Fn GR (clearWith X counts left row) := fun s t h => by
  show Grows s.st t.st
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · rw [leaveLink_st h]
      exact Grows.refl _
    · split at h
      · cases h
      · rename_i r os hr
        rw [leaveLink_st h]
        obtain ⟨k, f, hf, rfl⟩ := hrow _ _ _ _ _ _ hr
        exact grows_modOracle s.st k f hf
  · cases h

theorem tailHead_grows (X : LinkPub) (lay : WsLay) (lin : LinShape) :
    Fn GR (Close.tailHead X lay lin) := clearWith_grows _ _ _ (pendingRowO_rowGrows lay lin)

theorem fn_grows {f : S → Except String S} (h : Fn Quiet f) : Fn GR f :=
  fun s t k => grows_of_quiet (h s t k)

theorem fn_growsE {f : S → Except String S} (h : Fn Enters f) : Fn GR f :=
  fun s t k => grows_of_enters (h s t k)

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_grows {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn GR f.lay ∧ Fn GR f.opened ∧ Fn GR f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_grows (layFront_quiet l), fun s t k => by cases k; exact gr_refl s,
        tailHead_grows _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_grows (layFront_quiet 0), fn_growsE (openLayZero_enters _ _ _),
          clearWith_grows _ _ _ (pendingRowO_rowGrows _ _)⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_grows (layFront_quiet l), fn_growsE (openAtt_enters _),
          clearWith_grows _ _ _ (pendingRowO_rowGrows _ _)⟩
      · cases e
        exact ⟨fn_grows (layFront_quiet l), fn_growsE (openLay_enters _),
          clearWith_grows _ _ _ (pendingRowO_rowGrows _ _)⟩

/-! ## K1 -/

theorem firstAtS_grows (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    Whole GR (K1.firstSegmentOpening (Cl := Cl) q gp) :=
  ⟨K1.Rel.firstAtS_keeps groundKeeps_grows q gp, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem laterAt_grows (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Whole GR (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨K1.Rel.commitAtS_keeps groundKeeps_grows _ link moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

/-! ## K9 -/

theorem closeOf_grows (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole GR b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_by (Cl := Cl) groundKeeps_grows p, (fun _ hc => nomatch hc),
      (fun _ hc => nomatch hc)⟩
  · exact closing_grows P
  · exact whole_mono (fun _ _ q => grows_of_enters q.1) (shut_still p _)

theorem batch_grows (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl GR claims) : Whole GR (K9.batch K9.atS p claims) :=
  ⟨batch_by groundKeeps_grows p hcl, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

#print axioms closing_grows
#print axioms clearWith_grows
#print axioms framesOf_grows
#print axioms laterAt_grows
#print axioms closeOf_grows
#print axioms batch_grows

end Meaning.K2
