-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/StatementSeated.lean: EVERY MAKER OF THE FIRST CHAIN's SUB-PROTOCOLS KEEPS A
RELATION ON THE STATEMENT THAT MEETS StKeeps (Johnson/Desc/K13/Law/StatementCalls.lean): the lemmas,
maker by maker.

It follows Johnson/Goal/Meaning/GrowsSeated.lean ("the statement grows") lemma by lemma, general in
the relation R: where that file calls a law of the ground at "grows", this one calls StKeeps' field
ground; at the beginning of a proximity test: begun; at the one write of a pending row: row. A maker
that leaves the statement (Enters, Quiet, Still: Johnson/Goal/Meaning/RecQuiet.lean) keeps R because
R is reflexive. Kind K2's five texts go by other files' laws, which take any relation that the
ground's routines keep (Johnson/Top/H0/Tw/K2C/KeepsWhole.lean, SendsOn.lean, Keeps.lean).

  whole_by, fn_by, fn_byE   the makers that leave the statement.
  fold_by, closingP_by, closeFrame_by, closing_by   the closing of a link.
  RowBy, pendingRowO_rowBy, clearWith_by, tailHead_by, framesOf_by   the links' frames.
  firstAtS_by, laterAt_by   kind K1. closeOf_by, batchW_by   kind K9.
  k2_by, headFrontQ_by, headOpenQ_by, finishFrontQ_by, finishBehindQ_by   kind K2.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Meaning.GrowsSeated
import Johnson.Desc.K13.Law.StatementCalls
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Top.H0.Tw.K2C.SendsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.First.Close (closeFrame ok_bind got_ok bat_inv_layout)
open VerifiableInference.Desc.K13.Law (StKeeps)

variable {Cl : Type} {R : Statement → Statement → Prop}

/-! ## The makers that leave the statement -/

theorem by_refl (K : StKeeps R) (s : S) : ByS R s s := K.ground.refl _

theorem by_trans (K : StKeeps R) (a b c : S) (h : ByS R a b) (k : ByS R b c) : ByS R a c :=
  K.ground.trans h k

theorem by_of_st (K : StKeeps R) {s t : S} (e : t.st = s.st) : ByS R s t := by
  show R s.st t.st
  rw [e]
  exact K.ground.refl _

theorem by_of_enters (K : StKeeps R) {s s' : S} (q : Enters s s') : ByS R s s' := by_of_st K q.1

theorem by_of_quiet (K : StKeeps R) {s s' : S} (q : Quiet s s') : ByS R s s' := by_of_enters K q.1

theorem whole_by (K : StKeeps R) {b : Block S Cl} (W : Whole Quiet b) : Whole (ByS R) b :=
  whole_mono (fun _ _ => by_of_quiet K) W

theorem fn_by (K : StKeeps R) {f : S → Except String S} (h : Fn Quiet f) : Fn (ByS R) f :=
  fun s t k => by_of_quiet K (h s t k)

theorem fn_byE (K : StKeeps R) {f : S → Except String S} (h : Fn Enters f) : Fn (ByS R) f :=
  fun s t k => by_of_enters K (h s t k)

/-! ## The closing of a link -/

theorem fold_by (K : StKeeps R) {T T' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : Close.fold T F row m es rs = .ok (out, T')) : R T T' := by
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
      exact K.ground.spendAsMask _ _ _ (got_ok k5)
    · exact absurd hD (by simp)
  · exact absurd hD (by simp)

theorem closingP_by (K : StKeeps R) {P : Close.Plan} {T T' : Statement} {g : Nat}
    {mask : Option Nat} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : Close.closing P T g mask rs = .ok (out, T')) : R T T' := by
  unfold Close.closing at h
  split at h
  · obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨G, x, -, -, -, a4, -, -⟩ := bat_inv_layout (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    have g1 : R T p.2.2 := by
      rw [a4]
      exact K.begun T g G
    exact K.ground.trans g1 (fold_by K h)
  · exact absurd h (by simp)

theorem closeFrame_by (K : StKeeps R) {owed : Option Nat} {f f' : ReqFrame} {T T' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f T es rs = .ok (f', T')) :
    R T T' := by
  unfold closeFrame at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨L, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨rows, S1⟩, hc, h⟩ := bindE h
  cases h
  exact closingP_by K hc

theorem closing_by (K : StKeeps R) (P : Close.Par) : Whole (ByS R) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact closeFrame_by K (f' := x.1) (T' := x.2) hx

/-! ## The clearing of a link -/

open Johnson.Desc.First.Walk

/-- A row's function writes the messages so that R is kept. -/
def RowBy (R : Statement → Statement → Prop) (row : RowFn) : Prop :=
  ∀ im w n (T : Statement) r os', row im w n T.oracles = .ok (r, os') →
    R T { T with oracles := os' }

theorem pendingRowO_rowBy (K : StKeeps R) (lay : WsLay) (lin : LinShape) :
    RowBy R fun im w n os => Pend.pendingRowO lay im w n lin os :=
  fun im w n T r os' h => K.row lay im w n lin T r os' h

theorem clearWith_by (K : StKeeps R) (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) {row : RowFn} (hrow : RowBy R row) :
    Fn (ByS R) (clearWith X counts left row) := fun s t h => by
  show R s.st t.st
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · rw [leaveLink_st h]
      exact K.ground.refl _
    · split at h
      · cases h
      · rename_i r os hr
        rw [leaveLink_st h]
        exact hrow _ _ _ s.st _ _ hr
  · cases h

theorem tailHead_by (K : StKeeps R) (X : LinkPub) (lay : WsLay) (lin : LinShape) :
    Fn (ByS R) (Close.tailHead X lay lin) := clearWith_by K _ _ _ (pendingRowO_rowBy K lay lin)

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_by (K : StKeeps R) {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (ByS R) f.lay ∧ Fn (ByS R) f.opened ∧ Fn (ByS R) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_by K (layFront_quiet l), fun s t k => by cases k; exact by_refl K s,
        tailHead_by K _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_by K (layFront_quiet 0), fn_byE K (openLayZero_enters _ _ _),
          clearWith_by K _ _ _ (pendingRowO_rowBy K _ _)⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_by K (layFront_quiet l), fn_byE K (openAtt_enters _),
          clearWith_by K _ _ _ (pendingRowO_rowBy K _ _)⟩
      · cases e
        exact ⟨fn_by K (layFront_quiet l), fn_byE K (openLay_enters _),
          clearWith_by K _ _ _ (pendingRowO_rowBy K _ _)⟩

/-! ## K1 -/

theorem firstAtS_by (K : StKeeps R) (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    Whole (ByS R) (K1.firstSegmentOpening (Cl := Cl) q gp) :=
  ⟨K1.Rel.firstAtS_keeps K.ground q gp, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem laterAt_by (K : StKeeps R) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    Whole (ByS R) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨K1.Rel.commitAtS_keeps K.ground _ link moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

/-! ## K9 -/

theorem closeOf_by (K : StKeeps R) (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (ByS R) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_by (Cl := Cl) K.ground p, (fun _ hc => nomatch hc),
      (fun _ hc => nomatch hc)⟩
  · exact closing_by K P
  · exact whole_mono (fun _ _ q => by_of_enters K q.1) (shut_still p _)

theorem batchW_by (K : StKeeps R) (p : K9.Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Whole (ByS R) (K9.batch K9.atS p claims) :=
  ⟨batch_by K.ground p hcl, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## K2 -/

theorem k2_by (K : StKeeps R) (p : K2.P2) : Whole (ByS R) (K2.codeSwitchKind (Cl := Cl) p) :=
  ⟨fun _ _ _ _ h => K2.yes_keeps_whole K.ground h, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem headFrontQ_by (K : StKeeps R) (tl : HTailF2) : Fn (ByS R) (K2.headFrontQ tl) :=
  fun s t h => by
  obtain ⟨x, s₁, a, k⟩ := (K2.headFrontQ_iff tl s t).1 h
  show R s.st t.st
  rw [k.out]
  exact K2.firstFront_keeps K.ground k.front

theorem headOpenQ_by (K : StKeeps R) (P : K2.HeadPar) : Fn (ByS R) (K2.headOpenQ P) :=
  fun _ _ h => K2.headOpenQ_keeps K.ground h

theorem finishFrontQ_by (K : StKeeps R) : Fn (ByS R) K2.finishFrontQ :=
  fun _ _ h => K2.finishFrontQ_keeps K.ground h

theorem finishBehindQ_by (K : StKeeps R) : Fn (ByS R) K2.finishBehindQ :=
  fun _ _ h => by_of_st K (K2.finishBehindQ_st h)

end Meaning.K2
