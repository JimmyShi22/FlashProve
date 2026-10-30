-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/QuietSeated.lean: THE SEAT's MAKERS THAT ADMIT NO
SAMPLE, at every StQuiet R: the closing and the clearing of a link · the links' frames · K9's three
· K2's four texts without a round. ONE LINE TURNED BY HAND: closingP_byQ hands K.begun the fact "the
group is there", which bat_inv_layout gives.
CARRIED BY PROGRAM out of Johnson/Desc/K13/Law/StatementSeated.lean:
each declaration that is needed for the top and names
GroundKeeps | StKeeps is copied under its own name with a letter behind it (Q), with GroundQuiet |
StQuiet in that word's place; its docstrings are struck (they are that file's); where a proof opens
the word itself it is turned by hand. THE ORIGINAL IS IMPORTED AND NOT TURNED: what names neither
word is called from it. IF THE ORIGINAL ITSELF IS WIDENED INSTEAD, THIS FILE FALLS.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.StatementSeated
import Johnson.Desc.GroundQuiet
import Johnson.Desc.AtSeats.Fit.StQuiet
import Johnson.ToldDescR.K2KeepsQuiet
import Johnson.Desc.AtSeats.Fit.QuietK2Sends
import Johnson.Desc.AtSeats.Fit.QuietK9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundKeeps GroundQuiet By)
open VerifiableInference.Desc.First.Close (closeFrame ok_bind got_ok bat_inv_layout)
open VerifiableInference.Desc.K13.Law (StKeeps StQuiet)

variable {Cl : Type} {R : Statement → Statement → Prop}

theorem by_reflQ (K : StQuiet R) (s : S) : ByS R s s := K.quiet.refl _

theorem by_transQ (K : StQuiet R) (a b c : S) (h : ByS R a b) (k : ByS R b c) : ByS R a c :=
  K.quiet.trans h k

theorem by_of_stQ (K : StQuiet R) {s t : S} (e : t.st = s.st) : ByS R s t := by
  show R s.st t.st
  rw [e]
  exact K.quiet.refl _

theorem by_of_entersQ (K : StQuiet R) {s s' : S} (q : Enters s s') : ByS R s s' := by_of_stQ K q.1

theorem by_of_quietQ (K : StQuiet R) {s s' : S} (q : Quiet s s') : ByS R s s' := by_of_entersQ K q.1

theorem whole_byQ (K : StQuiet R) {b : Block S Cl} (W : Whole Quiet b) : Whole (ByS R) b :=
  whole_mono (fun _ _ => by_of_quietQ K) W

theorem fn_byQ (K : StQuiet R) {f : S → Except String S} (h : Fn Quiet f) : Fn (ByS R) f :=
  fun s t k => by_of_quietQ K (h s t k)

theorem fn_byEQ (K : StQuiet R) {f : S → Except String S} (h : Fn Enters f) : Fn (ByS R) f :=
  fun s t k => by_of_entersQ K (h s t k)

theorem fold_byQ (K : StQuiet R) {T T' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
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
      exact K.quiet.spendAsMask _ _ _ (got_ok k5)
    · exact absurd hD (by simp)
  · exact absurd hD (by simp)

theorem closingP_byQ (K : StQuiet R) {P : Close.Plan} {T T' : Statement} {g : Nat}
    {mask : Option Nat} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : Close.closing P T g mask rs = .ok (out, T')) : R T T' := by
  unfold Close.closing at h
  split at h
  · obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨G, x, hG, -, -, a4, -, -⟩ := bat_inv_layout (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    have g1 : R T p.2.2 := by
      rw [a4]
      exact K.begun T g G hG
    exact K.quiet.trans g1 (fold_byQ K h)
  · exact absurd h (by simp)

theorem closeFrame_byQ (K : StQuiet R) {owed : Option Nat} {f f' : ReqFrame} {T T' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f T es rs = .ok (f', T')) :
    R T T' := by
  unfold closeFrame at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨L, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨rows, S1⟩, hc, h⟩ := bindE h
  cases h
  exact closingP_byQ K hc

theorem closing_byQ (K : StQuiet R) (P : Close.Par) : Whole (ByS R) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact closeFrame_byQ K (f' := x.1) (T' := x.2) hx

open Johnson.Desc.First.Walk

theorem pendingRowO_rowByQ (K : StQuiet R) (lay : WsLay) (lin : LinShape) :
    RowBy R fun im w n os => Pend.pendingRowO lay im w n lin os :=
  fun im w n T r os' h => K.row lay im w n lin T r os' h

theorem clearWith_byQ (K : StQuiet R) (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) {row : RowFn} (hrow : RowBy R row) :
    Fn (ByS R) (clearWith X counts left row) := fun s t h => by
  show R s.st t.st
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · rw [leaveLink_st h]
      exact K.quiet.refl _
    · split at h
      · cases h
      · rename_i r os hr
        rw [leaveLink_st h]
        exact hrow _ _ _ s.st _ _ hr
  · cases h

theorem tailHead_byQ (K : StQuiet R) (X : LinkPub) (lay : WsLay) (lin : LinShape) :
    Fn (ByS R) (Close.tailHead X lay lin) := clearWith_byQ K _ _ _ (pendingRowO_rowByQ K lay lin)

open Johnson.Desc.First.Walk.Seat in
theorem framesOf_byQ (K : StQuiet R) {built : Array Stages.LinkH} {first : Params.First}
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
      exact ⟨fn_byQ K (layFront_quiet l), fun s t k => by cases k; exact by_reflQ K s,
        tailHead_byQ K _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_byQ K (layFront_quiet 0), fn_byEQ K (openLayZero_enters _ _ _),
          clearWith_byQ K _ _ _ (pendingRowO_rowByQ K _ _)⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_byQ K (layFront_quiet l), fn_byEQ K (openAtt_enters _),
          clearWith_byQ K _ _ _ (pendingRowO_rowByQ K _ _)⟩
      · cases e
        exact ⟨fn_byQ K (layFront_quiet l), fn_byEQ K (openLay_enters _),
          clearWith_byQ K _ _ _ (pendingRowO_rowByQ K _ _)⟩

theorem closeOf_byQ (K : StQuiet R) (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (ByS R) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_byQ (Cl := Cl) K.quiet p, (fun _ hc => nomatch hc),
      (fun _ hc => nomatch hc)⟩
  · exact closing_byQ K P
  · exact whole_mono (fun _ _ q => by_of_entersQ K q.1) (shut_still p _)

theorem batchW_byQ (K : StQuiet R) (p : K9.Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Whole (ByS R) (K9.batch K9.atS p claims) :=
  ⟨batch_byQ K.quiet p hcl, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem headFrontQ_byQ (K : StQuiet R) (tl : HTailF2) : Fn (ByS R) (K2.headFrontQ tl) :=
  fun s t h => by
  obtain ⟨x, s₁, a, k⟩ := (K2.headFrontQ_iff tl s t).1 h
  show R s.st t.st
  rw [k.out]
  exact K2.firstFront_keepsQ K.quiet k.front

theorem headOpenQ_byQ (K : StQuiet R) (P : K2.HeadPar) : Fn (ByS R) (K2.headOpenQ P) :=
  fun _ _ h => K2.headOpenQ_keepsQ K.quiet h

theorem finishFrontQ_byQ (K : StQuiet R) : Fn (ByS R) K2.finishFrontQ :=
  fun _ _ h => K2.finishFrontQ_keepsQ K.quiet h

theorem finishBehindQ_byQ (K : StQuiet R) : Fn (ByS R) K2.finishBehindQ :=
  fun _ _ h => by_of_stQ K (K2.finishBehindQ_st h)

end Meaning.K2
