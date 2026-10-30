-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/SizeSeated.lean: the makers of the first chain's blocks that SEND NOTHING, at a
relation on the three (Ground.Core: statement, book of trees, count of roots) THAT MAY READ THE
STATEMENT's NUMBER OF ORACLE MESSAGES beside the book and the count: ByC Rc coreS, general in Rc.

  ASKED OF Rc, as a premise: h3: a step that leaves the number of oracle messages, the book and the
    count of roots is related.
  three_of_quiet, whole_three, fn_three, fn_threeE: a Quiet step, and one that Enters, leave the
    statement whole.
  takeN_core, asRow_core, door_core: K9's door, at EVERY relation that the plain ground's eight keep
    (the library's CoreStill).
  oneEquation_three, closing_three (over fold_size, closingP_size, closeFrame_size),
    closeOf_three, batch_three: K9's and K10's.
  clearWith_three, tailHead_three, framesOf_three: the links' frames.
THE GROUND's EIGHT: Ground.coreStill_three, spendAsMaskP_size, closeLedgers_size'
  (Johnson/Desc/CoreKeepsSize.lean).
OBJECT: the laid makers. USER: Johnson/IMR/SizeSeat.lean.
Not claimed: anything on the sendings, or on kinds K2, K12, K13. No soundness.
-/
import Johnson.Goal.Meaning.CoreSeated
import Johnson.Desc.CoreKeepsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core coreOf ByC CoreStill coreStill_three)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.K9
open VerifiableInference.Desc.First.Close (closeFrame ok_bind got_ok bat_inv_layout)

variable {Cl : Type} {Rc : Core → Core → Prop}

theorem three_of_quiet
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) {s t : S} (q : Quiet s t) : ByC Rc coreS s t :=
  h3 _ _ (congrArg (·.oracles.size) q.1.1) q.1.2.2.1 q.1.2.2.2

theorem whole_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) {b : Block S Cl} (W : Whole Quiet b) :
    Whole (ByC Rc coreS) b := whole_mono (fun _ _ => three_of_quiet h3) W

theorem fn_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) {f : S → Except String S} (h : Fn Quiet f) :
    Fn (ByC Rc coreS) f := fun s t k => three_of_quiet h3 (h s t k)

theorem fn_threeE
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) {f : S → Except String S} (h : Fn Enters f) :
    Fn (ByC Rc coreS) f := fun s t k =>
  h3 _ _ (congrArg (·.oracles.size) (h s t k).1) (h s t k).2.2.1 (h s t k).2.2.2

/-! ## K9's door, at every relation that the ground's eight keep -/

theorem takeN_core {X : Type} (H : CoreStill Rc) (o : Nat) : ∀ (n : Nat) (d : St X)
    (acc : List Nat) (y : List Nat × St X), takeN o n d acc = .ok y → Rc (coreOf d) (coreOf y.2)
  | 0, d, acc, y, h => by
    cases h
    exact H.refl _
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact H.trans (H.takeMask d x.2 o x.1 (there_some hx)) (takeN_core H o n x.2 _ y h)

theorem asRow_core {X : Type} (H : CoreStill Rc) {Rw : ReqRows} {f : ReqFrame} {q : Equation}
    {d : St X} {y : Row × St X} (h : asRow Rw f q d = .ok y) : Rc (coreOf d) (coreOf y.2) := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    exact H.refl _
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_core H o _ d [] x hx

theorem door_core {X : Type} (H : CoreStill Rc) {owed : RowsOwed} {laid : Option Nat}
    {L : LinkCtx} {F : Fork} {d : St X} {o : Out X} (h : door owed laid L F d = .ok o) :
    Rc (coreOf d) (coreOf o.d) := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact H.trans (asRow_core H hy) (H.addRow y.2 d' _ y.1 (there_some hd))

theorem oneEquation_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) (p : Where) :
    Decides (ByC Rc coreS) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  have k := (door_core coreStill_three ho).1
  have e : q.d.st = s.st := (atS_get (there_some hq)).2
  refine h3 _ _ ?_ (atS_set_core s _).1 (atS_set_core s _).2
  show o.d.st.oracles.size = s.st.oracles.size
  rw [← e]
  exact k

/-! ## K10's closing -/

theorem fold_size {T T' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : Close.fold T F row m es rs = .ok (out, T')) : T'.oracles.size = T.oracles.size := by
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
      exact Ground.spendAsMaskP_size _ _ _ (got_ok k5)
    · exact absurd hD (by simp)
  · exact absurd hD (by simp)

theorem closingP_size {P : Close.Plan} {T T' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : Close.closing P T g mask rs = .ok (out, T')) :
    T'.oracles.size = T.oracles.size := by
  unfold Close.closing at h
  split at h
  · obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨G, x, -, -, -, a4, -, -⟩ := bat_inv_layout (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    have g1 : p.2.2.oracles.size = T.oracles.size := by
      rw [a4]
      exact Ground.closeLedgers_size' _ _
    exact (fold_size h).trans g1
  · exact absurd h (by simp)

theorem closeFrame_size {owed : Option Nat} {f f' : ReqFrame} {T T' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f T es rs = .ok (f', T')) :
    T'.oracles.size = T.oracles.size := by
  unfold closeFrame at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨L, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨rows, S1⟩, hc, h⟩ := bindE h
  cases h
  exact closingP_size hc

theorem closing_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) (P : Close.Par) :
    Whole (ByC Rc coreS) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact h3 _ _ (closeFrame_size (f' := x.1) (T' := x.2) hx) (putRec_core s _).1
    (putRec_core s _).2

theorem closeOf_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (ByC Rc coreS) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_three (Cl := Cl) h3 p, (fun _ hc => nomatch hc),
      (fun _ hc => nomatch hc)⟩
  · exact closing_three h3 P
  · exact whole_mono (fun _ _ q =>
      h3 _ _ (congrArg (·.oracles.size) q.1.1) q.1.2.2.1 q.1.2.2.2) (shut_still p _)

theorem batch_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b)
    (ht : ∀ {a b c : Core}, Rc a b → Rc b c → Rc a c) (p : K9.Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByC Rc coreS) claims) :
    Whole (ByC Rc coreS) (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : ByC Rc coreS s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      refine h3 _ _ ?_ (atS_set_core s _).1 (atS_set_core s _).2
      show q.d.st.oracles.size = s.st.oracles.size
      rw [(atS_get (there_some hq)).2]
    · cases h1
  have a2 : ByC Rc coreS t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    refine ht (hcl t₁ x hx) (h3 _ _ ?_ (atS_set_core x.2 _).1 (atS_set_core x.2 _).2)
    show q.d.st.oracles.size = x.2.st.oracles.size
    rw [(atS_get (there_some hq)).2]
  exact ht a1 a2

/-! ## The frames -/

open Johnson.Desc.First.Walk in
theorem clearWith_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b)
    (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut) {row : RowFn}
    (hrow : RowGrows row) : Fn (ByC Rc coreS) (clearWith X counts left row) := fun s t h => by
  refine h3 _ _ ?_ (Law.clear_carries h).2.1 (Law.clear_carries h).2.2.1
  show t.st.oracles.size = s.st.oracles.size
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · rw [leaveLink_st h]
    · split at h
      · cases h
      · rename_i r os hr
        rw [leaveLink_st h]
        obtain ⟨k, f, -, rfl⟩ := hrow _ _ _ _ _ _ hr
        exact Array.size_modify
  · cases h

open Johnson.Desc.First.Walk in
theorem tailHead_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b) (X : LinkPub) (lay : WsLay) (lin : LinShape) :
    Fn (ByC Rc coreS) (Close.tailHead X lay lin) :=
  clearWith_three h3 _ _ _ (pendingRowO_rowGrows lay lin)

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_three
    (h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
      b.roots = a.roots → Rc a b)
    {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (ByC Rc coreS) f.lay ∧ Fn (ByC Rc coreS) f.opened ∧ Fn (ByC Rc coreS) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_three h3 (layFront_quiet l), fun s t k => by cases k; exact h3 _ _ rfl rfl rfl,
        tailHead_three h3 _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_three h3 (layFront_quiet 0), fn_threeE h3 (openLayZero_enters _ _ _),
          clearWith_three h3 _ _ _ (pendingRowO_rowGrows _ _)⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_three h3 (layFront_quiet l), fn_threeE h3 (openAtt_enters _),
          clearWith_three h3 _ _ _ (pendingRowO_rowGrows _ _)⟩
      · cases e
        exact ⟨fn_three h3 (layFront_quiet l), fn_threeE h3 (openLay_enters _),
          clearWith_three h3 _ _ _ (pendingRowO_rowGrows _ _)⟩

#print axioms door_core
#print axioms closeOf_three
#print axioms batch_three
#print axioms framesOf_three

end Meaning.K2
