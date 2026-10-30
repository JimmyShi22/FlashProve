-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/CoreSeated.lean: the makers of the first chain's blocks, at a relation on THE
THREE that the plain ground writes (statement, book of trees, count of roots: Ground.Core,
Johnson/Desc/CoreKeeps.lean), read off the record by K1.RelCore.coreS
(Johnson/Desc/K1/KeepsAtSCore.lean): ByC Rc coreS. General in Rc.

  ASKED OF Rc, as premises: hs: a step that leaves the book and the count of roots is related
    (∀ a b, b.book = a.book → b.roots = a.roots → Rc a b); and, for the sendings, the library's
    CoreRecv 0 Rc.
  core_of_quiet, whole_core: a Quiet step (Johnson/Goal/Meaning/RecQuiet.lean) leaves all three.
  framesOf_core: every row of the links' frames: "laid" is Quiet, "opened" Enters; "cleared" by the
    library's Law.clear_carries (Johnson/Top/H0/Walk/FrameLaw.lean).
  firstAtS_core, laterAt_core: K1's two, by the library's RelCore.firstAtS_keeps and
    commitAtS_keeps, at a place whose first tree bears the number 0.
  atS_set_core, putRec_core; oneEquation_core, closing_core, closeOf_core, batch_core: K9's and
    K10's: their lenses lay back neither the book nor the count of roots.
  atM3_core, atM4_core: K13's two, by the library's K13.RelCore.atM3_keeps and atM4_keeps over
    RelCore.sendAtS_keeps.
OBJECT: the laid makers. USER: Johnson/IMR/BookSeat.lean, which lies in this library.
Not claimed: anything on kinds K2 and K12. No soundness.
-/
import Johnson.Goal.Meaning.GrowsSeated
import Johnson.Desc.K1.KeepsAtSCore
import Johnson.Desc.K13.KeepsCore
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC CoreStill CoreRecv)
open VerifiableInference.Desc.K1.RelCore (coreS putLink_core putFork_core)
open VerifiableInference.Desc.K9 (atS drawAlone adds batch oneEquation Where)

variable {Cl : Type} {Rc : Core → Core → Prop}

theorem core_of_quiet (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b) {s t : S}
    (q : Quiet s t) : ByC Rc coreS s t := hs _ _ q.1.2.2.1 q.1.2.2.2

theorem whole_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    {b : Block S Cl} (W : Whole Quiet b) : Whole (ByC Rc coreS) b :=
  whole_mono (fun _ _ => core_of_quiet hs) W

theorem fn_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    {f : S → Except String S} (h : Fn Quiet f) : Fn (ByC Rc coreS) f :=
  fun s t k => core_of_quiet hs (h s t k)

theorem fn_coreE (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    {f : S → Except String S} (h : Fn Enters f) : Fn (ByC Rc coreS) f :=
  fun s t k => hs _ _ (h s t k).2.2.1 (h s t k).2.2.2

/-! ## The frames -/

open Johnson.Desc.First.Walk in
theorem clearWith_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut) (row : RowFn) :
    Fn (ByC Rc coreS) (clearWith X counts left row) := fun _ _ h =>
  hs _ _ (Law.clear_carries h).2.1 (Law.clear_carries h).2.2.1

open Johnson.Desc.First.Walk in
theorem tailHead_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    (X : LinkPub) (lay : WsLay) (lin : LinShape) : Fn (ByC Rc coreS) (Close.tailHead X lay lin) :=
  clearWith_core hs _ _ _ _

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
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
      exact ⟨fn_core hs (layFront_quiet l), fun s t k => by cases k; exact hs _ _ rfl rfl,
        tailHead_core hs _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_core hs (layFront_quiet 0), fn_coreE hs (openLayZero_enters _ _ _),
          clearWith_core hs _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_core hs (layFront_quiet l), fn_coreE hs (openAtt_enters _),
          clearWith_core hs _ _ _ _⟩
      · cases e
        exact ⟨fn_core hs (layFront_quiet l), fn_coreE hs (openLay_enters _),
          clearWith_core hs _ _ _ _⟩

/-! ## K1 -/

theorem firstAtS_core (H : CoreRecv 0 Rc) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (h0 : gp.firstTree = 0) : Whole (ByC Rc coreS) (K1.firstSegmentOpening (Cl := Cl) q gp) :=
  ⟨K1.RelCore.firstAtS_keeps q gp (h0 ▸ H), (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem laterAt_core (H : CoreRecv 0 Rc) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) (h0 : gp.firstTree = 0) :
    Whole (ByC Rc coreS) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨K1.RelCore.commitAtS_keeps _ (h0 ▸ H) link moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

/-! ## K9 and K10 -/

/-- The lens lays back neither the book nor the count of roots. -/
theorem atS_set_core (s : S) (p : K9.Part) :
    (atS.set s p).book = s.book ∧ (atS.set s p).roots = s.roots := by
  have e : coreS ((s.putLink p.L).putFork p.F) = coreS s :=
    (putFork_core _ _).trans (putLink_core _ _)
  exact ⟨congrArg (·.book) e, congrArg (·.roots) e⟩

theorem oneEquation_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    (p : Where) : Decides (ByC Rc coreS) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  exact hs _ _ (atS_set_core s _).1 (atS_set_core s _).2

/-- The closing's lens lays back neither the book nor the count of roots. -/
theorem putRec_core (s : S) (r : Close.Rec) :
    (K9.putRec s r).book = s.book ∧ (K9.putRec s r).roots = s.roots := by
  have e : ∀ c : ChainCheck, coreS (s.putLive c) = coreS s := by
    intro c
    unfold S.putLive
    split
    · exact putLink_core _ _
    · rfl
  exact ⟨congrArg (·.book) (e _), congrArg (·.roots) (e _)⟩

theorem closing_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    (P : Close.Par) : Whole (ByC Rc coreS) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact hs _ _ (putRec_core s _).1 (putRec_core s _).2

theorem closeOf_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
    (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (ByC Rc coreS) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_core (Cl := Cl) hs p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact closing_core hs P
  · exact whole_mono (fun _ _ q => hs _ _ q.1.2.2.1 q.1.2.2.2) (shut_still p _)

theorem batch_core (hs : ∀ a b : Core, b.book = a.book → b.roots = a.roots → Rc a b)
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
      exact hs _ _ (atS_set_core s _).1 (atS_set_core s _).2
    · cases h1
  have a2 : ByC Rc coreS t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact ht (hcl t₁ x hx) (hs _ _ (atS_set_core x.2 _).1 (atS_set_core x.2 _).2)
  exact ht a1 a2

/-! ## K13 -/

theorem atM3_core (H : CoreStill Rc) (p : K13.Where) :
    Whole (ByC Rc coreS) (K13.atM3 (Cl := Cl) p) :=
  ⟨K13.RelCore.atM3_keeps H p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem atM4_core (H : CoreRecv 0 Rc) (p : K13.Where) (P : K1.Par) (h0 : P.gp.firstTree = 0) :
    Whole (ByC Rc coreS) (K13.atM4 (Cl := Cl) p (K1.sendAtS P)) :=
  ⟨K13.RelCore.atM4_keeps H.toCoreStill p _ (K1.RelCore.sendAtS_keeps P (h0 ▸ H)),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

#print axioms framesOf_core
#print axioms laterAt_core
#print axioms closeOf_core
#print axioms batch_core
#print axioms atM3_core
#print axioms atM4_core

end Meaning.K2
