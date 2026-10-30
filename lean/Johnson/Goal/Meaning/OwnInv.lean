-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/OwnInv.lean: AN INVARIANT OF THE FIRST CHAIN's RECORD, FOR THE LOOKUPS' TIE
OwnIs (Johnson/Desc/First/Look/K3CallerOwn.lean): the layout in every copy of the rows is the
plan's, and a link's context that counts as open bears, at its own number, the plan's list of
arrays. Definitions and the laws that read no maker's text but the frame's. Three definitions,
theorems, proved.

  OwnInv A lay t   over ctxOf (Johnson/Goal/Meaning/RecQuiet.lean): the walk's copy of the rows has
    the layout lay; so has the copy in a link's context, where one lies in the record; and where
    that context counts as open (ctxOf's mark is not 1: a layers' or an attention link's, or the
    head's behind its opening), its list of arrays is A at its own number.
  OwnRel A lay s t   the invariant is handed on. SameCtx s t what ctxOf reads stays.
  own_of_ctx, own_of_quiet, whole_own, whole_ownC, fn_own   so every step that is Quiet, or leaves
    ctxOf, hands it on.
  OwnInv.live   t.live.rows.layout = lay. OwnInv.atLay, OwnInv.atAtt, OwnInv.atHead the open link's
    list of arrays.
  ctx_putLink, ctx_putFork, ctx_putLive   three writers of the record leave ctxOf, the first and the
    third under what they must.
  openAtt_ctx, openLay_ctx, openLayZero_ctx   what "opened" lays at the three sorts of link: ctxOf t
    = (s.check.rows, some (0, s.check.rows, P.l, P.X.arrayOf)); at link 0 the number is 0.
  openAtt_own, openLay_own, openLayZero_own   "opened" at the three sorts of link, where the
    letters' list of arrays is A at the letters' number: by the laws on these steps
    (Johnson/Top/H0/Walk/FrameLaw.lean).
  clearWith_own   "cleared": by clear_carries.

Object, user, letters. Object: the record S; the frame's four steps. User:
Johnson/Goal/Meaning/OwnMakers.lean, Johnson/Goal/Meaning/K2Share/OwnKept.lean. Letters: A, lay:
free.

What is not claimed. That the invariant holds of any record. Anything on the number of the link that
is open. Nothing on soundness.
-/
import Johnson.Goal.Meaning.RecSeated
import Johnson.Goal.Meaning.RecGrows
import Johnson.Top.H0.Walk.FrameLaw

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

/-! ## The invariant -/

/-- **What holds of the record at every border**: the walk's copy of the rows has the layout lay; so
has the copy in a link's context, where one lies in the record; and a context that counts as open
has, at its own number, the list of arrays A. -/
def OwnInv (A : Nat → Array (Nat × String)) (lay : ReqLayout) (t : S) : Prop :=
  (ctxOf t).1.layout = lay ∧
    ∀ x, (ctxOf t).2 = some x → x.2.1.layout = lay ∧ (x.1 ≠ 1 → x.2.2.2 = A x.2.2.1)

/-- The invariant is handed on. -/
def OwnRel (A : Nat → Array (Nat × String)) (lay : ReqLayout) : S → S → Prop :=
  fun s t => OwnInv A lay s → OwnInv A lay t

/-- What ctxOf reads stays. -/
def SameCtx (s t : S) : Prop := ctxOf t = ctxOf s

theorem ownRel_refl (s : S) : OwnRel A lay s s := id

theorem ownRel_trans (a b c : S) (h : OwnRel A lay a b) (k : OwnRel A lay b c) :
    OwnRel A lay a c := fun x => k (h x)

theorem own_of_ctx {s t : S} (e : SameCtx s t) : OwnRel A lay s t := fun I => by
  unfold OwnInv
  rw [e]
  exact I

theorem own_of_quiet {s t : S} (q : Quiet s t) : OwnRel A lay s t := own_of_ctx q.ctx

theorem whole_own {b : Block S Cl} (W : Whole Quiet b) : Whole (OwnRel A lay) b :=
  whole_mono (fun _ _ => own_of_quiet) W

theorem whole_ownC {b : Block S Cl} (W : Whole SameCtx b) : Whole (OwnRel A lay) b :=
  whole_mono (fun _ _ => own_of_ctx) W

theorem fn_own {f : S → Except String S} (h : Fn Quiet f) : Fn (OwnRel A lay) f :=
  fun s t k => own_of_quiet (h s t k)

/-! ## What it says of the live state of the calls and of the open link -/

theorem OwnInv.live {t : S} (I : OwnInv A lay t) : t.live.rows.layout = lay := by
  unfold S.live S.link?
  cases h : t.here with
  | between => exact I.1
  | fin a => exact I.1
  | mem a => exact I.1
  | lay a => exact (I.2 (0, a.L.check.rows, a.L.link, a.L.arrayOf) (by simp [ctxOf, h])).1
  | att a => exact (I.2 (0, a.L.check.rows, a.L.link, a.L.arrayOf) (by simp [ctxOf, h])).1
  | head a =>
    by_cases ho : a.opened = true
    · simp only [ho, if_true]
      exact (I.2 (2, a.L.check.rows, a.L.link, a.L.arrayOf) (by simp [ctxOf, h, ho])).1
    · simp only [ho]
      exact I.1

theorem OwnInv.atLay {t : S} (I : OwnInv A lay t) {a : LayOwn} (h : t.here = .lay a) :
    a.L.arrayOf = A a.L.link :=
  (I.2 (0, a.L.check.rows, a.L.link, a.L.arrayOf) (by simp [ctxOf, h])).2 (fun k => nomatch k)

theorem OwnInv.atAtt {t : S} (I : OwnInv A lay t) {a : AttOwn} (h : t.here = .att a) :
    a.L.arrayOf = A a.L.link :=
  (I.2 (0, a.L.check.rows, a.L.link, a.L.arrayOf) (by simp [ctxOf, h])).2 (fun k => nomatch k)

theorem OwnInv.atHead {t : S} (I : OwnInv A lay t) {a : HeadOwn} (h : t.here = .head a)
    (ho : a.opened = true) : a.L.arrayOf = A a.L.link :=
  (I.2 (2, a.L.check.rows, a.L.link, a.L.arrayOf) (by simp [ctxOf, h, ho])).2 (fun k => nomatch k)

/-! ## Writing the open link's context, the fork, the live state of the calls -/

theorem ctx_putLink {s : S} {L L' : LinkCtx} (h : s.link? = some L)
    (e1 : L'.check.rows = L.check.rows) (e2 : L'.link = L.link) (e3 : L'.arrayOf = L.arrayOf) :
    ctxOf (s.putLink L') = ctxOf s := by
  unfold S.link? at h
  unfold S.putLink
  split
  · rename_i a ha
    rw [ha] at h
    obtain rfl := Option.some.inj h
    simp [ctxOf, *]
  · rename_i a ha
    rw [ha] at h
    obtain rfl := Option.some.inj h
    simp [ctxOf, *]
  · rename_i a ha
    rw [ha] at h
    split
    · rename_i ho
      have h' : (if a.opened = true then some a.L else none) = some L := h
      rw [if_pos ho] at h'
      obtain rfl := Option.some.inj h'
      simp [ctxOf, *]
    · rfl
  · rfl

theorem ctx_putFork (s : S) (F : Fork) : ctxOf (s.putFork F) = ctxOf s := by
  unfold S.putFork
  repeat' split
  all_goals first | rfl | simp [ctxOf, *]

theorem ctx_putLive (s : S) {c : ChainCheck} (e : c.rows = s.live.rows) :
    ctxOf (s.putLive c) = ctxOf s := by
  unfold S.putLive
  unfold S.live at e
  split
  · rename_i L hL
    rw [hL] at e
    exact ctx_putLink hL e rfl rfl
  · rename_i hL
    rw [hL] at e
    cases h : s.here <;> simp [ctxOf, h, e]

/-! ## The links' frames -/

theorem enterLay_ctx {s : S} (hB : s.atBetween = true) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    ctxOf (S.enterLay s L F tl) = (s.check.rows, some (0, L.check.rows, L.link, L.arrayOf)) := by
  unfold S.enterLay
  rw [if_pos hB]
  rfl

theorem enterAtt_ctx {s : S} (hB : s.atBetween = true) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    ctxOf (S.enterAtt s L F tl) = (s.check.rows, some (0, L.check.rows, L.link, L.arrayOf)) := by
  unfold S.enterAtt
  rw [if_pos hB]
  rfl

theorem own_opened {s t : S} {l : Nat} {ar : Array (Nat × String)}
    (e : ctxOf t = (s.check.rows, some (0, s.check.rows, l, ar))) (hA : ar = A l) :
    OwnRel A lay s t := fun I => by
  unfold OwnInv
  rw [e]
  refine ⟨I.1, fun x hx => ?_⟩
  obtain rfl := Option.some.inj hx
  exact ⟨I.1, fun _ => hA⟩

theorem openAtt_ctx {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    ctxOf t = (s.check.rows, some (0, s.check.rows, P.l, P.X.arrayOf)) := by
  obtain ⟨hB, -, -, -, hl, -⟩ := Law.openAtt_ok h
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := unmarked_eq h
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterAtt_ok (L := a.L) (F := a.F) (tl := a.tl) hB').1
  rw [← e, hl] at k
  have eL := Option.some.inj k
  rw [e, enterAtt_ctx hB', ← eL]

theorem openLay_ctx {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    ctxOf t = (s.check.rows, some (0, s.check.rows, P.l, P.X.arrayOf)) := by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLay_ok h
  unfold openLay at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := unmarked_eq h
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [← e, hl] at k
  have eL := Option.some.inj k
  rw [e, enterLay_ctx hB', ← eL]

theorem openLayZero_ctx {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) :
    ctxOf t = (s.check.rows, some (0, s.check.rows, 0, P.X.arrayOf)) := by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLayZero_ok h
  unfold openLayZero at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := unmarked_eq h
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [← e, hl] at k
  have eL := Option.some.inj k
  rw [e, enterLay_ctx hB', ← eL]

theorem openAtt_own (P : AttPar) (hA : P.X.arrayOf = A P.l) : Fn (OwnRel A lay) (openAtt P) :=
  fun _ _ h => own_opened (openAtt_ctx h) hA

theorem openLay_own (P : LayPar) (hA : P.X.arrayOf = A P.l) : Fn (OwnRel A lay) (openLay P) :=
  fun _ _ h => own_opened (openLay_ctx h) hA

theorem openLayZero_own (P : LayPar) (fvs : List Bool) (kCol : Nat) (hA : P.X.arrayOf = A 0) :
    Fn (OwnRel A lay) (openLayZero P fvs kCol) :=
  fun _ _ h => own_opened (openLayZero_ctx h) hA

theorem clearWith_own (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) :
    Fn (OwnRel A lay) (clearWith X counts left row) := fun s t h I => by
  obtain ⟨-, -, -, -, -, -, hc, -, -, hb⟩ := Law.clear_carries h
  have hh : t.here = .between := by
    unfold S.atBetween at hb
    cases k : t.here <;> simp [k] at hb ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · show t.check.rows.layout = lay
    rw [hc]
    exact I.live
  · simp [ctxOf, hh] at hx

#print axioms own_of_ctx
#print axioms OwnInv.live
#print axioms OwnInv.atLay
#print axioms OwnInv.atHead
#print axioms ctx_putLink
#print axioms ctx_putLive
#print axioms openAtt_ctx
#print axioms openLay_ctx
#print axioms openLayZero_ctx
#print axioms openAtt_own
#print axioms openLay_own
#print axioms openLayZero_own
#print axioms clearWith_own

end Meaning.K2
