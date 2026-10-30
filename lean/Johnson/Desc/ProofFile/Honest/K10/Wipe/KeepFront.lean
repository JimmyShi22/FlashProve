-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepFront.lean: the closing of a segment (K10): the four steps without a round
that stand around the code switch at the head's link and at the finish (headFrontQ, headOpenQ:
Johnson/Top/H0/Tw/K2C/Head.lean; finishFrontQ, finishBehindQ: K2C/Finish.lean) have like outcomes at two states that are
equal once wiped. One definition with code; the rest are theorems.

Words. The wiped state (wipeS, Honest/K10/WipeS.lean) is the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile out.pending, and the claim at the chain's end) keep theirs; the wipings of parts do the like
to a part. Two outcomes are alike (AlikeE, Wipe/Alike.lean) if both refuse with the same word, or both return and the
two values are equal once wiped.

  openTail         the last lines of headOpenQ, behind the walk's own lines, typed again as a function of what these
                   lines are handed; headOpenQ_wiped ties it to the library's text by unfolding alone, in one line of
                   its proof: no lemma of its own states the tie

What is proved.
  finishFront_wiped   the text in front of the finish's switch, at a wiped frame and at that frame unwiped, has like
                   outcomes
  headFrontQ_wiped, openTail_wiped, headOpenQ_wiped, finishFrontQ_wiped   each step at the wiped state is like the step
                   at the state
  finishBehindQ_comm   the step behind the finish's switch commutes with the wiping
  **front2**, **openQ2**   the fields front and openQ of SeatKeeps2 (Wipe/Lots2.lean) at wipeS
  **finFront2**, **finBehind2**   the fields finFront and finBehind of SeatRest2 (the same file) at wipeS

By what. The texts are followed arm by arm (Wipe/Alike.lean, Wipe/Carry.lean). What stands in front of and behind a
later link's switch is taken from Wipe/KeepK2.lean (swNewGroup_rel, swFirstFront_rel, swFirstBehind_rel); the walk's own
lines from Wipe/KeepFrames.lean (front_wipe); the state's functions from Wipe/WipeLaws.lean.

Limits. The laws speak of all states, reachable or not. The finish's two steps stand behind the last link. No property
of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepFrames
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK2
import Johnson.Top.H0.Tw.K2C.Head
import Johnson.Top.H0.Tw.K2C.Finish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement ReqFrame)
open OnBytes.Model (ChainCheck LinkCtx HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (HeadPar headFrontQ headOpenQ finishFrontQ finishBehindQ sizedOk)
open Johnson.Desc.First.Walk (firstKept emptySlots weightsAtZero)

/-! ## 1 The head's front -/

/-- **The step "H.0.front"** at the wiped state is like the step at the state. -/
theorem headFrontQ_wiped (tl : HTailF2) (s : S) : AlikeE wipeS (headFrontQ tl (wipeS s)) (headFrontQ tl s) := by
  unfold headFrontQ
  rw [atBetween_wipe, enterHead?_wipe]
  refine Carry.iteA (AlikeE.error _) ?_
  refine Carry.iteA (AlikeE.error _) ?_
  refine AlikeE.bind (swFirstFront_rel (wipeSt_idem s.st) s.check.frame) fun x x' hx => ?_
  have h1 : wipeSt x.st = wipeSt x'.st := (congrArg (fun q : Tw.K2.Front => q.st) hx :)
  have h2 : wipeFrame x.f = wipeFrame x'.f := (congrArg (fun q : Tw.K2.Front => q.f) hx :)
  cases s.enterHead? tl with
  | error e => exact AlikeE.error e
  | ok s₁ =>
    obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s₁
    cases here with
    | head a =>
      refine AlikeE.ok ?_
      show (⟨wipeSt x.st, book, roots, owed, failed, wipeCheck check, out,
          .head { a with fr := wipeFrame x.f, L := wipeCtx a.L }, req⟩ : S) =
        ⟨wipeSt x'.st, book, roots, owed, failed, wipeCheck check, out,
          .head { a with fr := wipeFrame x'.f, L := wipeCtx a.L }, req⟩
      rw [h1, h2]
    | between => exact AlikeE.error _
    | lay a => exact AlikeE.error _
    | att a => exact AlikeE.error _
    | fin a => exact AlikeE.error _
    | mem a => exact AlikeE.error _

/-- **The head's front** has like outcomes at two states that are equal once wiped. -/
theorem front2 (tl : HTailF2) : Fn2 wipeS (headFrontQ tl) := Fn2.of_wiped (headFrontQ_wiped tl)

/-! ## 2 The head's opening -/

/-- The last lines of the step "H.1.quiet". st, check: what stands behind the switch; L, out: what the walk's own lines
laid. -/
def openTail (P : HeadPar) (s : S) (st : Statement) (check : ChainCheck) (L : LinkCtx)
    (out : OnBytes.Proof.LinksResult) : Except String S :=
  match s.out.reply with
  | some y =>
    if !(y.c1 == 0 && y.c2 == 0 && Decidable.decide (y.c0.toNat < P.V)) then
        .error "Y1: header-y: the plain scalar is no entry of the vocabulary" else
    match ({ s with out := out } : S).covered P.T P.V with
    | .error e => .error ("C1: the covered positions cannot be made: " ++ e)
    | .ok cov =>
      if !sizedOk cov P.T then
          .error "C0: the covered positions' arrays have not the length T" else
      s.openHead?.bind fun s₁ =>
      match s₁.here with
      | .head b =>
        .ok { s₁ with
          st := st, check := check, out := out
          here := .head { b with
            L := L, F := emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } }
      | _ => .error "B2: the record stands at another sort of place than the block"
  | none => .error "Y0: no reply lies in the seat"

/-- These lines at the wiped state, handed values that are equal once wiped, are like the lines at the state. -/
theorem openTail_wiped (P : HeadPar) (s : S) {st st' : Statement} {ck ck' : ChainCheck} {L L' : LinkCtx}
    (h1 : wipeSt st = wipeSt st') (h2 : wipeCheck ck = wipeCheck ck') (h3 : wipeCtx L = wipeCtx L')
    (out : OnBytes.Proof.LinksResult) :
    AlikeE wipeS (openTail P (wipeS s) st ck L out) (openTail P s st' ck' L' out) := by
  have hcov : S.covered P.T P.V ({ wipeS s with out := out } : S) = S.covered P.T P.V ({ s with out := out } : S) :=
    covered_wipe P.T P.V { s with out := out }
  unfold openTail
  rw [hcov, out_wipe, openHead?_wipe]
  cases s.out.reply with
  | none => exact AlikeE.error _
  | some y =>
    refine Carry.iteA (AlikeE.error _) ?_
    cases S.covered P.T P.V ({ s with out := out } : S) with
    | error e => exact AlikeE.error _
    | ok cov =>
      refine Carry.iteA (AlikeE.error _) ?_
      cases s.openHead? with
      | error e => exact AlikeE.error e
      | ok s₁ =>
        obtain ⟨st0, book, roots, owed, failed, check, out0, here, req⟩ := s₁
        cases here with
        | head b =>
          refine AlikeE.ok ?_
          show (⟨wipeSt st, book, roots, owed, failed, wipeCheck ck, out,
              .head { b with fr := wipeFrame b.fr, L := wipeCtx L, F := _ }, req⟩ : S) =
            ⟨wipeSt st', book, roots, owed, failed, wipeCheck ck', out,
              .head { b with fr := wipeFrame b.fr, L := wipeCtx L', F := _ }, req⟩
          rw [h1, h2, h3]
        | between => exact AlikeE.error _
        | lay a => exact AlikeE.error _
        | att a => exact AlikeE.error _
        | fin a => exact AlikeE.error _
        | mem a => exact AlikeE.error _

/-- **The step "H.1.quiet"** at the wiped state is like the step at the state. -/
theorem headOpenQ_wiped (P : HeadPar) (s : S) : AlikeE wipeS (headOpenQ P (wipeS s)) (headOpenQ P s) := by
  obtain ⟨st0, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | head a =>
    refine Carry.iteA (AlikeE.error _) ?_
    refine Carry.iteA (AlikeE.error _) ?_
    refine AlikeE.bind (swFirstBehind_rel (wipeSt_idem st0) ?_ _ _) fun z z' hz => ?_
    · exact congrArg (fun T : Statement => (⟨T, wipeFrame a.fr, _, _, _, _⟩ : Tw.K2.Front)) (wipeSt_idem st0)
    · obtain ⟨st1, f1, mine⟩ := z
      obtain ⟨st1', f1', mine'⟩ := z'
      have k1 : wipeSt st1 = wipeSt st1' :=
        (congrArg (fun q : Statement × ReqFrame × Array Nat => q.1) hz :)
      have k2 : wipeFrame f1 = wipeFrame f1' :=
        (congrArg (fun q : Statement × ReqFrame × Array Nat => q.2.1) hz :)
      have k3 : mine = mine' := (congrArg (fun q : Statement × ReqFrame × Array Nat => q.2.2) hz :)
      subst k3
      have hk : wipeCheck (firstKept (wipeCheck check) f1 mine) = wipeCheck (firstKept check f1' mine) := by
        show ({ check with frame := wipeFrame f1, sent := mine, inLink := true, moments := 1 } : ChainCheck) =
          { check with frame := wipeFrame f1', sent := mine, inLink := true, moments := 1 }
        rw [k2]
      refine AlikeE.bind (Carry.relE (u := wipeCheck) (f := fun c => Johnson.Desc.First.Walk.front P.X P.l c out)
        (fun c => front_wipe P.X P.l c out) hk) fun y y' hy => ?_
      obtain ⟨L1, out1⟩ := y
      obtain ⟨L1', out1'⟩ := y'
      have m1 : wipeCtx L1 = wipeCtx L1' := (congrArg Prod.fst hy :)
      have m2 : out1 = out1' := (congrArg Prod.snd hy :)
      subst m2
      exact openTail_wiped P ⟨st0, book, roots, owed, failed, check, out, .head a, req⟩ k1 hk m1 out1
  | between => exact AlikeE.error _
  | lay a => exact AlikeE.error _
  | att a => exact AlikeE.error _
  | fin a => exact AlikeE.error _
  | mem a => exact AlikeE.error _

/-- **The head's opening** has like outcomes at two states that are equal once wiped. -/
theorem openQ2 (P : HeadPar) : Fn2 wipeS (headOpenQ P) := Fn2.of_wiped (headOpenQ_wiped P)

/-! ## 3 The finish's two -/

/-- **In front of the finish's switch**: like outcomes at a wiped frame and at that frame unwiped, and at statements
that are equal once wiped. -/
theorem finishFront_wiped {U U' : Statement} (hU : wipeSt U' = wipeSt U) (f : ReqFrame) :
    AlikeE wFront (Tw.K2.finishFront U' (wipeFrame f)) (Tw.K2.finishFront U f) := by
  have e : (wipeFrame f).groups[(wipeFrame f).link]? = f.groups[f.link]? := rfl
  unfold Tw.K2.finishFront
  rw [e]
  refine Carry.iteA (AlikeE.error _) ?_
  cases f.groups[f.link]? with
  | none => exact AlikeE.error _
  | some G =>
    rcases (swNewGroup_rel hU f.shape.code f.shape.maskCode).split with ⟨e0, h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
    · have h1' : Tw.K2.newGroupG U' (wipeFrame f).shape.code (wipeFrame f).shape.maskCode = .error e0 := h1
      rw [h1', h2]
      exact AlikeE.error e0
    · have h1' : Tw.K2.newGroupG U' (wipeFrame f).shape.code (wipeFrame f).shape.maskCode = .ok a := h1
      rw [h1', h2]
      obtain ⟨U1', g'⟩ := a
      obtain ⟨U1, g⟩ := a'
      have e1 : wipeSt U1' = wipeSt U1 := (congrArg (fun q : Statement × Nat => q.1) ha :)
      have e2 : g' = g := (congrArg (fun q : Statement × Nat => q.2) ha :)
      subst e2
      refine AlikeE.ok ?_
      exact congrArg (fun T : Statement => (⟨T, _, _, _, _, _⟩ : Tw.K2.Front)) e1

/-- The finish's front at the wiped state is like the step at the state. -/
theorem finishFrontQ_wiped (s : S) : AlikeE wipeS (finishFrontQ (wipeS s)) (finishFrontQ s) := by
  have e : (wipeS s).check.frame.groups[(wipeS s).check.frame.link]? =
      s.check.frame.groups[s.check.frame.link]? := rfl
  unfold finishFrontQ
  rw [atBetween_wipe, enterFin?_wipe, e]
  refine Carry.iteA (AlikeE.error _) ?_
  refine Carry.iteA (AlikeE.error _) ?_
  rcases (finishFront_wiped (wipeSt_idem s.st) s.check.frame).split with ⟨e0, h1, h2⟩ | ⟨x, x', h1, h2, hx⟩
  · have h1' : Tw.K2.finishFront (wipeS s).st (wipeS s).check.frame = .error e0 := h1
    rw [h1', h2]
    cases s.check.frame.groups[s.check.frame.link]? <;> exact AlikeE.error _
  · have h1' : Tw.K2.finishFront (wipeS s).st (wipeS s).check.frame = .ok x := h1
    rw [h1', h2]
    have k1 : wipeSt x.st = wipeSt x'.st := (congrArg (fun q : Tw.K2.Front => q.st) hx :)
    have k2 : wipeFrame x.f = wipeFrame x'.f := (congrArg (fun q : Tw.K2.Front => q.f) hx :)
    cases s.check.frame.groups[s.check.frame.link]? with
    | none => exact AlikeE.error _
    | some G =>
      cases s.enterFin? with
      | error e1 => exact AlikeE.error e1
      | ok s₁ =>
        obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s₁
        cases here with
        | fin a =>
          refine AlikeE.ok ?_
          show (⟨wipeSt x.st, book, roots, owed, failed, wipeCheck check, out,
              .fin { a with G := some G, fr := wipeFrame x.f, row := { a.row with target := OnBytes.zeroE } },
              req⟩ : S) =
            ⟨wipeSt x'.st, book, roots, owed, failed, wipeCheck check, out,
              .fin { a with G := some G, fr := wipeFrame x'.f, row := { a.row with target := OnBytes.zeroE } },
              req⟩
          rw [k1, k2]
        | between => exact AlikeE.error _
        | lay a => exact AlikeE.error _
        | att a => exact AlikeE.error _
        | head a => exact AlikeE.error _
        | mem a => exact AlikeE.error _

/-- **The finish's front** has like outcomes at two states that are equal once wiped. -/
theorem finFront2 : Fn2 wipeS finishFrontQ := Fn2.of_wiped finishFrontQ_wiped

/-- The step behind the finish's switch commutes with the wiping. -/
theorem finishBehindQ_comm (s : S) : finishBehindQ (wipeS s) = (finishBehindQ s).map wipeS := by
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | fin a =>
    show Except.map _ (Tw.K2.finishBehind a.sw) = Except.map wipeS (Except.map _ (Tw.K2.finishBehind a.sw))
    cases Tw.K2.finishBehind a.sw <;> rfl
  | between => rfl
  | lay a => rfl
  | att a => rfl
  | head a => rfl
  | mem a => rfl

/-- **The step behind the finish's switch** has like outcomes at two states that are equal once wiped. -/
theorem finBehind2 : Fn2 wipeS finishBehindQ := Fn2.of_comm finishBehindQ_comm

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.headFrontQ_wiped
#print axioms ProofFile.Honest.K10.front2
#print axioms ProofFile.Honest.K10.openTail
#print axioms ProofFile.Honest.K10.openTail_wiped
#print axioms ProofFile.Honest.K10.headOpenQ_wiped
#print axioms ProofFile.Honest.K10.openQ2
#print axioms ProofFile.Honest.K10.finishFront_wiped
#print axioms ProofFile.Honest.K10.finishFrontQ_wiped
#print axioms ProofFile.Honest.K10.finFront2
#print axioms ProofFile.Honest.K10.finishBehindQ_comm
#print axioms ProofFile.Honest.K10.finBehind2
