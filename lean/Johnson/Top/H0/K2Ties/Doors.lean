-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Doors.lean: THE QUIET STEPS THAT STAND AROUND THE CODE SWITCH's DECISION IN A
WRITTEN
DESCRIPTION LEAVE WHAT THE OPEN CLAIMS READ, AND SO DOES THE SEATED SUB-PROTOCOL. Nine theorems. A
law
file: no sub-protocol imports it.

Why. In a written description the code switch's decision does not stand bare: at the finish a quiet
step stands in front of it and one behind; at the output head and at a segment's first place one
behind; all under guards. `Left` (Left.lean) is shown of the decision; it passes such a door if each
quiet step has it.

What is said.
  `left_of_book`: a step that leaves the mark, `out`, `req` and the book, under which the statement
  only
    grows and keeps its sample rows, and that begins and ends outside the members' places.
  `left_finishFront`, `left_finishBehind`, `left_headOpen`: the three quiet steps of the kind's own
  text
    (`finishFrontQ`, `finishBehindQ`, `headOpenQ`: Johnson/Top/H0/Tw/K2C/).
  `left_opened`: the frame's step "opened" behind a segment's first place, from what its own authors
    show of it (`OpenedLeaves`, Johnson/Top/H0/Walk/FrameGives.lean) with `out` the same.
  `left_bind`: a guard behind a step that hands on the state that it was handed.
  `left_of_seat`: THE SEATED SUB-PROTOCOL: where B sits on the kind's sub-protocol behind a door
    (`SeatStep`, Johnson/Top/H0/K2Caller/SeatedAt.lean) whose way in and way out have `Left`: an
    accept
    of the piece at B has it: the field left of `K2Owes` (T5.lean) at `seatedAt`.

Limits. That a written description's list holds such a B, and which door, is said elsewhere (the row
K02_sits). For "opened": that the state stands outside the members' places in front and behind is a
premise here. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Ties.Left
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Top.H0.Tw.K2C.SendsOn
import Johnson.Top.H0.Walk.FrameGives
import Johnson.Top.H0.K2Caller.SeatedAt
import Johnson.Desc.Sound.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes OnBytes.Model OnBytes.Maker
open _root_.Tw.K2 (sendByL8)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece below piece_below_yes)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 HeadPar finishFrontQ finishBehindQ headOpenQ)
open VerifiableInference.Desc.First.K2Caller (SeatStep seatedAt seated_out)
open VerifiableInference.Desc.Ground (groundKeeps_grows)

/-- A step that leaves the mark, `out`, `req` and the book; the statement only grows. -/
theorem left_of_book {s s' : S} (h1 : s'.failed = s.failed) (h2 : s'.out = s.out)
    (h3 : s'.req = s.req) (hg : Desc.Grows s.st s'.st) (hs : Desc.K1.SmpStay s.st s'.st)
    (h5 : s'.book = s.book) (h6 : ∀ a, s.here ≠ .mem a) (h7 : ∀ a, s'.here ≠ .mem a) :
    Left s s' := by
  refine ⟨h1, h2, h3, ?_, hg, hs, ?_, ?_⟩
  · rw [rows_off h6, rows_off h7, h2]
  · intro j q e
    rw [h5]
    exact e
  · intro j t e
    rw [h5]
    exact ⟨t, e, rfl⟩

/-- The quiet step in front of the last switch. -/
theorem left_finishFront {s t : S} (h : finishFrontQ s = .ok t) : Left s t := by
  obtain ⟨hb, _, _, hf, _, ho, hr⟩ := K2.finishFrontQ_rest h
  obtain ⟨G, x, s₁, a, k⟩ := (K2.finishFrontQ_iff s t).1 h
  obtain ⟨a', _, e', _⟩ := K2.finishFrontQ_fr h
  have hbw : s.here = .between := by
    have := k.between
    unfold S.atBetween at this
    split at this
    · assumption
    · cases this
  exact left_of_book hf ho hr (K2.finishFrontQ_keeps groundKeeps_grows h)
    (K2.finishFrontQ_keeps Desc.K1.groundKeeps_smpStay h) hb
    (fun c e => by cases hbw.symm.trans e) (fun c e => by cases e'.symm.trans e)

/-- The quiet step behind the last switch. -/
theorem left_finishBehind {s t : S} (h : finishBehindQ s = .ok t) : Left s t := by
  obtain ⟨a, m, e, _, rfl⟩ := (K2.finishBehindQ_iff s t).1 h
  exact left_of_same rfl rfl rfl rfl rfl (fun c e' => by cases e.symm.trans e')
    (fun c e' => by cases e')

theorem mark_req (s : S) (n : String) : (s.mark n).req = s.req := by
  unfold S.mark
  split <;> rfl

theorem openHead_req (s : S) : s.openHead.req = s.req := by
  unfold S.openHead
  split
  · split
    · exact mark_req s _
    · rfl
  · exact mark_req s _

/-- The quiet step behind the output head's switch. -/
theorem left_headOpen {P : HeadPar} {s t : S} (h : headOpenQ P s = .ok t) : Left s t := by
  obtain ⟨⟨a, e, _⟩, ⟨b, e', _⟩, hf⟩ := K2.headOpenOpens P s t h
  obtain ⟨_, _, _, _, _, _, _, ho⟩ := K2.headOpenLays P s t h
  have hr : t.req = s.req := by
    obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (K2.headOpenQ_iff P s t).1 h
    rw [k.out', ← openHead_req s, ← K2.openHeadQ k.opens]
  exact left_of_book hf ho hr (K2.headOpenQ_keeps groundKeeps_grows h)
    (K2.headOpenQ_keeps Desc.K1.groundKeeps_smpStay h) (K2.headOpenQ_book h).1
    (fun c x => by cases e.symm.trans x) (fun c x => by cases e'.symm.trans x)

/-- The frame's step "opened" behind a segment's first place. -/
theorem left_opened {s t : S} (h : Johnson.Desc.First.Walk.Tied.OpenedLeaves s t)
    (ho : t.out = s.out) (h6 : ∀ a, s.here ≠ .mem a) (h7 : ∀ a, t.here ≠ .mem a) : Left s t :=
  left_of_same h.2.2.2.2.2.2.1 ho h.2.2.2.2.2.2.2 h.2.2.1 h.2.2.2.1 h6 h7

/-- A guard behind a step: it hands on the state that it was handed. -/
theorem left_bind {s u : S} {f : Except String S} {g : S → Except String S}
    (hg : ∀ x y, g x = .ok y → y = x) (hf : ∀ x, f = .ok x → Left s x) (h : f.bind g = .ok u) :
    Left s u := by
  cases f with
  | error e => cases h
  | ok x =>
    have e : u = x := hg x u h
    rw [e]
    exact hf x rfl

/-- **An accept of the seated sub-protocol leaves what the open claims read.** -/
theorem left_of_seat {F : Frame} {Cl Cl' W W' : Type} (q : Piece (ckP .two) F S Cl' W) (p : P2)
    (hq : q.b = below (K2.codeSwitchKind p)) (hback : q.back = []) (B : Block S Cl)
    (enter : S → Except String S) (leave : S → S → Except String S)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl') p).rounds)
    (h : SeatStep B (K2.codeSwitchKind (Cl := Cl') p) enter leave)
    (hin : ∀ s t, enter s = .ok t → Left s t) (hout : ∀ s t s', leave s t = .ok s' → Left t s')
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) q.ds) → W' → W') :
    ∀ a τ b, (seatedAt q B ext).ior.red.out a τ = some b → Left a.1 b.1 := by
  intro a τ b ho
  obtain ⟨t, t', e1, e2, e3⟩ := seated_out q _ hq hback B enter leave hr h ext a b τ ho
  obtain ⟨_, _, hd, _⟩ := piece_below_yes q (K2.codeSwitchKind p) hq (t, a.2) (t', b.2) τ e2
  exact (hin _ _ e1).trans ((left_of_yes hd).trans (hout _ _ _ e3))

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.left_finishFront
#print axioms VerifiableInference.Desc.First.K2Ties.left_finishBehind
#print axioms VerifiableInference.Desc.First.K2Ties.left_headOpen
#print axioms VerifiableInference.Desc.First.K2Ties.left_opened
#print axioms VerifiableInference.Desc.First.K2Ties.left_bind
#print axioms VerifiableInference.Desc.First.K2Ties.left_of_seat
