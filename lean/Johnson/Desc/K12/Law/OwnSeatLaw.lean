-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnSeatLaw.lean: where the first fold of the proximity test (the kind K12)
sends its own mask, the first written round behind "BAT" sends a tree as deep and as wide as the
mask's tree in the book.

So the premises DeepK.fresh and DeepK.wide (Johnson/Desc/K12/Law/K12Lemma.lean), at the letter that
takes that round with the message's oracle, follow from tests that can be run. Statements and
proofs, over Johnson/Desc/K12/Law/OwnSeat.lean, Johnson/Desc/K12/Law/OwnTieLaw.lean,
Johnson/Desc/K12/Law/FirstCutLaw.lean and Johnson/Desc/K12/Law/ViewWide.lean.
Main names:
  `last_of_ok`: lastOk's yes, where the record names no mask, gives that the last of D.ts is
    D.fresh.t.
  `getLast_map`: the last of a mapped list.
  `own_deep`: under ownTieOk, the yes of gpL at D (its clauses opens.a and opens.W) and "the last of
    D.ts is D.fresh.t", the first written round dE behind "BAT" has PQ.posN dE.rd.tree = 2 ^
    D.fresh.tsh.logN and PQ.colW dE.rd.tree = widthAt D.book D.fresh.t.
Limits: No soundness is claimed, and nothing is said on hiding.
It takes p.nums.ownMask = true (the plan) and t.mask = none (the record) as two premises: that the
two go together is the clause own of outOk
(Johnson/Desc/K12/Law/OutOk.lean [not in this library]), which is proved nowhere.
That the own mask's tree stands last is taken from the test, not proved from the text of
Ground.recvP.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.OwnSeat
import Johnson.Desc.K12.Law.OwnTieLaw
import Johnson.Desc.K12.Law.ViewWide

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.Pub (WR writtenOf)

theorem last_of_ok (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (hs : p.nums.stages = a :: rest)
    (hp : t.pass = .claim row L) (hD : gpOf p t a L = some D) (hm : t.mask = none)
    (h : lastOk p t = true) : D.ts.getLast? = some D.fresh.t := by
  unfold lastOk lastL at h
  rw [hs, hp] at h
  dsimp only at h
  rw [hD] at h
  dsimp only at h
  unfold lastOn ok at h
  rw [hm] at h
  simp only [Option.isNone_none, if_true, List.all_cons, List.all_nil, Bool.and_true,
    Bool.true_and, beq_iff_eq] at h
  exact h

theorem getLast_map {α β : Type} (f : α → β) (l : List α) :
    (l.map f).getLast? = l.getLast?.map f := by
  simp

/-- The first written round behind "BAT" against the mask's tree in the book. -/
theorem own_deep (p : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (hs : p.nums.stages = a :: rest)
    (ho : p.nums.ownMask = true) (hD : gpOf p t a L = some D)
    (hok : ok (gpL p a row D) = true) (hl : D.ts.getLast? = some D.fresh.t)
    (hT : ownTieOk p = true) :
    ∃ dE : WR, (writtenB p)[0]? = some dE ∧ PQ.posN dE.rd.tree = 2 ^ D.fresh.tsh.logN ∧
      PQ.colW dE.rd.tree = widthAt D.book D.fresh.t := by
  obtain ⟨dE, o, e1, e2, e3, _⟩ := ownTie_of_ok p a rest hs ho hT
  have hm := made_of p t a L D hD
  rw [← hm.opens] at e2
  have ha := congrArg List.getLast? (opens_a_of_ok p a row D hok)
  have hW := congrArg List.getLast? (opens_W_of_ok p a row D hok)
  rw [getLast_map, getLast_map, e2, hl] at ha hW
  have ha' : o.1.a = logAt D.book D.fresh.t := Option.some.inj ha
  have hW' : o.1.W = widthAt D.book D.fresh.t := Option.some.inj hW
  refine ⟨dE, e1, ?_, ?_⟩
  · show PQ.posN dE.tree = _
    rw [e3, ← (keyAt_of (F := 0) hm.fresh).2, ← ha']
    rfl
  · show PQ.colW dE.tree = _
    rw [e3, ← hW']
    rfl

end H2K.First

#print axioms H2K.First.last_of_ok
#print axioms H2K.First.own_deep
