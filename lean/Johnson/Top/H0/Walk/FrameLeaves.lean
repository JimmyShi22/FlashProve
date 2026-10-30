-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Walk/FrameLeaves.lean: the link's frame leaves the reply that was heard, in the form
of Johnson/Desc/Sound/FoldHeard.lean (Block.Leaves; LeavesLink's two premises on L.lay and
L.clear), at the reading S.heard (Johnson/Desc/First/StateHeard.lean).

  heard_of_link, heard_of_between   where a link is open (the head's: opened), and between two
                  links, S.heard is the reply in the walk's result
  lay_leaves, clear_leaves   in the very form of LeavesLink's premises: ∀ s s', L.lay s = .ok s' →
                  heard s' = heard s; the like for L.clear: at every link, the head's among them
                  (clearWith at any counts, any "left", any row's function)
  laidBlock_leaves, clearedBlock_leaves   the two as blocks without a round, by leavesQuiet
  openedAtt_leaves, openedLay_leaves, openedZero_leaves   "opened" as a block: Block.Leaves heard,
                  at every kind of record (front hands the walk's result on as it is)
  tailHead_leaves, tailHeadBlock_leaves, tailHead_messages, tailHead_carries   the tie to
                  Johnson/Desc/First/Close/TailHead.lean: its tailHead (the head's link's end) is
                  clearWith at its own counts and at the row's function pendingRowO: so the
                  frame's lemmas on "cleared" apply to it as it lies

Limits.
The frame's links, all but the head's, stand in front of the reply's block, and FoldLays asks
nothing of the blocks in front: so for the proof file's law these are wanted at the head's link's
lay and clear alone; they hold at all.
A block that refuses all has Leaves emptily: it is an implication from a yes. No soundness
statement.

-/
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.First.Close.TailHead
import Johnson.Desc.First.StateHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First (S)

/-- What was heard: S.heard, by name. -/
abbrev heard (s : S) : Option E := s.heard

/-- Where a link is open (the head's: opened), and between two links, what was heard is the reply in
  the walk's result. -/
theorem heard_of_link {s : S} {C : LinkCtx} (h : s.link? = some C) : s.heard = s.out.reply := by
  unfold S.link? at h
  unfold S.heard
  cases hh : s.here <;> simp_all

theorem heard_of_between {s : S} (h : s.atBetween = true) : s.heard = s.out.reply := by
  unfold S.atBetween at h
  unfold S.heard
  cases hh : s.here <;> simp_all

theorem lay_leaves (l : Nat) : ∀ s s', layFront l s = .ok s' → heard s' = heard s :=
  fun _ _ h => by rw [(layFront_ok h).1]

theorem clear_leaves (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
    (row : RowFn) :
    ∀ s s', clearWith X counts left row s = .ok s' → heard s' = heard s := by
  intro s s' h
  obtain ⟨C, F, hC, _, _, _, _, _, hb, _⟩ := clearWith_ok h
  show s'.heard = s.heard
  rw [heard_of_link hC, heard_of_between hb, clearWith_leaves h]

theorem laidBlock_leaves {Cl : Type} (name : String) (l : Nat) :
    (roundlessBlock (Cl := Cl) name 1 (some l) 0 (layFront l)).Leaves heard :=
  VerifiableInference.Desc.leavesQuiet S Cl _ heard name 1 (some l) 0 (layFront l) (lay_leaves l)

theorem clearedBlock_leaves {Cl : Type} (name : String) (l piece : Nat) (X : LinkPub) (counts : S →
    Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) :
    (roundlessBlock (Cl := Cl) name 1 (some l) piece (clearWith X counts left row)).Leaves heard :=
  VerifiableInference.Desc.leavesQuiet S Cl _ heard name 1 (some l) piece _ (clear_leaves X counts
      left row)

theorem openedAtt_leaves {Cl : Type} (name : String) (l piece : Nat) (plan : Bool) (P : AttPar) :
    (openedBlock (Cl := Cl) name l piece plan (openAtt P)).Leaves heard :=
  fun s _ _ s' h => by
    have ok := openAtt_ok h
    show s'.heard = s.heard
    rw [heard_of_link ok.2.2.2.2.1, heard_of_between ok.1, openAtt_leaves h]

theorem openedLay_leaves {Cl : Type} (name : String) (l piece : Nat) (plan : Bool) (P : LayPar) :
    (openedBlock (Cl := Cl) name l piece plan (openLay P)).Leaves heard :=
  fun s _ _ s' h => by
    have ok := openLay_ok h
    show s'.heard = s.heard
    rw [heard_of_link ok.2.2.2.2.2.1, heard_of_between ok.1, openLay_leaves h]

theorem openedZero_leaves {Cl : Type} (name : String) (piece : Nat) (plan : Bool) (P : LayPar) (fvs
    : List Bool) (kCol : Nat) :
    (openedBlock (Cl := Cl) name 0 piece plan (openLayZero P fvs kCol)).Leaves heard :=
  fun s _ _ s' h => by
    have ok := openLayZero_ok h
    show s'.heard = s.heard
    rw [heard_of_link ok.2.2.2.2.2.1, heard_of_between ok.1, openLayZero_leaves h]

/-- THE TIE TO THE TEXT FOR THE HEAD's LINK's END (Johnson/Desc/First/Close/TailHead.lean): its
  tailHead IS clearWith at its own counts: so it leaves the reply. -/
theorem tailHead_leaves (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) :
    ∀ s s', VerifiableInference.Desc.First.Close.tailHead X lay lin s = .ok s' → heard s' = heard s
        :=
  clear_leaves X _ _ _

theorem tailHeadBlock_leaves {Cl : Type} (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (l
    piece : Nat) :
    (VerifiableInference.Desc.First.Close.tailHeadBlock (Cl := Cl) X lay lin l piece).Leaves heard
        :=
  fun s _ _ s' h => tailHead_leaves X lay lin s s' h

/-- The head's row's function is the very function at which clear_messages and clear_row are stated:
  both apply to tailHead as it lies. -/
theorem tailHead_messages {X : LinkPub} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : VerifiableInference.Desc.First.Close.tailHead X lay lin s = .ok t) :
    t.st.oracles.size = s.st.oracles.size ∧
      ∀ i : Nat, (t.st.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
        (s.st.oracles[i]?).map fun (x : Oracle) => { x with ledger := none } :=
  clear_messages h

theorem tailHead_carries {X : LinkPub} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : VerifiableInference.Desc.First.Close.tailHead X lay lin s = .ok t) :
    t.check = s.live ∧ t.st.codes = s.st.codes ∧ t.st.groups = s.st.groups ∧ t.atBetween = true :=
  (clear_carries h).2.2.2.2.2.2

example {X : LinkPub} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : VerifiableInference.Desc.First.Close.tailHead X lay lin s = .ok t) (hv : X.fv = true) :=
        clear_row h hv

#print axioms tailHead_messages
#print axioms tailHead_carries
#print axioms heard_of_link
#print axioms heard_of_between
#print axioms tailHead_leaves
#print axioms tailHeadBlock_leaves
#print axioms openedZero_leaves
#print axioms lay_leaves
#print axioms clear_leaves
#print axioms laidBlock_leaves
#print axioms clearedBlock_leaves
#print axioms openedAtt_leaves
#print axioms openedLay_leaves

end Johnson.Desc.First.Walk.Law
