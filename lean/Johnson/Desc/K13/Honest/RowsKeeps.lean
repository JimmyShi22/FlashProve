-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/RowsKeeps.lean: kind K13's sub-protocol behind W's commitment (`rowsB` at
the lens `atS`: Johnson/Desc/K13/Kind.lean, AtS.lean): THE SECOND HALF OF THE SUB-PROTOCOL AT THE
PLACE "M:4": WHAT ITS STEP DOES TO THE FIRST CHAIN's STATE, AS ONE SENTENCE; THAT EVERY ACCEPTING
STEP OF ITS OWN GIVES THAT SENTENCE; AND THAT ITS STEP ACCEPTS UNDER TESTS ON THE STATE's SHAPE. Two
definitions, and statements with their proofs.

What it is for. The frame for the honest side carries, for each sub-protocol of a chain, a sentence
on the states in front of and behind an accepting step (the field `keeps` of a thread's parameters:
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean): it is all that others have of that step when a fact
of theirs must pass it. The sub-protocol at "M:4" is two in a row (`atM4`, AtS.lean): W's
commitment, which is kind K1's, then `rowsB`, which has no round, no oracle message and reads no
column. This file gives the second one's sentence: from the state t behind W's commitment to the
state s' behind both.
NOTHING HERE IS NEW BUT THE FORM, AND THE LEDGERS WHOLE. It is put together of the library's laws on
`rowsB` and on its text `rows`, which are called: `rowsB_ok`, `get_mem`
(Johnson/Desc/K13/Law/M4Proof.lean), `rows_same` (Law/PinDec.lean), `rows_ledStay`
(Law/LedgersAtW.lean), `addRows_one` (Law/M4.lean), `map_modify_same` (OnBytes/Model/HideLaws.lean),
`stepYes_decide` (Johnson/Top/H0/Walk/ReachInv.lean), `step_ok_iff`
(Johnson/Desc/Sound/RunIsDecide.lean); and of this folder's `rows_ownLaid`, `joinP_inv`,
`newGroupP_inv` (OwnLaid.lean), `rowsB_returns_shape` (ShapeM4Ready.lean).
Kin in the library: `rowsB_at` (Law/AtM4.lean: the same equation with the field `rowsOwed` under
"there is"), `rowsB_owed`, `atM4_rec` (Law/AtRecord.lean), `rowsB_rows`, `rowsB_core`, `rowsB_keeps`
(Johnson/Desc/K13/Keeps.lean, KeepsCore.lean), `rowsB_same`, `rowsB_sameRows`, `rowsB_ledStay`,
`rowsB_fr` (Johnson/IMR/RowsSent.lean), `rowsB_mask`, `atM4_mark`
(Johnson/Desc/AtSeats/Unmarked.lean). On the same three moves of the ground, of a message's shape,
mark and groups and not of its ledger: `grows_withGroup`, `grows_joined`, `grows_withRow`
(Johnson/Desc/Grows.lean), `joinP_grows`, `newGroupP_grows`, `addRowsP_grows` (GrowsGround.lean).
Main names:
  `K13RowsKeeps P t s'`: **the sentence: AN EQUATION ON THE WHOLE STATE**: t stands at the chain's
    end with a claim laid; the text `rows` returns there; s' is t with three fields written: `st`:
    what `rows` returns; `rowsOwed`: none where no count waits at t, else as it was; `here`: what
    `rows` lays beside the claim (what W's message holds and the numbers handed on stay). So t fixes
    s'.
  `rowsB_rowsKeeps`, `rowsB_rowsKeeps_of_yes`: **every return of the decision gives it; so does
    EVERY ACCEPTING STEP OF THE SUB-PROTOCOL's OWN** (`StepYes`, Johnson/Top/H0/Walk/Reach.lean).
    Nothing is asked of the state in front.
  What the sentence gives: `K13RowsKeeps.fields`: the six fields `failed`, `book`, `roots`, `check`,
    `out`, `req` are as they were: so the reply, the pile and the number of the index masks' message
    stay · `.noMark`: failed = none behind just if in front · `.owed`: where no count was owed in
    front, none is behind · `.same`: the codes, and of each oracle message the shape, the mark
    "sampled", the sample rows and the pad (`SameAll`) · `.led` (`LedStay`) · `.ledgers`: **every
    oracle message's ledger is as it was, whole: "closed" too** (`ledgersOf`; `join_ledgers`,
    `joinAll_ledgers`, `rows_ledgers`) · `.groups`: there is one group more, and every group that
    was there is as it was · `.joins`: **who joins the new group** (`OwnLaid`, `ownMember`): W, the
    messages of the claim's masks, and the split's message where the shape asks for one; each of
    these gets the group's number behind its list; every other message is as it was · `.maskJoins`:
    so EACH MESSAGE THAT A MASK OF THE CLAIM NAMES GAINS A GROUP.
  `rowsB_yes_of_ready`: **its own step, the one with no round and no column, accepts wherever the
    state in front passes `ready4` and `pads4`** (tests on the state's shape: ShapeM4Ready.lean),
    and the shape behind is the update.

MIND. The claim that the batching lays has masks in the index masks' message. So behind this
sub-protocol THAT MESSAGE IS IN A GROUP: a sentence "no group holds the index masks' message" (the
library's `P1L20.outOfGroupsB`) does not pass it.
What is not claimed. What W's commitment does. That the state behind W's commitment passes the two
tests at any run. How the two halves are joined; the two guards around them. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.K13.Honest.OwnLaid
import Johnson.Desc.K13.Honest.ShapeM4Ready
import Johnson.Desc.K13.Law.PinDec
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K13.Law.LedgersAtW
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Desc.Sound.RunIsDecide
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open OnBytes.Params (LinShape)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

variable {Cl : Type}

/-! ## The ledgers -/

/-- The oracle messages' ledgers, in the messages' order. -/
def ledgersOf (St : Statement) : Array (Option Ledger) := St.oracles.map (·.ledger)

/-- One joining that returns leaves the ledgers. -/
theorem join_ledgers {d d' : St} {g o : ℕ} {k : Bool} (h : Ground.joinP d g o k = some d') :
    ledgersOf d'.st = ledgersOf d.st := by
  obtain ⟨G, _, _, e⟩ := joinP_inv h
  rw [e]
  exact OnBytes.Model.map_modify_same (·.ledger) (fun x => { x with groups := x.groups ++ [g] })
    (fun _ => rfl) d.st.oracles o

/-- Joinings in a row that return leave them. -/
theorem joinAll_ledgers {g : ℕ} : ∀ (l : List ℕ) (d d' : St), K13.joinAll g l d = .ok d' →
    ledgersOf d'.st = ledgersOf d.st
  | [], d, d', hj => by
    obtain rfl : d = d' := Except.ok.inj hj
    rfl
  | o :: l, d, d', hj => by
    simp only [K13.joinAll, Law.bind_ok, Law.there_ok] at hj
    obtain ⟨d₁, h1, h2⟩ := hj
    rw [joinAll_ledgers l d₁ d' h2, join_ledgers h1]

/-- **The text behind W's commitment leaves every ledger as it was.** -/
theorem rows_ledgers {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (h : rows Sh claim ids d = .ok o) : ledgersOf o.2.st = ledgersOf d.st := by
  simp only [rows_is, Law.bind_ok, Law.there_ok, Law.pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨_, e2⟩ := newGroupP_inv hb
  obtain ⟨_, _, _, e4⟩ := addRows_one h4
  have s0 : ledgersOf b.2.st = ledgersOf d.st := by
    rw [e2]
    rfl
  have s3 : ledgersOf d₃.st = ledgersOf d₂.st := by
    split at h3
    · exact join_ledgers h3
    · rw [Option.some.inj h3]
  show ledgersOf d₄.st = _
  rw [e4]
  show ledgersOf d₃.st = _
  rw [s3, join_ledgers h2, joinAll_ledgers _ _ _ h1, s0]

/-! ## The sentence -/

/-- **THE SENTENCE: an equation on the whole state.** t: the state behind W's commitment. s': the
state behind `rowsB`. -/
def K13RowsKeeps (P : Where) (t s' : S) : Prop :=
  ∃ (m₀ : First.MemOwn) (l : LinFirst) (o : LinFirst × St),
    t.here = .mem m₀ ∧ m₀.lin = some l ∧ rows P.lin l.claim m₀.ids (dOf t) = .ok o ∧
    s' = { t with st := o.2.st, rowsOwed := if t.noneWaits then none else t.rowsOwed,
                  here := .mem ⟨m₀.msg, m₀.ids, some o.1⟩ }

/-- Every return of the decision gives it. -/
theorem rowsB_rowsKeeps {P : Where} {t s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) atS P).decide t rs gs = .ok s') : K13RowsKeeps P t s' := by
  obtain ⟨p, l, o, hp, hl, hrows, hb1⟩ := rowsB_ok atS P h
  obtain ⟨m₀, hs, h1, h2, h3⟩ := get_mem hp
  have hp' := hp
  simp only [atS, hs] at hp'
  have hmsg : p.msg = m₀.msg := by rw [← Option.some.inj hp']
  have howed : p.owed = if t.noneWaits then none else t.rowsOwed := by
    rw [← Option.some.inj hp']
  refine ⟨m₀, l, o, hs, by rw [← h1, hl], by rw [← h2, ← h3]; exact hrows, ?_⟩
  rw [hb1]
  simp only [atS, hs, hmsg, h2, howed]

/-- **SO DOES EVERY ACCEPTING STEP OF THE SUB-PROTOCOL's OWN.** -/
theorem rowsB_rowsKeeps_of_yes {P : Where} {ft : ℕ} {t s' : S}
    (h : StepYes ft (rowsB (Cl := Cl) atS P) t s') : K13RowsKeeps P t s' := by
  obtain ⟨rs, gs, hd⟩ := stepYes_decide h
  exact rowsB_rowsKeeps hd

/-- Six fields are as they were. -/
theorem K13RowsKeeps.fields {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    s'.failed = t.failed ∧ s'.book = t.book ∧ s'.roots = t.roots ∧ s'.check = t.check ∧
      s'.out = t.out ∧ s'.req = t.req := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- failed = none behind just if in front. -/
theorem K13RowsKeeps.noMark {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    s'.failed = none ↔ t.failed = none := by
  rw [h.fields.1]

/-- Where no count was owed in front, none is behind. -/
theorem K13RowsKeeps.owed {P : Where} {t s' : S} (h : K13RowsKeeps P t s')
    (h0 : t.rowsOwed = none) : s'.rowsOwed = none := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := h
  show (if t.noneWaits then none else t.rowsOwed) = none
  rw [h0]
  split <;> rfl

/-- The codes, and of each oracle message the shape, the mark, the sample rows and the pad. -/
theorem K13RowsKeeps.same {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    SameAll t.st s'.st := by
  obtain ⟨_, _, _, _, _, hr, rfl⟩ := h
  exact Law.rows_same hr

/-- Of each oracle message the shape and the ledger's four numbers. -/
theorem K13RowsKeeps.led {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    LedStay t.st s'.st := by
  obtain ⟨_, _, _, _, _, hr, rfl⟩ := h
  exact rows_ledStay _ _ _ _ _ hr

/-- **Every oracle message's ledger is as it was, whole.** -/
theorem K13RowsKeeps.ledgers {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    ledgersOf s'.st = ledgersOf t.st := by
  obtain ⟨_, _, _, _, _, hr, rfl⟩ := h
  exact rows_ledgers hr

/-- **Who joins the new group.** -/
theorem K13RowsKeeps.joins {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    ∃ (m₀ : First.MemOwn) (l l' : LinFirst), t.here = .mem m₀ ∧ m₀.lin = some l ∧
      s'.here = .mem ⟨m₀.msg, m₀.ids, some l'⟩ ∧
      OwnLaid t.st s'.st l'.own (ownMember P.lin l.claim l') := by
  obtain ⟨m₀, l, o, h1, h2, hr, rfl⟩ := h
  exact ⟨m₀, l, o.1, h1, h2, rfl, rows_ownLaid hr⟩

/-- One group more; every group that was there is as it was. -/
theorem K13RowsKeeps.groups {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    s'.st.groups.size = t.st.groups.size + 1 ∧
      ∀ g < t.st.groups.size, s'.st.groups[g]? = t.st.groups[g]? := by
  obtain ⟨_, _, _, _, _, _, hO⟩ := h.joins
  exact ⟨by rw [hO.size, hO.num], fun g hg => hO.elder g (by rw [hO.num]; exact hg)⟩

/-- **Each message that a mask of the claim names gains a group.** -/
theorem K13RowsKeeps.maskJoins {P : Where} {t s' : S} (h : K13RowsKeeps P t s') :
    ∃ (m₀ : First.MemOwn) (l : LinFirst), t.here = .mem m₀ ∧ m₀.lin = some l ∧
      ∀ u ∈ l.claim.masks.toList, ∀ x, t.st.oracles[u.oracle]? = some x →
        ∃ x', s'.st.oracles[u.oracle]? = some x' ∧
          x'.groups = x.groups ++ [t.st.groups.size] := by
  obtain ⟨m₀, l, l', h1, h2, _, hO⟩ := h.joins
  refine ⟨m₀, l, h1, h2, fun u hu x hx => ?_⟩
  obtain ⟨x', e1, _, e2⟩ := hO.inn u.oracle x hx (Or.inr (Or.inl (List.mem_map_of_mem hu)))
  exact ⟨x', e1, by rw [e2, hO.num]⟩

/-- **ITS OWN STEP ACCEPTS WHEREVER THE STATE IN FRONT PASSES THE TESTS ON ITS SHAPE**: the step
with no round and no column; and the shape behind is the update. -/
theorem rowsB_yes_of_ready {P : Where} {t : S} (h : ready4 P.lin (sh4 t) = true)
    (hp : pads4 P.lin (sh4 t) = true) (ft : ℕ) :
    ∃ s', StepYes ft (rowsB (Cl := Cl) atS P) t s' ∧ sh4 s' = step4 P.lin (sh4 t) := by
  obtain ⟨s', hd, hs⟩ := rowsB_returns_shape (Cl := Cl) h hp [] []
  refine ⟨s', ⟨[], [], rfl, ?_⟩, hs⟩
  exact (VerifiableInference.Desc.Sound.step_ok_iff ft _ t s' [] [] 0).2 ⟨rfl, rfl, rfl, hd⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.join_ledgers
#print axioms VerifiableInference.Desc.K13.Honest.joinAll_ledgers
#print axioms VerifiableInference.Desc.K13.Honest.rows_ledgers
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_rowsKeeps
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_rowsKeeps_of_yes
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.fields
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.noMark
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.owed
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.same
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.led
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.ledgers
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.joins
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.groups
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.maskJoins
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_yes_of_ready
