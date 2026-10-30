-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/RoomAcross.lean: across an accept of the proximity test (the kind K12), an
oracle message that stood in front of the test and was a member of no group keeps its ledger of mask
entries, to the letter, and is a member of no group behind. Definitions, statements and proofs.

What it is for. Along the proof file's first chain one fact is carried from sub-protocol to
sub-protocol: the ledger of the message that the state names as out.indexMasks is not closed and has
a known count of entries left, and that message is a member of no group. Each kind owes that its own
sub-protocol hands the fact on. This file pays the proximity test's part on the statement; that the
number out.indexMasks itself stays is read off atFinish_ok (Johnson/Desc/K12/SeatLaws.lean), as
atFinish_leaves_out (Johnson/Desc/K12/SeatLeaves.lean) says it too.

Why a second walk. Calls (Johnson/Desc/K12/Law/CallsDef.lean) and k12_calls
(Johnson/Desc/K12/Law/Calls.lean) say that an accept of the test's decision is a run of the ground's
plain calls. In Calls the three calls that can lay, shut or expose a ledger (admitP lays a fresh
one, closeLedgerP shuts one, joinP makes a message a member, whose ledger the next beginRunP shuts)
stand at ANY message number, and closeLedgerP asks only that the message is there: so no fact on the
state alone, carried call by call along Calls, can say that one given elder ledger stays open. What
is lacking is which numbers the test's own text passes to these three. OutK2
(Johnson/Desc/K12/Law/OutK2.lean) says much of it in closed form, but not the members of the groups
that come, nor the first mask's ledger, and it stands under p.early = true and p.answers = 1. So the
walk of Calls.lean is typed once more with a floor N in these three constructors. It is a twin by
need: one relation with a test on the number as a parameter would serve both, but the two files of
Calls are not this file's to turn. CallsF.toCalls and Calls.toF tie the two relations, so that they
cannot drift: a run with a floor is a run, and a run is a run with the floor 0. The walk's lemmas
(batJ_callsF to stages_callsF) follow those of Calls.lean line by line; what is new in them is the
floor at sampleLoop_callsF, sendP_callsF, joins_callsF, tailB_callsF, switchBehind_callsF and
switchJ_callsF. The walk is some 400 of this file's lines.

Main names:
  `CallF ft N`, `CallsF ft N`: one step, a run of steps: as Call and Calls, but admitP, joinP and
    closeLedgerP only at message numbers o with N ≤ o.
  `CallsF.toCalls`, `Calls.toF`: the tie to Calls.
  `Apart S o`: the message o is a member of no group of the statement S.
  `callF_room`, `callsF_room`: where N is at most the count of messages, o < N and Apart holds in
    front: a step, a run leaves the ledger of o as it was, and Apart, and N is at most the count
    behind.
  `k12_callsF`: an accept of the decision of proximityTestKind guardedProximityTestParts p is a run whose floor is the count of
    messages in front: the test admits, joins and shuts ledgers only at messages that it has itself
    received. No premise on the place p, on the state or on the view.
  `k12_room`: the two clauses across the decision, at every message that stood in front.
  `atFinish_room`: the same at the first chain's seat (atFinish p), at out.indexMasks, with the
    look-up of the ledger written out: its two sides are Law.ledgerAt
    (Johnson/Top/H0/Walk/FrameLaw.lean) of the two states by definition.
Limits: laws from an accept; no example of an accept is shown here. Nothing says that the ledger at
out.indexMasks is open, or that Apart holds, at any state. A member of a group is not spoken of: its
ledger is shut when the group's test begins. Nothing on what an accept is worth: no soundness is
claimed, and nothing is said on hiding.
What each theorem rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.Law.OutK2
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)
open _root_.Desc.Plain (DState GPar sendP sampleLoop rowsFor)

/-- One step, with a floor N. -/
inductive CallF (ft N : Nat) : DS → DS → Prop
  | newGroup {d d' : DS} {a b n : Nat} : Ground.newGroupP d a b = some (n, d') → CallF ft N d d'
  | recv {d d' : DS} {sent : Array OracleNotice} {ids : Array Nat} :
      Ground.recvP ft d sent = some (ids, d') → CallF ft N d d'
  | admit {d d' : DS} {o : Nat} {rows : Array OnBytes.Row} {s : OracleShape}
      {seeds : List SampleSeed} {ys ys' : List E} : N ≤ o →
      (d.st.oracles[o]?).map (·.shape) = some s → Blk.shapeOk d.st.codes s = true →
      (∀ sd ∈ seeds, (Send.cube d.st.codes s).bits ≤ sd.z.length) →
      rowsFor d.st.codes s o seeds (List.range s.answers) ys #[] = some (rows, ys') →
      Ground.admitP d o rows = some d' → CallF ft N d d'
  | join {d d' : DS} {g o : Nat} {k : Bool} : N ≤ o → Ground.joinP d g o k = some d' →
      CallF ft N d d'
  | addRow {d d' : DS} {g : Nat} {row : OnBytes.Row} : Ground.addRowP d g row = some d' →
      CallF ft N d d'
  | closeLedger {d d' : DS} {o : Nat} : N ≤ o → Ground.closeLedgerP d o = some d' → CallF ft N d d'
  | spend {d d' : DS} {o : Nat} : Ground.spendAsMaskP d o = some d' → CallF ft N d d'
  | begin {d d' : DS} {g : Nat} {run : RunInput} : Ground.beginRunP d g = some (run, d') →
      CallF ft N d d'
  | count (d : DS) (t : Nat) : CallF ft N d { d with book := { d.book with
      trees := d.book.trees.modify t fun x => { x with lists := x.lists + 1 } } }
  | cols (d : DS) (l : List (Nat × Nat × List UInt64)) : CallF ft N d { d with opened := l }

/-- A run of such steps. -/
inductive CallsF (ft N : Nat) : DS → DS → Prop
  | nil (d : DS) : CallsF ft N d d
  | cons {a b c : DS} : CallF ft N a b → CallsF ft N b c → CallsF ft N a c

variable {ft N : ℕ}

theorem CallsF.one {a b : DS} (h : CallF ft N a b) : CallsF ft N a b := .cons h (.nil b)

theorem CallsF.trans {a b c : DS} (h : CallsF ft N a b) (k : CallsF ft N b c) :
    CallsF ft N a c := by
  induction h with
  | nil _ => exact k
  | cons s _ ih => exact .cons s (ih k)

theorem CallsF.toCols (d : DS) (l : List (Nat × Nat × List UInt64)) :
    CallsF ft N d { d with opened := l } := .one (.cols d l)

/-- A step with a floor is a step. -/
theorem CallF.toCall {a b : DS} (h : CallF ft N a b) : Call ft a b := by
  cases h with
  | newGroup h => exact .newGroup h
  | recv h => exact .recv h
  | admit _ h1 h2 h3 h4 h => exact .admit h1 h2 h3 h4 h
  | join _ h => exact .join h
  | addRow h => exact .addRow h
  | closeLedger _ h => exact .closeLedger h
  | spend h => exact .spend h
  | begin h => exact .begin h
  | count t => exact .count _ t
  | cols l => exact .cols _ l

/-- A run with a floor is a run. -/
theorem CallsF.toCalls {a b : DS} (h : CallsF ft N a b) : Calls ft a b := by
  induction h with
  | nil d => exact .nil d
  | cons s _ ih => exact .cons s.toCall ih

/-- A run is a run with the floor 0. -/
theorem Calls.toF {a b : DS} (h : Calls ft a b) : CallsF ft 0 a b := by
  induction h with
  | nil d => exact .nil d
  | cons s _ ih =>
    refine .cons ?_ ih
    cases s with
    | newGroup h => exact .newGroup h
    | recv h => exact .recv h
    | admit h1 h2 h3 h4 h => exact .admit (Nat.zero_le _) h1 h2 h3 h4 h
    | join h => exact .join (Nat.zero_le _) h
    | addRow h => exact .addRow h
    | closeLedger h => exact .closeLedger (Nat.zero_le _) h
    | spend h => exact .spend h
    | begin h => exact .begin h
    | count t => exact .count _ t
    | cols l => exact .cols _ l

/-- The message o is a member of no group. -/
def Apart (S : Statement) (o : ℕ) : Prop := ∀ G ∈ S.groups, o ∉ G.members

/-- A change of the groups that turns no list of members but by numbers other than o. -/
theorem apart_modify {gs : Array OnBytes.Group} {g o : ℕ} {f : OnBytes.Group → OnBytes.Group}
    (hf : ∀ G, o ∉ G.members → o ∉ (f G).members) (h : ∀ G ∈ gs, o ∉ G.members) :
    ∀ G ∈ gs.modify g f, o ∉ G.members := by
  intro G hG
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hG
  rw [Array.size_modify] at hi
  rw [Array.getElem_modify]
  split
  · exact hf _ (h _ (Array.getElem_mem hi))
  · exact h _ (Array.getElem_mem hi)

theorem mem_insertIf {a : Array ℕ} {i x o : ℕ} (h : o ∈ a.insertIdxIfInBounds i x) :
    o = x ∨ o ∈ a := by
  unfold Array.insertIdxIfInBounds at h
  split at h
  · exact Array.mem_insertIdx.1 h
  · exact .inr h

theorem apart_joined {S : Statement} {g o' o : ℕ} {k : Bool} {G : OnBytes.Group} (hne : o ≠ o')
    (h : Apart S o) : Apart (withMessageInGroup S g o' k G) o := by
  unfold Apart Slice.withMessageInGroup
  dsimp only
  refine apart_modify ?_ h
  intro G' hG' hm
  rcases mem_insertIf hm with e | hm
  · exact hne e
  · exact hG' hm

theorem apart_withRow {S : Statement} {g o : ℕ} {row : OnBytes.Row} (h : Apart S o) :
    Apart (withRow S g row) o := by
  unfold Apart withRow
  dsimp only
  refine apart_modify ?_ h
  exact fun _ h => h

theorem apart_begun {S : Statement} {g o : ℕ} {G : OnBytes.Group} (h : Apart S o) :
    Apart (begun S g G) o := by
  unfold Apart begun
  dsimp only
  rw [closeLedgers_groups]
  refine apart_modify ?_ h
  exact fun _ h => h

theorem ledger_modify_ne {os : Array OnBytes.Oracle} {a o : ℕ}
    {f : OnBytes.Oracle → OnBytes.Oracle} (h : a ≠ o) :
    ((os.modify a f)[o]?).bind (·.ledger) = (os[o]?).bind (·.ledger) := by
  rw [Array.getElem?_modify, if_neg h]

theorem ledger_modify_same {os : Array OnBytes.Oracle} {a o : ℕ}
    {f : OnBytes.Oracle → OnBytes.Oracle} (hf : ∀ x, (f x).ledger = x.ledger) :
    ((os.modify a f)[o]?).bind (·.ledger) = (os[o]?).bind (·.ledger) := by
  rw [Array.getElem?_modify]
  split
  · cases os[o]? with
    | none => rfl
    | some x => exact hf x
  · rfl

/-- **One step**: below the floor, a message that is a member of no group keeps its ledger and stays
a member of no group. -/
theorem callF_room {d d' : DS} (h : CallF ft N d d') (hN : N ≤ d.st.oracles.size) {o : ℕ}
    (ho : o < N) (ha : Apart d.st o) :
    (d'.st.oracles[o]?).bind (·.ledger) = (d.st.oracles[o]?).bind (·.ledger) ∧ Apart d'.st o ∧
      N ≤ d'.st.oracles.size := by
  cases h with
  | newGroup h =>
    unfold Ground.newGroupP at h
    split at h
    · cases h
      refine ⟨rfl, fun G hG => ?_, hN⟩
      rcases Array.mem_push.1 hG with hG | rfl
      · exact ha G hG
      · simp
    · cases h
  | recv h =>
    obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok h
    refine ⟨?_, ha, ?_⟩
    · show ((stSent d.st _).oracles[o]?).bind _ = _
      rw [stSent_old _ _ o (by omega)]
    · show N ≤ (stSent d.st _).oracles.size
      simp only [stSent, Array.size_append]
      omega
  | admit ho _ _ _ _ h =>
    obtain ⟨x, places, _, _, rfl⟩ := admitP_ok h
    refine ⟨ledger_modify_ne (by omega), ha, ?_⟩
    show N ≤ (d.st.oracles.modify _ _).size
    rw [Array.size_modify]
    exact hN
  | join ho h =>
    rename_i g o' k
    unfold Ground.joinP at h
    split at h
    · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
      refine ⟨ledger_modify_ne (by omega), ?_, ?_⟩
      · exact apart_joined (by omega) ha
      · show N ≤ (d.st.oracles.modify _ _).size
        rw [Array.size_modify]
        exact hN
    · cases h
  | addRow h =>
    rename_i g row
    unfold Ground.addRowP at h
    split at h
    · cases h
      exact ⟨rfl, apart_withRow ha, hN⟩
    · cases h
  | closeLedger ho h =>
    unfold Ground.closeLedgerP at h
    split at h
    · cases h
      refine ⟨?_, ?_, ?_⟩
      · show ((closeLedgers d.st _).oracles[o]?).bind _ = _
        rw [closeLedgers_other _ _ _ (by simp; omega)]
      · show ∀ G ∈ (closeLedgers d.st _).groups, _
        rw [closeLedgers_groups]
        exact ha
      · show N ≤ (closeLedgers d.st _).oracles.size
        rw [closeLedgers_size]
        exact hN
    · cases h
  | spend h =>
    rw [spendP_form h]
    refine ⟨ledger_modify_same fun _ => rfl, ha, ?_⟩
    show N ≤ (d.st.oracles.modify _ _).size
    rw [Array.size_modify]
    exact hN
  | begin h =>
    rename_i g run
    obtain ⟨G, hG, rfl⟩ : ∃ G, d.st.groups[g]? = some G ∧ d' = { d with st := begun d.st g G } := by
      unfold Ground.beginRunP at h
      split at h
      · obtain ⟨G, hG, h⟩ := obind_ok h
        cases h
        exact ⟨G, hG, rfl⟩
      · cases h
    have hm : o ∉ G.members.toList := by
      rw [Array.mem_toList_iff]
      exact ha G (Array.mem_of_getElem? hG)
    refine ⟨?_, ?_, ?_⟩
    · show ((closeLedgers d.st _).oracles[o]?).bind _ = _
      rw [closeLedgers_other _ _ _ hm]
    · exact apart_begun ha
    · show N ≤ (closeLedgers d.st _).oracles.size
      rw [closeLedgers_size]
      exact hN
  | count t => exact ⟨rfl, ha, hN⟩
  | cols l => exact ⟨rfl, ha, hN⟩

/-- **A run.** -/
theorem callsF_room {d d' : DS} (h : CallsF ft N d d') (hN : N ≤ d.st.oracles.size) {o : ℕ}
    (ho : o < N) (ha : Apart d.st o) :
    (d'.st.oracles[o]?).bind (·.ledger) = (d.st.oracles[o]?).bind (·.ledger) ∧ Apart d'.st o ∧
      N ≤ d'.st.oracles.size := by
  induction h with
  | nil d => exact ⟨rfl, ha, hN⟩
  | cons s _ ih =>
    obtain ⟨a1, a2, a3⟩ := callF_room s hN ho ha
    obtain ⟨b1, b2, b3⟩ := ih a3 a2
    exact ⟨b1.trans a1, b2, b3⟩

/-- Along a run the count of messages does not fall below the floor. -/
theorem CallF.floor {d d' : DS} (h : CallF ft N d d') (hN : N ≤ d.st.oracles.size) :
    N ≤ d'.st.oracles.size := by
  cases h with
  | newGroup h =>
    unfold Ground.newGroupP at h
    split at h
    · cases h; exact hN
    · cases h
  | recv h =>
    obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok h
    show N ≤ (stSent d.st _).oracles.size
    simp only [stSent, Array.size_append]
    omega
  | admit _ _ _ _ _ h =>
    obtain ⟨x, places, _, _, rfl⟩ := admitP_ok h
    show N ≤ (d.st.oracles.modify _ _).size
    rw [Array.size_modify]
    exact hN
  | join _ h =>
    unfold Ground.joinP at h
    split at h
    · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
      show N ≤ (d.st.oracles.modify _ _).size
      rw [Array.size_modify]
      exact hN
    · cases h
  | addRow h =>
    unfold Ground.addRowP at h
    split at h
    · cases h; exact hN
    · cases h
  | closeLedger _ h =>
    unfold Ground.closeLedgerP at h
    split at h
    · cases h
      show N ≤ (closeLedgers d.st _).oracles.size
      rw [closeLedgers_size]
      exact hN
    · cases h
  | spend h =>
    rw [spendP_form h]
    show N ≤ (d.st.oracles.modify _ _).size
    rw [Array.size_modify]
    exact hN
  | begin h =>
    obtain ⟨G, _, _, _, _, rfl⟩ := beginRunP_ok h
    show N ≤ (closeLedgers d.st _).oracles.size
    rw [closeLedgers_size]
    exact hN
  | count t => exact hN
  | cols l => exact hN

theorem CallsF.floor {d d' : DS} (h : CallsF ft N d d') (hN : N ≤ d.st.oracles.size) :
    N ≤ d'.st.oracles.size := by
  induction h with
  | nil d => exact hN
  | cons s _ ih => exact ih (s.floor hN)

/-! ## The walk along the sub-protocol's own text, with the floor -/

theorem batJ_callsF (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) (l l' : List (Nat × Nat × List UInt64)) :
    CallsF ft N (dT t l) (dT t1 l') := by
  unfold batJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨⟨row, L⟩, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.batE at hx
    split at hx
    · obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨⟨row', L', S'⟩, hb, hx⟩ := bind_ok hx
      cases hx
      have hb' := mapError_ok hb
      unfold First.Close.bat at hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨⟨input, d⟩, hbeg, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      cases hb'
      have k := beginRunP_at (First.Close.onSt t.st) (dT t l) rfl (got_ok hbeg)
      exact (CallsF.one (.begin k)).trans (CallsF.toCols _ l')
    · cases hx
  · cases h

theorem behindJ_callsF (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t2 t3 : T12) (h : (behindJ p j nxt cut).decide t2 [] [] = .ok t3)
    (l l' : List (Nat × Nat × List UInt64)) : CallsF ft N (dT t2 l) (dT t3 l') := by
  simp only [behindJ] at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    replace hx := H2K.Sw.named_ok hx
    unfold VerifiableInference.Desc.Test.csTest at hx
    dsimp only at hx
    split at hx
    · cases hx
    · rename_i run s2 hb
      split at hx
      · cases hx
      · rename_i s3 ha
        split at hx
        · cases hx
        · cases hx
          have a5 := askOwedE_ok ha
          have hbp := beginRunE_call hb
          obtain ⟨G, lay', _, _, _, a4⟩ := beginRunE_ok hb
          have k :=
            beginRunP_at (lay p [] (cut.getLast?.map (·.entry)) t2 [] []).d (dT t2 l) rfl hbp
          refine (CallsF.one (.begin k)).trans ?_
          show CallsF ft N _ (⟨s3.d.st, s3.d.book, s3.d.roots, l', ()⟩ : DS)
          rw [a5, a4]
          exact CallsF.toCols _ l'
  · cases h

theorem foldJ_callsF (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1)
    (l l' : List (Nat × Nat × List UInt64)) : CallsF p.nums.firstTree N (dT t l) (dT t1 l') := by
  simp only [foldJ] at h
  split at h
  · rename_i row L c n e1 e2 e3
    obtain ⟨⟨rows, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨⟨gp, s2⟩, hy, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.foldE at hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨⟨rows', d'⟩, hf, hx⟩ := bind_ok hx
    cases hx
    obtain ⟨id, d1, hcase, hsp⟩ := foldD_state _ _ _ _ _ _ _ _ _ (mapError_ok hf)
    have k0 : CallsF p.nums.firstTree N (dT t l) (lay p cut none t rs gs).d := CallsF.toCols _ _
    have k1 : CallsF p.nums.firstTree N (lay p cut none t rs gs).d d1 := by
      rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
      · exact .nil _
      · exact .one (.recv hr)
    have k2 : CallsF p.nums.firstTree N d1 d' := .one (.spend hsp)
    unfold H2K.newGroupE at hy
    cases hg : Ground.newGroupP d' n.1 n.2 with
    | none => simp [hg, H2K.opt, Except.map] at hy
    | some v =>
      simp only [hg, H2K.opt, Except.map] at hy
      cases hy
      have k3 : CallsF p.nums.firstTree N d' v.2 := .one (.newGroup hg)
      exact ((k0.trans k1).trans (k2.trans k3)).trans (CallsF.toCols _ l')
  · cases h

/-- The samples' answers are admitted at the listed numbers alone. -/
theorem sampleLoop_callsF (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DS) (left : List E),
      d.st.codes = codes → (∀ x ∈ l, (d.st.oracles[x.1]?).map (·.shape) = some x.2) →
      (∀ x ∈ l, Own.sentShapeFits codes x.2 = true ∧
        ∀ sd ∈ seeds, (Send.cube codes x.2).bits ≤ sd.z.length) →
      (∀ x ∈ l, N ≤ x.1) →
      sampleLoop Ground.groundG p codes seeds l ys d = some (d', left) → CallsF ft N d d'
  | [], ys, d, d', left, _, _, _, _, h => by
    cases h
    exact .nil _
  | (o, s) :: l, ys, d, d', left, hc, hs, hq, hf, h => by
    rw [sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' hrows
      split at h
      · cases h
      · rename_i d1 had
        have had' : Ground.admitP d o rows = some d1 := had
        obtain ⟨x', places, _, _, e1⟩ := admitP_ok had'
        have k1 : CallF ft N d d1 := .admit (hf (o, s) List.mem_cons_self)
          (hs (o, s) (List.mem_cons_self))
          (by rw [hc]; exact (hq (o, s) (List.mem_cons_self)).1)
          (by rw [hc]; exact (hq (o, s) (List.mem_cons_self)).2) (by rw [hc]; exact hrows) had'
        refine .cons k1 (sampleLoop_callsF p codes seeds l ys' d1 d' left ?_ ?_
          (fun x hx => hq x (List.mem_cons_of_mem _ hx))
          (fun x hx => hf x (List.mem_cons_of_mem _ hx)) h)
        · rw [e1]
          exact hc
        · intro x hx
          rw [e1]
          show ((admitted d.st o x'.shape places rows).oracles[x.1]?).map (·.shape) = _
          rw [admitted_shape]
          exact hs x (List.mem_cons_of_mem _ hx)

/-- A sending: the numbers that it returns are the next ones; it admits at these alone. -/
theorem sendP_callsF (p : GPar) (own : Bool) (d d₂ : DS) (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) (ids : Array ℕ) (sd an : List E) (took : ℕ)
    (h : sendP Ground.groundG p own d sent r₁ r₂ = some (ids, sd, an, took, d₂))
    (hN : N ≤ d.st.oracles.size) :
    CallsF p.firstTree N d d₂ ∧ ids = (Array.range sent.size).map (· + d.st.oracles.size) := by
  unfold sendP at h
  obtain ⟨⟨ids', d₁⟩, hr, h⟩ := obind_ok h
  dsimp only at h
  obtain ⟨shapes, hsh, h⟩ := obind_ok h
  obtain ⟨seeds, hseeds, h⟩ := obind_ok h
  obtain ⟨an', _, h⟩ := obind_ok h
  split at h
  · obtain ⟨⟨d₂', left⟩, hl, h⟩ := obind_ok h
    split at h
    · cases h
      obtain ⟨lay, _, _, hids, _⟩ := recvP_ok hr
      refine ⟨.cons (.recv hr)
        (sampleLoop_callsF _ _ _ _ _ _ _ _ rfl (mapM_zip _ _ _ hsh) ?_ ?_ hl), hids⟩
      · intro x hx
        have hx1 : x.1 ∈ ids.toList := (List.mem_filter.1 (List.of_mem_zip hx).1).1
        refine ⟨recvP_fits hr x.1 hx1 x.2 (mapM_zip _ _ _ hsh x hx), fun sd hsd => ?_⟩
        exact Nat.le_trans (mem_foldl_max' (fun s => (Send.cube d₁.st.codes s).bits) shapes 0 x.2
          (List.of_mem_zip hx).2) (seedsMade_long _ _ _ _ hseeds sd hsd)
      · intro x hx
        have hx1 : x.1 ∈ ids.toList := (List.mem_filter.1 (List.of_mem_zip hx).1).1
        rw [hids] at hx1
        simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hx1
        obtain ⟨i, _, hi⟩ := hx1
        omega
    · cases h
  · cases h

theorem openOne_callsF (d : DS) (S : Statement) (f0 : ℕ) (pos : Positions) (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : Tw.L9.openOne S f0 pos B0 t s = .ok s') :
    CallsF ft N { d with book := s.1 } { d with book := s'.1 } := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact .one (.count { d with book := s.1 } t))
      | cases h
  · cases h

theorem readOld_callsF (d : DS) (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook)
    (left : List Tw.L9.Col) (y : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, y)) :
    CallsF ft N { d with book := i.book } { d with book := B } := by
  unfold Tw.L9.readOld at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i B' left' cols hfold
        split at h
        · cases h
        · split at h
          · cases h
          · cases h
            exact foldlM_brE
              (fun (a b : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F))) =>
                CallsF ft N { d with book := a.1 } { d with book := b.1 }) (fun _ => .nil _)
              (fun _ _ _ h1 h2 => h1.trans h2) _
              (fun s a s' hs => openOne_callsF d _ _ _ _ _ _ _ hs) _ _ _ hfold

/-- Joins one behind the other, at numbers not below the floor. -/
theorem joins_callsF (d : DS) (g : ℕ) : ∀ (l : List (ℕ × KeptTarget)) (S S' : Statement),
    (∀ a ∈ l, N ≤ a.1) →
    l.foldlM (fun S p => Tw.L9.joinS S g p.1 p.2.keptAgain) S = .ok S' →
    CallsF ft N { d with st := S } { d with st := S' }
  | [], S, S', _, h => by cases h; exact .nil _
  | a :: l, S, S', hq, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bind_ok h
    exact .cons (.join (hq a List.mem_cons_self)
        (joinS_joinP { d with st := S } g a.1 a.2.keptAgain S1 h1))
      (joins_callsF d g l S1 S' (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h2)

theorem rows_callsF (d : DS) (g : ℕ) : ∀ (l : List OnBytes.Row) (S S' : Statement),
    l.foldlM (fun S r => Tw.L9.addRowS S g r) S = .ok S' →
    CallsF ft N { d with st := S } { d with st := S' }
  | [], S, S', h => by cases h; exact .nil _
  | a :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bind_ok h
    exact .cons (.addRow (addRowS_addRowP { d with st := S } g a S1 h1))
      (rows_callsF d g l S1 S' h2)

theorem tailB_callsF (d : DS) (i : Tw.L9.SwIn) (out : Switched) (B : TreeBook)
    (left : List Tw.L9.Col) (y : Array E) (S1 : Statement) (o : Tw.L9.SwOut)
    (hg : N ≤ out.g) (hk : ∀ a ∈ out.kept, N ≤ a)
    (h : tailB i out B left y S1 = .ok o) :
    CallsF ft N { d with st := S1 } { d with st := o.st } ∧ o.book = B := by
  unfold tailB at h
  obtain ⟨S2, h2, h⟩ := bind_ok h
  obtain ⟨S3, h3, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · simp only [pure_bind] at h
      split at h
      · obtain ⟨S4, h4, h⟩ := bind_ok h
        cases h
        rw [← Array.foldlM_toList] at h3
        refine ⟨(CallsF.one (.join hg (joinS_joinP { d with st := S1 } _ _ _ S2 h2))).trans
          ((joins_callsF d _ _ S2 S3 (fun a ha => ?_) h3).trans (rows_callsF d _ _ S3 S4 h4)), rfl⟩
        rw [Array.toList_zip] at ha
        exact hk _ (Array.mem_toList_iff.1 (List.of_mem_zip ha).1)
      · cases h
  · cases h

/-- The step behind a code switch's sending: it shuts a ledger and joins at the numbers that the
sending returned, and at no other. -/
theorem switchBehind_callsF (d : DS) (i : Tw.L9.SwIn) (o : Tw.L9.SwOut)
    (hg : N ≤ i.ids.getD 0 noId) (hk : ∀ a ∈ i.ids.extract 1 (1 + i.T.kept.size), N ≤ a)
    (h : Tw.L9.switchBehind i = .ok o) :
    CallsF ft N { d with st := i.st, book := i.book } { d with st := o.st, book := o.book } := by
  rw [switchBehind_eq] at h
  cases hcode : i.st.codes.base[i.old.code]? with
  | none => simp only [hcode] at h; cases h
  | some code =>
  simp only [hcode, pure_bind] at h
  obtain ⟨pos, _, h⟩ := bind_ok h
  obtain ⟨⟨B, left, y⟩, hread, h⟩ := bind_ok h
  have k1 : CallsF ft N { d with st := i.st, book := i.book } { d with st := i.st, book := B } :=
    readOld_callsF { d with st := i.st } i pos B left y hread
  refine k1.trans ?_
  by_cases hm : 0 < i.T.shape.maskRows
  · rw [if_pos hm] at h
    obtain ⟨S1, h1, h⟩ := bind_ok h
    split at h1
    · rename_i hlt
      cases h1
      obtain ⟨k2, hB⟩ :=
        tailB_callsF (ft := ft) (N := N) { d with book := B } i _ B left y _ o hg hk h
      rw [hB]
      exact .cons (.closeLedger hg (shut_closeLedgerP { d with st := i.st, book := B } _ hlt)) k2
    · cases h1
  · rw [if_neg hm] at h
    obtain ⟨k2, hB⟩ :=
      tailB_callsF (ft := ft) (N := N) { d with book := B } i _ B left y _ o hg hk h
    rw [hB]
    exact k2

theorem switchJ_callsF (p : P12) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) (t1 t2 : T12) (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (hN : N ≤ t1.st.oracles.size)
    (l l' : List (Nat × Nat × List UInt64)) : CallsF p.nums.firstTree N (dT t1 l) (dT t2 l') := by
  simp only [switchJ] at h1
  split at h1
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out', theta⟩, s'⟩, hx, h1⟩ := bind_ok h1
    obtain ⟨rfl, _⟩ := back_ok h1
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    obtain ⟨e₁, e₂, es, ids, sd, an, took, d₂, x, o, _, hsend, _, _, hbeh, _, hd⟩ :=
      switchE_sendP rows _ gp _ _ s' out' theta r1 r2 hr hx
    have k0 : CallsF p.nums.firstTree N (dT t1 l) (lay p cut none t1 rs gs).d := CallsF.toCols _ _
    obtain ⟨k1, hids⟩ := sendP_callsF (N := N) _ _ _ _ _ _ _ _ _ _ _ hsend hN
    have k1' : CallsF p.nums.firstTree N (lay p cut none t1 rs gs).d d₂ := k1
    have hall : ∀ a ∈ ids, N ≤ a := by
      intro a ha
      rw [hids] at ha
      obtain ⟨i, _, rfl⟩ := Array.mem_map.1 ha
      have : N ≤ (lay p cut none t1 rs gs).d.st.oracles.size := hN
      omega
    have h0 : 0 < ids.size := by
      rw [hids]
      simp [Tw.L9.switchNotices]
    have k2 := switchBehind_callsF (ft := p.nums.firstTree) (N := N) d₂ _ o
      (by
        show N ≤ ids.getD 0 noId
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h0]
        exact hall _ (Array.getElem_mem h0))
      (by
        intro a ha
        obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
        rw [Array.getElem_extract]
        exact hall _ (Array.getElem_mem _)) hbeh
    show CallsF _ _ _ (⟨s'.d.st, s'.d.book, s'.d.roots, l', ()⟩ : DS)
    rw [hd]
    exact ((k0.trans k1').trans k2).trans (CallsF.toCols _ l')
  · cases h1

theorem baseJ5_callsF (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE)
    (l l' : List (Nat × Nat × List UInt64)) : CallsF ft N (dT t l) (dT tE l') := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, _, h⟩ := bind_ok h
    obtain ⟨star, hs, h⟩ := bind_ok h
    obtain ⟨_, hp, h⟩ := bind_ok h
    obtain ⟨a, _, h⟩ := bind_ok h
    cases h
    have k1 := lastPair_spend _ (dT t l) _ m star (H2K.FoldLaw.need_ok hp)
    exact (CallsF.cons (.spend k1) (.one (.count _ a))).trans (CallsF.toCols _ l')
  · cases h

/-- Along the stages. -/
theorem stages_callsF (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (la : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
    (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE →
    N ≤ t.st.oracles.size →
    ∀ l l' : List (Nat × Nat × List UInt64), CallsF p.nums.firstTree N (dT t l) (dT tE l')
  | [], j, cur, la, t, tE, rs, gs, h, _, l, l' => by
    rw [stagesFrom_last] at h
    exact baseJ5_callsF p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1 l l'
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h, hN, l, l' => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := foldJ_callsF (N := N) p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1) l []
    have hN1 : N ≤ t1.st.oracles.size := k1.floor hN
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switchJ_callsF (N := N) p j cur nxt rest.isEmpty _ t1 t2 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) hN1 [] []
    have hN2 : N ≤ t2.st.oracles.size := k2.floor hN1
    have k3 := behindJ_callsF (ft := p.nums.firstTree) (N := N) p (j + 1) nxt _ t2 t3
      ((like_P5 p).behind _ _ _ _ _ f3) [] []
    have hN3 : N ≤ t3.st.oracles.size := k3.floor hN2
    have k4 := stages_callsF p rest (j + 1) nxt _ t3 tE _ _ f5 hN3 [] l'
    exact ((k1.trans k2).trans k3).trans k4

/-- An accept of the proximity test's decision is a run of the ground's calls in which every
admitting, every joining and every shutting of a ledger is at a message that was not there in
front. -/
theorem k12_callsF (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE)
    (l l' : List (Nat × Nat × List UInt64)) :
    CallsF p.nums.firstTree t0.st.oracles.size (dT t0 l) (dT tE l') := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  have k1 := batJ_callsF (ft := p.nums.firstTree) (N := tF.st.oracles.size) p _ _ _ _ _
    ((like_P5 p).bat _ _ _ _ _ hbat) l []
  exact k1.trans (stages_callsF p rest 0 first _ _ tE _ _ hst (k1.floor (Nat.le_refl _)) [] l')

/-- Across an accept of the test's decision: a message that stood in front and was a member of no
group keeps its ledger, to the letter, and is a member of no group behind. -/
theorem k12_room (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) {o : ℕ} (ho : o < t0.st.oracles.size)
    (ha : Apart t0.st o) :
    (tE.st.oracles[o]?).bind (·.ledger) = (t0.st.oracles[o]?).bind (·.ledger) ∧ Apart tE.st o := by
  obtain ⟨a1, a2, _⟩ := callsF_room (k12_callsF p t0 tE rs gs h [] []) (Nat.le_refl _) ho ha
  exact ⟨a1, a2⟩

/-- At the first chain's seat, at the number that the state names as the index masks'. -/
theorem atFinish_room (p : P12) {s s' : First.S} {rs : List Fmt.RoundView} {gs : Gs}
    (h : (K12.atFinish p).decide s rs gs = .ok s') (ho : s.out.indexMasks < s.st.oracles.size)
    (ha : Apart s.st s.out.indexMasks) :
    s'.out.indexMasks = s.out.indexMasks ∧
      (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) =
        (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) ∧
      Apart s'.st s'.out.indexMasks := by
  obtain ⟨o, t', _, _, _, hd, rfl⟩ := VerifiableInference.Desc.K12.Seat.atFinish_ok p s s' rs gs h
  obtain ⟨a1, a2⟩ := k12_room p _ t' rs gs hd ho ha
  exact ⟨rfl, a1, a2⟩

end H2K.Out

#print axioms H2K.Out.CallsF.toCalls
#print axioms H2K.Out.Calls.toF
#print axioms H2K.Out.callsF_room
#print axioms H2K.Out.k12_callsF
#print axioms H2K.Out.k12_room
#print axioms H2K.Out.atFinish_room
