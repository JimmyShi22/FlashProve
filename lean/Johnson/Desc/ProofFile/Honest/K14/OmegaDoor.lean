-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaDoor.lean: kind K14: WHAT THE TESTS OF
Honest/K14/OmegaEnd.lean GIVE OF THE ELEVEN THAT "K14, second part" LEAVES (secondDoor,
Honest/K14/SecondDoor.lean: a list of this kind's own; that it is all true is by itself no accept of
the sub-protocol: door_owed there); AND: EACH OF THESE TESTS STAYS UNDER A RELATION BETWEEN TWO
STATES, AND THE THREE RELATIONS HOLD AT EVERY ACCEPTING DECISION OF EITHER PROXIMITY TEST WHERE THAT
TEST's OWN TEST ON THE PLAN ACCEPTS (at the first test two of the three ask beside that the first
mask's number is not Omega's), AND AT EVERY ACCEPTING DECISION OF THE CHAIN's CLOSING SUB-PROTOCOL:
BY THE LIBRARY's OWN LAWS ON THESE. Definitions with code, and statements with their proofs.

  secondRest p s  **WHAT IS LEFT OF THE ELEVEN**: at most six tests. Four are of the eleven:
                  statement and book are in step; no member twice; the row's terms fit their places;
                  no coefficient on a pad. Two are not of the eleven: the weights have as many
                  variables as a row's number has bits; each can be cut below the matrix's rows:
                  with the shared point's length these two give a fifth of the eleven, that the row
                  (Dot) can be made. In three cases the list is shorter, and in one of them
                  secondDoor lists a false clause where this list is silent: its docstring tells
                  them. (The short name stands once more in the library, in another namespace and
                  for another thing: OnBytes/Tie/Pv/Keeps/AdoptNote.lean)
  door_of_omega   **omegaEndL at the shared end that lies in the state, and secondRest: all of
                  secondDoor.** That the row (Dot) can be made: the library's dot_yes
                  (Johnson/Desc/K14/Law/DotLaw.lean)
  OmegaKept, PadKept, NotedKept what a member behind "SPLIT" has to leave for each of the three
                  tests to stay: no more than omega_stays, pad_stays and noted_stays spend
  omega_stays, pad_stays, noted_stays under its relation each test stays
  mask_of_omegaEnd omegaEndB gives that the first mask's number is not Omega's
  begun_pad, inside_pad a proximity test's beginning, and an accepting decision of the test as the
                  shared chain holds it, leave the pad of every elder message but the first mask;
                  inside_pad asks that the test's parameters have early = true and answers = 1. (A
                  note on kin: a file on the proximity test's honest part, which is not in this
                  library, states begun_pad's sentence under the same short name, but for the order
                  of two arguments, and a wider sentence than inside_pad's proof has at hand: the
                  test's own decide function leaves the pad of EVERY prior message, the first mask's
                  too. Outside this file the library has neither: so begun_pad is proved here, the
                  proof of inside_pad goes by the library's k12_old, and inside_pad leaves the first
                  mask out. inside_pad speaks of the test between enter and leave)
  omegaKept_of_leaves, padKept_of_leaves the first two relations from what the library says that
                  such a test leaves
  omegaKept_onGu, padKept_onGu, notedKept_onGu, and at the second test omegaKept_onGomega,
  padKept_onGomega, notedKept_onGomega
                  **EACH RELATION, BY ITSELF, AT EVERY ACCEPTING DECISION OF THE TWO PROXIMITY TESTS
                  AS THE SHARED CHAIN HAS THEM** (Johnson/Desc/K12/Seat/Fill.lean), where the test's
                  own test on the plan accepts. At the first test OmegaKept and PadKept ask beside
                  that the first mask's number is not Omega's; NotedKept asks nothing more than the
                  decision. By the library's onGu_leaves, onGomega_leaves, k12_old
                  (Johnson/Desc/K12/Coin/SamplesThrough.lean), onGu_grows, onGomega_grows
                  (GrowsThrough.lean), early_of_planOk, answers_of_planOk
                  (Johnson/Desc/K12/Law/Top.lean)
  closing_same, kept_closing the closing sub-protocol returns the state that it was handed, and only
                  where its two clauses hold (the library's untested_of_chainEnd,
                  Johnson/Desc/ChainEndLaw.lean): the three relations hold there of themselves
  ended_of_closing **where the closing sub-protocol accepts, Desc.K14.ended returns**, and what the
                  last chain takes of its value is the library's oOf of the state: by the library's
                  programs_of_untested (ChainEndLaw.lean) and sharedOfEnd_ended
                  (Johnson/Desc/Third/Law/Row0AtWords.lean)
  notes_pays, noted_pays **notedB, and a test begun on every group: each of o_u, o_omega and o_sp is
                  in a tested group**: the closing sub-protocol's second clause at this kind's three
                  messages, from its first. (That o_sp notes G_u too, notedB's fourth part, is not
                  spent)

OF THE ELEVEN, omegaEndL GIVES SIX (a place, the tree, in the statement, a tree to itself, the
plan's shape, sampled there) AND THE SHARED POINT's HALF OF "the row (Dot) can be made". WHERE
OMEGA's PAD LIES GIVES NO TEST OF THE ELEVEN BY ITSELF: "no coefficient on a pad" asks beside how
the weights are formed and where W's pad lies (Honest/K14/DotPads.lean, OmegaJoin.lean). notedB
gives none of the eleven: it is this kind's share of what the closing sub-protocol asks.

HOW THE RELATIONS ARE SPENT: Honest/K14/OmegaTwelve.lean calls them on the run that Thr
(Honest/Thread/Thr.lean) holds: no field keeps and no clause of the field rides of a Thread is
asked.

What is not claimed. That the two proximity tests or the closing sub-protocol accept at any run: the
closing wants a test begun on every group, and that no other sampled message stands outside a tested
group. THE BOOK-KEEPING AT THE LAST CHAIN's BORDER 0 ASKS MORE OF THE SHARED END THAN THE ELEVEN
TESTS DO (Johnson/Desc/Last/ShapeDoor.lean: the statement is in order; the book fits; Omega is part
0 of its tree; Omega has one sample row): none of that is served here. secondRest at any state. The
converse of door_of_omega. Nothing on any property of the protocol: nothing on completeness, on
soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaEnd
import Johnson.Desc.K14.Law.DotLaw
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.K12.Coin.GrowsThrough
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.ChainEndLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW tensorBelow)
open OnBytes.Slice (BookKeeps begun)
open OnBytes.Slice.ProxRun (shut closeLedgers_get)
open VerifiableInference.Desc (Block Grows Own.tensorInOrder Own.placeFits Own.allZero)
open VerifiableInference.Desc.Ground (Clauses ok has)
open VerifiableInference.Desc.Third (S₃ P₁₄ takeOver)
open VerifiableInference.Desc.Third.Law (oOf)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (onGu_leaves onGomega_leaves onGu_grows onGomega_grows
  k12_old smpPart)
open Desc.K14 (St)

/-! ## What the list gives of the eleven -/

/-- **WHAT IS LEFT OF THE ELEVEN**, meant at a state that the start returns. Four of its six tests
are tests of secondDoor (Honest/K14/SecondDoor.lean) to the letter: the first two and the last two.
The two on the weights are not among the eleven: with the shared point's length they give "the row
(Dot) can be made" (door_of_omega). THREE ARMS LIST LESS. Where the state holds no border the list
is empty, so all of it is true. Where takeOver returns an error the last two tests are not listed;
secondDoor does not list them there either. Where linDotRow returns nothing the last two are not
listed, WHILE secondDoor LISTS A FALSE CLAUSE THERE: so by itself secondRest can be all true at a
state where that clause of secondDoor is false; door_of_omega shuts this arm out by the two tests on
the weights and omegaEndL's test on the shared point's length. By itself secondRest is no test of
the member. -/
def secondRest (p : P₁₄) (s : S₃) : Clauses :=
  match s.loc.border with
  | none => []
  | some x =>
    ("adopt: statement and book are in step", s.st.oracles.size == s.book.place.size) ::
    ("join: no member twice",
      has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size)) ::
    ("the weights have as many variables as a row's number has bits",
      x.g.all (·.vars == p.S.kRow)) ::
    ("each of the weights can be cut below the matrix's rows",
      x.g.all fun g => (tensorBelow g 0 p.S.kRow p.S.matrixRows).isSome) ::
    match takeOver p.S s.loc.own x.shared (s.withCols []) with
    | .error _ => []
    | .ok a =>
      match linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => []
      | some dot =>
        [("addRow: the terms fit their places", has a.2.st.groups[s.loc.own]? fun G =>
            dot.terms.all fun t =>
              Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0),
         ("addRow: ON VALUES: no coefficient on a pad", has a.2.st.groups[s.loc.own]? fun G =>
            G.members.all fun o =>
              ((a.2.st.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
                Own.allZero (dot.coefficient o q.1 q.2))]

/-- **omegaEndL at the shared end that lies in the state, and secondRest: all of secondDoor.** -/
theorem door_of_omega (p : P₁₄) (s : S₃) (x : VerifiableInference.Desc.Third.Border)
    (hx : s.loc.border = some x) (hO : ok (omegaEndL p.S x.shared) = true)
    (hR : ok (secondRest p s) = true) : ok (secondDoor p s) = true := by
  unfold omegaEndL at hO
  unfold secondRest at hR
  unfold secondDoor
  rw [hx] at hR ⊢
  dsimp only at hR ⊢
  cases hq : x.shared.book.place[x.shared.omega]? with
  | none => rw [hq] at hO; cases hO
  | some q =>
    rw [hq] at hO
    dsimp only at hO ⊢
    cases ht : x.shared.book.trees[q.1]? with
    | none => rw [ht] at hO; cases hO
    | some t =>
      rw [ht] at hO
      dsimp only at hO ⊢
      cases hy : x.shared.st.oracles[x.shared.omega]? with
      | none => rw [hy] at hO; cases hO
      | some y =>
        rw [hy] at hO
        dsimp only at hO ⊢
        simp only [ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hO
        obtain ⟨o7, o8, o14, opsi⟩ := hO
        rw [ok_cons, ok_cons, ok_cons, ok_cons] at hR
        simp only [Bool.and_eq_true] at hR
        obtain ⟨r11, r21, rv, rc, hR⟩ := hR
        rw [ok_cons, ok_cons, ok_cons, ok_cons, ok_cons]
        simp only [Bool.and_eq_true]
        refine ⟨o7, o8, r11, o14, r21, ?_⟩
        cases ha : takeOver p.S s.loc.own x.shared (s.withCols []) with
        | error e => rfl
        | ok a =>
          rw [ha] at hR
          dsimp only at hR ⊢
          obtain ⟨dot, hd⟩ := Option.isSome_iff_exists.1 (Desc.K14.Law.dot_yes p.S x.g x.shared.psi
            a.1 (linLayOmega a.2.st.codes p.S) s.loc.w (linLayW a.2.st.codes p.S) (eq_of_beq opsi)
            (fun g hg => eq_of_beq (List.all_eq_true.1 rv g hg))
            (fun g hg => List.all_eq_true.1 rc g hg))
          rw [hd] at hR ⊢
          exact hR

/-! ## What a member behind "SPLIT" has to leave -/

/-- What omega_stays spends: for omegaEndB. -/
structure OmegaKept (s s' : St) : Prop where
  omega : s'.loc.oOmega = s.loc.oOmega
  psi : s'.loc.psiSh = s.loc.psiSh
  mask : s'.loc.firstMask = s.loc.firstMask
  /-- Omega's place, where it has one, stays -/
  place : ∀ q, s.book.place[s.loc.oOmega]? = some q → s'.book.place[s.loc.oOmega]? = some q
  /-- the tree that the place names is there behind, with as many parts -/
  tree : ∀ q t, s.book.place[s.loc.oOmega]? = some q → s.book.trees[q.1]? = some t →
    ∃ t', s'.book.trees[q.1]? = some t' ∧ t'.parts.size = t.parts.size
  /-- Omega's entry is there behind, with the same shape; sampled stays sampled -/
  entry : ∀ y, s.st.oracles[s.loc.oOmega]? = some y →
    ∃ y', s'.st.oracles[s.loc.oOmega]? = some y' ∧ y'.shape = y.shape ∧
      (y.sampled = true → y'.sampled = true)

/-- What pad_stays spends: for omegaPadB. -/
structure PadKept (s s' : St) : Prop where
  omega : s'.loc.oOmega = s.loc.oOmega
  codes : s'.st.codes = s.st.codes
  pad : ∀ y, s.st.oracles[s.loc.oOmega]? = some y →
    ∃ y', s'.st.oracles[s.loc.oOmega]? = some y' ∧ y'.pad = y.pad

/-- What noted_stays spends: for notedB. -/
structure NotedKept (s s' : St) : Prop where
  u : s'.loc.oU = s.loc.oU
  omega : s'.loc.oOmega = s.loc.oOmega
  sp : s'.loc.oSp = s.loc.oSp
  gU : s'.loc.gU = s.loc.gU
  gOmega : s'.loc.gOmega = s.loc.gOmega
  grows : Grows s.st s'.st

/-- Under OmegaKept the first test stays. -/
theorem omega_stays (S : OnBytes.Params.LinShape) {s s' : St} (K : OmegaKept s s')
    (h : omegaEndB S s = true) : omegaEndB S s' = true := by
  unfold omegaEndB at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, by rw [K.mask, K.omega]; exact h.2⟩
  have h := h.1
  unfold omegaEndL at h ⊢
  have e0 : (oOf s).book.place[(oOf s).omega]? = s.book.place[s.loc.oOmega]? := rfl
  rw [e0] at h
  cases hq : s.book.place[s.loc.oOmega]? with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    dsimp only at h
    have e1 : (oOf s').book.place[(oOf s').omega]? = some q := by
      show s'.book.place[s'.loc.oOmega]? = _
      rw [K.omega]
      exact K.place q hq
    rw [e1]
    dsimp only
    have f0 : (oOf s).book.trees[q.1]? = s.book.trees[q.1]? := rfl
    rw [f0] at h
    cases ht : s.book.trees[q.1]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      dsimp only at h
      obtain ⟨t', ht', hp⟩ := K.tree q t hq ht
      have f1 : (oOf s').book.trees[q.1]? = some t' := ht'
      rw [f1]
      dsimp only
      have g0 : (oOf s).st.oracles[(oOf s).omega]? = s.st.oracles[s.loc.oOmega]? := rfl
      rw [g0] at h
      cases hy : s.st.oracles[s.loc.oOmega]? with
      | none => rw [hy] at h; cases h
      | some y =>
        rw [hy] at h
        dsimp only at h
        obtain ⟨y', hy', a1, a2⟩ := K.entry y hy
        have g1 : (oOf s').st.oracles[(oOf s').omega]? = some y' := by
          show s'.st.oracles[s'.loc.oOmega]? = _
          rw [K.omega]
          exact hy'
        rw [g1]
        simp only [ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h ⊢
        obtain ⟨b1, b2, b3, b4⟩ := h
        refine ⟨by rw [hp]; exact b1, by rw [a1]; exact b2, a2 b3, ?_⟩
        show (s'.loc.psiSh.length == S.kCol) = true
        rw [K.psi]
        exact b4

/-- Under PadKept the second stays. -/
theorem pad_stays (S : OnBytes.Params.LinShape) {s s' : St} (K : PadKept s s')
    (h : omegaPadB S s = true) : omegaPadB S s' = true := by
  unfold omegaPadB at h ⊢
  cases hy : s.st.oracles[s.loc.oOmega]? with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain ⟨y', hy', a⟩ := K.pad y hy
    rw [K.omega, hy', K.codes]
    show decide (y'.pad = _) = true
    rw [a]
    exact h

/-- Under NotedKept the third stays. -/
theorem noted_stays {s s' : St} (K : NotedKept s s') (h : notedB s = true) : notedB s' = true :=
  noted_grows K.grows K.u K.omega K.sp K.gU K.gOmega h

/-! ## The two proximity tests and the closing sub-protocol leave all that -/

/-- The test's beginning leaves every message's pad. -/
theorem begun_pad (S : OnBytes.Statement) (g : Nat) (G : OnBytes.Group) (o : Nat) :
    ((begun S g G).oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) := by
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e, Option.map_map]
  congr 1
  funext x
  show (if o ∈ G.members.toList then shut x else x).pad = x.pad
  split <;> rfl

/-- At a proximity test as the shared chain holds it (laid by the library between enter and leave of
Johnson/Desc/K12/Seat.lean), where the test's parameters have early = true and answers = 1 (he, ha):
an accepting decision leaves the pad of every elder message (ho) but the first mask (hm). -/
theorem inside_pad (g : Desc.K14.Lin → Nat) (mask : Desc.K14.Lin → Option Nat) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave).decide d rs gs =
      .ok d') (o : Nat) (ho : o < d.st.oracles.size) (hm : mask d.loc ≠ some o) :
    (d'.st.oracles[o]?).map (·.pad) = (d.st.oracles[o]?).map (·.pad) := by
  have h' : ((VerifiableInference.Desc.K12.Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t rs gs).bind
        (VerifiableInference.Desc.K12.Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  obtain ⟨G, -, k⟩ := k12_old p he ha _ t' rs gs ht'
  show (t'.st.oracles[o]?).map (·.pad) = _
  rw [k o ho hm, begun_pad]

/-- omegaEndB gives that the first mask's number is not Omega's. -/
theorem mask_of_omegaEnd {S : OnBytes.Params.LinShape} {d : St} (h : omegaEndB S d = true) :
    d.loc.firstMask ≠ some d.loc.oOmega := by
  unfold omegaEndB at h
  rw [Bool.and_eq_true] at h
  simpa using h.2

/-- OmegaKept, from what the library says that such a test leaves. -/
theorem omegaKept_of_leaves {d d' : St}
    (hs : d.loc.oOmega < d.st.oracles.size →
      (d'.st.oracles[d.loc.oOmega]?).map smpPart = (d.st.oracles[d.loc.oOmega]?).map smpPart)
    (hl : d'.loc = d.loc) (hb : BookKeeps d.book d'.book) : OmegaKept d d' := by
  refine ⟨by rw [hl], by rw [hl], by rw [hl], fun q hq => hb.place _ q hq, ?_, ?_⟩
  · intro q t _ ht
    obtain ⟨t', ht', -, -, hpp⟩ := hb.tree _ t ht
    exact ⟨t', ht', by rw [hpp]⟩
  · intro y hy
    have e := hs (Array.getElem?_eq_some_iff.1 hy).1
    rw [hy] at e
    cases hy' : d'.st.oracles[d.loc.oOmega]? with
    | none => rw [hy'] at e; cases e
    | some y' =>
      rw [hy'] at e
      have e' : smpPart y' = smpPart y := Option.some.inj e
      exact ⟨y', rfl, congrArg Prod.fst e', fun h => by
        have : y'.sampled = y.sampled := congrArg (fun z => z.2.1) e'
        rw [this]
        exact h⟩

/-- PadKept, likewise. -/
theorem padKept_of_leaves {d d' : St} (hc : d'.st.codes = d.st.codes)
    (hp : d.loc.oOmega < d.st.oracles.size →
      (d'.st.oracles[d.loc.oOmega]?).map (·.pad) = (d.st.oracles[d.loc.oOmega]?).map (·.pad))
    (hl : d'.loc = d.loc) : PadKept d d' := by
  refine ⟨by rw [hl], hc, ?_⟩
  intro y hy
  have e := hp (Array.getElem?_eq_some_iff.1 hy).1
  rw [hy] at e
  cases hy' : d'.st.oracles[d.loc.oOmega]? with
  | none => rw [hy'] at e; cases e
  | some y' =>
    rw [hy'] at e
    exact ⟨y', rfl, Option.some.inj e⟩

section tests
variable (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (d d' : St)
  (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
include hp

/-- **OmegaKept at the test on G_u**: between the state d and the state d' that an accepting
decision returns, where the test's own test on the plan accepts (hp) and the first mask's number is
not Omega's (hm). -/
theorem omegaKept_onGu
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') (hm : d.loc.firstMask ≠ some d.loc.oOmega) : OmegaKept d d' := by
  obtain ⟨-, b, -, e, f⟩ := onGu_leaves p (H2K.JointK.early_of_planOk p hp)
    (H2K.JointK.answers_of_planOk p hp) d d' rs gs h
  exact omegaKept_of_leaves (fun ho => b _ ho hm) e f

/-- **PadKept at the test on G_u**: between the state d and the state d' that an accepting decision
returns, where the test's own test on the plan accepts (hp) and the first mask's number is not
Omega's (hm). -/
theorem padKept_onGu
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') (hm : d.loc.firstMask ≠ some d.loc.oOmega) : PadKept d d' := by
  have he := H2K.JointK.early_of_planOk p hp
  have ha := H2K.JointK.answers_of_planOk p hp
  obtain ⟨a, -, -, e, -⟩ := onGu_leaves p he ha d d' rs gs h
  exact padKept_of_leaves a
    (fun ho => inside_pad (·.gU) (·.firstMask) p he ha d d' rs gs h _ ho hm) e

/-- **OmegaKept at the test on G_omega**: between the state d and the state d' that an accepting
decision returns, where the test's own test on the plan accepts (hp). -/
theorem omegaKept_onGomega
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') : OmegaKept d d' := by
  obtain ⟨-, b, -, e, f⟩ := onGomega_leaves p (H2K.JointK.early_of_planOk p hp)
    (H2K.JointK.answers_of_planOk p hp) d d' rs gs h
  exact omegaKept_of_leaves (fun ho => b _ ho) e f

/-- **PadKept at the test on G_omega**: between the state d and the state d' that an accepting
decision returns, where the test's own test on the plan accepts (hp). -/
theorem padKept_onGomega
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') : PadKept d d' := by
  have he := H2K.JointK.early_of_planOk p hp
  have ha := H2K.JointK.answers_of_planOk p hp
  obtain ⟨a, -, -, e, -⟩ := onGomega_leaves p he ha d d' rs gs h
  exact padKept_of_leaves a
    (fun ho => inside_pad (·.gOmega) (fun _ => none) p he ha d d' rs gs h _ ho (by simp)) e

/-- **NotedKept at the test on G_u**: between the state d and the state d' that an accepting
decision returns, where the test's own test on the plan accepts (hp). -/
theorem notedKept_onGu
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') : NotedKept d d' := by
  obtain ⟨-, -, -, e, -⟩ := onGu_leaves p (H2K.JointK.early_of_planOk p hp)
    (H2K.JointK.answers_of_planOk p hp) d d' rs gs h
  exact ⟨by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], onGu_grows p d d' rs gs h⟩

/-- **NotedKept at the test on G_omega**: between the state d and the state d' that an accepting
decision returns, where the test's own test on the plan accepts (hp). -/
theorem notedKept_onGomega
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') : NotedKept d d' := by
  obtain ⟨-, -, -, e, -⟩ := onGomega_leaves p (H2K.JointK.early_of_planOk p hp)
    (H2K.JointK.answers_of_planOk p hp) d d' rs gs h
  exact ⟨by rw [e], by rw [e], by rw [e], by rw [e], by rw [e], onGomega_grows p d d' rs gs h⟩

end tests

/-- The closing sub-protocol returns the state that it was handed, and only where its two clauses
hold: the library's untested_of_chainEnd at the shared chain's closing sub-protocol. -/
theorem closing_same (front : List (Block St Unit)) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d') :
    d' = d ∧ VerifiableInference.Desc.ChainEnd.refuse
      (VerifiableInference.Desc.ChainEnd.untestedL d.st) = .ok () :=
  VerifiableInference.Desc.ChainEnd.untested_of_chainEnd (Cl := Unit) 2 11 true
    (front.flatMap (·.rounds)) (fun x : St => x.st)
    (fun x => VerifiableInference.Desc.ChainEnd.untestedL x.st) (fun _ _ hc => hc) d d' rs gs h

/-- So the three relations hold there of themselves. -/
theorem kept_closing (front : List (Block St Unit)) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d') :
    OmegaKept d d' ∧ PadKept d d' ∧ NotedKept d d' := by
  obtain ⟨rfl, -⟩ := closing_same front d d' rs gs h
  exact ⟨⟨rfl, rfl, rfl, fun _ h => h, fun _ t _ ht => ⟨t, ht, rfl⟩,
    fun y hy => ⟨y, hy, rfl, id⟩⟩, ⟨rfl, rfl, fun y hy => ⟨y, hy, rfl⟩⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, Grows.refl _⟩⟩

/-- **Where the closing sub-protocol accepts, Desc.K14.ended returns**, and what the last chain
takes of its value is oOf of the state. -/
theorem ended_of_closing (front : List (Block St Unit)) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d') :
    ∃ e, Desc.K14.ended d' = some e ∧ VerifiableInference.Desc.Third.sharedOfEnd e = oOf d' := by
  obtain ⟨rfl, hc⟩ := closing_same front d d' rs gs h
  have ht : Desc.K14.tested d' = true :=
    VerifiableInference.Desc.ChainEnd.programs_of_untested d'.st hc
  have he : ∃ e, Desc.K14.ended d' = some e := by
    unfold Desc.K14.ended
    dsimp only
    rw [if_pos ht]
    exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ := he
  exact ⟨e, he, VerifiableInference.Desc.Third.Law.sharedOfEnd_ended d' e he⟩

/-- A message that notes a group which is there, where a test has begun on every group, is in a
tested group. -/
theorem notes_pays {d : St} {o g : Nat} (hn : notesB d o g = true) (ht : thereB d g = true)
    (hall : d.st.groups.all (·.inRun) = true) :
    ∃ x, d.st.oracles[o]? = some x ∧
      (x.groups.any fun g => (d.st.groups[g]?).any (·.inRun)) = true := by
  unfold notesB at hn
  unfold thereB at ht
  cases hx : d.st.oracles[o]? with
  | none => rw [hx] at hn; cases hn
  | some x =>
    rw [hx] at hn
    have hm : g ∈ x.groups := List.contains_iff_mem.1 hn
    obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 ht
    refine ⟨x, rfl, List.any_eq_true.2 ⟨g, hm, ?_⟩⟩
    rw [hG]
    exact (Array.all_eq_true_iff_forall_mem.1 hall) G (Array.mem_of_getElem? hG)

/-- **notedB, and a test begun on every group: each of o_u, o_omega and o_sp is in a tested
group.** -/
theorem noted_pays {d : St} (h : notedB d = true) (hall : d.st.groups.all (·.inRun) = true) :
    ∀ o ∈ [d.loc.oU.oracle, d.loc.oOmega, d.loc.oSp], ∃ x, d.st.oracles[o]? = some x ∧
      (x.groups.any fun g => (d.st.groups[g]?).any (·.inRun)) = true := by
  unfold notedB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, -⟩, e⟩, f⟩ := h
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact notes_pays a e hall
  · exact notes_pays b f hall
  · exact notes_pays c f hall

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.door_of_omega
#print axioms ProofFile.Honest.K14.omega_stays
#print axioms ProofFile.Honest.K14.pad_stays
#print axioms ProofFile.Honest.K14.noted_stays
#print axioms ProofFile.Honest.K14.begun_pad
#print axioms ProofFile.Honest.K14.inside_pad
#print axioms ProofFile.Honest.K14.mask_of_omegaEnd
#print axioms ProofFile.Honest.K14.omegaKept_of_leaves
#print axioms ProofFile.Honest.K14.padKept_of_leaves
#print axioms ProofFile.Honest.K14.omegaKept_onGu
#print axioms ProofFile.Honest.K14.padKept_onGu
#print axioms ProofFile.Honest.K14.omegaKept_onGomega
#print axioms ProofFile.Honest.K14.padKept_onGomega
#print axioms ProofFile.Honest.K14.notedKept_onGu
#print axioms ProofFile.Honest.K14.notedKept_onGomega
#print axioms ProofFile.Honest.K14.closing_same
#print axioms ProofFile.Honest.K14.kept_closing
#print axioms ProofFile.Honest.K14.ended_of_closing
#print axioms ProofFile.Honest.K14.notes_pays
#print axioms ProofFile.Honest.K14.noted_pays
