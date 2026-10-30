-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/BlindAtt.lean: K5's three runs, and K3's "join", "planes" and "guests"
(with no guest), are Blind to the real adding (Johnson/Desc/First/Batch/ObjectsLaw.lean: Blind) at
any seat that meets `SeatQuiet`; "join" and "planes" at `seatCS` with no premise. That these are the
runs of an attention segment's step of adding is not shown here. No Mathlib.
  `addAll_cols`: an adding leaves each array's number of columns.
  `SeatQuiet seat`: the five readers of a seat of K5's claims are not turned by an adding.
      EVERYTHING BELOW IS GENERAL IN SUCH A SEAT (one text over a seat serves
      every road). `seatCS_quiet`: the seat that reads the four records of the program
      `verify-on-bytes` in the state is one.
  `keysOfK_unturned` · `readersOfK_unturned`: the premises of K3's "join" and "planes" are paid.
  `readRun` · `readRun_blind`: a run that reads the state, lays claims and leaves the state.
  `firstAt_blind` · `keysAt_blind` · `secondAt_blind`: K5's three runs, their forms as claims.
  `joinAt_blind` · `planesAt_blind`; at that seat: `joinAtt_blind` · `planesAtt_blind`;
  `guestsNone_blind`.
Limits: the last laws stand at the seat `seatCS` (it reads the four records of `verify-on-bytes` in
the state); the general ones take any seat that meets `SeatQuiet`. Laws on programs' commuting.
Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.BlindPlanes
import Johnson.Desc.First.Att.SeatW
import Johnson.Desc.First.Att.Guest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (seatCS parCOf ParC)

/-! ## an adding leaves each array's number of columns -/

/-- The numbers of columns. -/
def colsAt (trees : Array HTree) (j : Nat) : Option Nat := (trees[j]?).map (·.K)

theorem modify_cols (trees : Array HTree) (i j : Nat) (f : HTree → HTree)
    (hf : ∀ X, (f X).K = X.K) : colsAt (trees.modify i f) j = colsAt trees j := by
  unfold colsAt
  rw [Array.getElem?_modify]
  split
  · cases trees[j]? with
    | none => rfl
    | some X => simp [hf]
  · rfl

theorem pushEnt_cols (w : E) (trees trees' : Array HTree) (x : Ent) (j : Nat)
    (h : Fork.pushEnt w trees x = some trees') : colsAt trees' j = colsAt trees j := by
  unfold Fork.pushEnt at h
  split at h
  · injection h with h'
    rw [← h']
    exact modify_cols _ _ _ _ fun _ => rfl
  · simp at h

theorem pushRun_cols (k : E) (trees trees' : Array HTree) (r : Run2) (j : Nat)
    (h : pushRun k trees r = some trees') : colsAt trees' j = colsAt trees j := by
  unfold pushRun at h
  split at h
  · injection h with h'
    rw [← h']
    exact modify_cols _ _ _ _ fun _ => rfl
  · simp at h

/-- A fold of steps that each leave the numbers of columns. -/
theorem foldlM_cols {α : Type} (f : Array HTree → α → Option (Array HTree)) (j : Nat)
    (hf : ∀ a b x, f a x = some b → colsAt b j = colsAt a j) : ∀ (l : List α)
    (a b : Array HTree), l.foldlM f a = some b → colsAt b j = colsAt a j := by
  intro l
  induction l with
  | nil =>
    intro a b h
    simp [pure] at h
    rw [h]
  | cons x l ih =>
    intro a b h
    rw [List.foldlM_cons] at h
    obtain ⟨c, hc, hl⟩ := bind_some h
    rw [ih c b hl, hf a c x hc]

theorem push_cols (F G : Fork) (w : E) (a : Aff) (j : Nat) (h : F.push w a = some G) :
    colsAt G.trees j = colsAt F.trees j := by
  unfold Fork.push at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · rename_i trees' LS' ht _
      injection h with h'
      rw [← h']
      rw [← Array.foldlM_toList] at ht
      exact foldlM_cols _ j (fun a b x hx => pushEnt_cols w a b x j hx) _ _ _ ht
    · simp at h

theorem pushRuns_cols (F G : Fork) (k : E) (runs : Array Run2) (j : Nat)
    (h : F.pushRuns k runs = some G) : colsAt G.trees j = colsAt F.trees j := by
  unfold Fork.pushRuns at h
  obtain ⟨tr, ht, hG⟩ := map_some h
  rw [← hG]
  rw [← Array.foldlM_toList] at ht
  exact foldlM_cols _ j (fun a b x hx => pushRun_cols k a b x j hx) _ _ _ ht

theorem kapTake_trees (F : Fork) (c : Nat) (x : E × Fork) (h : F.kapTake c = some x) :
    x.2.trees = F.trees := by
  unfold Fork.kapTake at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨k, _, hk⟩ := map_some h
      rw [← hk]
    · split at h
      · obtain ⟨k, _, hk⟩ := map_some h
        rw [← hk]
      · simp at h

theorem kap_trees (F : Fork) (x : E × Fork) (h : F.kap = some x) : x.2.trees = F.trees := by
  unfold Fork.kap at h
  obtain ⟨y, hy, hx⟩ := map_some h
  rw [← hx]
  exact kapTake_trees F F.nClaim y hy

theorem addClaim_cols (F G : Fork) (cl : Claim) (j : Nat) (h : addClaim F cl = some G) :
    colsAt G.trees j = colsAt F.trees j := by
  unfold addClaim at h
  obtain ⟨x, hx, h1⟩ := bind_some h
  obtain ⟨k, _, h2⟩ := bind_some h1
  obtain ⟨P, hP, h3⟩ := bind_some h2
  rw [pushRuns_cols P G k cl.runs j h3, push_cols x.2 P k cl.form j hP, kap_trees F x hx]

theorem addAll_cols (j : Nat) : ∀ (cs : List Claim) (F G : Fork), addAll F cs = some G →
    colsAt G.trees j = colsAt F.trees j := by
  intro cs
  induction cs with
  | nil =>
    intro F G h
    simp [addAll, pure] at h
    rw [h]
  | cons c l ih =>
    intro F G h
    unfold addAll at h
    rw [List.foldlM_cons] at h
    obtain ⟨H, hH, hl⟩ := bind_some h
    rw [ih H G hl, addClaim_cols F H c j hH]

/-! ## K5's claims' seat at S is not turned by an adding -/

/-- The four readers that do not look at the ledger. -/
theorem seatCS_four (c : ParC) (t : S) (q : Part) :
    (seatCS c).pts (atS.set t q) = (seatCS c).pts t ∧
    (seatCS c).look (atS.set t q) = (seatCS c).look t ∧
    (seatCS c).pad (atS.set t q) = (seatCS c).pad t ∧
    (seatCS c).zk (atS.set t q) = (seatCS c).zk t := by
  cases hh : t.here with
  | between => simp [seatCS, atS, S.putLink, S.putFork, hh]
  | fin a => simp [seatCS, atS, S.putLink, S.putFork, hh]
  | mem a => simp [seatCS, atS, S.putLink, S.putFork, hh]
  | lay a => simp [seatCS, atS, S.putLink, S.putFork, hh]
  | att a => simp [seatCS, atS, S.putLink, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [seatCS, atS, S.putLink, S.putFork, hh, ho]
    | true => simp [seatCS, atS, S.putLink, S.putFork, hh, ho]

/-- The fifth: the number of columns of one array of the ledger. -/
theorem seatCS_cols (c : ParC) : Unturned (seatCS c).cols := by
  intro t p cs G hp hG
  have hc := addAll_cols c.iU3 cs p.F G hG
  unfold colsAt at hc
  cases hh : t.here with
  | between => simp [atS, S.link?, hh] at hp
  | fin a => simp [atS, S.link?, hh] at hp
  | mem a => simp [atS, S.link?, hh] at hp
  | lay a => simp [seatCS, atS, S.putLink, S.putFork, hh]
  | att a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at hp
    subst hp
    simp at hc
    simp [seatCS, atS, S.putLink, S.putFork, hh, hc]
  | head a =>
    cases ho : a.opened with
    | false => simp [seatCS, atS, S.putLink, S.putFork, hh, ho]
    | true => simp [seatCS, atS, S.putLink, S.putFork, hh, ho]

/-- **A seat of K5's claims whose five readers are not turned by an adding.** -/
structure SeatQuiet (seat : First.Att.P.SeatC S) : Prop where
  pts : Unturned seat.pts
  cols : Unturned seat.cols
  look : Unturned seat.look
  pad : Unturned seat.pad
  zk : Unturned seat.zk

/-- The seat that reads the four records of `verify-on-bytes` in the state is such a seat. -/
theorem seatCS_quiet (c : ParC) : SeatQuiet (seatCS c) where
  pts := fun t p _ G _ _ => (seatCS_four c t { p with F := G }).1
  cols := seatCS_cols c
  look := fun t p _ G _ _ => (seatCS_four c t { p with F := G }).2.1
  pad := fun t p _ G _ _ => (seatCS_four c t { p with F := G }).2.2.1
  zk := fun t p _ G _ _ => (seatCS_four c t { p with F := G }).2.2.2

theorem inOf_unturned (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Unturned (First.Att.P.inOf seat c) := by
  intro t p cs G hp hG
  unfold First.Att.P.inOf
  rw [h.pts t p cs G hp hG, h.look t p cs G hp hG, h.zk t p cs G hp hG, h.cols t p cs G hp hG]

/-- The calls' key forms, at any quiet seat. -/
theorem keysOfK_unturned (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Unturned (First.Att.P.keysOfK seat c) := by
  intro t p cs G hp hG
  unfold First.Att.P.keysOfK
  rw [inOf_unturned seat h c t p cs G hp hG, h.pad t p cs G hp hG]

/-- The readers for "planes", at any quiet seat. -/
theorem readersOfK_unturned (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Unturned (First.Att.P.readersOfK seat c) := by
  intro t p cs G hp hG
  unfold First.Att.P.readersOfK
  rw [inOf_unturned seat h c t p cs G hp hG]

/-! ## a run that reads the state, lays claims and leaves the state -/

/-- Such a run. -/
def readRun (read : S → Except String (List Claim)) : Fn S := fun _ s =>
  (read s).map fun l => (l, s)

theorem readRun_blind (read : S → Except String (List Claim)) (h : Unturned read) :
    Blind (addsOf atS atS_ok) (readRun read) where
  moves := by
    intro k t t' cs hadd
    obtain ⟨p, hp, hq⟩ := bind_some (show (atS.get? t).bind _ = some t' from hadd)
    obtain ⟨G, hG, ht'⟩ := map_some hq
    subst ht'
    simp only [readRun, h t p cs G hp hG]
    cases read t with
    | error e => rfl
    | ok l => exact ⟨_, rfl, hadd⟩
  keeps := by
    intro n t y cs hy
    simp only [readRun] at hy
    cases hr : read t with
    | error e => simp [hr, Except.map] at hy
    | ok l =>
      simp only [hr, Except.map] at hy
      injection hy with hy'
      rw [← hy']

/-- The forms of a run of K5's, as claims. -/
def asClaimsOf (name : String) (x : Option (List Aff × S)) : Except String (List Claim) :=
  (named name x).map fun y => y.1.map fun a => ({ form := a } : Claim)

/-- K5's "first", at a seat, its forms as claims. -/
def firstAt (seat : First.Att.P.SeatC S) (c : ParC) : Fn S :=
  readRun fun s => asClaimsOf "K5.first" (First.Att.P.firstK seat c s)

def keysAt (seat : First.Att.P.SeatC S) (c : ParC) : Fn S :=
  readRun fun s => asClaimsOf "K5.keys" (First.Att.P.keysK seat c s)

def secondAt (seat : First.Att.P.SeatC S) (c : ParC) : Fn S :=
  readRun fun s => asClaimsOf "K5.second" (First.Att.P.secondK seat c s)

/-- **K5's "first" is Blind, at any quiet seat.** -/
theorem firstAt_blind (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Blind (addsOf atS atS_ok) (firstAt seat c) :=
  readRun_blind _ fun t p cs G hp hG => by
    unfold First.Att.P.firstK
    rw [inOf_unturned seat h c t p cs G hp hG]
    cases First.Att.P.inOf seat c t with
    | none => rfl
    | some x =>
      obtain ⟨i, K⟩ := x
      cases hq : First.Att.P.Runs.firstRun i K <;>
        simp [hq, asClaimsOf, named, Except.map, bind, Option.bind]

/-- **K5's "keys" is Blind, at any quiet seat.** -/
theorem keysAt_blind (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Blind (addsOf atS atS_ok) (keysAt seat c) :=
  readRun_blind _ fun t p cs G hp hG => by
    unfold First.Att.P.keysK
    rw [keysOfK_unturned seat h c t p cs G hp hG]
    cases First.Att.P.keysOfK seat c t <;> rfl

/-- **K5's "second" is Blind, at any quiet seat.** -/
theorem secondAt_blind (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Blind (addsOf atS atS_ok) (secondAt seat c) :=
  readRun_blind _ fun t p cs G hp hG => by
    unfold First.Att.P.secondK
    rw [inOf_unturned seat h c t p cs G hp hG]
    cases First.Att.P.inOf seat c t with
    | none => rfl
    | some x =>
      obtain ⟨i, K⟩ := x
      cases hq : First.Att.P.Runs.secondRun i K <;>
        simp [hq, asClaimsOf, named, Except.map, bind, Option.bind]

/-- **K3's "join" with K5's keys is Blind, at any quiet seat.** -/
theorem joinAt_blind (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Blind (addsOf atS atS_ok) (joinCalls (First.Att.P.keysOfK seat c)) :=
  joinCalls_blind _ (keysOfK_unturned seat h c)

/-- **K3's "planes" with K5's readers is Blind, at any quiet seat.** -/
theorem planesAt_blind (lm : Nat) (seat : First.Att.P.SeatC S) (h : SeatQuiet seat) (c : ParC) :
    Blind (addsOf atS atS_ok) (planesCalls lm (First.Att.P.readersOfK seat c)) :=
  planesCalls_blind lm _ (readersOfK_unturned seat h c)

/-- At the seat `seatCS`: no premise. -/
theorem joinAtt_blind (A : Attention.Plan) :
    Blind (addsOf atS atS_ok) (joinCalls (First.Att.P.keysOfPS A)) :=
  joinAt_blind _ (seatCS_quiet _) _

theorem planesAtt_blind (lm : Nat) (A : Attention.Plan) :
    Blind (addsOf atS atS_ok) (planesCalls lm (First.Att.P.readersOfPS A)) :=
  planesAt_blind lm _ (seatCS_quiet _) _

/-- K3's "guests" where no guest is handed: it lays nothing and leaves the state. -/
def guestsNone : Fn S := readRun fun _ => .ok []

theorem guestsNone_blind : Blind (addsOf atS atS_ok) guestsNone :=
  readRun_blind _ fun _ _ _ _ _ _ => rfl

end VerifiableInference.Desc.K9
