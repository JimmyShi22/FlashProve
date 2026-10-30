-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LeftItem.lean: THE TABLE OF JOINTS' PUBLIC ITEM "WHAT THE LOOKUP ON THE
CALLS LEFT" (Pub.left m, Johnson/Desc/First/Borders.lean): ITS WORDING, one definition for all
three sorts of link, at the kind's own parameters; that at each sort of link it is the sharp promise
K3LeftAt (Johnson/Top/H/K3LeftStatement.lean) AT THE PLAN's LETTERS; and that a yes of the kind's
decide makes it. Definitions of type Prop, statements and proofs. Ties: no error term. NO SOUNDNESS
IS CLAIMED.

OBJECT: the record First.S behind the lookup's block at a link's calls; Desc.K3.block's decide at
  seatCalls claim.
Used by K03LeftQ.lean, K03ReachedAt.lean, K3At.lean (Johnson/Desc/First/Look/) and others.
LETTERS: p: the kind's parameters (placeAt X i false's value); X, i free.


Compiled with the whole library.

Main names:
  `k3LeftItem p s`: the parameters make a shape h, and K3LeftAt holds at the record's two readers
    fork? and lookHeard?, at h, p.lm, p.first, and at Q := LeftQ p.ns; AND LeavesBare s.
  `LeavesBare s`: the starting form of the sumcheck over the leaves, in what was heard, names no
    entry of a virtual row (a calling kind's runs want it beside K3Left's cEndEnts; it stands
    OUTSIDE K3Left and K3LeftAt).
  `LeftQ n F`: WHAT IS KEPT OF THE LEDGER IN FRONT: what the promise in front of the lookup's block
    says of it (the table's ledger m, freeAbove m): sized; n slots; free from its next free number
    on. (A calling kind's law wants the room in front; what the hearing leaves cannot give it
    back.)
  `k3LeftItemAt X i s`: the same at placeAt X i false's value. WHERE placeAt GIVES NOTHING, OR THE
    PARAMETERS MAKE NO SHAPE, IT IS FALSE: there no block of the kind stands (K3.theOwn gives none)
    or none says yes (K3.hear gives nothing): so nobody is asked to make it there; a law that has it
    as a premise says nothing there.
  `k3LeftOnItem p s`, `k3LeftOnItemAt X i s`: THE ITEM Pub.leftOn m: the like from K3LeftOn, at the
    same p and the same Q. `leftOn_of_left`: the sharp item gives it. `leftOn_stays`: it stands at
    every later record at which what was heard stays and the ledger is later and has its sizes.
    `leftOn_lay | leftOn_att | leftOn_head`: at the plan's letters, both ways.
  `leftAt_mono`, `leftAt_ns`: Q may be weakened; and "F has n slots" may be ADDED to Q from the
    ledger IN HAND alone: the hearing keeps the number of slots.
  `left_lay | left_att | left_head`: wherever publicOf returns: k3LeftItemAt X i s IS K3LeftAt at
    X.y.fo, X.y.h.lmb, 0 | a.fs, a.S.cf.lmb, 0 | X.HLy.fs, X.hS.lmbH, 0, at LeftQ of the plan's
    number of slots, AND LeavesBare s: both ways. `left_lay_ns`: at Q F := "F has the plan's number
    of slots": one way.
  `k3_calls_left_any`: behind a yes of the kind's decide, from a sized ledger of which Q holds:
    K3LeftAt at Q. `k3_calls_leavesBare`: and LeavesBare. `k3_calls_leftItem`: so the item, from a
    ledger of which LeftQ p.ns holds.

Limits. A Prop, no Bool: the rounds and the ledger in front are not in the record. The head's second
reader (look?) is not spoken of. Nothing on who pays LeftQ in front: the table's items ledger m and
freeAbove m.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3CEnd
import Johnson.Top.H.K3DecideMore
import Johnson.Desc.First.Look.K3LeftRule
import Johnson.Top.H.Keep.K3Named
import Johnson.Desc.First.Look.K3PlaceLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look

/-- **WHAT THE ITEM KEEPS OF THE LEDGER IN FRONT OF THE LOOKUP**: what the promise in front of the
lookup's block says of it: it has its sizes; it has n slots; every slot from its next free number on
is free. -/
def LeftQ (n : ℕ) (F : Fork) : Prop :=
  OnBytes.PscRun.Sized F ∧ F.ns = n ∧ ∀ j, F.next ≤ j → j < F.ns → F.gotF.getD j true = false

/-- What was heard at the calls holds a sumcheck over the leaves whose starting form names no entry
of a virtual row. It reads what was heard alone: so it rides wherever that stays. -/
def LeavesBare (s : Desc.First.S) : Prop :=
  ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]

/-- **WHAT THE LOOKUP ON THE CALLS LEFT, at the kind's parameters.** -/
def k3LeftItem (p : Desc.First.Look.P) (s : Desc.First.S) : Prop :=
  (∃ h, p.shape = some h ∧
    K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) h p.lm
      p.first (LeftQ p.ns) s) ∧ LeavesBare s

/-- **The same at link i of a public record.** -/
def k3LeftItemAt (X : Verify.Public) (i : ℕ) (s : Desc.First.S) : Prop :=
  ∃ p, placeAt X i false = some p ∧ k3LeftItem p s

/-- **THE FORM THAT STANDS AT EVERY LATER RECORD (Pub.leftOn m), at the same parameters.** -/
def k3LeftOnItem (p : Desc.First.Look.P) (s : Desc.First.S) : Prop :=
  (∃ h, p.shape = some h ∧
    K3LeftOn (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) h p.lm
      p.first (LeftQ p.ns) s) ∧ LeavesBare s

/-- **The same at link i of a public record.** -/
def k3LeftOnItemAt (X : Verify.Public) (i : ℕ) (s : Desc.First.S) : Prop :=
  ∃ p, placeAt X i false = some p ∧ k3LeftOnItem p s

/-- The sharp item gives the other, at the same record. -/
theorem leftOn_of_left {p : Desc.First.Look.P} {s : Desc.First.S} (L : k3LeftItem p s) :
    k3LeftOnItem p s := by
  obtain ⟨⟨h, e, L⟩, hb⟩ := L
  exact ⟨⟨h, e, k3LeftOnOfAt _ _ _ _ _ _ _ _ L⟩, hb⟩

/-- **The item stands at every later record** at which what was heard stays and the ledger is later
and has its sizes. -/
theorem leftOn_stays {p : Desc.First.Look.P} {s t : Desc.First.S} {Fs Ft : Fork}
    (hh : t.lookHeard? = s.lookHeard?) (hs : s.fork? = some Fs) (ht : t.fork? = some Ft)
    (hl : _root_.Fo.Later Fs Ft) (hz : OnBytes.PscRun.Sized Ft) (L : k3LeftOnItem p s) :
    k3LeftOnItem p t := by
  obtain ⟨⟨h, e, L⟩, hb⟩ := L
  exact ⟨⟨h, e, k3LeftOnStays _ _ _ _ _ _ _ s t Fs Ft hh hs ht hl hz L⟩,
    fun g hg => hb g (hh.symm.trans hg)⟩

section
variable {S : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
  {h : Forest.Shape} {lm first : ℕ} {Q Q' : Fork → Prop} {s : S}

/-- Q may be weakened. -/
theorem leftAt_mono (hQ : ∀ F, Q F → Q' F) (L : K3LeftAt fork heard h lm first Q s) :
    K3LeftAt fork heard h lm first Q' s := by
  obtain ⟨F, F', g, rs, q, a, b, c, d⟩ := L
  exact ⟨F, F', g, rs, hQ F q, a, b, c, d⟩

/-- **The number of slots of the ledger in front is that of the ledger in hand.** -/
theorem leftAt_ns {G : Fork} {n : ℕ} (hG : fork s = some G) (hn : G.ns = n)
    (L : K3LeftAt fork heard h lm first Q s) :
    K3LeftAt fork heard h lm first (fun F => Q F ∧ F.ns = n) s := by
  obtain ⟨F, F', g, rs, q, a, b, c, d⟩ := L
  obtain rfl : F' = G := Option.some.inj (d.symm.trans hG)
  exact ⟨F, F', g, rs, ⟨q, b.padLeft.rest.2.1.symm.trans hn⟩, a, b, c, d⟩

end

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ}
  {s : Desc.First.S}

/-- Where the group's plan is there, so is the place. -/
theorem placeAt_lay_some {hp : Layer.HPlan2} (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) = 0) (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) :
    ∃ p, placeAt X i false = some p := by
  cases e : lookAt X i false with
  | some x => exact ⟨_, placeAt_iff.2 ⟨x, e, rfl⟩⟩
  | none =>
    exfalso
    unfold lookAt at e
    dsimp only at e
    rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hg] at e
    simp at e

theorem placeAt_att_some {a : Attention.Plan} (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) ≠ 0) (hg : X.A[i / (if X.p4 then 2 else 1)]? = some a) :
    ∃ p, placeAt X i false = some p := by
  cases e : lookAt X i false with
  | some x => exact ⟨_, placeAt_iff.2 ⟨x, e, rfl⟩⟩
  | none =>
    exfalso
    unfold lookAt at e
    dsimp only at e
    rw [if_neg (by simpa using hn), if_neg (by simpa using h0), hg] at e
    simp at e

theorem placeAt_head_some : ∃ p, placeAt X ((if X.p4 then 2 else 1) * X.NGr) false = some p := by
  cases e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false with
  | some x => exact ⟨_, placeAt_iff.2 ⟨x, e, rfl⟩⟩
  | none =>
    exfalso
    unfold lookAt at e
    dsimp only at e
    rw [if_pos (by simp)] at e
    simp at e

/-- **AT A LAYERS' LINK THE ITEM IS THE SHARP PROMISE AT THE PLAN's LETTERS.** -/
theorem left_lay {hp : Layer.HPlan2} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) :
    k3LeftItemAt X i s ↔
      K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) X.y.fo
        X.y.h.lmb 0 (LeftQ hp.ns) s ∧ LeavesBare s := by
  constructor
  · rintro ⟨p, e, ⟨h1, e1, L⟩, hb⟩
    obtain ⟨hp', hg', a1, a2, a3, a4⟩ := place_lay h e hn h0
    obtain rfl : hp' = hp := Option.some.inj (hg'.symm.trans hg)
    obtain rfl : h1 = X.y.fo := Option.some.inj (e1.symm.trans a1)
    rw [a2, a3, a4] at L
    exact ⟨L, hb⟩
  · rintro ⟨L, hb⟩
    obtain ⟨p, e⟩ := placeAt_lay_some hn h0 hg
    obtain ⟨hp', hg', a1, a2, a3, a4⟩ := place_lay h e hn h0
    obtain rfl : hp' = hp := Option.some.inj (hg'.symm.trans hg)
    refine ⟨p, e, ⟨X.y.fo, a1, ?_⟩, hb⟩
    rw [a2, a3, a4]
    exact L

/-- So the calling kind's own form at a layers' link: of the ledger in front its number of slots
alone. ONE WAY. -/
theorem left_lay_ns {hp : Layer.HPlan2} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) (L : k3LeftItemAt X i s) :
    K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) X.y.fo
      X.y.h.lmb 0 (fun F => F.ns = hp.ns) s :=
  leftAt_mono (fun _ q => q.2.1) ((left_lay h hn h0 hg).1 L).1

/-- **At an attention link.** -/
theorem left_att {a : Attention.Plan} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0)
    (hg : X.A[i / (if X.p4 then 2 else 1)]? = some a) :
    k3LeftItemAt X i s ↔
      K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) a.fs
        a.S.cf.lmb 0 (LeftQ a.ns) s ∧ LeavesBare s := by
  constructor
  · rintro ⟨p, e, ⟨h1, e1, L⟩, hb⟩
    obtain ⟨a', hg', a1, a2, a3, a4⟩ := place_att h e hn h0
    obtain rfl : a' = a := Option.some.inj (hg'.symm.trans hg)
    obtain rfl : h1 = a'.fs := Option.some.inj (e1.symm.trans a1)
    rw [a2, a3, a4] at L
    exact ⟨L, hb⟩
  · rintro ⟨L, hb⟩
    obtain ⟨p, e⟩ := placeAt_att_some hn h0 hg
    obtain ⟨a', hg', a1, a2, a3, a4⟩ := place_att h e hn h0
    obtain rfl : a' = a := Option.some.inj (hg'.symm.trans hg)
    refine ⟨p, e, ⟨a'.fs, a1, ?_⟩, hb⟩
    rw [a2, a3, a4]
    exact L

/-- **At the head's link.** -/
theorem left_head (h : Verify.publicOf pol KL layout = .ok X) :
    k3LeftItemAt X ((if X.p4 then 2 else 1) * X.NGr) s ↔
      K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) X.HLy.fs
        X.hS.lmbH 0 (LeftQ X.H.ns) s ∧ LeavesBare s := by
  constructor
  · rintro ⟨p, e, ⟨h1, e1, L⟩, hb⟩
    obtain ⟨a1, a2, a3, a4⟩ := place_head h e
    obtain rfl : h1 = X.HLy.fs := Option.some.inj (e1.symm.trans a1)
    rw [a2, a3, a4] at L
    exact ⟨L, hb⟩
  · rintro ⟨L, hb⟩
    obtain ⟨p, e⟩ := placeAt_head_some (X := X)
    obtain ⟨a1, a2, a3, a4⟩ := place_head h e
    refine ⟨p, e, ⟨X.HLy.fs, a1, ?_⟩, hb⟩
    rw [a2, a3, a4]
    exact L

/-- **The later form at a layers' link.** -/
theorem leftOn_lay {hp : Layer.HPlan2} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) :
    k3LeftOnItemAt X i s ↔
      K3LeftOn (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) X.y.fo
        X.y.h.lmb 0 (LeftQ hp.ns) s ∧ LeavesBare s := by
  constructor
  · rintro ⟨p, e, ⟨h1, e1, L⟩, hb⟩
    obtain ⟨hp', hg', a1, a2, a3, a4⟩ := place_lay h e hn h0
    obtain rfl : hp' = hp := Option.some.inj (hg'.symm.trans hg)
    obtain rfl : h1 = X.y.fo := Option.some.inj (e1.symm.trans a1)
    rw [a2, a3, a4] at L
    exact ⟨L, hb⟩
  · rintro ⟨L, hb⟩
    obtain ⟨p, e⟩ := placeAt_lay_some hn h0 hg
    obtain ⟨hp', hg', a1, a2, a3, a4⟩ := place_lay h e hn h0
    obtain rfl : hp' = hp := Option.some.inj (hg'.symm.trans hg)
    refine ⟨p, e, ⟨X.y.fo, a1, ?_⟩, hb⟩
    rw [a2, a3, a4]
    exact L

/-- The later form at an attention link. -/
theorem leftOn_att {a : Attention.Plan} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0)
    (hg : X.A[i / (if X.p4 then 2 else 1)]? = some a) :
    k3LeftOnItemAt X i s ↔
      K3LeftOn (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) a.fs
        a.S.cf.lmb 0 (LeftQ a.ns) s ∧ LeavesBare s := by
  constructor
  · rintro ⟨p, e, ⟨h1, e1, L⟩, hb⟩
    obtain ⟨a', hg', a1, a2, a3, a4⟩ := place_att h e hn h0
    obtain rfl : a' = a := Option.some.inj (hg'.symm.trans hg)
    obtain rfl : h1 = a'.fs := Option.some.inj (e1.symm.trans a1)
    rw [a2, a3, a4] at L
    exact ⟨L, hb⟩
  · rintro ⟨L, hb⟩
    obtain ⟨p, e⟩ := placeAt_att_some hn h0 hg
    obtain ⟨a', hg', a1, a2, a3, a4⟩ := place_att h e hn h0
    obtain rfl : a' = a := Option.some.inj (hg'.symm.trans hg)
    refine ⟨p, e, ⟨a'.fs, a1, ?_⟩, hb⟩
    rw [a2, a3, a4]
    exact L

/-- The later form at the head's link. -/
theorem leftOn_head (h : Verify.publicOf pol KL layout = .ok X) :
    k3LeftOnItemAt X ((if X.p4 then 2 else 1) * X.NGr) s ↔
      K3LeftOn (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) X.HLy.fs
        X.hS.lmbH 0 (LeftQ X.H.ns) s ∧ LeavesBare s := by
  constructor
  · rintro ⟨p, e, ⟨h1, e1, L⟩, hb⟩
    obtain ⟨a1, a2, a3, a4⟩ := place_head h e
    obtain rfl : h1 = X.HLy.fs := Option.some.inj (e1.symm.trans a1)
    rw [a2, a3, a4] at L
    exact ⟨L, hb⟩
  · rintro ⟨L, hb⟩
    obtain ⟨p, e⟩ := placeAt_head_some (X := X)
    obtain ⟨a1, a2, a3, a4⟩ := place_head h e
    refine ⟨p, e, ⟨X.HLy.fs, a1, ?_⟩, hb⟩
    rw [a2, a3, a4]
    exact L

end

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **A YES OF THE KIND's decide MAKES THE SHARP PROMISE, at any Q that holds of the ledger in
front.** -/
theorem k3_calls_left_any (hs : p.shape = some h) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hz : OnBytes.PscRun.Sized F) (Q : Fork → Prop)
    (hQ : Q F) :
    K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) h p.lm
      p.first Q s' := by
  obtain ⟨F1, F', g, hF1, hF', hg, hL⟩ :=
    k3LeavesAtCalls Cl claim piece laid before p guests h hs Cb.Gl.E Reading.gl p.lm s s' rs cols
      hw hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  exact ⟨F, F', g, _, hQ,
    decide_first (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols F hF1 hd,
    hL hz, hg, hF'⟩

/-- **And what it leaves as heard has a bare starting form at the leaves.** -/
theorem k3_calls_leavesBare
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hz : OnBytes.PscRun.Sized F) : LeavesBare s' := by
  obtain ⟨F1, x, hF1, hn, e, hN⟩ :=
    decide_named (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : s'.lookHeard? = some x.1 := by
    rw [e]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn
  intro g hg
  obtain rfl : x.1 = g := Option.some.inj (hg1.symm.trans hg)
  exact _root_.Fo.Tp.bare_ents (hN hz).start.1

/-- **So it makes the item.** -/
theorem k3_calls_leftItem (hs : p.shape = some h) (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hQ : LeftQ p.ns F) : k3LeftItem p s' :=
  ⟨⟨h, hs, k3_calls_left_any claim piece laid before p guests s s' rs cols hs hw hd hF hQ.1 _ hQ⟩,
    k3_calls_leavesBare claim piece laid before p guests s s' rs cols hd hF hQ.1⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.leftAt_ns
#print axioms VerifiableInference.OnPublicFiles.left_lay
#print axioms VerifiableInference.OnPublicFiles.left_lay_ns
#print axioms VerifiableInference.OnPublicFiles.left_att
#print axioms VerifiableInference.OnPublicFiles.left_head
#print axioms VerifiableInference.OnPublicFiles.leftOn_lay
#print axioms VerifiableInference.OnPublicFiles.leftOn_att
#print axioms VerifiableInference.OnPublicFiles.leftOn_head
#print axioms VerifiableInference.OnPublicFiles.leftOn_of_left
#print axioms VerifiableInference.OnPublicFiles.leftOn_stays
#print axioms VerifiableInference.OnPublicFiles.k3_calls_left_any
#print axioms VerifiableInference.OnPublicFiles.k3_calls_leavesBare
#print axioms VerifiableInference.OnPublicFiles.k3_calls_leftItem
