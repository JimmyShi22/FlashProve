--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/TapeSteer.lean: TWO INVARIANTS ON TAPES (OnBytes/K/Kc/Flat.lean), in the manner
of Johnson/Top/H/Keep/TapeNZ.lean: (1) every round behind the open one that bears a given name, and
sends as many elements as a given list has, still holds just that list; (2) every drawn element of
every round has a given property. Every call on a tape keeps both. Definitions, statements and
proofs.

OBJECT: the ground functions recv, recvN, closeN, closeOne of OnBytes/K/Kc/Flat.lean, as the calls
  At and Evs of Johnson/Top/H/FlPort/Kit.lean name them.
USER: Johnson/Top/H/Keep/CEndSteer.lean.
LETTERS: nm a round's name, ys a list of elements, Q a property of elements: all free.
  It stands on no Block, State or K3 text.

Main names:
  Holds nm ys x: if the round x bears the name nm and sends as many elements as ys has, they are
    just ys. (Rounds of one name may send other numbers of elements: nothing is asked of these.)
  AllH, TailH: of every round of a tape; of every round but the first.
  at_tailH, evs_tailH: every call keeps TailH. closeOne_allH, closeN_allH: behind a call that closes
    a round, AllH.
  closeN_name: the round that closeN closes bears the name asked.
  read_all: where AllH holds, as many elements are read as ys has, and the round is then closed
    under the name nm with nothing drawn: what was read is ys.
  AllD Q: every drawn element of every round has Q. at_d, evs_d: kept; and every element that a call
    ans or ansNZ of the row returns has Q, and every element of a drawn point.

Limits. On tapes alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.FlPort.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

/-! ## A named round still holds its elements -/

def Holds (nm : String) (ys : List E) (x : FlatRound) : Prop :=
  x.name = some nm → x.sent.length = ys.length → x.sent = ys

def AllH (nm : String) (ys : List E) (t : Tape) : Prop := ∀ x ∈ t, Holds nm ys x

def TailH (nm : String) (ys : List E) (t : Tape) : Prop := ∀ x ∈ t.tail, Holds nm ys x

variable {nm : String} {ys : List E}

theorem AllH.tailH {t : Tape} (h : AllH nm ys t) : TailH nm ys t :=
  fun x hx => h x (List.mem_of_mem_tail hx)

theorem recv_tailH {c c' : Tape} {x : E} (h : recv c = some (x, c')) (hc : TailH nm ys c) :
    TailH nm ys c' := by
  unfold recv at h
  split at h
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hc
  · cases h

theorem recvLoop_tailH : ∀ (n : Nat) (a v : Array E) (c c' : Tape),
    recvLoop n a c = some (v, c') → TailH nm ys c → TailH nm ys c'
  | 0, a, v, c, c', h, hc => by
    unfold recvLoop at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hc
  | n + 1, a, v, c, c', h, hc => by
    unfold recvLoop at h
    split at h
    · rename_i x u hx
      exact recvLoop_tailH n _ v u c' h (recv_tailH hx hc)
    · cases h

theorem closeN_allH {name : String} {nz n : Nat} {c c' : Tape} {d : List E}
    (h : closeN name nz n c = some (d, c')) (hc : TailH nm ys c) : AllH nm ys c' := by
  obtain ⟨_, a, z, w, rfl⟩ := closeN_some h
  exact hc

theorem closeOne_allH {name : String} {nz : Nat} {c c' : Tape} {x : E}
    (h : closeOne name nz c = some (x, c')) (hc : TailH nm ys c) : AllH nm ys c' := by
  obtain ⟨a, z, w, rfl⟩ := closeOne_some h
  exact hc

theorem at_tailH {e : Ev} {c c' : Tape} (h : At e c c') (hc : TailH nm ys c) :
    TailH nm ys c' := by
  cases e with
  | sum x => exact recv_tailH h hc
  | ans r x => exact (closeOne_allH h hc).tailH
  | ansNZ r x => exact (closeOne_allH h hc).tailH
  | read n v => exact recvLoop_tailH n _ v c c' h hc
  | empty r =>
    have h' : (closeN r.name 0 0 c).map (fun x => ((), x.2)) = some ((), c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact (closeN_allH (d := y.1) (c' := y.2) hy hc).tailH
  | point r n v =>
    have h' : (closeN r.name 0 n c).map (fun x => (x.1.toArray, x.2)) = some (v, c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact (closeN_allH (d := y.1) (c' := y.2) hy hc).tailH

theorem evs_tailH : ∀ (l : List Ev) (c c' : Tape), Evs l c c' → TailH nm ys c → TailH nm ys c'
  | [], c, c', h, hc => by
    obtain rfl : c' = c := h
    exact hc
  | e :: l, c, c', h, hc => by
    obtain ⟨c1, h1, h2⟩ := h
    exact evs_tailH l c1 c' h2 (at_tailH h1 hc)

/-- The round that closeN closes bears the name asked. -/
theorem closeN_name {name : String} {nz n : Nat} {c c' : Tape} {d : List E}
    (h : closeN name nz n c = some (d, c')) : ∃ z w, c = ⟨some name, z, w, [], d⟩ :: c' := by
  unfold closeN at h
  split at h
  · split at h
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨rfl, _⟩, _⟩ := hb
      exact ⟨_, _, rfl⟩
    · cases h
  · cases h

/-- **What is read of a whole round that bears the name.** -/
theorem read_all {n : Nat} {v : Array E} {c c1 c2 : Tape} (hc : AllH nm ys c) (hn : n = ys.length)
    (h1 : recvN n c = some (v, c1)) (h2 : Fl.emptyOn nm c1 = some ((), c2)) : v.toList = ys := by
  have h' : (closeN nm 0 0 c1).map (fun x => ((), x.2)) = some ((), c2) := h2
  obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 h'
  obtain ⟨z, w, e⟩ := closeN_name (d := y.1) (c' := y.2) hy
  obtain ⟨hsz, rfl⟩ := recvN_some h1 e
  exact hc _ List.mem_cons_self rfl (by
    show v.toList.length = ys.length
    rw [Array.length_toList, hsz, hn])

/-! ## Every drawn element has a property -/

def AllD (Q : E → Prop) (t : Tape) : Prop := ∀ x ∈ t, ∀ d ∈ x.drawn, Q d

variable {Q : E → Prop}

theorem AllD.tail {x : FlatRound} {t : Tape} (h : AllD Q (x :: t)) : AllD Q t :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem recv_d {c c' : Tape} {x : E} (h : recv c = some (x, c')) (hc : AllD Q c) : AllD Q c' := by
  unfold recv at h
  split at h
  · rename_i a z w y s d t
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hc ⟨a, z, w, y :: s, d⟩ List.mem_cons_self
    · exact hc r (List.mem_cons_of_mem _ hr)
  · cases h

theorem recvLoop_d : ∀ (n : Nat) (a v : Array E) (c c' : Tape), recvLoop n a c = some (v, c') →
    AllD Q c → AllD Q c'
  | 0, a, v, c, c', h, hc => by
    unfold recvLoop at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hc
  | n + 1, a, v, c, c', h, hc => by
    unfold recvLoop at h
    split at h
    · rename_i x u hx
      exact recvLoop_d n _ v u c' h (recv_d hx hc)
    · cases h

theorem closeN_d {name : String} {nz n : Nat} {c c' : Tape} {d : List E}
    (h : closeN name nz n c = some (d, c')) (hc : AllD Q c) : AllD Q c' ∧ ∀ x ∈ d, Q x := by
  obtain ⟨_, a, z, w, rfl⟩ := closeN_some h
  exact ⟨hc.tail, hc _ List.mem_cons_self⟩

theorem closeOne_d {name : String} {nz : Nat} {c c' : Tape} {x : E}
    (h : closeOne name nz c = some (x, c')) (hc : AllD Q c) : AllD Q c' ∧ Q x := by
  obtain ⟨a, z, w, rfl⟩ := closeOne_some h
  exact ⟨hc.tail, hc _ List.mem_cons_self x (by simp)⟩

theorem at_d {e : Ev} {c c' : Tape} (h : At e c c') (hc : AllD Q c) : AllD Q c' := by
  cases e with
  | sum x => exact recv_d h hc
  | ans r x => exact (closeOne_d h hc).1
  | ansNZ r x => exact (closeOne_d h hc).1
  | read n v => exact recvLoop_d n _ v c c' h hc
  | empty r =>
    have h' : (closeN r.name 0 0 c).map (fun x => ((), x.2)) = some ((), c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact (closeN_d (d := y.1) (c' := y.2) hy hc).1
  | point r n v =>
    have h' : (closeN r.name 0 n c).map (fun x => (x.1.toArray, x.2)) = some (v, c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact (closeN_d (d := y.1) (c' := y.2) hy hc).1

/-- **Calls in a row.** -/
theorem evs_d : ∀ (l : List Ev) (c c' : Tape), Evs l c c' → AllD Q c →
    AllD Q c' ∧ (∀ r x, Ev.ans r x ∈ l → Q x) ∧ (∀ r x, Ev.ansNZ r x ∈ l → Q x) ∧
      ∀ r n v, Ev.point r n v ∈ l → ∀ x ∈ v.toList, Q x
  | [], c, c', h, hc => by
    obtain rfl : c' = c := h
    refine ⟨hc, fun _ _ hm => ?_, fun _ _ hm => ?_, fun _ _ _ hm => ?_⟩
    · exact absurd hm List.not_mem_nil
    · exact absurd hm List.not_mem_nil
    · exact absurd hm List.not_mem_nil
  | e :: l, c, c', h, hc => by
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨a, b1, b2, b3⟩ := evs_d l c1 c' h2 (at_d h1 hc)
    refine ⟨a, fun r x hm => ?_, fun r x hm => ?_, fun r n v hm => ?_⟩
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact (closeOne_d (nz := 0) h1 hc).2
      · exact b1 r x hm
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact (closeOne_d (nz := 1) h1 hc).2
      · exact b2 r x hm
    · rcases List.mem_cons.1 hm with rfl | hm
      · have h' : (closeN r.name 0 n c).map (fun x => (x.1.toArray, x.2)) = some (v, c1) := h1
        obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
        obtain ⟨rfl, -⟩ := Prod.mk.inj e
        intro x hx
        exact (closeN_d (d := y.1) (c' := y.2) hy hc).2 x (by simpa using hx)
      · exact b3 r n v hm

end Fo.Tp

#print axioms Fo.Tp.evs_tailH
#print axioms Fo.Tp.read_all
#print axioms Fo.Tp.evs_d
