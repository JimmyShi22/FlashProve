-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/LinesCap.lean: the ranges of the numbers in the first 32 lines of a parameter
file, from the reader's yes.

"readLines" (OnBytes/Params/File.lean) reads the 32 lines and refuses a number outside its range.
This file says which ranges a record of lines has that the reader returns.

Main names.
 - Gets x R: every value that the reader x returns, from whatever text, has the property R; with
   laws for pure, bind, refuse, demand and one.
 - StageCap, GroupCap, WorkCap, LinesCap: the ranges of a stage, of a group with its stages, of a
   line of work, and of all lines.
 - stagesOf_cap: the stages that stagesOf spells have their ranges, and there are a quarter as many
   as numbers.
 - **linesCap_of_read**: readLines pol = .ok (l, rest) gives LinesCap l.

Limits. Not every test of the reader is in LinesCap: that slots is a power of two, that salt is a
multiple of 8, the two tests that compare groups, that the last stage alone has k = 0, and "the
table's radius is 0" are left out; so are the version line, the
spelling of the numbers, and that a group has at least one stage. Nothing on the text behind the
lines. The program does not import this file.

-/
import OnBytes.Params.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-! ## What a reader's values have -/

/-- Every value that the reader returns has the property R. -/
def Gets {α : Type} (x : Reading α) (R : α → Prop) : Prop :=
  ∀ t a t', x t = .ok (a, t') → R a

theorem gets_any {α : Type} (x : Reading α) : Gets x fun _ => True := fun _ _ _ _ => trivial

theorem gets_pure {α : Type} {R : α → Prop} {a : α} (h : R a) :
    Gets (pure a : Reading α) R := by
  intro t b t' e
  have e2 : (Except.ok (a, t) : Except String (α × List UInt8)) = .ok (b, t') := e
  cases e2
  exact h

theorem gets_refuse {α : Type} (why : String) (R : α → Prop) : Gets (refuse why) R := by
  intro t a t' e
  have e2 : (Except.error why : Except String (α × List UInt8)) = .ok (a, t') := e
  cases e2

theorem gets_bind {α β : Type} {x : Reading α} {f : α → Reading β} {R : α → Prop}
    {R' : β → Prop} (h1 : Gets x R) (h2 : ∀ a, R a → Gets (f a) R') : Gets (x >>= f) R' := by
  intro t b t' e
  have e1 : (x t >>= fun p => f p.1 p.2) = .ok (b, t') := e
  cases hx : x t with
  | error er =>
    rw [hx] at e1
    have e2 : (Except.error er : Except String (β × List UInt8)) = .ok (b, t') := e1
    cases e2
  | ok p =>
    rw [hx] at e1
    exact h2 p.1 (h1 t p.1 p.2 hx) p.2 b t' e1

theorem gets_demand (b : Bool) (why : String) : Gets (demand b why) fun _ => b = true := by
  intro t a t' e
  cases b with
  | true => rfl
  | false =>
    have e2 : (Except.error why : Except String (Unit × List UInt8)) = .ok (a, t') := e
    cases e2

/-- The one number of a line lies in its range. -/
theorem gets_one (head : String) (lo hi : Nat) :
    Gets (one head lo hi) fun x => lo ≤ x ∧ x ≤ hi := by
  unfold one
  refine gets_bind (gets_any _) fun v _ => ?_
  split
  · rename_i x
    refine gets_bind (gets_demand _ _) fun _ hd => gets_pure ?_
    simpa using hd
  · exact gets_refuse _ _

/-! ## The ranges -/

/-- The ranges of a stage. -/
structure StageCap (g : StageLine) : Prop where
  k : g.k ≤ 8
  h : g.h ≤ g.k
  logN : g.logN ≤ 32
  mask : g.maskLogN ≤ g.logN

/-- The ranges of a group and of its stages. -/
structure GroupCap (g : GroupLine) : Prop where
  logN : g.logN ≤ 32
  logL : g.logL < g.logN
  mask : g.maskLogN ≤ g.logN
  maskL : g.maskLogL < g.maskLogN
  count : g.stages.length ≤ 8
  stages : ∀ s ∈ g.stages, StageCap s

/-- The ranges of a line of work, at the target sec. -/
structure WorkCap (sec : Nat) (w : Work) : Prop where
  request : w.request ≤ 58 ∧ w.request < sec
  shared : w.shared ≤ 58 ∧ w.shared < sec
  once : w.once ≤ 58 ∧ w.once < sec

/-- **The ranges of the 32 lines.** -/
structure LinesCap (l : Lines) : Prop where
  sec : 1 ≤ l.sec ∧ l.sec ≤ 256
  reading : 1 ≤ l.reading ∧ l.reading ≤ 2
  rowcost : 1 ≤ l.rowcost ∧ l.rowcost ≤ 2
  slots : 1 ≤ l.slots ∧ l.slots ≤ 2 ^ 20
  answers : 1 ≤ l.answers ∧ l.answers ≤ 4
  workField : WorkCap l.sec l.workField
  workSample : WorkCap l.sec l.workSample
  workCloseness : WorkCap l.sec l.workCloseness
  workPositions : WorkCap l.sec l.workPositions
  workSmallness : WorkCap l.sec l.workSmallness
  salt : 40 ≤ l.salt ∧ l.salt ≤ 64
  listed : l.listed ≤ 8
  link : GroupCap l.link
  folded : GroupCap l.folded
  omega : GroupCap l.omega
  own : GroupCap l.own
  onceFolded : GroupCap l.onceFolded
  onceOmega : GroupCap l.onceOmega
  onceOwn : GroupCap l.onceOwn
  onceRanges : GroupCap l.onceRanges
  part : 1 ≤ l.rangesPart ∧ l.rangesPart ≤ 40
  tLogN : l.tableLogN ≤ 32
  tRows : l.tableRowsLog ≤ 20
  tData : l.tableData ≠ 0
  tFit : l.tableData + l.tableRandom < 2 ^ l.tableLogN
  block : l.blockLog ≤ 40
  rowsBlock : l.tableRowsLog ≤ l.blockLog

/-! ## The readers of a line -/

/-- The stages that the numbers spell have their ranges; four numbers a stage. n is any bound on the
list's length; it serves the induction alone. -/
theorem stagesOf_cap : ∀ (n : Nat) (ns : List Nat) (st : List StageLine), ns.length ≤ n →
    stagesOf ns = some st → (∀ s ∈ st, StageCap s) ∧ 4 * st.length = ns.length := by
  intro n
  induction n with
  | zero =>
    intro ns st hn h
    have e : ns = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)
    subst e
    simp [stagesOf] at h
    subst h
    exact ⟨fun s hs => (List.not_mem_nil hs).elim, rfl⟩
  | succ n ih =>
    intro ns st hn h
    match ns, hn, h with
    | [], _, h =>
      simp [stagesOf] at h
      subst h
      exact ⟨fun s hs => (List.not_mem_nil hs).elim, rfl⟩
    | k :: hh :: m :: nz :: rest, hn, h =>
      unfold stagesOf at h
      by_cases hc : (decide (k ≤ 8) && decide (hh ≤ k) && decide (m ≤ mostGroupLogN) &&
          decide (nz ≤ m) && (if rest.isEmpty then k == 0 else k != 0)) = true
      · rw [if_pos hc] at h
        cases hr : stagesOf rest with
        | none =>
          rw [hr] at h
          cases h
        | some st' =>
          rw [hr] at h
          have e : st = ⟨k, hh, m, nz⟩ :: st' := (Option.some.inj h).symm
          subst e
          have hl : rest.length ≤ n := by
            simp only [List.length_cons] at hn
            omega
          obtain ⟨c1, c2⟩ := ih rest st' hl hr
          simp only [Bool.and_eq_true, decide_eq_true_eq, mostGroupLogN] at hc
          refine ⟨fun s hs => ?_, ?_⟩
          · rcases List.mem_cons.1 hs with rfl | hs'
            · exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2⟩
            · exact c1 s hs'
          · simp only [List.length_cons]
            omega
      · rw [if_neg hc] at h
        cases h
    | [_], _, h => simp [stagesOf] at h
    | [_, _], _, h => simp [stagesOf] at h
    | [_, _, _], _, h => simp [stagesOf] at h

/-- A group's two lines. -/
theorem gets_groupLines (name : String) : Gets (groupLines name) GroupCap := by
  unfold groupLines
  refine gets_bind (gets_any _) fun v _ => ?_
  split
  · rename_i j n l nz lz
    refine gets_bind (gets_demand _ _) fun _ h1 => ?_
    refine gets_bind (gets_any _) fun s _ => ?_
    refine gets_bind (gets_demand _ _) fun _ h2 => ?_
    split
    · rename_i st hst
      refine gets_pure ?_
      obtain ⟨c1, c2⟩ := stagesOf_cap s.length s st (Nat.le_refl _) hst
      simp only [Bool.and_eq_true, decide_eq_true_eq, mostGroupLogN] at h1 h2
      have h32 := h2.2
      have h8 : st.length ≤ 8 := by omega
      exact ⟨h1.1.1.1.2, h1.1.1.2, h1.1.2, h1.2, h8, c1⟩
    · exact gets_refuse _ _
  · exact gets_refuse _ _

/-- A line of work. -/
theorem gets_workLine (head : String) (sec : Nat) : Gets (workLine head sec) (WorkCap sec) := by
  unfold workLine
  refine gets_bind (gets_any _) fun v _ => ?_
  split
  · rename_i a b c
    refine gets_bind (gets_demand _ _) fun _ hd => gets_pure ?_
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq, and_true] at hd
    exact ⟨hd.1, hd.2.1, hd.2.2⟩
  · exact gets_refuse _ _

/-! ## All lines -/

/-- The 32 lines. -/
theorem gets_lines : Gets lines LinesCap := by
  unfold lines
  refine gets_bind (gets_any _) fun _ _ => ?_
  refine gets_bind (gets_one _ _ _) fun sec hsec => ?_
  refine gets_bind (gets_one _ _ _) fun reading hreading => ?_
  refine gets_bind (gets_one _ _ _) fun rowcost hrowcost => ?_
  refine gets_bind (gets_one _ _ _) fun slots hslots => ?_
  refine gets_bind (gets_any _) fun _ _ => ?_
  refine gets_bind (gets_one _ _ _) fun answers hanswers => ?_
  refine gets_bind (gets_one _ _ _) fun record hrecord => ?_
  refine gets_bind (gets_workLine _ _) fun wf hwf => ?_
  refine gets_bind (gets_workLine _ _) fun ws hws => ?_
  refine gets_bind (gets_workLine _ _) fun wc hwc => ?_
  refine gets_bind (gets_workLine _ _) fun wp hwp => ?_
  refine gets_bind (gets_workLine _ _) fun wm hwm => ?_
  refine gets_bind (gets_one _ _ _) fun salt hsalt => ?_
  refine gets_bind (gets_any _) fun _ _ => ?_
  refine gets_bind (gets_one _ _ _) fun listed hlisted => ?_
  refine gets_bind (gets_groupLines _) fun g0 hg0 => ?_
  refine gets_bind (gets_groupLines _) fun g1 hg1 => ?_
  refine gets_bind (gets_groupLines _) fun g2 hg2 => ?_
  refine gets_bind (gets_groupLines _) fun g3 hg3 => ?_
  refine gets_bind (gets_groupLines _) fun g4 hg4 => ?_
  refine gets_bind (gets_groupLines _) fun g5 hg5 => ?_
  refine gets_bind (gets_groupLines _) fun g6 hg6 => ?_
  refine gets_bind (gets_groupLines _) fun g7 hg7 => ?_
  refine gets_bind (gets_one _ _ _) fun part hpart => ?_
  refine gets_bind (gets_any _) fun _ _ => ?_
  refine gets_bind (gets_any _) fun _ _ => ?_
  refine gets_bind (gets_any _) fun v _ => ?_
  split
  · rename_i b n i m e w
    refine gets_bind (gets_demand _ _) fun _ h1 => ?_
    refine gets_bind (gets_demand _ _) fun _ h2 => gets_pure ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1 h2
    exact ⟨hsec, hreading, hrowcost, hslots, hanswers, hwf, hws, hwc, hwp, hwm, hsalt,
      hlisted.2, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hpart, h1, h2.1.1.1.1.1,
      h2.1.1.1.1.2, h2.1.1.1.2, h2.1.2, h2.2⟩
  · exact gets_refuse _ _

/-- **The reader's yes gives the ranges.** -/
theorem linesCap_of_read {pol rest : ByteArray} {l : Lines} (h : readLines pol = .ok (l, rest)) :
    LinesCap l := by
  unfold readLines at h
  cases hx : lines pol.toList with
  | error er =>
    rw [hx] at h
    cases h
  | ok p =>
    rw [hx] at h
    have e : l = p.1 := by
      have := Except.ok.inj h
      exact (congrArg Prod.fst this).symm
    rw [e]
    exact gets_lines pol.toList p.1 p.2 hx

end OnBytes.Params

#print axioms OnBytes.Params.gets_bind
#print axioms OnBytes.Params.stagesOf_cap
#print axioms OnBytes.Params.gets_groupLines
#print axioms OnBytes.Params.gets_lines
#print axioms OnBytes.Params.linesCap_of_read
