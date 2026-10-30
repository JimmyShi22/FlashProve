-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HitemsStill.lean: `TableOwes.hitems` (LinkTable.lean), AN ITEM AT A
TIME, FOR EVERY ENTRY WHOSE RUN LEAVES THE RECORD AS IT IS (`Still`, StillRun.lean), AT THE READERS
OF THE LINK ITSELF (`K9.readersOfLink`, Johnson/Desc/First/Batch/ReadersOfLink.lean: «the reader is
the run itself»). Theorems.

Why. The table says a run's forms through a reader: a function of the record. Its filling at a link
calls the very run that the link's hearing block states, at the record at hand, with no claim in
front. The kinds' laws say a run's values through forms that are read off what is fixed before the
draw. For a run that hands the record back and whose claims are the plain claims of such forms, the
two are one list, and by WorldsMeet.lean each form has one worth in the two worlds.

What is said.
  `lateOf_self`: no slot is late between a ledger and itself. `ItemAt`: one item's clause in its
    stronger form (an equation of lists); `ItemIn`: the clause as `TableOwes.hitems` asks it:
    an inclusion: each value of the item's forms is among the runs'
    values (at the approximate range proof's item the equation is false by a count: its run has four
    terms more than its reader lists); `ItemAt.toIn`; `hitems_of_items`. `reader_still`: a still
    run's claims are the
    law's forms, and it leaves no late slot. `reader_of_run`: the reader of the link, opened at the
    run that stands at the entry. `run_of_reader`: **the converse: where the reader's second hole
    says nothing, whatever the reader gives comes out of the run itself: the run says yes there,
    with no claim in front.** `reader_of_formsIn`, `named_of_formsIn`: what the table's public
    test's yes says. `item_still`: the clause at a still entry, from the run's yes at the statement.
    `item_still_in`: **the clause at a still entry, from: the entry is of the order and a run stands
    there, under a still run; the table of terms there is `plainTm (valsStill …)` at `entUnit`; and
    at the statement: a part is there; the state goes on from what is fixed; the second hole says
    nothing; the table's public test says yes.**

Limits. An item at a time; the entries with windows (the layers' two runs, the merge's), the
lookup's and the smallness test's are not here. THE SECOND HOLE OF THE READERS IS A LETTER: where it
speaks, the public test's yes does not say that the run says yes: so its silence at the statement is
a premise (at `LinkHoles.none` it holds outright). WHETHER THE PUBLIC TEST SAYS YES AT A REAL RECORD
IN FRONT OF A BATCHING is a run's to show: until then the condition in front has no known member.
The items are the driver's own pairs (the block's number from 0; the run's name), by which a run's
reader is looked up: the table's names are its own. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTable
import Johnson.Desc.First.Link.Law.WorldsMeet
import Johnson.Desc.First.Link.Law.StillRun
import Johnson.Desc.First.Link.Law.Under
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {α W : Type} {F : Frame}

/-- No slot is late between a ledger and itself. -/
theorem lateOf_self (G : Fork) : K9.lateOf G G = [] := by
  unfold K9.lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  cases G.gotF.getD j false <;> rfl

/-- One item's clause in its stronger form: the runs' values in a row ARE the values of the item's
forms (an equation of lists): so at the items whose reader is the run itself. What
TableOwes.hitems asks is `ItemIn`, which follows (`ItemAt.toIn`). -/
def ItemAt (L : Link S Claim) (φ : S → α)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (a : S × F.E.Str) (w : W) (e : ℕ × String) : Prop :=
  ∃ (b : K9.Part) (R : K9.Read)
    (rs : List (TermedRun S (α × Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ))),
    atS.get? a.1 = some b ∧
    (∀ x ∈ rs, x.1 ∈ rlOf L tmOf lenOf ∧
      ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
    Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
    (rs.flatMap fun x => x.2 (fixed9 φ a.1) (dataQ own b (rdW w))) =
      R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w)))

/-- **One item's clause of TableOwes.hitems, as that field asks it**: `ItemAt` with an INCLUSION in
the place of the equation of lists: each value of the item's forms is among the runs' values. WHY: a
run may have terms that the item's reader does not list: the approximate range proof's run has four
numbered terms in front of its single equations, and the reader of that item lists the single
equations alone: there the equation of lists is false by a count. The core law spends no more than
the inclusion. -/
def ItemIn (L : Link S Claim) (φ : S → α)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (a : S × F.E.Str) (w : W) (e : ℕ × String) : Prop :=
  ∃ (b : K9.Part) (R : K9.Read)
    (rs : List (TermedRun S (α × Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ))),
    atS.get? a.1 = some b ∧
    (∀ x ∈ rs, x.1 ∈ rlOf L tmOf lenOf ∧
      ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
    Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
    ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈
      rs.flatMap fun x => x.2 (fixed9 φ a.1) (dataQ own b (rdW w))

/-- The equation of lists gives the inclusion. -/
theorem ItemAt.toIn {L : Link S Claim} {φ : S → α}
    {tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {lenOf : ℕ × String → α × Option Pub9 → ℕ} {Rd : K9.Readers} {own : List (ℕ × ℕ)}
    {rdW : W → ℕ × ℕ → MsgQ} {a : S × F.E.Str} {w : W} {e : ℕ × String}
    (h : ItemAt L φ tmOf lenOf Rd own rdW a w e) : ItemIn L φ tmOf lenOf Rd own rdW a w e := by
  obtain ⟨b, R, rs, h1, h2, h3, h4, h5⟩ := h
  exact ⟨b, R, rs, h1, h2, h3, h4, fun f hf => by
    rw [h5]
    exact List.mem_map.2 ⟨f, hf, rfl⟩⟩

/-- TableOwes.hitems is ItemIn at every listed item. -/
theorem hitems_of_items (L : Link S Claim) (φ : S → α)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (on0 : S × F.E.Str → Prop) (Rd : K9.Readers)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (h : ∀ e ∈ items, ∀ a w, on0 a → ItemIn L φ tmOf lenOf Rd own rdW a w e) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L φ tmOf lenOf Rd own rdW a w e :=
  fun a w ha e he => h e he a w ha

/-- Where the run itself is the reader, and the run is still: the reader's forms are the law's, and
it has no late slot. -/
theorem reader_still (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (run r : ℕ → S → Except String (List Claim × S)) (fs : α × Option Pub9 → Option (List Aff))
    (hu : Under run r) (hS : Still φ Ok r fs) (q : α × Option Pub9) (s : S) (hf : Fx9 φ Ok q s)
    (z : List Claim × S) (hz : run 0 s = .ok z) (G : Fork) (hG : s.fork? = some G) :
    ∃ l, fs q = some l ∧ z.1.map (·.form) = l ∧ z.2 = s ∧
      (z.2.fork?).map (K9.lateOf G) = some [] := by
  have hz' : r 0 s = .ok (z.1, z.2) := hu 0 s z.1 z.2 hz
  obtain rfl' := hS.hands 0 s z.1 z.2 hz'
  obtain ⟨l, hl, hc⟩ := hS.forms q 0 s z.1 z.2 hf hz'
  refine ⟨l, hl, ?_, rfl', ?_⟩
  · rw [hc, List.map_map]
    exact List.map_id' l
  · rw [rfl', hG]
    exact congrArg some (lateOf_self G)

/-- What a lookup finds, the search by the name's test finds. -/
theorem find_of_lookup {β : Type} (n : String) : ∀ (l : List (String × β)) (v : β),
    l.lookup n = some v → ∃ x, l.find? (fun r => r.1 == n) = some x ∧ x.2 = v
  | [], _, h => nomatch h
  | (k, b) :: l, v, h => by
    rw [List.lookup_cons] at h
    rw [List.find?_cons]
    by_cases e : n = k
    · subst e
      simp only [beq_self_eq_true] at h ⊢
      exact ⟨_, rfl, Option.some.inj h⟩
    · have e1 : (n == k) = false := beq_false_of_ne e
      have e2 : (k == n) = false := beq_false_of_ne fun h' => e h'.symm
      simp only [e1] at h
      simp only [e2]
      exact find_of_lookup n l v h

/-- **The reader of the link, opened at the run itself.** -/
theorem reader_of_run (H : K9.LinkHoles) (L : Link S Claim) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (s : S) (z : List Claim × S) (hz : run 0 s = .ok z) (G0 G : Fork)
    (h0 : s.fork? = some G0) (hG : z.2.fork? = some G)
    (hc : (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
      c.form.ents.all (K9.ownRow G0)) = true) :
    (K9.readersOfLink H L).forms o.1 o.2 s =
      some { forms := z.1.map (·.form), late := K9.lateOf G0 G } := by
  obtain ⟨blk, hb, hl⟩ := Option.bind_eq_some_iff.1 hAt
  obtain ⟨x, hx, rfl⟩ := find_of_lookup o.2 blk.claims run hl
  have hs : K9.statesOfLink L o.1 = blk.claims := by
    unfold K9.statesOfLink
    rw [hb]
    rfl
  have hr : K9.readerOf (K9.statesOfLink L) o.1 o.2 s =
      some { forms := z.1.map (·.form), late := K9.lateOf G0 G } := by
    unfold K9.readerOf
    rw [hs, hx]
    show (match x.2 0 s, s.fork? with
      | .ok (z : List Claim × S), some F =>
        (z.2.fork?).bind fun G =>
          if z.1.all fun (c : Claim) =>
            c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow F)
          then some ({ forms := z.1.map fun (c : Claim) => c.form, late := K9.lateOf F G } :
            K9.Read) else none
      | _, _ => none) = _
    rw [hz, h0]
    show ((z.2.fork?).bind fun G =>
      if z.1.all fun (c : Claim) =>
        c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow G0)
      then some ({ forms := z.1.map fun (c : Claim) => c.form, late := K9.lateOf G0 G } : K9.Read)
      else none) = _
    rw [hG]
    show (if z.1.all fun (c : Claim) =>
        c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow G0)
      then some ({ forms := z.1.map fun (c : Claim) => c.form, late := K9.lateOf G0 G } : K9.Read)
      else none) = _
    rw [if_pos hc]
  show (if o.2 == "K8.equations" then H.small s
    else match K9.readerOf (K9.statesOfLink L) o.1 o.2 s with
      | some R => some R
      | Option.none => H.silent o.1 o.2 s) = _
  rw [hne, hr]
  rfl

/-- **THE CONVERSE**: where the second hole says nothing, whatever the reader of the link gives at
an entry other than the smallness test's comes out of the run itself: THE RUN SAYS YES THERE, with
no claim in front; the reader's side test on its claims says yes; and what is given is the claims'
forms with the slots that are late between the two ledgers. -/
theorem run_of_reader (H : K9.LinkHoles) (L : Link S Claim) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (s : S) (hsil : H.silent o.1 o.2 s = none) (R : K9.Read)
    (hR : (K9.readersOfLink H L).forms o.1 o.2 s = some R) :
    ∃ (z : List Claim × S) (G0 G : Fork), run 0 s = .ok z ∧ s.fork? = some G0 ∧
      z.2.fork? = some G ∧
      (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
        c.form.ents.all (K9.ownRow G0)) = true ∧
      R = { forms := z.1.map (·.form), late := K9.lateOf G0 G } := by
  obtain ⟨blk, hb, hl⟩ := Option.bind_eq_some_iff.1 hAt
  obtain ⟨x, hx, rfl⟩ := find_of_lookup o.2 blk.claims run hl
  have hs : K9.statesOfLink L o.1 = blk.claims := by
    unfold K9.statesOfLink
    rw [hb]
    rfl
  have hR' : (if o.2 == "K8.equations" then H.small s
    else match K9.readerOf (K9.statesOfLink L) o.1 o.2 s with
      | some R => some R
      | Option.none => H.silent o.1 o.2 s) = some R := hR
  rw [hne] at hR'
  cases hr : K9.readerOf (K9.statesOfLink L) o.1 o.2 s with
  | none =>
    rw [hr] at hR'
    have h' : H.silent o.1 o.2 s = some R := hR'
    rw [hsil] at h'
    exact nomatch h'
  | some R' =>
    rw [hr] at hR'
    obtain rfl : R' = R := Option.some.inj hR'
    unfold K9.readerOf at hr
    rw [hs, hx] at hr
    have hr' : (match x.2 0 s, s.fork? with
      | .ok (z : List Claim × S), some F =>
        (z.2.fork?).bind fun G =>
          if z.1.all fun (c : Claim) =>
            c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow F)
          then some ({ forms := z.1.map fun (c : Claim) => c.form, late := K9.lateOf F G } :
            K9.Read) else none
      | _, _ => none) = some R' := hr
    cases hz : x.2 0 s with
    | error m =>
      rw [hz] at hr'
      exact nomatch hr'
    | ok z =>
      cases h0 : s.fork? with
      | none =>
        rw [hz, h0] at hr'
        exact nomatch hr'
      | some G0 =>
        rw [hz, h0] at hr'
        obtain ⟨G, hG, hi⟩ := Option.bind_eq_some_iff.1 hr'
        by_cases hc : (z.1.all fun (c : Claim) =>
            c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow G0)) = true
        · rw [if_pos hc] at hi
          exact ⟨z, G0, G, rfl, rfl, hG, hc, (Option.some.inj hi).symm⟩
        · rw [if_neg hc] at hi
          exact nomatch hi

/-- The table's public test's yes says that the reader gives something. -/
theorem reader_of_formsIn (Rd : K9.Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (name : String)
    (s : S) (hin : K9.formsIn Rd own piece name s = true) :
    ∃ R, Rd.forms piece name s = some R := by
  unfold K9.formsIn at hin
  cases hR : Rd.forms piece name s with
  | some R => exact ⟨R, rfl⟩
  | none =>
    rw [hR] at hin
    cases hs : K9.segAt? s with
    | none =>
      rw [hs] at hin
      exact absurd hin Bool.false_ne_true
    | some a =>
      rw [hs] at hin
      exact absurd hin Bool.false_ne_true

/-- The table's public test on a run's forms says that every array which a form names is named by
the segment's list. -/
theorem named_of_formsIn (Rd : K9.Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (name : String) (s : S)
    (b : K9.Part) (R : K9.Read) (hb : atS.get? s = some b) (hR : Rd.forms piece name s = some R)
    (hin : K9.formsIn Rd own piece name s = true) :
    ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList, (b.L.arrayOf[x.tree]?).isSome = true := by
  intro f hf x hx
  unfold K9.formsIn at hin
  rw [K9.segAt_of_atS s b hb, hR] at hin
  have h1 := Bool.and_eq_true_iff.1 hin
  have h2 := List.all_eq_true.1 h1.2 f hf
  unfold K9.affIn at h2
  have h3 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h2).1 x hx
  obtain ⟨A, hA⟩ := K9.entIn_some own b x h3
  obtain ⟨y, _, _, hy, _⟩ := K9.arrayIn_some own b x.tree A hA
  rw [hy]
  rfl

/-- **ONE ITEM's CLAUSE AT AN ENTRY WHOSE RUN LEAVES THE RECORD AS IT IS.** -/
theorem item_still (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (fs : α × Option Pub9 → Option (List Aff)) (hu : Under run r) (hS : Still φ Ok r fs)
    (ht : tmOf o = plainTm (valsStill Reading.gl fs entUnit))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hf : Fx9 φ Ok (fixed9 φ a.1) a.1) (z : List Claim × S) (hz : run 0 a.1 = .ok z)
    (hc : (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
      c.form.ents.all (K9.ownRow b.F)) = true)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemAt L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  have h0 : a.1.fork? = some b.F := K9.get_fork a.1 b hb
  obtain ⟨l, hl, hfm, hz2, _⟩ := reader_still φ Ok run r fs hu hS _ a.1 hf z hz b.F h0
  have hG : z.2.fork? = some b.F := by rw [hz2]; exact h0
  have hR := reader_of_run H L o hne run hAt a.1 z hz b.F b.F h0 hG hc
  rw [hfm, lateOf_self] at hR
  have hq : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  refine ⟨b, ⟨l, []⟩, [(⟨(o.2, run), tmOf o, lenOf o⟩, valsStill Reading.gl fs entUnit)], hb, ?_,
    hR, hin, ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · have he := named_of_formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 b ⟨l, []⟩ hb hR hin
    show valsStill Reading.gl fs entUnit (fixed9 φ a.1) (dataQ own b (rdW w)) ++ [] = _
    rw [List.append_nil]
    unfold valsStill
    rw [hq, hl]
    exact List.map_congr_left fun f hf' =>
      value_meets_still b (dataQ own b (rdW w)) (fixed9 φ a.1) hq f (he f hf')

/-- **THE SAME ON THREE FACTS AT THE STATEMENT AND A SILENT HOLE**: a part is there; the state goes
on from what is fixed; the table's public test says yes; the second hole says nothing there. That
the run says yes there, and the reader's side test, come out of the public test's yes. -/
theorem item_still_in (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (fs : α × Option Pub9 → Option (List Aff)) (hu : Under run r) (hS : Still φ Ok r fs)
    (ht : tmOf o = plainTm (valsStill Reading.gl fs entUnit))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hf : Fx9 φ Ok (fixed9 φ a.1) a.1) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemAt L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨z, G0, G, hz, h0, _, hc, _⟩ := run_of_reader H L o hne run hAt a.1 hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (K9.get_fork a.1 b hb))
  exact item_still H L φ Ok tmOf lenOf own rdW o ho hne run r hAt fs hu hS ht a w b hb hf z hz hc
    hin

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lateOf_self
#print axioms VerifiableInference.Desc.LinkJoin.ItemAt.toIn
#print axioms VerifiableInference.Desc.LinkJoin.hitems_of_items
#print axioms VerifiableInference.Desc.LinkJoin.reader_still
#print axioms VerifiableInference.Desc.LinkJoin.reader_of_run
#print axioms VerifiableInference.Desc.LinkJoin.named_of_formsIn
#print axioms VerifiableInference.Desc.LinkJoin.item_still
#print axioms VerifiableInference.Desc.LinkJoin.run_of_reader
#print axioms VerifiableInference.Desc.LinkJoin.reader_of_formsIn
#print axioms VerifiableInference.Desc.LinkJoin.item_still_in
