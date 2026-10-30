-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/LookInMade.lean: K4's ROW MAKES THE PUBLIC ITEM lookIn OF THE LOOKUP ON THE
DIGITS: behind a yes of K4's block that lookup's condition in front of its block (k3LookInAt,
Johnson/Desc/First/Look/K3BoolsAt.lean) holds, under four public tests on the state in front and
named lines on the plan. Statements and proofs: a join.

THE ONE LINE THAT SEEMED NOBODY's, "behind the yes the ledger's next free number is the lookup's
first slot", COMES OFF A LAW: hear_count (Johnson/Road/K4/HearCount.lean): the hearing takes
just the slots that the plan counts for it (slotsOf, OnBytes/Model/LayerPlan.lean).

  `hear_next_plan`: behind a hearing: next + the calls' lookup's slots = next in front + the plan's
    count.
  `hear_next_block`, `front_ledger`, `freeB_of`, `link_clause`, `digits_unheard`: the parts.
  `LookInPlan`: THE LINES ON THE PLAN, BY NAME: each an equation or an inequality of numbers that
    the plan holds: place, shape, digits (the lookup's place is there, has a shape, is the digits')
    · lamS, ncl (two numbers of K4's plan are the layout's) · count (the plan's next free number in
    front of K4's block, with the plan's count, is the lookup's first slot with the calls' lookup's
    slots) · room (the lookup's slots end inside the ledger's number of slots).
  **`lookIn_made`**: KeptAtS par s s' · LookInPlan · the four tests at s: ledgerB · freeAboveB ns ·
    linkFreshB · callerInLayB n · and hlink: then k3LookInAt X3 D3 m true s' = true.
No new argument: k3OnIn_of_kept (Johnson/Road/K4/LookOutKept.lean), hear_count.
**Limits.** PREMISES, none paid here. LookInPlan: seven lines on the plan. ITS LINE count MAY BE
FALSE AT A REAL PLAN: it says that right behind K4's yes (piece 3) the ledger's next free number is
already the first slot of the digits' lookup (piece 7): true only if the blocks at pieces 4, 5 and 6
take no slot: THE ITEM IS MADE ONLY UNDER THE TEST lookInPlanB
(Johnson/Road/K4/Riders/LookInPlanB.lean): where that test has merely been evaluated at a plan, that
is a run, no theorem. The four tests: the table's items ledger m, freeAbove m, linkFresh m, callerIn
m in front of K4's block. hlink: THE OPEN LINK's NUMBER IS THE PLACE's: none of the four tests says
it: NOBODY's YET. That the ledger's next free number in front is not above the lookup's first slot
needs no line: the hearing does not lower it. Nothing on soundness. K04_law, the law of K4's block
itself, IS NOT PROVED. Met through Lean at no member.


-/
import Johnson.Road.K4.LookOutKept
import Johnson.Road.K4.HearCount
import Johnson.Desc.First.Look.K3BoolsAt
import Johnson.Desc.First.Look.K3CallsKeeps
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.FillK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own lamSOf nclOf slotsOf)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par hear hear_count engFl)
open VerifiableInference.Desc.First (S LayOwn ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillK4 (callerInLayB)
open VerifiableInference.Desc.First.Look (Sent placeAt k3LookIn k3LookInAt)
open VerifiableInference.OnPublicFiles (linkFreshB digitsUnheardB)
open VerifiableInference.Desc.K3 (k3OnIn heardAt sizedB freeB)

/-- Behind a hearing: the ledger's next free number, by the plan's count. -/
theorem hear_next_plan {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (hF : PscRun.Sized F) (h : hear engFl P hp g fo F t = some (o, G, u))
    (hl : hp.lamS = lamSOf P.y) (hn : hp.NCL = nclOf P.y g) :
    G.next + Forest.elems P.y.fo = F.next + slotsOf P.y P.rd g P.wsLay.lk 0 :=
  hear_count Reading.gl hF h hl hn 0

/-- Numbers alone: so that no count of the plan is unfolded. -/
private theorem next_is {Gn e Fn sl n pf : ℕ} (h1 : Gn + e = Fn + sl) (h2 : Fn = n)
    (h3 : n + sl = pf + e) : Gn = pf := by omega

private theorem inside {nx pf j ns el : ℕ} (hle : nx ≤ pf) (hj : j < el) (room : pf + el ≤ ns) :
    pf + j - nx < ns - nx := by omega

/-- **The lines on the plan.** n: the plan's next free number in front of K4's block. ns: the
ledger's number of slots. -/
structure LookInPlan (par : Par) (X3 : Verify.Public) (m : ℕ)
    (p : VerifiableInference.Desc.First.Look.P) (h3 : Forest.Shape) (n ns : ℕ) : Prop where
  place : placeAt X3 m true = some p
  shape : p.shape = some h3
  digits : p.digits = true
  lamS : par.hp.lamS = lamSOf par.P.y
  ncl : par.hp.NCL = nclOf par.P.y par.g
  count : n + slotsOf par.P.y par.P.rd par.g par.P.wsLay.lk 0 = p.first + Forest.elems par.P.y.fo
  room : p.first + Forest.elems h3 ≤ ns

/-- The same at K4's block's hearing: at its own public parameters with tokens laid in. -/
theorem hear_next_block {P : Pub} {x : Array ℕ} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {t u : Tape} (hF : PscRun.Sized F)
    (h : hear engFl { P with tokv := x } hp g fo F t = some (o, G, u))
    (hl : hp.lamS = lamSOf P.y) (hn : hp.NCL = nclOf P.y g) :
    G.next + Forest.elems P.y.fo = F.next + slotsOf P.y P.rd g P.wsLay.lk 0 :=
  hear_next_plan (P := { P with tokv := x }) hF h hl hn

/-- What three of the tests in front say of the ledger at a layers' link. -/
theorem front_ledger {s : S} {a : LayOwn} {n ns : ℕ} (ha : s.here = .lay a)
    (hled : ledgerB s = true) (hfa : freeAboveB ns s = true) (hcall : callerInLayB n s = true) :
    sizedB a.F = true ∧ PscRun.Sized a.F ∧ a.F.next = n ∧ a.F.ns = ns ∧
      ((List.range (a.F.ns - a.F.next)).all fun j =>
        !a.F.gotF.getD (a.F.next + j) true) = true := by
  have eF : s.fork? = some a.F := by simp only [S.fork?, ha]
  have hz : sizedB a.F = true := by
    unfold ledgerB at hled
    rw [eF] at hled
    exact hled
  have hS : PscRun.Sized a.F := by
    have hz' := hz
    unfold sizedB at hz'
    simp only [Bool.and_eq_true, beq_iff_eq] at hz'
    exact ⟨hz'.1.1, hz'.1.2, hz'.2⟩
  have hnx : a.F.next = n := by
    unfold callerInLayB at hcall
    rw [ha] at hcall
    have h2 : (a.own.isNone && a.F.next == n) = true := hcall
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact h2.2
  have hfa' : (((List.range (a.F.ns - a.F.next)).all fun j =>
      !a.F.gotF.getD (a.F.next + j) true) && a.F.ns == ns) = true := by
    unfold freeAboveB at hfa
    rw [eF] at hfa
    exact hfa
  rw [Bool.and_eq_true] at hfa'
  exact ⟨hz, hS, hnx, by simpa using hfa'.2, hfa'.1⟩

/-- el slots from first on are free, where all is free from the ledger's next free number on. -/
theorem freeB_of {F : Fork} {first el : ℕ}
    (hall : ((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) = true)
    (hle : F.next ≤ first) (room : first + el ≤ F.ns) : freeB F first el = true := by
  unfold freeB
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true room, List.all_eq_true.2 fun j hj => ?_⟩
  have k : (!F.gotF.getD (F.next + (first + j - F.next)) true) = true :=
    List.all_eq_true.1 hall (first + j - F.next)
      (List.mem_range.2 (inside hle (List.mem_range.1 hj) room))
  rw [Nat.add_sub_cancel' (Nat.le_trans hle (Nat.le_add_right _ _))] at k
  exact k

/-- The item's clause on the open link. -/
theorem link_clause {s s' : S} {arrs : Array (ℕ × String)} {lk : ℕ} (hl : s'.link? = s.link?)
    (hfresh : linkFreshB arrs s = true) (hlink : ∀ Lk, s.link? = some Lk → Lk.link = lk) :
    (s'.link?.any fun L => L.link == lk && L.arrayOf == arrs) = true := by
  unfold linkFreshB at hfresh
  rw [Bool.and_eq_true] at hfresh
  rw [hl]
  cases hlk : s.link? with
  | none =>
    rw [hlk] at hfresh
    exact absurd hfresh.2 (by simp)
  | some Lk =>
    rw [hlk] at hfresh
    have h2 : (Lk.arrayOf == arrs) = true := hfresh.2
    show (Lk.link == lk && Lk.arrayOf == arrs) = true
    rw [h2, Bool.and_true, hlink Lk hlk]
    exact beq_self_eq_true _

/-- Nothing is heard at the digits' seat. -/
theorem digits_unheard {s : S} {arrs : Array (ℕ × String)} (hfresh : linkFreshB arrs s = true) :
    heardAt true s = none := by
  unfold linkFreshB at hfresh
  rw [Bool.and_eq_true] at hfresh
  have h1 := hfresh.1
  unfold digitsUnheardB at h1
  show s.tl?.bind (·.heard) = none
  exact Option.isNone_iff_eq_none.1 h1

/-- **K4's row makes lookIn at the digits' lookup.** UNDER: KeptAtS (had at a yes of K4's block);
the seven lines on the plan; the four public tests at the state in front (ledgerB, freeAboveB ns,
linkFreshB, callerInLayB n); hlink: the open link's number is the place's. -/
theorem lookIn_made {par : Par} {s s' : S} {X3 : Verify.Public} {D3 : Sent} {m : ℕ}
    {p : VerifiableInference.Desc.First.Look.P} {h3 : Forest.Shape} {n ns : ℕ}
    (K : KeptAtS par s s') (L : LookInPlan par X3 m p h3 n ns) (hled : ledgerB s = true)
    (hfa : freeAboveB ns s = true) (hfresh : linkFreshB (D3.arrayOf.getD m #[]) s = true)
    (hcall : callerInLayB n s = true) (hlink : ∀ Lk, s.link? = some Lk → Lk.link = p.link) :
    k3LookInAt X3 D3 m true s' = true := by
  have K' := K
  obtain ⟨a, fo, o, G, ha, _, hG, hLat, _, _, _, _, hR, _, _, t, u, hh⟩ := K'
  have eF : s.fork? = some a.F := by simp only [S.fork?, ha]
  obtain ⟨hz, hS, hnx, hns, hall⟩ := front_ledger ha hled hfa hcall
  have hGn : G.next = p.first := next_is (hear_next_block hS hh L.lamS L.ncl) hnx L.count
  have hle : a.F.next ≤ p.first := by
    rw [← hGn]
    exact hLat.next
  have hfree : freeB a.F p.first (Forest.elems h3) = true :=
    freeB_of hall hle (by rw [hns]; exact L.room)
  have hd : heardAt p.digits s = none := by
    rw [L.digits]
    exact digits_unheard hfresh
  have hOn : k3OnIn p s' = true :=
    k3OnIn_of_kept K p L.shape hd
      (fun F hF => by
        obtain rfl := Option.some.inj (eF.symm.trans hF)
        exact ⟨hz, hfree⟩)
      (fun G' hG' => by
        obtain rfl := Option.some.inj (hG.symm.trans hG')
        exact hGn)
  have hLk := link_clause hR.link hfresh hlink
  unfold k3LookInAt
  rw [L.place]
  show k3LookIn p (D3.arrayOf.getD m #[]) s' = true
  unfold k3LookIn
  rw [hOn, hLk]
  rfl

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.hear_next_plan
#print axioms OnBytes.Road.K4.Riders.hear_next_block
#print axioms OnBytes.Road.K4.Riders.front_ledger
#print axioms OnBytes.Road.K4.Riders.freeB_of
#print axioms OnBytes.Road.K4.Riders.link_clause
#print axioms OnBytes.Road.K4.Riders.digits_unheard
#print axioms OnBytes.Road.K4.Riders.lookIn_made
