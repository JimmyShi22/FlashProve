-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/MarksKept.lean: "THESE SLOTS ARE STILL FREE AT MY ENTRY": ONE CLAUSE, CUT ONCE FOR
EVERY KIND THAT NEEDS IT. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is
stated.

A run of claims that lays a sumcheck's row (the smallness test's list at the lookup's leaves; the head's merge) asks
that the sumcheck's own slots are there and still free AT ITS OWN CALL inside the batching (`D6.Ret.Open`,
OnBytes/K/Kc/Returns/FlReturns6.lean). K9's `LedgerCore`, the library's `OnlySide` and `SameCore` keep neither
the marks nor the three arrays' sizes: the runs in front write them. What each run in front can say WITHOUT KNOWING
WHO COMES BEHIND IT is which slots it fills.
  `MarksKept W u v`   of two states and a set W of slots: where u has an open ledger, v has one, with the same number
      of slots; and IF u's three arrays are sized, so are v's, and each slot in W is marked as filled in v just if it
      was in u. (Under "sized", as the sealed `hide_ok` and `hideRun_ok` hand it. Another thing than the sealed
      `OnBytes.Model.Road.SlotsKept`, which is on ledgers and says that what is filled stays filled.)
  `MarksKept.refl`, `.trans`, `.mono`
  `RunFills I own run`   **EACH KIND's OWN LAW ON ITS RUN**: at the numbers and states with I, where the run returns,
      the marks OUTSIDE own are kept: "my run fills slots of own alone". It names no other kind's data.
      `RunFills.weaken`: from a kind's own I' to any I that gives it · `RunFills.under`: from a kind's own run to a run
      that only refuses more: so to the wrapped run in the description's list (called by no line)
  `open_of_kept`    what a sumcheck's row asks of the ledger passes from u to v where its own slots' marks are kept
      (the sealed `Open.keep`)
  `draw_kept`       K9's draw keeps every mark
  `upTo own j`      the slots that no run at an entry in front of j fills
  `withKept J own b`   **THE TURN OF A FAMILY**: from a family J i cs u (Honest/K9/GatherList.lean) the family "J, and
      the marks of `upTo own i` are kept since the state b". NO WINDOW AND NO ENTRY IS FIXED: each kind takes its own
      window at its own entry by `.mono`: so several kinds in one order are served by one turn
  **`withKept_step`**   each run of the order is `RunFills` at its entry; and each run's clause holds of J WITH "the
      marks of `upTo own j` are kept since b" AS A FURTHER PREMISE: then the clause holds of `withKept J own b`: in
      the very form that `gather_returns_list`, `seated_yes_family`, `yes_seated` and the steps take
  `withKept_start`  at b itself; `withKept_draw`: at the state behind K9's draw from b: so "since b" may reach back IN
      FRONT OF THE BATCHING
  `gather_returns_kept`   `gather_returns_list` at that family
So the clause rides through the entries in front by the fold, not kind by kind: what is owed is one `RunFills` a run,
AT EVERY ENTRY OF THE ORDER (also behind the last window that anyone needs: there own j may be every slot, which still
owes that a ledger is open behind, with as many slots, and that sized stays sized); and, of whoever needs a window W at
entry j: that W lies in `upTo own j`, a fact on the plan's numbers, and what it asks of the ledger AT b ITSELF. Called
at members: Honest/K9/YesToy.lean. There no run's clause USES the further premise; `open_of_kept` is called by no
line.
WHAT IS NOT CLAIMED. `RunFills` of any kind's run. That any window lies in `upTo own j`. What lies outside the ledger:
in which sort of segment the state stands, and the merge's own data (for the draw alone: `head_slots_behind_draw`,
Honest/K9/DrawSlots.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GatherList
import Johnson.Desc.ProofFile.Honest.K9.DrawSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Block Claim claimsInBy)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where drawAlone)

/-- The marks of the slots of W are kept from u to v. -/
def MarksKept (W : Nat → Prop) (u v : S) : Prop :=
  ∀ F, u.fork? = some F → ∃ G, v.fork? = some G ∧ G.ns = F.ns ∧
    (Sized F → Sized G ∧ ∀ i, W i → (Filled G i ↔ Filled F i))

theorem MarksKept.refl (W : Nat → Prop) (u : S) : MarksKept W u u :=
  fun F hF => ⟨F, hF, rfl, fun h => ⟨h, fun _ _ => Iff.rfl⟩⟩

theorem MarksKept.trans {W : Nat → Prop} {u v w : S} (h1 : MarksKept W u v) (h2 : MarksKept W v w) :
    MarksKept W u w := by
  intro F hF
  obtain ⟨G, hG, n1, k1⟩ := h1 F hF
  obtain ⟨H, hH, n2, k2⟩ := h2 G hG
  refine ⟨H, hH, n2.trans n1, fun hs => ?_⟩
  obtain ⟨s1, f1⟩ := k1 hs
  obtain ⟨s2, f2⟩ := k2 s1
  exact ⟨s2, fun i hi => (f2 i hi).trans (f1 i hi)⟩

theorem MarksKept.mono {W W' : Nat → Prop} {u v : S} (h : MarksKept W u v) (hW : ∀ i, W' i → W i) :
    MarksKept W' u v := by
  intro F hF
  obtain ⟨G, hG, n1, k1⟩ := h F hF
  exact ⟨G, hG, n1, fun hs => ⟨(k1 hs).1, fun i hi => (k1 hs).2 i (hW i hi)⟩⟩

/-- **A kind's own law on its run**: it fills slots of own alone. -/
def RunFills (I : Nat → S → Prop) (own : Nat → Prop) (run : ClaimsRun) : Prop :=
  ∀ n u z, I n u → run n u = .ok z → MarksKept (fun i => ¬ own i) u z.2

theorem RunFills.weaken {I I' : Nat → S → Prop} {own : Nat → Prop} {run : ClaimsRun}
    (h : RunFills I' own run) (hI : ∀ n u, I n u → I' n u) : RunFills I own run :=
  fun n u z hu hz => h n u z (hI n u hu) hz

/-- The law passes to a run that only refuses more: SO FROM A KIND's OWN RUN TO THE RUN IN THE DESCRIPTION's LIST, which
its makers have wrapped (`RunUnder`, Honest/K9/GatherFold.lean). -/
theorem RunFills.under {I : Nat → S → Prop} {own : Nat → Prop} {run' run : ClaimsRun}
    (h : RunFills I own run) (hu : RunUnder run' run) : RunFills I own run' :=
  fun n u z hI hz => h n u z hI (hu n u z hz)

/-- What a sumcheck's row asks of the ledger passes where its own slots' marks are kept. -/
theorem open_of_kept {W : Nat → Prop} {u v : S} (h : MarksKept W u v) (q : Psc) (F : Fork)
    (hF : u.fork? = some F) (ho : D6.Ret.Open q F)
    (hW : ∀ i, q.first ≤ i → i < q.first + D6.Ret.taken q → W i) :
    ∃ G, v.fork? = some G ∧ D6.Ret.Open q G := by
  obtain ⟨G, hG, n1, k1⟩ := h F hF
  obtain ⟨s1, f1⟩ := k1 ho.sized
  exact ⟨G, hG, ho.keep s1 n1 fun i h1 h2 => f1 i (hW i h1 h2)⟩

/-- K9's draw keeps every mark. -/
theorem draw_kept (p : Where) (s t : S) (x : E)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) :
    MarksKept (fun _ => True) s t := by
  intro F hF
  obtain ⟨a, ha⟩ := draw_open p s t x h
  have e : a.F = F := Option.some.inj ((VerifiableInference.Desc.K9.get_fork s a ha).symm.trans hF)
  subst e
  refine ⟨(drawnPart p a x).F, ?_, rfl, fun hs => ⟨hs, fun _ _ => Iff.rfl⟩⟩
  rw [draw_is p s t x a ha h]
  exact set_fork s a _ ha

/-- The slots that no run at an entry in front of j fills. -/
def upTo (own : Nat → Nat → Prop) (j i : Nat) : Prop := ∀ j', j' < j → ¬ own j' i

/-- **The turn of a family.** -/
def withKept (J : Nat → List Claim → S → Prop) (own : Nat → Nat → Prop) (b : S) (j : Nat) (cs : List Claim)
    (u : S) : Prop := J j cs u ∧ MarksKept (upTo own j) b u

theorem withKept_start (J : Nat → List Claim → S → Prop) (own : Nat → Nat → Prop) (b : S) (h : J 0 [] b) :
    withKept J own b 0 [] b := ⟨h, MarksKept.refl _ b⟩

theorem withKept_draw (J : Nat → List Claim → S → Prop) (own : Nat → Nat → Prop) (p : Where) (b t : S) (x : E)
    (hd : (drawAlone (Cl := Claim) atS p).decide b [⟨[], drawnOne x⟩] [] = .ok t) (h : J 0 [] t) :
    withKept J own b 0 [] t := ⟨h, (draw_kept p b t x hd).mono fun _ _ => trivial⟩

/-- One entry further. -/
theorem kept_succ {own : Nat → Nat → Prop} {b u v : S} {j : Nat} (h1 : MarksKept (upTo own j) b u)
    (h2 : MarksKept (fun i => ¬ own j i) u v) : MarksKept (upTo own (j + 1)) b v :=
  (h1.mono fun _ hi j' hj' => hi j' (by omega)).trans (h2.mono fun _ hi => hi j (by omega))

/-- **The runs' clauses, at the turned family.** -/
theorem withKept_step (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (order : List (Nat × String)) (J : Nat → List Claim → S → Prop) (own : Nat → Nat → Prop) (b : S)
    (fills : ∀ j o, order[j]? = some o → ∀ run, claimsRunOf bs o = some run →
      RunFills (fun n u => ∃ cs, cs.length = n ∧ J j cs u) (own j) run)
    (step : ∀ j o, order[j]? = some o → ∀ cs u, J j cs u → MarksKept (upTo own j) b u →
      ∃ run z, claimsRunOf bs o = some run ∧ run cs.length u = .ok z ∧ each o z.1 z.2 = .ok () ∧
        J (j + 1) (cs ++ z.1) z.2) :
    ∀ j o, order[j]? = some o → ∀ cs u, withKept J own b j cs u →
      ∃ run z, claimsRunOf bs o = some run ∧ run cs.length u = .ok z ∧ each o z.1 z.2 = .ok () ∧
        withKept J own b (j + 1) (cs ++ z.1) z.2 := by
  intro j o hj cs u hu
  obtain ⟨run, z, hr, hz, he, hJ⟩ := step j o hj cs u hu.1 hu.2
  exact ⟨run, z, hr, hz, he, hJ, kept_succ hu.2 (fills j o hj run hr cs.length u z ⟨cs, rfl, hu.1⟩ hz)⟩

/-- `gather_returns_list` at the turned family. -/
theorem gather_returns_kept (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (J : Nat → List Claim → S → Prop)
    (own : Nat → Nat → Prop) (t : S) (hJ : J 0 [] t)
    (fills : ∀ j o, order[j]? = some o → ∀ run, claimsRunOf bs o = some run →
      RunFills (fun n u => ∃ cs, cs.length = n ∧ J j cs u) (own j) run)
    (step : ∀ j o, order[j]? = some o → ∀ cs u, J j cs u → MarksKept (upTo own j) t u →
      ∃ run z, claimsRunOf bs o = some run ∧ run cs.length u = .ok z ∧ each o z.1 z.2 = .ok () ∧
        J (j + 1) (cs ++ z.1) z.2) :
    ∃ y, claimsInBy each bs order t = .ok y ∧ J order.length y.1 y.2 ∧
      MarksKept (upTo own order.length) t y.2 :=
  gather_returns_list each bs order (withKept J own t) t (withKept_start J own t hJ)
    (withKept_step each bs order J own t fills step)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.MarksKept.trans
#print axioms ProofFile.Honest.K9.RunFills.under
#print axioms ProofFile.Honest.K9.open_of_kept
#print axioms ProofFile.Honest.K9.draw_kept
#print axioms ProofFile.Honest.K9.kept_succ
#print axioms ProofFile.Honest.K9.withKept_step
#print axioms ProofFile.Honest.K9.gather_returns_kept
