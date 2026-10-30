-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/K3Start.lean: The kind "lookup" (K3), for the law "a stretch of slots
that is owed stays owed along a walk of steps" (StepKeepsUnder, Johnson/Desc/Part/LedgerKeeps.lean):
ITS decide BESIDE ANOTHER's STRETCH; THE START OF THE WALK AT ITS OWN STRETCH; THE WALK; AND TWO
MEMBERS THAT MUST FAIL. Statements and proofs. The promises and the runs' laws:
Johnson/Top/H/Keep/K3Inv.lean. Which slots are filled behind a hearing:
Johnson/Top/H/Keep/PadExact.lean.

Main names:
  decide_keepsA: role (A): under K3InvA the kind's decide keeps another's stretch owed (it turns no
    mark below the next slot) and hands the promise on (the leaves' stretch that it lays begins at
    or above the next slot, and the watched stretch ends below it).
  decide_starts: role (B): from a ledger that has its sizes and in which nothing at or above the
    next slot is filled, a yes of decide leaves K3InvB at what was heard, and the leaves' stretch,
    lvLen g slots from g.leaves.first on, is owed.
  own_walk: so, along any walk of steps each of which has the law under K3InvB, what was heard
    stays, the ledger is later and the stretch is still owed.
  own_write_returns: there, where the stretch lies inside the ledger's slots, the write that
    "planes" does returns.
  invA_of_owed, invA_of_none: role (A)'s FIRST RECORD: K3InvA at a stretch that begins at or above
    the ledger's next slot, where K3's own stretch is still owed (what own_walk hands out); and
    where nothing has been heard.
  mover_fails: a step that lays a heard record whose leaves' stretch begins at the watched
    stretch's first slot does not hand K3InvA on. mover_meets: such a record there is.
  off_writer_fails: a step that writes one slot BELOW the address in the heard record fails the law
    under K3InvA, at a watched stretch that ends just below that address.

Limits. own_walk's list of steps is a letter: that a link's other steps have the law under K3InvB
("heard stays, the sizes stay, they write above or apart") is each kind's own. own_write_returns
speaks of the write alone, not of the whole run "planes" (its readers, its test on the debt).
"Nothing at or above the next slot is filled" is a promise in front of the hearing.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.Keep.PadExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.K3 (Seat SeatReads)
open VerifiableInference.Desc.Part (StepKeepsUnder decides Walked walked_keeps_under owedLedger
  owedLedger_free owedLedger_sized)

variable {S Cl : Type}

/-- **Role (A): decide beside another's stretch.** -/
theorem decide_keepsA (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (hk : SeatKeeps seat)
    (hr : SeatReads seat) (a n : ℕ) :
    StepKeepsUnder (K3InvA seat.fork seat.heard a n) seat.fork a n
      (decides (Desc.K3.block seat piece laid before p guests)) := by
  rintro s s' F hI ⟨rs, gs, h⟩ hF ho
  obtain ⟨F1, x, e1, hn, rfl, hE⟩ := decide_exact seat piece laid before p guests s s' rs gs h
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨E, hL⟩ := hE (hI.1 F hF)
  have hsome : (seat.fork s).isSome = true := by rw [hF]; rfl
  have f' := hk s x.1 x.2 hsome hn
  have g' := hr s x.1 x.2 hsome hn
  refine ⟨⟨fun H hH => ?_, fun g hg => ?_⟩, x.2, f', hL, owed_of_writesAbove ho E.writesAbove⟩
  · obtain rfl : x.2 = H := Option.some.inj (f'.symm.trans hH)
    exact hL.sized (hI.1 F hF)
  · obtain rfl : x.1 = g := Option.some.inj (g'.symm.trans hg)
    exact Or.inr (Nat.le_trans ho.1 E.first)

/-- **Role (B): the start.** -/
theorem decide_starts (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (hk : SeatKeeps seat)
    (hr : SeatReads seat) {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    {F : Fork} (hF : seat.fork s = some F) (hS : Sized F) (hA : FreeAbove F)
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (g : Forest.Heard) (F' : Fork), seat.fork s' = some F' ∧ Later F F' ∧
      K3InvB seat.fork seat.heard g s' ∧ SlotsOwed F' g.leaves.first (lvLen g) := by
  obtain ⟨F1, x, e1, hn, rfl, hE⟩ := decide_exact seat piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨E, hL⟩ := hE hS
  have hsome : (seat.fork s).isSome = true := by rw [hF]; rfl
  have f' := hk s x.1 x.2 hsome hn
  refine ⟨x.1, x.2, f', hL, ⟨hr s x.1 x.2 hsome hn, fun H hH => ?_⟩, ?_⟩
  · obtain rfl : x.2 = H := Option.some.inj (f'.symm.trans hH)
    exact hL.sized hS
  · have := E.owed hA
    rwa [← E.len] at this

/-- **The walk at K3's own stretch.** -/
theorem own_walk (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (hk : SeatKeeps seat)
    (hr : SeatReads seat) {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    {F : Fork} (hF : seat.fork s = some F) (hS : Sized F) (hA : FreeAbove F)
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (g : Forest.Heard) (F' : Fork), seat.fork s' = some F' ∧ seat.heard s' = some g ∧
      ∀ st : List (S → S → Prop),
        (∀ r ∈ st, StepKeepsUnder (K3InvB seat.fork seat.heard g) seat.fork g.leaves.first
          (lvLen g) r) →
        ∀ (N : ℕ) (t : S), Walked st N s' t →
          seat.heard t = some g ∧ ∃ G, seat.fork t = some G ∧ Sized G ∧ Later F' G ∧
            SlotsOwed G g.leaves.first (lvLen g) := by
  obtain ⟨g, F', f', _, hI, ho⟩ :=
    decide_starts seat piece laid before p guests hk hr hF hS hA hd
  refine ⟨g, F', f', hI.1, fun st hst N t hw => ?_⟩
  obtain ⟨hIt, G, hG, hL, hoG⟩ := walked_keeps_under hst N s' t F' hI hw f' ho
  exact ⟨hIt.1, G, hG, hIt.2 G hG, hL, hoG⟩

/-- **There the write of "planes" returns**, where the stretch lies inside the ledger's slots. -/
theorem own_write_returns {G : Fork} {g : Forest.Heard} (hS : Sized G)
    (ho : SlotsOwed G g.leaves.first (lvLen g)) (hroom : g.leaves.first + lvLen g ≤ G.ns) :
    ∃ H, G.hideRun g.leaves.first (Array.replicate (lvLen g) zeroE) (subE zeroE oneE) = some H :=
  owed_returns ho hS.2.2 hroom _ Array.size_replicate _

/-- **Role (A)'s first record, from role (B)'s walk**: where K3 was heard earlier and its own
stretch is still owed in the ledger G, every stretch that begins at or above G's next slot lies
apart from it: so whoever takes slots there and walks its own stretch past K3's steps has K3InvA at
its walk's first record. -/
theorem invA_of_owed {fork : S → Option Fork} {heard : S → Option Forest.Heard} {s : S}
    {g : Forest.Heard} {G : Fork} (hh : heard s = some g) (hG : fork s = some G) (hS : Sized G)
    (ho : SlotsOwed G g.leaves.first (lvLen g)) {a : ℕ} (ha : G.next ≤ a) (n : ℕ) :
    K3InvA fork heard a n s := by
  refine ⟨fun F hF => ?_, fun g' hg' => ?_⟩
  · obtain rfl : G = F := Option.some.inj (hG.symm.trans hF)
    exact hS
  · obtain rfl : g = g' := Option.some.inj (hh.symm.trans hg')
    exact Or.inl (Nat.le_trans ho.1 ha)

/-- And where nothing has been heard at this seat. -/
theorem invA_of_none {fork : S → Option Fork} {heard : S → Option Forest.Heard} {s : S}
    (hh : heard s = none) (hS : ∀ F, fork s = some F → Sized F) (a n : ℕ) :
    K3InvA fork heard a n s :=
  ⟨hS, fun g hg => by rw [hh] at hg; cases hg⟩

/-! ## Two members that must fail -/

/-- A step that lays a heard record. The record: what was heard, and a ledger. -/
def mover (g' : Forest.Heard) : Option Forest.Heard × Fork → Option Forest.Heard × Fork → Prop :=
  fun s s' => s' = (some g', s.2)

/-- **It does not hand the promise on**, where the record's leaves' stretch begins at the watched
stretch's first slot and neither is empty. -/
theorem mover_fails (a n : ℕ) (hn : 1 ≤ n) (g' : Forest.Heard) (h1 : g'.leaves.first = a)
    (hl : 1 ≤ lvLen g') :
    ¬ StepKeepsUnder (K3InvA (fun s : Option Forest.Heard × Fork => some s.2) (·.1) a n)
      (fun s : Option Forest.Heard × Fork => some s.2) a n (mover g') := by
  intro H
  have ho : SlotsOwed (owedLedger a n) a n :=
    ⟨Nat.le_refl _, fun j _ _ => owedLedger_free a n j⟩
  obtain ⟨⟨_, hap⟩, _⟩ := H (none, owedLedger a n) (some g', owedLedger a n) (owedLedger a n)
    ⟨fun F hF => by
        obtain rfl : owedLedger a n = F := Option.some.inj hF
        exact owedLedger_sized a n,
      fun g hg => by cases hg⟩ rfl rfl ho
  have := hap g' rfl
  omega

/-- **Its premises are met**: at every a there is a heard record whose leaves' stretch begins at a
and is not empty. -/
theorem mover_meets (a : ℕ) (g0 : Forest.Heard) :
    ∃ g' : Forest.Heard, g'.leaves.first = a ∧ 1 ≤ lvLen g' := by
  refine ⟨{ g0 with leaves :=
    { first := a, vars := #[OnBytes.Psc.Weight.equality zeroE 2], r := #[zeroE] } }, rfl, ?_⟩
  show 1 ≤ (OnBytes.Psc.hidingWalk
    (zipT [OnBytes.Psc.Weight.equality zeroE 2] [zeroE])).1.length
  decide

/-- A step that writes one slot below the address in the heard record. -/
def offWriter : Option Forest.Heard × Fork → Option Forest.Heard × Fork → Prop :=
  fun s s' => s'.1 = s.1 ∧ ∃ g, s.1 = some g ∧
    s.2.hide (g.leaves.first - 1) zeroE (subE zeroE oneE) = some s'.2

/-- **It fails the law under K3InvA**, at every watched stretch of one slot or more. -/
theorem off_writer_fails (a n : ℕ) (hn : 1 ≤ n) (g0 : Forest.Heard) :
    ¬ StepKeepsUnder (K3InvA (fun s : Option Forest.Heard × Fork => some s.2) (·.1) a n)
      (fun s : Option Forest.Heard × Fork => some s.2) a n offWriter := by
  intro H
  obtain ⟨g, hg1⟩ : ∃ g : Forest.Heard, g.leaves.first = a + n :=
    ⟨{ g0 with leaves := { g0.leaves with first := a + n } }, rfl⟩
  have ho : SlotsOwed (owedLedger a n) a n :=
    ⟨Nat.le_refl _, fun j _ _ => owedLedger_free a n j⟩
  have hj : a + n - 1 < (owedLedger a n).ns := by
    show a + n - 1 < a + n
    omega
  obtain ⟨G, hG⟩ : ∃ G, (owedLedger a n).hide (a + n - 1) zeroE (subE zeroE oneE) = some G :=
    ⟨_, hide_returns (F := owedLedger a n) (j := a + n - 1) zeroE (subE zeroE oneE)
      (owedLedger_sized a n).2.2 hj (owedLedger_free a n _)⟩
  obtain ⟨_, F', e, _, o⟩ := H (some g, owedLedger a n) (some g, G) (owedLedger a n)
    ⟨fun F hF => by
        obtain rfl : owedLedger a n = F := Option.some.inj hF
        exact owedLedger_sized a n,
      fun g2 hg2 => by
        obtain rfl : g = g2 := Option.some.inj hg2
        exact Or.inr (Nat.le_of_eq hg1.symm)⟩
    ⟨rfl, g, rfl, by rw [hg1]; exact hG⟩ rfl ho
  have e' : G = F' := Option.some.inj e
  rw [← e'] at o
  exact o.2 (a + n - 1) (by omega) (by omega)
    (hide_ok _ G _ _ _ (owedLedger_sized a n) hG).2.2.2.2.1

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decide_keepsA
#print axioms VerifiableInference.OnPublicFiles.decide_starts
#print axioms VerifiableInference.OnPublicFiles.own_walk
#print axioms VerifiableInference.OnPublicFiles.own_write_returns
#print axioms VerifiableInference.OnPublicFiles.invA_of_owed
#print axioms VerifiableInference.OnPublicFiles.mover_fails
#print axioms VerifiableInference.OnPublicFiles.mover_meets
#print axioms VerifiableInference.OnPublicFiles.off_writer_fails
