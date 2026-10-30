-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/FreeAboveKept.lean: K4 HANDS THE LEDGER's FREE ROOM ON: "every slot from the
ledger's next free number on is free" (the table of joints' public item freeAbove) holds behind a
yes of K4's block, and behind each of its two listings of claims, if it held in front. AND WITH IT
THE NEXT LOOKUP's PROMISE IN FRONT (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean) HOLDS BEHIND
K4's YES UNDER PREMISES THAT ARE ALL ITEMS OF THE TABLE OR NUMBERS OF THE PLAN. A definition,
statements and proofs, off `hear_fresh` (Slots/HearSpares.lean), `formsFront_past`, `formsBack_past`
(Slots/RunsSpare.lean), `kept_atS` (KeptAtS.lean), `k3OnIn_behind` (LookOutKept.lean).

  `freeAboveF G`: a Bool on a ledger: each slot from G.next up to G.ns is free. Its body has run, as
    a Bool on the record, at the borders of an honest walk at which the item is open (a file of
    evaluations; no library file).
  `freeAbove_iff`: written out.
  `freeAbove_fresh`: it goes from F to G if `Fresh F G`, G has F's number of slots and both have
    arrays of the right sizes.
  **`freeAbove_kept`**: at the carried record: where `KeptAtS q s s'` (KeptAtS.lean: a yes of
    `(blockAtS q).decide` gives it: `kept_atS`; so does a yes of the piece: `kept_of_yes`), the
    ledger in front sized and free above: the ledger behind is free above. `sized_kept`: and sized.
  `freeAbove_front`, `freeAbove_back`: the two listings keep it, if their windows lie below the
    ledger's next (premises w1, w2 | w: `hear_wins` has two of the three windows behind the hearing;
    the leaves' is the lookup's).
  `freeAboveN n G`, **`freeAboveN_kept`**: the stronger Bool: the room is free AND the ledger's
    number of slots is n (meant: the plan's): kept by K4's yes likewise
    (`Later.ns`). `k3OnIn_of_itemsN`: with it the bound hm is a test on the plan:
    p.first + elems h ≤ n.
  `unheard_kept`: what is heard at the digits' seat is the same behind K4's yes (`Rest.tl`).
  **`k3OnIn_of_items`**: behind K4's yes `k3OnIn p s' = true`, at a place p with a shape h, IF: (hd)
    nothing is heard at p's seat in front; (hz) the ledger in front is sized; (hf) it is free above;
    (hn) the ledger's next behind K4 is p.first; (hm) p.first + elems h is at most the ledger's
    number of slots.

Limits. ONE DIRECTION, FROM A YES OR A RETURN. hn AND hm ARE NUMBERS OF THE PLAN, PAID NOWHERE HERE
(`hear_next` has the next behind as the merge's first slot + 2 lk + 3). hn SPEAKS OF THE LEDGER
BEHIND K4's YES; THE LOOKUP ON THE DIGITS STANDS FOUR BLOCKS ON: hn is p.first only if the blocks
between take no slot, and the promise must still ride over them: nothing on that here. That the
block's runs lay just the listings' ledgers is `front_ok`, `back_ok`'s. Nothing on soundness.

-/
import Johnson.Road.K4.LookOutKept
import Johnson.Road.K4.Slots.RunsSpare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Filled Later)
open OnBytes.Desc.First.K4 (Par blockAtS Rest formsFrontWith formsBack formsFrontWith_later
  formsBack_later)
open OnBytes.Desc.First.K4.Slots (Fresh SameAt formsFront_past formsBack_past)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (k3OnIn heardAt sizedB freeB)

/-- Each slot from the ledger's next free number up to its number of slots is free. -/
def freeAboveF (G : Fork) : Bool :=
  (List.range (G.ns - G.next)).all fun j => !G.gotF.getD (G.next + j) true

/-- Written out. -/
theorem freeAbove_iff (G : Fork) :
    freeAboveF G = true ↔ ∀ x, G.next ≤ x → x < G.ns → G.gotF.getD x true = false := by
  unfold freeAboveF
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true']
  constructor
  · intro h x h1 h2
    have := h (x - G.next) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  · intro h j hj
    exact h _ (Nat.le_add_right _ _) (by omega)

/-- One slot: what is free in F is free in G, where nothing has turned under it. -/
theorem free_same {F G : Fork} {x : ℕ} (hF : PscRun.Sized F) (hG : PscRun.Sized G)
    (hn : G.ns = F.ns) (hx : x < F.ns) (hs : SameAt F G x) (h : F.gotF.getD x true = false) :
    G.gotF.getD x true = false := by
  have xF : x < F.gotF.size := by
    rw [hF.2.2]
    exact hx
  have xG : x < G.gotF.size := by
    rw [hG.2.2, hn]
    exact hx
  have a : ¬ Filled F x := by
    unfold Filled
    rw [getD_any xF false true, h]
    exact Bool.false_ne_true
  have b : ¬ Filled G x := fun e => a (hs.1.mp e)
  unfold Filled at b
  rw [getD_any xG true false]
  exact eq_false_of_ne_true b

/-- The room goes from F to G, if nothing has turned from G's next on. -/
theorem freeAbove_fresh {F G : Fork} (hF : PscRun.Sized F) (hG : PscRun.Sized G)
    (hn : G.ns = F.ns) (hf : Fresh F G) (h : freeAboveF F = true) : freeAboveF G = true := by
  rw [freeAbove_iff] at h ⊢
  intro x h1 h2
  exact free_same hF hG hn (by omega) (hf.same x (Or.inr h1))
    (h x (Nat.le_trans hf.next h1) (by omega))

/-- **A yes of K4's block hands the room on**: said of `KeptAtS`. -/
theorem freeAbove_kept {q : Par} {s s' : S} (K : KeptAtS q s s')
    (hz : ∀ F, s.fork? = some F → sizedB F = true)
    (hf : ∀ F, s.fork? = some F → freeAboveF F = true) :
    ∀ G, s'.fork? = some G → freeAboveF G = true := by
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _, _, _, _, _, _, hS, _⟩ := K
  have e : s.fork? = some a.F := by simp [S.fork?, ha]
  have sF : PscRun.Sized a.F := (sized_iff _).mp (hz _ e)
  intro G' hG'
  obtain rfl : G = G' := Option.some.inj (h3.symm.trans hG')
  exact freeAbove_fresh sF (hL.sized sF) hL.ns (hS sF).2 (hf _ e)

/-- The listing in front keeps the room, if its two windows lie below the ledger's next. -/
theorem freeAbove_front {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork} {fs : Array Aff}
    (hF : PscRun.Sized F) (h : formsFrontWith rows P g o F = some (fs, G))
    (w1 : o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ F.next)
    (w2 : o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next)
    (hf : freeAboveF F = true) : freeAboveF G = true := by
  obtain ⟨sG, n, k⟩ := formsFront_past hF h w1 w2
  have hn : G.ns = F.ns := (formsFrontWith_later h).ns
  rw [freeAbove_iff] at hf ⊢
  intro x h1 h2
  rw [n] at h1
  exact free_same hF sG hn (by omega) (k x h1) (hf x h1 (by omega))

/-- The listing behind keeps the room, if the merge's window lies below the ledger's next. -/
theorem freeAbove_back {o : Own} {F G : Fork} {fs : Array Aff} (hF : PscRun.Sized F)
    (h : formsBack o F = some (fs, G))
    (w : o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ F.next)
    (hf : freeAboveF F = true) : freeAboveF G = true := by
  obtain ⟨sG, n, k⟩ := formsBack_past hF h w
  have hn : G.ns = F.ns := (formsBack_later h).ns
  rw [freeAbove_iff] at hf ⊢
  intro x h1 h2
  rw [n] at h1
  exact free_same hF sG hn (by omega) (k x h1) (hf x h1 (by omega))

/-- The stronger Bool: the room is free, AND THE LEDGER's NUMBER OF SLOTS IS n (meant: the plan's).
-/
def freeAboveN (n : ℕ) (G : Fork) : Bool := freeAboveF G && G.ns == n

/-- **A yes of K4's block hands on the room and the number of slots.** -/
theorem freeAboveN_kept {q : Par} {s s' : S} (K : KeptAtS q s s') {n : ℕ}
    (hz : ∀ F, s.fork? = some F → sizedB F = true)
    (hf : ∀ F, s.fork? = some F → freeAboveN n F = true) :
    ∀ G, s'.fork? = some G → freeAboveN n G = true := by
  have K' := K
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _⟩ := K'
  have e : s.fork? = some a.F := by simp [S.fork?, ha]
  have k := hf _ e
  unfold freeAboveN at k
  rw [Bool.and_eq_true] at k
  intro G' hG'
  have g1 := freeAbove_kept K hz (fun F hF => by
    have := hf F hF
    unfold freeAboveN at this
    rw [Bool.and_eq_true] at this
    exact this.1) G' hG'
  obtain rfl : G = G' := Option.some.inj (h3.symm.trans hG')
  unfold freeAboveN
  rw [Bool.and_eq_true, hL.ns]
  exact ⟨g1, k.2⟩

/-- The ledger's arrays keep their sizes. -/
theorem sized_kept {q : Par} {s s' : S} (K : KeptAtS q s s')
    (hz : ∀ F, s.fork? = some F → sizedB F = true) : ∀ G, s'.fork? = some G → sizedB G = true := by
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _⟩ := K
  have e : s.fork? = some a.F := by simp [S.fork?, ha]
  intro G' hG'
  obtain rfl : G = G' := Option.some.inj (h3.symm.trans hG')
  exact (sized_iff _).mpr (hL.sized ((sized_iff _).mp (hz _ e)))

/-- What is heard at a lookup's seat is the same behind K4's yes. -/
theorem unheard_kept {q : Par} {s s' : S} (K : KeptAtS q s s')
    (digits : Bool) : heardAt digits s' = heardAt digits s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := K
  unfold heardAt
  rw [hR.tl, hR.lookHeard]

/-- **AT A PLACE WITH A SHAPE (hs), UNDER hd, hz, hf, hn, hm: the next lookup's promise in front
holds behind K4's yes.** -/
theorem k3OnIn_of_items {q : Par} {s s' : S} (K : KeptAtS q s s')
    (p : VerifiableInference.Desc.First.Look.P) {hp : Forest.Shape} (hs : p.shape = some hp)
    (hd : heardAt p.digits s = none) (hz : ∀ F, s.fork? = some F → sizedB F = true)
    (hf : ∀ F, s.fork? = some F → freeAboveF F = true)
    (hn : ∀ G, s'.fork? = some G → G.next = p.first)
    (hm : ∀ F, s.fork? = some F → p.first + Forest.elems hp ≤ F.ns) : k3OnIn p s' = true := by
  have K' := K
  obtain ⟨a, fo, o, G, ha, _, h3, hL, _⟩ := K'
  have e : s.fork? = some a.F := by simp [S.fork?, ha]
  have hle : a.F.next ≤ p.first := by
    rw [← hn G h3]
    exact hL.next
  refine k3OnIn_of_kept K p hs hd (fun F hF => ?_) hn
  obtain rfl : a.F = F := Option.some.inj (e.symm.trans hF)
  refine ⟨hz _ e, ?_⟩
  have k := (freeAbove_iff a.F).mp (hf _ e)
  have m := hm _ e
  unfold freeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  exact ⟨m, fun j hj => k _ (by omega) (by omega)⟩

/-- The same with the room's bound as A TEST ON THE PLAN: hm speaks of the plan's number of
slots. -/
theorem k3OnIn_of_itemsN {q : Par} {s s' : S} (K : KeptAtS q s s')
    (p : VerifiableInference.Desc.First.Look.P) {hp : Forest.Shape} (hs : p.shape = some hp)
    {n : ℕ} (hd : heardAt p.digits s = none) (hz : ∀ F, s.fork? = some F → sizedB F = true)
    (hf : ∀ F, s.fork? = some F → freeAboveN n F = true)
    (hn : ∀ G, s'.fork? = some G → G.next = p.first) (hm : p.first + Forest.elems hp ≤ n) :
    k3OnIn p s' = true :=
  k3OnIn_of_items K p hs hd hz
    (fun F hF => by
      have := hf F hF
      unfold freeAboveN at this
      rw [Bool.and_eq_true] at this
      exact this.1) hn
    (fun F hF => by
      have := hf F hF
      unfold freeAboveN at this
      rw [Bool.and_eq_true, beq_iff_eq] at this
      rw [this.2]
      exact hm)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sized_kept
#print axioms OnBytes.Road.K4.freeAbove_kept
#print axioms OnBytes.Road.K4.freeAbove_front
#print axioms OnBytes.Road.K4.freeAbove_back
#print axioms OnBytes.Road.K4.k3OnIn_of_items
#print axioms OnBytes.Road.K4.freeAboveN_kept
#print axioms OnBytes.Road.K4.k3OnIn_of_itemsN
