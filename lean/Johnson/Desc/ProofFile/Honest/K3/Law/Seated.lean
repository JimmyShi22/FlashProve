-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Seated.lean: from the lookup's hearing `hearV` to the texts
that are seated at a proof file's links: the hearing `hearVia` and the decision `decideVia`
(Johnson/Desc/First/Look/Via/Via.lean), and the late claim of the leaves' sumcheck as the seated run
of claims on the planes makes it, `leavesRowOwn` (Johnson/Desc/First/Look/LookPlanesOwn.lean).
Conditional on `countsOk`. Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("decision", "hearing", "heard structure", "seat", "world, worth"). In
this file the seated hearing is `hearVia`, the seated decision is `decideVia`, and the seated text
of the leaves' late claim is `leavesRowOwn`.

What is shown, by the file's sections.
  1. `keys_of_hearV`: where `hearV` returns at a shape's face: one key tree's point and form, and
     the point has as many coordinates as the shape's keys have bits.
     `countsOk`, `countsOk_iff`: the two public counts that `toHeard` tests, as a test on the shape
       alone; and in plain form.
     `toHeard_returns`, `hearVia_returns`, `decideVia_returns`: so the seated hearing returns, and
       the seated decision accepts, where `hearV` returns, at a place whose parameters make the
       shape and at several calls.
  2. `walk_length`: the program's structure of a heard sumcheck has as many hiding coefficients as
     the part's own.
     `leavesRowOwn_of_row`: where the part's own `row` returns, the seated text returns, with the
       same ledger behind.
     `rowForm_value`: and its form is worth, in every world, what the part's own row is worth.
     `leavesRowOwn_returns`: so the seated text returns wherever the leaves' own slots are owed
       (`SlotsOwed`: free, and below the ledger's next slot).

Hypotheses that remain.
  `countsOk`: a test on public numbers. That every shape which the plan's own maker yields passes it
    is not shown here; Honest/K3/Law/CountsOk.lean shows it at every place's shape.
  `hc` is its name. `hp`, `hN`: (in `hearVia_returns`) the place's parameters make the shape h; it
    has more than one call.
  The seat's four tests in front of the hearing (`hF`, `h0`, `hO`, `hn`, in `decideVia_returns`,
    with `hh`: the seated hearing returns).
  The return of `hearV` (`hh`).
  In `leavesRowOwn_returns` besides: `hS`, `hroom`: the first ledger's arrays have their size, and
    it has room for the lookup's slots; `hS'`, `hL`, `ho`: the later ledger's arrays have their
    size; it is `Later` than the hearing's; the leaves' own slots are owed at it.
  In `toHeard_returns`: `hk`, `hs`: one key tree's point and form; the point's size. In
    `leavesRowOwn_of_row`: `h0`, `hr`: the sumcheck was heard without ends; the part's own row
    returns.

Users. This file is imported by Honest/K3/Law/CountsOk.lean, Honest/K3/Law/SeatedPlanes.lean,
Honest/K3/Law/Seats.lean and Honest/K3/Law/Thread/MergedPoint.lean.

Limits. The run of claims "planes" as a whole (the caller's readers, the packing's test, the mark)
is not reached here: its one step that writes into the ledger is. Shown in: `planesRun_returns`
(Honest/K3/Law/SeatedPlanes.lean), conditional on the caller's readers answering, the packing's
test, the seat's three in front and the return of the leaves' late claim. Nothing is said on what a
claim says of the planes.
Instances: Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LeavesFree
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.First.Look.LookPlanesOwn
import Johnson.Desc.Part.MaskedSumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots hidingAt)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV faceOf toHeard toHeardG toPsc weightOf
  leafVars
  Seat)
open VerifiableInference.Desc.K3.Law (hearVia decideVia)
open VerifiableInference.Desc.First.Look (P leavesRowOwn)
open VerifiableInference.Desc.First.ProdV (layBack)

/-! ## 1 The seated hearing and decision -/

theorem foldl_set_size (g : Nat → Nat) (l : List (Nat × E)) (a : Array E) :
    (l.foldl (fun (r : Array E) x => r.set! (g x.1) x.2) a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, ih]; simp

theorem layBack_size (m : Nat) (order : List Nat) (cs : List E) : (layBack m order cs).size = m :=
    by
  unfold layBack
  rw [foldl_set_size (fun b => m - 1 - b)]
  simp

theorem lastPt_size (orders : Nat → List Nat) (z : Array E) (rs : List Fmt.RoundView) (a n : Nat) :
    (lastPt 0 orders z rs a (n + 1)).size = n + 1 := by
  show (behind (0 + n) _ _ _).size = n + 1
  unfold behind
  rw [Array.size_append, layBack_size]
  simp
  omega

/-- **Where the hearing returns at a shape's face**: one key tree, whose last point has as many
coordinates as the shape's keys have bits.
Conditional on the return of `hearV`. -/
theorem keys_of_hearV (h : Shape) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ pt form, g.keys = [(pt, form)] ∧ pt.size = h.v := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have hp := two_le_planes_of_ok _ hok
  have W := walk (faceOf h) h.v rfl hp hm
  have hv : 1 ≤ h.v := by
    simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hok
    exact hok.1.1.1.2 h.v (by simp [faceOf])
  obtain ⟨n, hn⟩ : ∃ n, h.v = n + 1 := ⟨h.v - 1, by omega⟩
  have hk := W.keys
  cases hq : g.keys with
  | nil => simp [hq] at hk
  | cons a l =>
    cases l with
    | cons b l' => simp [hq] at hk
    | nil =>
      obtain ⟨pt, form⟩ := a
      refine ⟨pt, form, rfl, ?_⟩
      have e : pt = lastPt 0 ((faceOf h).orders 0) #[] rs (oKey (faceOf h)) h.v := by
        simpa [hq] using hk
      rw [e, hn, lastPt_size]

/-- **The two public counts of `toHeard`**, at a key point of h.v coordinates: no call has more
trees than the shape numbers; each call's key point has as many coordinates as the call's
keys have bits. -/
def countsOk (h : Shape) : Bool :=
  (h.iota.all fun i => decide (i ≤ h.rK)) && ((List.range h.NC).all fun c =>
    (h.v - h.dT - (h.rK - h.iota.getD c 0)) + min h.dT h.v == ((h.calls[c]?).map (·.n)).getD 0)

/-- The two counts in plain form: a shape's keys have dT + rK bits by definition, so the second
count says that a call's keys have dT bits more than its trees' number has. -/
theorem countsOk_iff (h : Shape) :
    countsOk h = true ↔ (∀ i ∈ h.iota.toList, i ≤ h.rK) ∧
      ∀ c, c < h.NC → h.iota.getD c 0 ≤ h.rK →
        h.iota.getD c 0 + h.dT = ((h.calls[c]?).map (·.n)).getD 0 := by
  have hv : h.v = h.dT + h.rK := rfl
  unfold countsOk
  rw [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true_iff_forall_mem]
  simp only [decide_eq_true_eq, beq_iff_eq, List.mem_range, Array.mem_toList_iff, hv]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, fun c hc hi => by have := b c hc; omega⟩
  · rintro ⟨a, b⟩
    refine ⟨a, fun c hc => ?_⟩
    by_cases hs : c < h.iota.size
    · have hi : h.iota.getD c 0 ≤ h.rK := by
        have : h.iota.getD c 0 = h.iota[c] := by simp [Array.getD, hs]
        rw [this]
        exact a _ (Array.getElem_mem hs)
      have := b c hc hi
      omega
    · have hz : h.iota.getD c 0 = 0 := by simp [Array.getD, hs]
      have := b c hc (by omega)
      omega

/-- **`toHeard` returns**, and what it gives is what was heard: the leaves' sumcheck as the
program's structure, the bits' slot, the claims, the debts, the shift, alpha, the public factor, the
two points, the key tree's last form; and the factor of a bit in a leaf is the face's own.
Conditional on `countsOk` (shown at every place's shape in Honest/K3/Law/CountsOk.lean) and on one
key tree whose point has h.v coordinates (`keys_of_hearV`). -/
theorem toHeard_returns (h : Shape) (g : HeardV) (pt : Array E) (form : Aff)
    (hk : g.keys = [(pt, form)]) (hs : pt.size = h.v) (hc : countsOk h = true) :
    ∃ g', toHeard h (toHeardG g) = some g' ∧ g'.shape = h ∧ g'.leaves = toPsc g.leaves ∧
      g'.sBit = g.sBit ∧ g'.rows = g.rows ∧ g'.owedPlanes = g.owedPlanes ∧
      g'.owedObjects = g.owedObjects ∧ g'.owedJoin = g.owedJoin ∧
      g'.theta = g.theta ∧ g'.alpha = g.alpha ∧ g'.a = g.a ∧ g'.zb0 = g.zb0 ∧ g'.zb1 = g.zb1 ∧
      g'.cEnd = form ∧ g'.leavesA = (faceOf h).leaf g.theta g.alpha g.zb0 := by
  have hk' : (toHeardG g).keys = [(pt, form)] := hk
  unfold countsOk at hc
  rw [Bool.and_eq_true] at hc
  have h2 : ((List.range h.NC).all fun c =>
      (((Array.range h.NC).map fun c =>
        (pt.extract h.dT pt.size).extract (h.rK - h.iota.getD c 0) (pt.extract h.dT pt.size).size ++
          pt.extract 0 h.dT).getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0) = true := by
    rw [List.all_eq_true] at hc ⊢
    intro c hcm
    have hlt : c < h.NC := List.mem_range.1 hcm
    have := hc.2 c hcm
    simp only [beq_iff_eq] at this ⊢
    rw [← this]
    simp [Array.getD, hlt, hs]
    omega
  unfold toHeard
  rw [hk']
  simp only [hc.1, h2, Bool.and_self, if_true]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The seated hearing returns where `hearV` returns.**
Conditional on the return of `hearV`, several calls and `countsOk`. Instances:
Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation). -/
theorem hearVia_returns (p : P) (h : Shape) (hp : p.shape = some h) (hN : 1 < h.NC)
    (hc : countsOk h = true) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g', toHeard h (toHeardG g) = some g' ∧ hearVia p F rs = some (g', G) := by
  obtain ⟨pt, form, hk, hs⟩ := keys_of_hearV h hh
  obtain ⟨g', hg, _⟩ := toHeard_returns h g pt form hk hs hc
  refine ⟨g', hg, ?_⟩
  unfold hearVia
  rw [hp]
  simp only [hN, if_true, hh, Option.bind_some, hg, Option.map_some]

/-- **The seated decision accepts**: a sub-proof's ledger is open; nothing is heard yet at the seat;
no rows are owed; the ledger's count of slots is the place's; and the seated hearing returns. This
is the decision's acceptance, not that the seat has stored what was heard: that is shown in
Honest/K3/Law/Seats.lean. Conditional on these five. Instances, and an alteration for four of them
(not for "no rows are owed"): Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation).
-/
theorem decideVia_returns {S Cl : Type} (seat : Seat S Cl) (p : P) (s : S) {F G : Fork}
    {rs : List Fmt.RoundView} {g' : OnBytes.Model.Forest.Heard} (hF : seat.fork s = some F)
    (h0 : (seat.heard s).isNone = true) (hO : (seat.owed s).noneWaits = true)
    (hn : F.next = p.first) (hh : hearVia p F rs = some (g', G)) :
    decideVia seat p s rs = .ok (seat.put s g' G) := by
  unfold decideVia
  simp [hF, h0, hO, hn, hh, named, need, bind, Except.bind, pure, Except.pure]

/-! ## 2 The late claim of the leaves' sumcheck, as it is seated -/

theorem weightOf_eq : weightOf = Var.weight := by
  funext v
  cases v <;> rfl

/-- The program's walk over its structure of a heard sumcheck, in the part's own pairs. -/
theorem walk_eq (hd : MaskedSum.Heard) :
    (toPsc hd).walk = OnBytes.Psc.hidingWalk ((hd.vars.zip hd.r).map MaskedSum.asW) := by
  unfold OnBytes.Model.Psc.walk toPsc
  simp only
  rw [OnBytes.zipT_eq, weightOf_eq, MaskedSum.zip_weight]

/-- The program's structure of a heard sumcheck has as many hiding coefficients as
the part's own. -/
theorem walk_length (hd : MaskedSum.Heard) :
    (toPsc hd).walk.1.length = (hidingAt (hd.vars.zip hd.r)).1.length := by
  have h := congrArg List.length (MaskedSum.hidingAt_read Reading.gl (hd.vars.zip hd.r)).1
  rw [List.length_map, List.length_map] at h
  rw [h]
  rw [walk_eq]

/-- **Where the part's own row returns, the seated text returns, with the same ledger behind.** hd:
a structure that the part's hearing made at a call without ends.
Conditional on the return of the part's `hear` and `row`. -/
theorem leavesRowOwn_of_row {C : Aff} {vs : List Var} {F₀ G₀ F' G' : Fork} {rs₀ : List Fmt.RoundView}
    {hd : MaskedSum.Heard} {S0 S1 : E} {kept kept1 y : Aff} (t : OnBytes.K.Kc.Tape)
    (h0 : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F₀ rs₀ = some (hd, G₀))
    (hr : MaskedSum.row hd S0 kept F' = some (y, G')) :
    leavesRowOwn (toPsc hd) S1 kept1 F' t = some ((toPsc hd).rowForm S1 kept1, G', t) := by
  obtain ⟨hs, T, R, _, hR, he, _⟩ := MaskedSum.hear_spec h0
  have hlen : R.rounds.length = vs.length := MaskedSum.readAll_none_len hR
  have hne : vs.isEmpty = false := by
    simp only [MaskedSum.shapeOk, Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hv : hd.vars = vs := by rw [he]; rfl
  have hrl : hd.r.length = vs.length := by rw [he]; simp [hlen]
  have hcond : (!(toPsc hd).rowMade && (toPsc hd).started && !(toPsc hd).vars.isEmpty &&
      (toPsc hd).r.size == (toPsc hd).vars.size) = true := by
    cases vs with
    | nil => simp at hne
    | cons v vs' => simp [toPsc, hv, hrl]
  have hw := MaskedSum.row_write hr
  rw [← walk_length] at hw
  have hw' : F'.hideRun (toPsc hd).first (Array.replicate (toPsc hd).walk.1.length zeroE)
      (subE zeroE oneE) = some G' := hw
  simp only [leavesRowOwn, bind, OnBytes.K.Kc.Fl.andThen, OnBytes.K.Kc.Fl.must,
    OnBytes.K.Kc.Fl.change, pure, OnBytes.K.Kc.Fl.ret, hcond, if_true, hw', Option.map_some]

/-- **The seated text's form is worth what the part's own row is worth**, in every
world and reading. -/
theorem rowForm_value {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (hd : MaskedSum.Heard)
    (S0 : E) (kept : Aff) :
    ((toPsc hd).rowForm S0 kept).value ρ W = (MaskedSum.rowAff hd S0 kept).value ρ W := by
  obtain ⟨h1, h2⟩ := MaskedSum.hidingAt_read ρ (hd.vars.zip hd.r)
  rw [OnBytes.Model.Psc.rowForm_value, MaskedSum.rowAff_value, walk_eq,
    MaskedSum.sumFrom_congr ρ W _ _ _ h1, h2]
  rfl

/-- **The seated text of the leaves' late claim returns**, at every later ledger with arrays of the
right size at which the leaves' own slots are owed; its form is the program's own on the structure
that `toHeard` gives. Conditional on the return of `hearV`, on `Sized` and room in front, and on the
leaves' own slots being owed at F'. Instances (through the run of claims):
Honest/K3/Law/SeatedGuards.lean [not in this library] (by evaluation). -/
theorem leavesRowOwn_returns (f : LFace) {F G F' : Fork} {x : List Fmt.RoundView} {g : HeardV}
    (hS : Sized F) (hroom : F.next + f.slots ≤ F.ns) (hh : hearV f F x = some (g, G))
    (hS' : Sized F') (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot f .leaves) (Stage.own f .leaves)) :
    ∃ G', Later F' G' ∧ ∀ (S1 : E) (kept1 : Aff) (t : OnBytes.K.Kc.Tape),
      leavesRowOwn (toPsc g.leaves) S1 kept1 F' t =
        some ((toPsc g.leaves).rowForm S1 kept1, G', t) := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have hp := two_le_planes_of_ok f hok
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, hn⟩ := leaves_heard f hS hm
  have hF0 := leaves_first f hp hn
  have hown : Stage.own f .leaves = 1 + f.mu + 2 * f.d := slots_leaves f
  have hall : ownSlots ({ lead := 0, vs := leafVars f z, ends := none } : Call).all =
      1 + f.mu + 2 * f.d := own_leafVars f z
  have hns : F'.ns = F.ns := hL.ns.trans (hearV_later hh).ns
  have hr := MaskedSum.row_returns_later h0 hS' (by rw [hall, hns]; omega)
    (fun j a b => ho.2 j (by omega) (by rw [hall] at b; omega)) oneE {}
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hr
  have hy' : MaskedSum.row g.leaves oneE {} F' = some (y.1, y.2) := hy
  exact ⟨y.2, MaskedSum.row_keeps hy', fun _ _ t => leavesRowOwn_of_row t h0 hy'⟩

#print axioms ProofFile.Honest.K3.Law.foldl_set_size
#print axioms ProofFile.Honest.K3.Law.layBack_size
#print axioms ProofFile.Honest.K3.Law.lastPt_size
#print axioms ProofFile.Honest.K3.Law.keys_of_hearV
#print axioms ProofFile.Honest.K3.Law.countsOk_iff
#print axioms ProofFile.Honest.K3.Law.toHeard_returns
#print axioms ProofFile.Honest.K3.Law.hearVia_returns
#print axioms ProofFile.Honest.K3.Law.decideVia_returns
#print axioms ProofFile.Honest.K3.Law.weightOf_eq
#print axioms ProofFile.Honest.K3.Law.walk_eq
#print axioms ProofFile.Honest.K3.Law.walk_length
#print axioms ProofFile.Honest.K3.Law.leavesRowOwn_of_row
#print axioms ProofFile.Honest.K3.Law.rowForm_value
#print axioms ProofFile.Honest.K3.Law.leavesRowOwn_returns

end ProofFile.Honest.K3.Law
