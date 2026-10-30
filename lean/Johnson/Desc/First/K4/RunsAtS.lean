-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/RunsAtS.lean: WHAT K4's RUNS WRITE AT THE FIRST CHAIN's CARRIED RECORD, AS
EQUATIONS: the two runs of claims "front" and "back" and the run "free-slot" behind the batching, of
the block that rides (`blockAtS p`, Johnson/Desc/First/K4/AtS.lean: K4's block lifted along the lens
`part?`, `setPart`). Statements and proofs.

  `liftPart_run`, `liftPart_after`: a run of a lifted block is the block's own run of that name,
    lifted. General in the block.
  `Wrote s a G s'`: the chain stands in a layers' link a, and s' is s with the ledger G laid in that
    link and the debt of rows read once through the lens ("some 0" comes back as none). ALL ELSE OF
    s IS UNTOUCHED.
  `frontAtS`, `backAtS`: WHERE THE RUN RETURNS (cl, s'): what was heard, o, lies in the link; the
    plain listing at o and the link's ledger returns (fs, G); cl is fs as a list; `Wrote s a G s'`.
  `freeSlotAtS`: where it returns s': `Wrote s a a.F s'`: the ledger is as it was.
  `frontAtS_pays`, `backAtS_pays`: so, at the carried record: eleven of the ledger's fifteen fields
    stay (`Core`); G is a later ledger (`Later`); what was heard stays in the link; the number of
    claims is `frontLen (!p.k3Runs) p.g o`, or 4.

What it is for: «link for proof file»'s premise RunOk on a run of claims speaks at the carried
record. Of its clauses these pay, for K4's two runs: the core stays; the ledger behind is later; the
run writes the link's ledger and (at one state) the debt's form, and nothing else of the record; the
number of claims is a function of what was heard.

Limits. NOT PAID: RunOk's equation on the sum of the claims' values; that its lens (atS) finds its
part behind the run, and its letters core, good, Fx: its Lean is not with us, so these are read off
its posts' words. THE RUN CAN WRITE `rowsOwed`: at rowsOwed = some 0 it lays none. One direction,
from a return. Nothing on soundness.
-/
import Johnson.Desc.First.K4.RunsCore
import Johnson.Desc.First.K4.RunsLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block named)
open VerifiableInference.Desc.First (S LayOwn)

/-! ### A lifted block's runs -/

/-- A run of claims of a lifted block is the block's own run of that name, lifted. -/
theorem liftPart_run {T U Cl : Type} (get? : T → Option U) (set : T → U → T) (b : Block U Cl)
    (name : String) :
    (b.liftPart get? set).claims.lookup name =
      (b.claims.lookup name).map fun run n t =>
        (named "the part is not there" (get? t)).bind fun q =>
          (run n q).map fun y => (y.1, set t y.2) := by
  show (b.claims.map fun c => (c.1, fun n t =>
    (named "the part is not there" (get? t)).bind fun q =>
      (c.2 n q).map fun y => (y.1, set t y.2))).lookup name = _
  induction b.claims with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    cases name == x.1 with
    | true => rfl
    | false => exact ih

/-- The like for a run behind the batching. -/
theorem liftPart_after {T U Cl : Type} (get? : T → Option U) (set : T → U → T) (b : Block U Cl)
    (name : String) :
    (b.liftPart get? set).after.lookup name =
      (b.after.lookup name).map fun run t =>
        (named "the part is not there" (get? t)).bind fun q => (run q).map (set t) := by
  show (b.after.map fun c => (c.1, fun t =>
    (named "the part is not there" (get? t)).bind fun q => (c.2 q).map (set t))).lookup name = _
  induction b.after with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    cases name == x.1 with
    | true => rfl
    | false => exact ih

/-! ### What is written -/

/-- The chain stands in a layers' link a; s' is s with the ledger G laid in that link, and the debt
of rows read once through the lens. -/
def Wrote (s : S) (a : LayOwn) (G : Fork) (s' : S) : Prop :=
  s.here = .lay a ∧
    s' = { s with here := .lay { a with F := G },
                  rowsOwed := if s.noneWaits then none else s.rowsOwed }

/-- The lens finds a part just inside a layers' link. -/
theorem part_some {s : S} {q : Part} (h : part? s = some q) :
    ∃ a, s.here = .lay a ∧ q = (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
  cases hs : s.here with
  | lay a =>
    simp only [part?, hs, Option.some.injEq] at h
    exact ⟨a, rfl, h.symm⟩
  | between => simp [part?, hs] at h
  | att _ => simp [part?, hs] at h
  | head _ => simp [part?, hs] at h
  | fin _ => simp [part?, hs] at h
  | mem _ => simp [part?, hs] at h

/-- A lifted run of claims of K4's, taken apart. -/
theorem runOfAtS {name : String} {f : Own → Fork → Option (Array Aff × Fork)} {s s' : S}
    {cl : List Aff}
    (h : ((named "the part is not there" (part? s)).bind fun q =>
      (runOf seatOwn name f q).map fun y => (y.1, setPart s y.2)) = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (fs : Array Aff) (G : Fork),
      a.own = some o ∧ f o a.F = some (fs, G) ∧ cl = fs.toList ∧ Wrote s a G s' := by
  cases hq : part? s with
  | none => simp [hq, named, Except.bind] at h
  | some q =>
    cases hd : runOf seatOwn name f q with
    | error e => simp [hq, named, Except.bind, hd, Except.map] at h
    | ok y =>
      simp only [hq, named, Except.bind, hd, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨a, ha, rfl⟩ := part_some hq
      obtain ⟨o, fs, G, ho, hf, hc, e⟩ := (runOf_ok seatOwn name f _ y.2 y.1).mp hd
      refine ⟨a, o, fs, G, ho, hf, h.1.symm.trans hc, ha, ?_⟩
      rw [← h.2, e]
      rfl

/-- **Where the run "front" returns, at the carried record.** -/
theorem frontAtS {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (fs : Array Aff) (G : Fork),
      a.own = some o ∧ frontOf p o a.F = some (fs, G) ∧ cl = fs.toList ∧ Wrote s a G s' := by
  have e := liftPart_run part? setPart (block seatOwn p) "front"
  rw [block_front] at e
  obtain rfl := Option.some.inj (e.symm.trans hr)
  exact runOfAtS h

/-- **Where the run "back" returns, at the carried record.** -/
theorem backAtS {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "back" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (fs : Array Aff) (G : Fork),
      a.own = some o ∧ formsBack o a.F = some (fs, G) ∧ cl = fs.toList ∧ Wrote s a G s' := by
  have e := liftPart_run part? setPart (block seatOwn p) "back"
  rw [block_back] at e
  obtain rfl := Option.some.inj (e.symm.trans hr)
  exact runOfAtS h

/-- **Where the run "free-slot" returns, at the carried record**: the ledger is as it was. -/
theorem freeSlotAtS {p : Par} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) {s s' : S} (h : run s = .ok s') :
    ∃ a : LayOwn, Wrote s a a.F s' := by
  have e := liftPart_after part? setPart (block seatOwn p) "free-slot"
  have eb : (block seatOwn p).after.lookup "free-slot" = some (freeSlot seatOwn p.hp) := by
    simp [block]
  rw [eb] at e
  obtain rfl := Option.some.inj (e.symm.trans hr)
  have h' : ((named "the part is not there" (part? s)).bind fun q =>
      (freeSlot seatOwn p.hp q).map (setPart s)) = .ok s' := h
  cases hq : part? s with
  | none => simp [hq, named, Except.bind] at h'
  | some q =>
    cases hd : freeSlot seatOwn p.hp q with
    | error e => simp [hq, named, Except.bind, hd, Except.map] at h'
    | ok q' =>
      simp only [hq, named, Except.bind, hd, Except.map, Except.ok.injEq] at h'
      obtain ⟨a, ha, rfl⟩ := part_some hq
      rw [freeSlot_same seatOwn hd] at h'
      exact ⟨a, ha, h'.symm⟩

/-! ### What that pays -/

/-- **The run "front" at the carried record**: the core stays; the ledger behind is later; what was
heard stays; the number of claims is a function of what was heard. -/
theorem frontAtS_pays {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (G : Fork), a.own = some o ∧ Wrote s a G s' ∧ Core a.F G ∧
      Later a.F G ∧ cl.length = frontLen (!p.k3Runs) p.g o := by
  obtain ⟨a, o, fs, G, ho, hf, hc, hw⟩ := frontAtS hr h
  refine ⟨a, o, G, ho, hw, ?_, ?_, ?_⟩
  · unfold frontOf at hf
    split at hf
    · exact formsFrontWith_core hf
    · exact formsFrontWith_core hf
  · unfold frontOf at hf
    split at hf
    · exact formsFrontWith_later hf
    · exact formsFrontWith_later hf
  · rw [hc, Array.length_toList]
    unfold frontOf at hf
    cases hk : p.k3Runs with
    | true =>
      simp only [hk, if_true] at hf
      exact formsFrontWith_length hf
    | false =>
      simp only [hk, Bool.false_eq_true, if_false] at hf
      exact formsFrontWith_length hf

/-- **The run "back" at the carried record.** -/
theorem backAtS_pays {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "back" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (G : Fork), a.own = some o ∧ Wrote s a G s' ∧ Core a.F G ∧
      Later a.F G ∧ cl.length = 4 := by
  obtain ⟨a, o, fs, G, ho, hf, hc, hw⟩ := backAtS hr h
  exact ⟨a, o, G, ho, hw, formsBack_core hf, formsBack_later hf, by
    rw [hc, Array.length_toList]
    exact formsBack_length hf⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.frontAtS
#print axioms OnBytes.Desc.First.K4.backAtS
#print axioms OnBytes.Desc.First.K4.freeSlotAtS
#print axioms OnBytes.Desc.First.K4.frontAtS_pays
#print axioms OnBytes.Desc.First.K4.backAtS_pays
