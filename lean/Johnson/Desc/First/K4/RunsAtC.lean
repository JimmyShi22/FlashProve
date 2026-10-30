-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/RunsAtC.lean: THE LAWS OF K4's RUNS AT THE CARRIED RECORD, OF THE BLOCK WHOSE
RUNS ARE TYPED AT THE ONE TYPE OF A CLAIM (`blockAtC p`, Johnson/Desc/First/K4/AtC.lean); and riders
to Johnson/Desc/First/K4/RunsAtS.lean. Statements and proofs.

Riders:
  `wrote_own`: what a run of K4's writes leaves what was heard where `S.own?` reads it.
  `freeSlot_ok`: at a seat: where the run behind the batching returns, what was heard was there and
    THE TEST HELD (`freeSlotOk`): of the slots below `used`, the slot o.wo.sFv has the coefficient 0
    in the one equation, and every other one a coefficient that is not 0. («0»: all three words are
    0, `isZeroE`; a slot beyond the coefficients' end reads as 0.)
  `blockAtS_after`: the block's one run behind the batching, as it stands. `freeSlot_body`,
    `freeSlotAtS_test`: `freeSlot_ok` at the carried record: of that run's body; of the run that the
    name "free-slot" finds.
General in the block b:
  `atClaims_claims`, `atClaims_same`: EVERY FIELD OF `atClaims b` IS PINNED: the list of its runs of
    claims is b's list, run by run, under the same names, each with its forms carried over; name,
    place, test on the plan, rounds, oracles, `before`, `decide`, and the runs behind the batching
    with their functions are b's own.
  `runAtC`: where a run of `atClaims b` returns, b's run of that name returns the same record, and
    the claims are its forms carried over.
At `blockAtC p`:
  `frontAtC`, `backAtC`: `frontAtS`, `backAtS` of the typed block: cl is the listing's forms, each
    as a claim (`claimOf`).
  `frontAtC_pays`, `backAtC_pays`: the core stays; the ledger behind is later; the number of claims.
  `k4C_runsStep`, `k4C_steps`, `k4C_afterStep`: the three frame's laws of
    Johnson/Desc/First/K4/CarriesAtS.lean of the typed block.

Limits. As RunsAtS.lean's and CarriesAtS.lean's. NOTHING HERE SHOWS THAT ANY DECISION OR RUN OF
`blockAtS p` OR `blockAtC p` RETURNS ANYWHERE: a block that refuses all has every law of this file
for nothing. One direction, from a return: of refusals nothing is said. Nothing on the claims'
values. Nothing on soundness.
-/
import Johnson.Desc.First.K4.CarriesAtS
import Johnson.Desc.First.K4.AtCLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim named)
open VerifiableInference.Desc.First (S LayOwn)

/-! ### Two riders -/

/-- What a run of K4's writes leaves what was heard. -/
theorem wrote_own {s s' : S} {a : LayOwn} {G : Fork} (h : Wrote s a G s') :
    s.own? = a.own ∧ s'.own? = a.own := by
  obtain ⟨ha, rfl⟩ := h
  exact ⟨by simp [S.own?, ha], rfl⟩

/-- Where the run behind the batching returns: what was heard is there, the test holds, and the
state is handed on as it is. -/
theorem freeSlot_ok {T : Type} (L : Seat T) {hp : HPlan2} {s s' : T}
    (h : freeSlot L hp s = .ok s') :
    ∃ o, L.own s = some o ∧ freeSlotOk hp.used o.wo.sFv (L.fork s) = true ∧ s' = s := by
  have e := freeSlot_same L h
  unfold freeSlot at h
  cases ho : L.own s with
  | none => simp [ho, named, bind, Except.bind] at h
  | some o =>
    cases hb : freeSlotOk hp.used o.wo.sFv (L.fork s) with
    | false =>
      simp [ho, named, test, VerifiableInference.Desc.need, hb, bind, Except.bind] at h
    | true => exact ⟨o, rfl, hb, e⟩

/-- The block's one run behind the batching, as it stands. -/
theorem blockAtS_after (p : Par) : (blockAtS p).after =
    [("free-slot", fun t => (named "the part is not there" (part? t)).bind fun q =>
      (freeSlot seatOwn p.hp q).map (setPart t))] := rfl

/-- Where that run's body returns: the test held. -/
theorem freeSlot_body {p : Par} {s s' : S}
    (h : ((named "the part is not there" (part? s)).bind fun q =>
      (freeSlot seatOwn p.hp q).map (setPart s)) = .ok s') :
    ∃ (a : LayOwn) (o : Own), a.own = some o ∧ freeSlotOk p.hp.used o.wo.sFv a.F = true ∧
      Wrote s a a.F s' := by
  cases hq : part? s with
  | none => simp [hq, named, Except.bind] at h
  | some q =>
    cases hd : freeSlot seatOwn p.hp q with
    | error e => simp [hq, named, Except.bind, hd, Except.map] at h
    | ok q' =>
      simp only [hq, named, Except.bind, hd, Except.map, Except.ok.injEq] at h
      obtain ⟨a, ha, rfl⟩ := part_some hq
      obtain ⟨o, ho, ht, rfl⟩ := freeSlot_ok seatOwn hd
      exact ⟨a, o, ho, ht, ha, h.symm⟩

/-- **Where the run "free-slot" returns, at the carried record: the test held.** -/
theorem freeSlotAtS_test {p : Par} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) {s s' : S} (h : run s = .ok s') :
    ∃ (a : LayOwn) (o : Own), a.own = some o ∧ freeSlotOk p.hp.used o.wo.sFv a.F = true ∧
      Wrote s a a.F s' := by
  have e : (blockAtS p).after.lookup "free-slot" = some fun t =>
      (named "the part is not there" (part? t)).bind fun q =>
        (freeSlot seatOwn p.hp q).map (setPart t) := by
    rw [blockAtS_after]
    simp
  obtain rfl := Option.some.inj (e.symm.trans hr)
  exact freeSlot_body h

/-! ### The typed block's runs -/

/-- **The list of the runs of claims is the block's, run by run, each with its forms carried
over.** -/
theorem atClaims_claims {T : Type} (b : Block T Aff) :
    (atClaims b).claims = b.claims.map fun x =>
      (x.1, fun n s => (x.2 n s).map fun y => (y.1.map claimOf, y.2)) := rfl

/-- **All but the runs of claims is the block's own.** -/
theorem atClaims_same {T : Type} (b : Block T Aff) :
    (atClaims b).name = b.name ∧ (atClaims b).place = b.place ∧ (atClaims b).planOk = b.planOk ∧
      (atClaims b).rounds = b.rounds ∧ (atClaims b).oracles = b.oracles ∧
      (atClaims b).before = b.before ∧ (atClaims b).decide = b.decide ∧
      (atClaims b).after = b.after :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Where a run of `atClaims b` returns, b's run of that name returns the same record, and the
claims are its forms carried over. -/
theorem runAtC {T : Type} {b : Block T Aff} {name : String}
    {run : Nat → T → Except String (List Claim × T)}
    (hr : (atClaims b).claims.lookup name = some run) {n : Nat} {s s' : T} {cl : List Claim}
    (h : run n s = .ok (cl, s')) :
    ∃ r0 fl, b.claims.lookup name = some r0 ∧ r0 n s = .ok (fl, s') ∧ cl = fl.map claimOf := by
  rw [atClaims_run] at hr
  obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp hr
  cases hd : r0 n s with
  | error e => simp [hd, Except.map] at h
  | ok y =>
    obtain ⟨y1, y2⟩ := y
    simp only [hd, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨r0, y1, h0, hd, rfl⟩

/-- **Where the typed run "front" returns.** -/
theorem frontAtC {p : Par} {run : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "front" = some run) {n : Nat} {s s' : S} {cl : List Claim}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (fs : Array Aff) (G : Fork), a.own = some o ∧
      frontOf p o a.F = some (fs, G) ∧ cl = fs.toList.map claimOf ∧ Wrote s a G s' := by
  obtain ⟨r0, fl, h0, h1, rfl⟩ := runAtC hr h
  obtain ⟨a, o, fs, G, ho, hf, rfl, hw⟩ := frontAtS h0 h1
  exact ⟨a, o, fs, G, ho, hf, rfl, hw⟩

/-- **Where the typed run "back" returns.** -/
theorem backAtC {p : Par} {run : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "back" = some run) {n : Nat} {s s' : S} {cl : List Claim}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (fs : Array Aff) (G : Fork), a.own = some o ∧
      formsBack o a.F = some (fs, G) ∧ cl = fs.toList.map claimOf ∧ Wrote s a G s' := by
  obtain ⟨r0, fl, h0, h1, rfl⟩ := runAtC hr h
  obtain ⟨a, o, fs, G, ho, hf, rfl, hw⟩ := backAtS h0 h1
  exact ⟨a, o, fs, G, ho, hf, rfl, hw⟩

/-- **The typed run "front"**: the core stays; the ledger behind is later; the number of claims. -/
theorem frontAtC_pays {p : Par} {run : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "front" = some run) {n : Nat} {s s' : S} {cl : List Claim}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (G : Fork), a.own = some o ∧ Wrote s a G s' ∧ Core a.F G ∧
      Later a.F G ∧ cl.length = frontLen (!p.k3Runs) p.g o := by
  obtain ⟨r0, fl, h0, h1, rfl⟩ := runAtC hr h
  obtain ⟨a, o, G, ho, hw, hc, hl, hn⟩ := frontAtS_pays h0 h1
  exact ⟨a, o, G, ho, hw, hc, hl, by rw [List.length_map, hn]⟩

/-- **The typed run "back".** -/
theorem backAtC_pays {p : Par} {run : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "back" = some run) {n : Nat} {s s' : S} {cl : List Claim}
    (h : run n s = .ok (cl, s')) :
    ∃ (a : LayOwn) (o : Own) (G : Fork), a.own = some o ∧ Wrote s a G s' ∧ Core a.F G ∧
      Later a.F G ∧ cl.length = 4 := by
  obtain ⟨r0, fl, h0, h1, rfl⟩ := runAtC hr h
  obtain ⟨a, o, G, ho, hw, hc, hl, hn⟩ := backAtS_pays h0 h1
  exact ⟨a, o, G, ho, hw, hc, hl, by rw [List.length_map, hn]⟩

/-! ### The three frame's laws of the typed block -/

/-- **Every run of claims of the typed block carries.** -/
theorem k4C_runsStep {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    ∀ c ∈ (blockAtC p).claims, ∀ (n : Nat) (s : S) (cl : List Claim) (s' : S),
      c.2 n s = .ok (cl, s') → Carried hd s s' := by
  intro c hc n s cl s' h
  have hc' : c ∈ (blockAtS p).claims.map fun x =>
      (x.1, fun n s => (x.2 n s).map fun y => (y.1.map claimOf, y.2)) := hc
  obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc'
  cases hd0 : c0.2 n s with
  | error e => simp [hd0, Except.map] at h
  | ok y =>
    obtain ⟨y1, y2⟩ := y
    simp only [hd0, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact k4_runsStep H p c0 hc0 n s y1 y2 hd0

/-- **Its decision carries.** -/
theorem k4C_steps {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    ∀ (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s' : S),
      (blockAtC p).decide s rs gs = .ok s' → Carried hd s s' :=
  k4_steps H p

/-- **Its run behind the batching carries.** -/
theorem k4C_afterStep {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    ∀ c ∈ (blockAtC p).after, ∀ (s s' : S), c.2 s = .ok s' → Carried hd s s' :=
  k4_afterStep H p

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.wrote_own
#print axioms OnBytes.Desc.First.K4.freeSlotAtS_test
#print axioms OnBytes.Desc.First.K4.atClaims_claims
#print axioms OnBytes.Desc.First.K4.atClaims_same
#print axioms OnBytes.Desc.First.K4.frontAtC
#print axioms OnBytes.Desc.First.K4.backAtC
#print axioms OnBytes.Desc.First.K4.frontAtC_pays
#print axioms OnBytes.Desc.First.K4.backAtC_pays
#print axioms OnBytes.Desc.First.K4.k4C_runsStep
#print axioms OnBytes.Desc.First.K4.k4C_steps
#print axioms OnBytes.Desc.First.K4.k4C_afterStep
