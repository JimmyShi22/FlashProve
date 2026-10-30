-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/CallsAtK9.lean: THE BATCHING's LAW `Calls`
(Johnson/Desc/Sound/FoldSteps.lean) PAID AT THE BATCHING's OWN TEXT: the kind K9's `batch`
(Johnson/Desc/First/Batch/Kind.lean | AtS.lean | Add.lean;
`adds` there calls `addList`: its law `K9L.addList_older`
(Batch/Law/AddAgrees.lean) carries a yes to the older `addAll`). Theorems with their proofs.
THESE SPEAK OF A TEXT OF THE PROTOCOL, at every place p of the kind.

  `batchIs`: WHAT `batch`'s YES IS, WHOLE, at any lens X: the draw's block went on, from t to t₁; at
    t₁ a segment is open and the draw has run; THE CLAIMS WERE CALLED AT t₁, and went on, to
    cls and e; at e a segment is open, with the part s; all of cls were added to s's ledger, giving
    F'; and the record behind is e with that ledger laid.
  `QK9 X p`: that, as the letter Q of `Calls`.
  `callsK9`: GENERAL IN R: if the draw's block steps R, and laying the ledger with claims added
    steps R, then `Calls R (QK9 X p) (batch X p)`.
  `addAll_slots`, `drawn_slots`: adding claims, and the draw, leave the ledger's slots (their
    number, the next one, the three arrays): over the library's `kap_slots` | `push_slots`
    (OnBytes/Tie/Pv/Psc/PscLater.lean).
  `carriesSetAtS`: at the lens at the first chain's carried record (`atS`): laying a part whose
    ledger has the same slots carries what the lookup heard and the ledger.
  **`callsK9AtS`: `Calls (CarriesFo S.fork? S.lookHeard?) (QK9 atS p) (batch atS p)`: AT EVERY PLACE
    p. NO PREMISE.** `callsAtK9AtS`: so `CallsAt … (batch atS p f) f`, for every f: what the
    statements "…At" of FoldSteps.lean ask.

  NOT EMPTY: by evaluation (`#guard`), at a small made-up record `s₀`: `batch atS p₀` says yes with
    no claim and with one claim (chi is drawn; one claim is counted), and no at two claims where one
    is planned, at claims that refuse, at no round, at a second draw, and where no link is open.

Limits. A frame's law: no error, nothing on soundness: it says that the batching calls the claims
and what it does to two readings of the record. By report `batch` itself has
run nowhere: the folds that have ridden lay `drawAlone` and `adds` apart; both are `batch`'s two
halves by its text. K9's kind's files are imported at their true paths (Johnson/Desc/First/Batch/…:
by program the same code as files K9/…).
`batch atS p` IS THE TEXT THAT IS SEATED: it is what K9's lot answers at a place of the kind
(`k9MakerIs`, Johnson/Desc/First/K9x/LotsAtPure.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Law.AddAgrees
import Johnson.Desc.First.LedgerAtFo
import Johnson.Desc.Sound.StepsThrough
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open OnBytes.PscRun (SlotsSame Sized)

variable {T : Type}

theorem thereOk {α : Type} {name : String} {o : Option α} {a : α} (h : there name o = .ok a) :
    o = some a := by
  cases o with
  | none => exact nomatch h
  | some x => exact congrArg some (Except.ok.inj h)

theorem needOk {name : String} {b : Bool} {u : Unit} (h : K9.need name b = .ok u) : b = true := by
  unfold K9.need at h
  split at h
  · assumption
  · exact nomatch h

/-- **What the batching's yes is, whole.** -/
theorem batchIs (X : Lens T) (p : Where) (f : T → Except String (List Claim × T)) (t t' : T)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (H : (batch X p f).decide t rs gs = .ok t') :
    ∃ t₁ s₀ cls e s F', (drawAlone (Cl := Claim) X p).decide t rs gs = .ok t₁ ∧
      X.get? t₁ = some s₀ ∧ s₀.L.handed = true ∧ f t₁ = .ok (cls, e) ∧ X.get? e = some s ∧
      addAll s.F cls = some F' ∧ t' = X.set e { s with F := F' } := by
  obtain ⟨t₁, h₁, H⟩ := bindOk (x := (drawAlone (Cl := Claim) X p).decide t rs gs) H
  obtain ⟨s₀, hs₀, H⟩ := bindOk (x := X.part t₁) H
  obtain ⟨u, hn, H⟩ := bindOk (x := K9.need "K9.draw-has-run" s₀.L.handed) H
  obtain ⟨x, hx, H⟩ := bindOk (x := f t₁) H
  obtain ⟨s, hs, H⟩ := bindOk (x := X.part x.2) H
  obtain ⟨F', hF, H⟩ := bindOk (x := addList s.F x.1) H
  exact ⟨t₁, s₀, x.1, x.2, s, F', h₁, thereOk hs₀, needOk hn, hx, thereOk hs,
    K9L.addList_older _ _ _ hF,
    (Except.ok.inj H).symm⟩

/-- What `batch` did, as the letter Q of `Calls`. -/
def QK9 (X : Lens T) (p : Where) (t : T) (rs : List Fmt.RoundView) (t₁ : T) (cls : List Claim) (e t' : T) :
    Prop :=
  (∃ gs, (drawAlone (Cl := Claim) X p).decide t rs gs = .ok t₁) ∧
    (∃ s₀, X.get? t₁ = some s₀ ∧ s₀.L.handed = true) ∧
    ∃ s F', X.get? e = some s ∧ addAll s.F cls = some F' ∧ t' = X.set e { s with F := F' }

/-- **`Calls` at K9's own text, general in R.** -/
theorem callsK9 {R : T → T → Prop} (X : Lens T) (p : Where)
    (hd : (drawAlone (Cl := Claim) X p).Steps R)
    (ha : ∀ e s cls F', X.get? e = some s → addAll s.F cls = some F' →
      R e (X.set e { s with F := F' })) :
    Calls R (QK9 X p) (batch X p) := by
  intro f t rs gs t' H
  obtain ⟨t₁, s₀, cls, e, s, F', h₁, h₂, h₃, h₄, h₅, h₆, rfl⟩ := batchIs X p f t t' rs gs H
  exact ⟨t₁, cls, e, hd _ _ _ _ h₁, h₄, ha e s cls F' h₅ h₆, ⟨gs, h₁⟩, ⟨s₀, h₂, h₃⟩,
    ⟨s, F', h₅, h₆, rfl⟩⟩

/-! ## The ledger's slots -/

theorem pushRuns_slots {F G : Fork} {k : E} {runs : Array Run2} (h : F.pushRuns k runs = some G) :
    SlotsSame F G := by
  unfold Fork.pushRuns at h
  obtain ⟨tr, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem addClaim_slots {F G : Fork} {cl : Claim} (h : addClaim F cl = some G) : SlotsSame F G := by
  unfold addClaim at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨H, hH, h⟩ := Option.bind_eq_some_iff.1 h
  exact ((OnBytes.PscRun.kap_slots (k := x.1) (G := x.2) hx).trans
    (OnBytes.PscRun.push_slots hH)).trans (pushRuns_slots h)

theorem addAll_slots : ∀ (cls : List Claim) (F G : Fork), addAll F cls = some G → SlotsSame F G
  | [], F, G, h => by
    obtain rfl : F = G := by simpa [addAll] using h
    exact SlotsSame.refl F
  | c :: l, F, G, h => by
    unfold addAll at h
    rw [List.foldlM_cons] at h
    obtain ⟨H, hH, h⟩ := Option.bind_eq_some_iff.1 h
    exact (addClaim_slots hH).trans (addAll_slots l H G h)

theorem drawn_slots {rows : Nat} {chi : E} {owed : Option Nat}
    {used : Nat} {L : LinkCtx} {F : Fork} {o : Drawn}
      (h : drawnClean rows chi owed used L F = .ok o) :
    SlotsSame F o.F := by
  obtain ⟨o', ho, h⟩ := bindOk (x := drawn rows chi owed used L F) h
  obtain ⟨_, _, h⟩ := bindOk (x := K9.need "K9.ledger-empty" (ledgerEmpty F)) h
  obtain ⟨_, _, h⟩ := bindOk (x := K9.need "K9.no-claim-yet" (F.nClaim == 0)) h
  obtain ⟨_, _, h⟩ := bindOk (x := K9.need "K9.a-coefficient-a-slot" (F.LS.size == F.ns)) h
  obtain rfl : o' = o := Except.ok.inj h
  obtain ⟨_, _, ho⟩ := bindOk (x := K9.need "K9.nothing-owed" owed.isNone) ho
  obtain ⟨_, _, ho⟩ := bindOk (x := K9.need "K9.slots-used" (L.list.planned && used == F.ns)) ho
  obtain ⟨_, _, ho⟩ := bindOk (x := K9.need "K9.link-ready"
    (L.list.link && !L.handed && L.moments == L.check.momentsOf L.link)) ho
  obtain ⟨_, _, ho⟩ := bindOk (x := K9.need "K9.drawn-once" !F.thetaDrawnF) ho
  obtain ⟨_, _, ho⟩ := bindOk (x := K9.need "K9.claims-planned" (F.planClaimsF != 0)) ho
  rw [← Except.ok.inj ho]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The same slots: a later ledger in the lookups' order, and the sizes are kept. -/
theorem slotsLater {F G : Fork} (h : SlotsSame F G) : _root_.Fo.Later F G :=
  ⟨Nat.le_of_eq h.next.symm, h.ns, fun j hj => by
    unfold OnBytes.PscRun.Filled at *
    rw [h.vp, h.mf, h.gotF]
    exact ⟨hj, rfl, rfl⟩⟩

theorem slotsSized {F G : Fork} (h : SlotsSame F G) (s : Sized F) : Sized G := by
  unfold Sized at *
  rw [h.vp, h.mf, h.gotF, h.ns]
  exact s

/-! ## At the first chain's carried record -/

/-- Where the lens gives a part, its ledger is the record's. -/
theorem atS_fork {s : S} {q : Part} (h : atS.get? s = some q) : s.fork? = some q.F := by
  obtain ⟨L, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨F, hF, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨used, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [hF, ← Option.some.inj h]

/-- **Laying a part whose ledger has the same slots carries.** -/
theorem carriesSetAtS (s : S) (q q' : Part) (h : atS.get? s = some q) (hs : SlotsSame q.F q'.F) :
    CarriesFo S.fork? S.lookHeard? s (atS.set s q') := by
  have hF := atS_fork h
  have e₁ : (atS.set s q').fork? = ((s.putLink q'.L).putFork q'.F).fork? := rfl
  have e₂ : (atS.set s q').lookHeard? = ((s.putLink q'.L).putFork q'.F).lookHeard? := rfl
  refine ⟨fun g hg => ?_, fun F hF' hsz => ?_⟩
  · rw [e₂, S.look_putFork, S.look_putLink]
    exact hg
  · obtain rfl : q.F = F := Option.some.inj (hF.symm.trans hF')
    exact ⟨q'.F, by rw [e₁]; exact S.fork_putFork _ q.F _ (by rw [S.fork_putLink]; exact hF),
      slotsLater hs, slotsSized hs hsz⟩

theorem drawStepsAtS (p : Where) :
    (drawAlone (Cl := Claim) atS p).Steps (CarriesFo S.fork? S.lookHeard?) := by
  intro t rs gs t' H
  match rs, H with
  | [r], H =>
    obtain ⟨s, hs, H⟩ := bindOk (x := atS.part t) H
    obtain ⟨chi, _, H⟩ := bindOk (x := chiOf r) H
    obtain ⟨o, ho, H⟩ := bindOk (x := drawnClean p.rows chi s.owed s.used s.L s.F) H
    rw [← Except.ok.inj H]
    exact carriesSetAtS t s _ (thereOk hs) (drawn_slots ho)

/-- **THE BATCHING's LAW AT THE BATCHING's OWN TEXT, AT THE CARRIED RECORD, AT EVERY PLACE.** -/
theorem callsK9AtS (p : Where) :
    Calls (CarriesFo S.fork? S.lookHeard?) (QK9 atS p) (batch atS p) :=
  callsK9 atS p (drawStepsAtS p) fun e s cls F' h₁ h₂ =>
    carriesSetAtS e s _ h₁ (addAll_slots cls s.F F' h₂)

/-- **What the statements "…At" ask**: of the block `batch atS p f`, at the function f with which it
was made: for every f: so also where a link's field `batch` does not read its argument and this
block, made with the link's claims, stands there. -/
theorem callsAtK9AtS (p : Where) (f : S → Except String (List Claim × S)) :
    CallsAt (CarriesFo S.fork? S.lookHeard?) (QK9 atS p) (batch atS p f) f :=
  callsAtOfCalls _ _ _ _ _ (callsK9AtS p) f

/-! ## The text says yes somewhere, and no elsewhere: by evaluation -/

/-- A small record: a layers' link is open; its list is closed; no slot; one claim is planned;
nothing is drawn; the ledger is empty. MADE UP: of no proof. -/
def s₀ : S :=
  (S.start default { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ }).enterLay
    { check := { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ }
      list := { link := true, planned := true }, moments := 0 }
    { planClaimsF := 1 } {}

/-- A place. -/
def p₀ : Where := { chain := 1, link := 0, piece := 8, pieceEq := 10, rows := 1, sent := 0 }

/-- A round at which one element was drawn. -/
def r₀ : Fmt.RoundView := ⟨[], ⟨[(5, 0, 0)], [], [], none⟩⟩

/-- Claims: none · one, the form 0. -/
def f₀ (t : S) : Except String (List Claim × S) := .ok ([], t)
def f₁ (t : S) : Except String (List Claim × S) := .ok ([{}], t)

-- YES, with no claim and with one claim.
#guard ((batch atS p₀ f₀).decide s₀ [r₀] []).toOption.isSome
#guard ((batch atS p₀ f₁).decide s₀ [r₀] []).toOption.isSome
-- The ledger behind: chi is drawn; one claim is counted.
#guard (((batch atS p₀ f₁).decide s₀ [r₀] []).toOption.bind (·.fork?)).map
  (fun F => (F.thetaDrawnF, F.nClaim)) == some (true, 1)
-- NO: two claims where one is planned · claims that refuse · no round · a second draw ·
-- where no link is open.
#guard ((batch atS p₀ fun t => .ok ([{}, {}], t)).decide s₀ [r₀] []).toOption.isNone
#guard ((batch atS p₀ fun _ => .error "no").decide s₀ [r₀] []).toOption.isNone
#guard ((batch atS p₀ f₀).decide s₀ [] []).toOption.isNone
#guard (((batch atS p₀ f₀).decide s₀ [r₀] []).toOption.bind fun t =>
  ((batch atS p₀ f₀).decide t [r₀] []).toOption).isNone
#guard ((batch atS p₀ f₀).decide
  (S.start default { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ }) [r₀]
  []).toOption.isNone

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.thereOk
#print axioms VerifiableInference.Desc.K9.needOk
#print axioms VerifiableInference.Desc.K9.batchIs
#print axioms VerifiableInference.Desc.K9.callsK9
#print axioms VerifiableInference.Desc.K9.pushRuns_slots
#print axioms VerifiableInference.Desc.K9.addClaim_slots
#print axioms VerifiableInference.Desc.K9.addAll_slots
#print axioms VerifiableInference.Desc.K9.drawn_slots
#print axioms VerifiableInference.Desc.K9.slotsLater
#print axioms VerifiableInference.Desc.K9.slotsSized
#print axioms VerifiableInference.Desc.K9.atS_fork
#print axioms VerifiableInference.Desc.K9.carriesSetAtS
#print axioms VerifiableInference.Desc.K9.drawStepsAtS
#print axioms VerifiableInference.Desc.K9.callsK9AtS
#print axioms VerifiableInference.Desc.K9.callsAtK9AtS
