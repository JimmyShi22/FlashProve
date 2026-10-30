-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/BatYes.lean: WHEN K9's BATCHING SAYS YES, AND WHEN K9's TESTS BEHIND IT DO: from
named Bools with code. Statements and proofs ON THE VERIFIER's OWN TEXT; no prover is in this file, and no goal
is stated.

  `drawReady a`     K9's eight tests at the draw, as one Bool on K9's part of the state: nothing owed · the slots
                    used · the link ready · not drawn before · claims planned · the ledger empty · no claim yet ·
                    a coefficient a slot
  `draw_iff`        **the draw says yes at x just where a segment is open and `drawReady` holds**: SO ITS YES HANGS
                    ON NO CHALLENGE
  `batch_join`      the other direction of `batch_split` (Honest/K9/FallFew.lean): where `gathered` answers and
                    K9's adding returns, the batching says yes, to the gathered state with the new ledger
  `batch_yes`       so the batching says yes where: `gathered` answers · the ledger behind the gatherer can take
                    the claims (`K9H.addReady`) · each claim fits (`K9H.claimFits`)
                    (Johnson/Desc/K9/Honest/AddYes.lean); and which ledger lies behind
  `gathered_of`     `gathered` answers where `drawReady` holds and the gatherer returns behind the draw
  `ready_behind`    K9's OWN SHARE OF `addReady`: out of what the draw leaves and the ledger's core kept: IF THE
                    EQUATION WAS OPEN IN FRONT OF THE DRAW: no test at the draw asks that: A DEBT OF WHOEVER
                    SAYS WHAT STANDS IN FRONT
  `fits_behind`     the claims' test may be asked at the arrays behind the draw
  `round_fit`       a real round's one drawn element, with or without a sealed digest, as `Block.step` shows it
  `batch_yes_of`    **THE PIECES JOINED: from named facts on the state in front and on the gatherer: the batching
                    says yes at x, and in the open ledger behind it as many claims are counted as the gatherer
                    made** (what "K9.claims-counted" in the tests behind then holds against the plan's number)
  `tests_iff`       K9's tests behind the adding at the proof file's description (`k9Tests`): a yes is: a segment
                    is open · `slotsFree` (the value test: the fall's) · the sort's counts hold (structure)

WHAT IS NOT CLAIMED. That any of these Bools is true at a state of a run. That the gatherer answers: other kinds'
runs. AT K9's BARE BATCHING: the description's makers wrap it. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf
import Johnson.Desc.K9.Honest.AddYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS tAtS Where mergeOf drawAlone drawnClean drawn ledgerEmpty chiOf need
  batch addList)
open VerifiableInference.Desc.K9H (addReady claimFits addList_yes AddedAll)

/-- K9's eight tests at the draw. -/
def drawReady (a : VerifiableInference.Desc.K9.Part) : Bool :=
  a.owed.isNone && (a.L.list.planned && a.used == a.F.ns) &&
    (a.L.list.link && !a.L.handed && a.L.moments == a.L.check.momentsOf a.L.link) &&
    !a.F.thetaDrawnF && a.F.planClaimsF != 0 && ledgerEmpty a.F && a.F.nClaim == 0 &&
    a.F.LS.size == a.F.ns

theorem clean_iff (rows : Nat) (x : E) (a : VerifiableInference.Desc.K9.Part) :
    (∃ o, drawnClean rows x a.owed a.used a.L a.F = .ok o) ↔ drawReady a = true := by
  unfold drawnClean drawn drawReady
  cases a.owed.isNone <;> cases (a.L.list.planned && a.used == a.F.ns) <;>
    cases (a.L.list.link && !a.L.handed && a.L.moments == a.L.check.momentsOf a.L.link) <;>
    cases a.F.thetaDrawnF <;> cases (a.F.planClaimsF != 0) <;> cases ledgerEmpty a.F <;>
    cases (a.F.nClaim == 0) <;> cases (a.F.LS.size == a.F.ns) <;>
    simp [need, bind, Except.bind, pure, Except.pure]

/-- **The draw's yes.** -/
theorem draw_iff (p : Where) (s : S) (x : E) :
    (∃ t, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t) ↔
      ∃ a, atS.get? s = some a ∧ drawReady a = true := by
  have hd : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] =
      (atS.part s).bind fun a => (drawnClean p.rows x a.owed a.used a.L a.F).bind fun o =>
        .ok (atS.set s { a with owed := o.owed, L := o.L, F := o.F }) := rfl
  rw [hd]
  unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there
  cases hq : atS.get? s with
  | none => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | some a =>
    constructor
    · rintro ⟨t, h⟩
      obtain ⟨o, ho, _⟩ := bind_ok (x := drawnClean p.rows x a.owed a.used a.L a.F) h
      exact ⟨a, rfl, (clean_iff p.rows x a).1 ⟨o, ho⟩⟩
    · rintro ⟨b, hb, hr⟩
      obtain rfl : a = b := Option.some.inj hb
      obtain ⟨o, ho⟩ := (clean_iff p.rows x a).2 hr
      exact ⟨_, by show (drawnClean p.rows x a.owed a.used a.L a.F).bind _ = _; rw [ho]; rfl⟩

/-- Where a segment is open in front of a yes of the draw. -/
theorem draw_open (p : Where) (s t₁ : S) (x : E)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    ∃ a, atS.get? s = some a := by
  obtain ⟨a, hs₀, _⟩ := bind_ok (x := atS.part s) h
  unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there at hs₀
  cases hq : atS.get? s with
  | none => rw [hq] at hs₀; exact nomatch hs₀
  | some b => exact ⟨b, rfl⟩

/-- **Where `gathered` answers and the adding returns, the batching says yes.** -/
theorem batch_join (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim) (G : Fork)
    (hy : gathered p g s x = some y) (hG : addList y.2.1.F y.2.2 = .ok G) :
    (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok (atS.set y.1 { y.2.1 with F := G }) := by
  obtain ⟨t₁, hd, hg, he⟩ := gathered_split p g s x y hy
  obtain ⟨a, ha⟩ := draw_open p s t₁ x hd
  obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ x a ha hd
  have h2 := hl.handed
  have hb : (batch atS p g).decide s [⟨[], drawnOne x⟩] [] =
      ((drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] []).bind fun t₁ =>
        (atS.part t₁).bind fun s₀ => (need "K9.draw-has-run" s₀.L.handed).bind fun _ =>
          (g t₁).bind fun z => (atS.part z.2).bind fun a => (addList a.F z.1).bind fun F =>
            .ok (atS.set z.2 { a with F := F }) := rfl
  have p1 : atS.part t₁ = .ok a₁ := by
    unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there
    rw [h1]
  have p2 : atS.part y.1 = .ok y.2.1 := by
    unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there
    rw [he]
  rw [hb, hd]
  simp only [Except.bind, p1, h2, need, hg, p2, hG, if_true]

/-- **The batching's yes, out of named Bools**: and what ledger lies behind it. -/
theorem batch_yes (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (hy : gathered p g s x = some y) (hr : addReady y.2.1.F y.2.2.length = true)
    (hf : y.2.2.all (claimFits y.2.1.F.trees y.2.1.F.ns) = true) :
    ∃ G, (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok (atS.set y.1 { y.2.1 with F := G }) ∧
      addList y.2.1.F y.2.2 = .ok G ∧ AddedAll y.2.1.F G y.2.2.length := by
  obtain ⟨G, hG, hA⟩ := addList_yes y.2.2 y.2.1.F hr hf
  exact ⟨G, batch_join p g s x y G hy hG, hG, hA⟩

/-- **`gathered` answers** where: a segment is open and `drawReady` holds · the gatherer returns at the state
behind the draw · K9's lens answers behind the gatherer. -/
theorem gathered_of (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (a : VerifiableInference.Desc.K9.Part) (ha : atS.get? s = some a) (hr : drawReady a = true)
    (hg : ∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      ∃ z a', g t₁ = .ok z ∧ atS.get? z.2 = some a') :
    ∃ y, gathered p g s x = some y := by
  obtain ⟨t₁, ht⟩ := (draw_iff p s x).2 ⟨a, ha, hr⟩
  obtain ⟨z, a', hz, ha'⟩ := hg t₁ ht
  refine ⟨(z.2, a', z.1), ?_⟩
  unfold gathered
  simp only [ht, hz, ha', Option.map_some]

/-- **K9's OWN SHARE OF `addReady`**: behind the draw, and behind a gatherer that keeps the ledger's core, the
ledger can take k claims, for every k up to the plan's number: IF THE EQUATION WAS OPEN IN FRONT OF THE DRAW,
which no test at the draw asks. -/
theorem ready_behind (a a₁ a' : VerifiableInference.Desc.K9.Part) (x : E) (hl : DrawLeaves a a₁ x)
    (hc : LedgerCore a₁ a') (hdoor : a.F.doorShutF = false) (k : Nat) (hk : k ≤ a.F.planClaimsF) :
    addReady a'.F k = true := by
  unfold addReady
  rw [hc.door, hl.door, hdoor, hc.drawn, hl.drawn, hc.count, hl.count, hc.plan, hl.plan, hc.marks,
    hl.marks]
  simp only [Bool.not_false, Bool.and_self, Bool.true_and, Nat.zero_add, Array.size_replicate,
    beq_self_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  refine ⟨⟨hk, trivial⟩, fun i hi => ?_⟩
  have hi' : i < a.F.planClaimsF := by omega
  simp [Array.getD_eq_getD_getElem?, hi']

/-- The claims' test may be asked at the arrays BEHIND THE DRAW: a gatherer that keeps the core keeps the
arrays' frame, and the number of slots. -/
theorem fits_behind (a₁ a' : VerifiableInference.Desc.K9.Part) (hc : LedgerCore a₁ a') (cl : Claim) :
    claimFits a'.F.trees a'.F.ns cl = claimFits a₁.F.trees a₁.F.ns cl := by
  unfold claimFits
  rw [hc.ns, VerifiableInference.Desc.K9H.all_congr _ _ _
      (VerifiableInference.Desc.K9H.entryThere_congr a'.F.trees a₁.F.trees hc.frame),
    VerifiableInference.Desc.K9H.all_congr _ _ _
      (VerifiableInference.Desc.K9H.runFitsRow_congr a'.F.trees a₁.F.trees hc.frame)]

/-- A round in which one element and nothing else is drawn, as `Block.step` shows it (without the sealed
digest), is the round of `drawnOne`. -/
theorem round_fit (t : UInt64 × UInt64 × UInt64) (dg : Option ByteArray) :
    VerifiableInference.Desc.noDigest ⟨[], ⟨[t], [], [], dg⟩⟩ = ⟨[], drawnOne (E.ofTriple t)⟩ := rfl

/-- **THE PIECES JOINED**: from the state in front: a segment is open · `drawReady` · the equation is open ·
the gatherer keeps the ledger's core, returns behind the draw and leaves the lens answering · its claims are
at most the plan's number and each fits the arrays behind the draw ⟹ THE BATCHING SAYS YES AT x, and behind it
as many claims are counted as the gatherer made. -/
theorem batch_yes_of (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (a : VerifiableInference.Desc.K9.Part) (ha : atS.get? s = some a) (hr : drawReady a = true)
    (hdoor : a.F.doorShutF = false) (hk : GatherKeeps g)
    (hg : ∀ t₁ a₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      atS.get? t₁ = some a₁ → ∃ z a', g t₁ = .ok z ∧ atS.get? z.2 = some a' ∧
        z.1.length ≤ a.F.planClaimsF ∧ z.1.all (claimFits a₁.F.trees a₁.F.ns) = true) :
    ∃ y G, gathered p g s x = some y ∧
      (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok (atS.set y.1 { y.2.1 with F := G }) ∧
      (atS.set y.1 { y.2.1 with F := G }).fork? = some G ∧ G.nClaim = y.2.2.length := by
  obtain ⟨t₁, ht⟩ := (draw_iff p s x).2 ⟨a, ha, hr⟩
  obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ x a ha ht
  obtain ⟨z, a', hz, ha', hlen, hfit⟩ := hg t₁ a₁ ht h1
  have hy : gathered p g s x = some (z.2, a', z.1) := by
    unfold gathered
    simp only [ht, hz, ha', Option.map_some]
  have hc := hk t₁ z.1 z.2 a₁ a' hz h1 ha'
  have hfit' : z.1.all (claimFits a'.F.trees a'.F.ns) = true := by
    rw [VerifiableInference.Desc.K9H.all_congr _ _ _ (fits_behind a₁ a' hc)]
    exact hfit
  obtain ⟨G, hb, _, hA⟩ := batch_yes p g s x (z.2, a', z.1) hy
    (ready_behind a a₁ a' x hl hc hdoor _ hlen) hfit'
  exact ⟨_, G, hy, hb, set_fork z.2 a' _ ha', by rw [hA.count, hc.count, hl.count, Nat.zero_add]⟩

/-- **K9's tests behind the adding**, at the proof file's description: the value test and the counts. -/
theorem tests_iff (Z : Pub) (l : Nat) (f : S → Except String Unit) (hf : k9Tests Z l = some f)
    (s : S) : f s = .ok () ↔
      ∃ w, VerifiableInference.Desc.K9.testsWhere Z.p.X l 0 = some w ∧ (tAtS.get? s).isSome = true ∧
        slotsFree w.2.2.filled s = true ∧
        VerifiableInference.Desc.K9.countsHold
          (VerifiableInference.Desc.K9.countsAt w.1 w.2.1) s = .ok () := by
  unfold k9Tests at hf
  cases hw : VerifiableInference.Desc.K9.testsWhere Z.p.X l 0 with
  | none => rw [hw] at hf; exact nomatch hf
  | some w =>
    rw [hw] at hf
    have ef := Option.some.inj hf
    rw [← ef]
    unfold slotsFree
    cases hq : tAtS.get? s with
    | none =>
      constructor
      · intro h
        simp only [VerifiableInference.Desc.K9.there, hq] at h
        exact nomatch h
      · rintro ⟨_, _, h, _⟩
        exact nomatch h
    | some a =>
      simp only [VerifiableInference.Desc.K9.there, hq]
      constructor
      · intro h
        obtain ⟨_, h1, h2⟩ := bind_ok
          (x := VerifiableInference.Desc.K9.freeSlot w.2.2.filled a.merge a.F) h
        refine ⟨w, rfl, rfl, ?_, h2⟩
        exact need_ok h1
      · rintro ⟨w', hw', _, h1, h2⟩
        obtain rfl : w = w' := Option.some.inj hw'
        show (VerifiableInference.Desc.K9.freeSlot w.2.2.filled a.merge a.F).bind _ = _
        have e : VerifiableInference.Desc.K9.freeSlot w.2.2.filled a.merge a.F = .ok () := by
          unfold VerifiableInference.Desc.K9.freeSlot
          have h1' : ((List.range w.2.2.filled).all fun j =>
              isZeroE (a.F.LS.getD j zeroE) == (a.merge == some j)) = true := h1
          rw [h1']
          rfl
        rw [e]
        exact h2

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.clean_iff
#print axioms ProofFile.Honest.K9.draw_iff
#print axioms ProofFile.Honest.K9.batch_join
#print axioms ProofFile.Honest.K9.batch_yes
#print axioms ProofFile.Honest.K9.gathered_of
#print axioms ProofFile.Honest.K9.ready_behind
#print axioms ProofFile.Honest.K9.fits_behind
#print axioms ProofFile.Honest.K9.round_fit
#print axioms ProofFile.Honest.K9.batch_yes_of
#print axioms ProofFile.Honest.K9.tests_iff
#print axioms ProofFile.Honest.K9.drawReady
#print axioms ProofFile.Honest.K9.draw_open
