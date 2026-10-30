-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WalkK5.lean: kind K5: FROM THE KIND's HEARING TO THE RECORD IN FRONT OF THE
SEGMENT's BATCHING: the named premise K5OkAt (Claims/InAt.lean) holds of that record's ledger and of what
that record holds as heard, IF every block between carries the ledger and what was heard.

The frame is that of Johnson/Desc/Sound/FoldSteps.lean, FoldStepsProofs.lean: Carries fork heard
later sized; Block.Steps; Traced, whose records t₁ (behind b's own decision) and u₀ (the fold over the
link's first block and all its places in front of the batching) are values of foldBlocks, with
toBatch : R t₁ u₀. Here it is taken at CarK5 := Carries S.fork? S.heard5? Fo.Later PscRun.Sized: the order
Fo.Later, in which the lookup's files' laws on its blocks end, so that every kind's row is one relation.

Main names:
  CarK5 · carK5_pre · carK5_same · carK5_putFork; heard5_of_here · heard5_putFork · heard5_putTl ·
    heard5_putLink: the record's puts leave what the kind heard.
  later_of_fo: Fo.Later (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean) with "sized in front gives sized behind"
    is PscRun.Later; fo_of_later: the other way.
  k5OkAt_behind: a yes of the kind's decision at seatSO from t to t₁, a sized ledger at t, GeoFits, and
    CarK5 t₁ u₀ give: u₀ has a ledger U, holds as heard what the hearing returned, and K5OkAt c zk h U.
  k5OkAt_at_batch: the same from a trace of the link's fold.
  WHO CARRIES: commitAtS_steps (kind K1's later moment; over Johnson/Desc/K1/KeepsSlots.lean) ·
    readsAtO_steps (the step without a round that makes the tables).
IS IT EMPTY HERE?
  · Where the kind's decision or the link's fold refuses, nothing is said.
  · k5OkAt_at_batch takes a Traced: whoever makes it (linkTrace) owes c.Steps CarK5 for every block behind
    K5's in the link's list, RunsStep for all, and the batching's Calls. OF THE LOOKUP ON THE SMALLNESS
    TEST's DIGITS NO SUCH LAW IS KNOWN TO US. Kind K8's hearing: Claims/WalkK8.lean.
  · NO MEMBER, AT NO SIZE.
Limits. That the record where a law in other files takes its snapshot is this u₀ is not said here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.FoldStepsProofs
import Johnson.Desc.First.StateLedger
import Johnson.Desc.K1.KeepsSlots
import Johnson.Desc.First.Att.K05LeavesTl
import Johnson.Desc.First.Att.SeatOFork
import Johnson.Desc.First.Att.Claims.ReadsNextO
import Johnson.Desc.First.Att.Claims.InAt
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled Later)
open VerifiableInference.Desc (First.S First.AttOwn Block Link Carries Traced Pre carriesPre)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)

/-- From s to s': what the kind heard stands; a sized ledger is followed by a later sized one (Fo.Later). -/
abbrev CarK5 : First.S → First.S → Prop :=
  Carries First.S.fork? First.S.heard5? Fo.Later PscRun.Sized

theorem carK5_pre : Pre CarK5 :=
  carriesPre _ _ _ _ _ _ _ Fo.Later.refl fun _ _ _ => Fo.Later.trans

/-! ### the two orders on ledgers -/

theorem later_of_fo {F G : Fork} (h : Fo.Later F G) (hs : PscRun.Sized F → PscRun.Sized G) : Later F G :=
  ⟨h.next, h.ns, hs, h.keep⟩

theorem fo_of_later {F G : Fork} (h : Later F G) : Fo.Later F G := ⟨h.next, h.ns, h.keep⟩

/-! ### the record's puts leave what the kind heard -/

theorem heard5_of_here (s s' : First.S) (h : s'.here = s.here) : s'.heard5? = s.heard5? := by
  unfold First.S.heard5?
  rw [h]

theorem heard5_putFork (s : First.S) (F : Fork) : (s.putFork F).heard5? = s.heard5? := by
  unfold First.S.heard5? First.S.putFork
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
  | _ => simp [hh]

theorem heard5_putTl (s : First.S) (tl : HTailF2) : (s.putTl tl).heard5? = s.heard5? := by
  unfold First.S.heard5? First.S.putTl
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
  | _ => simp [hh]

theorem heard5_putLink (s : First.S) (L : LinkCtx) : (s.putLink L).heard5? = s.heard5? := by
  unfold First.S.heard5? First.S.putLink
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, hh]
  | _ => simp [hh]

theorem carK5_same (s s' : First.S) (hf : s'.fork? = s.fork?) (h5 : s'.heard5? = s.heard5?) :
    CarK5 s s' :=
  ⟨fun _ hg => h5.trans hg, fun F hF hs => ⟨F, hf.trans hF, Fo.Later.refl F, hs⟩⟩

theorem carK5_putFork (s : First.S) (G : Fork)
    (h : ∀ F, s.fork? = some F → PscRun.Sized F → Later F G) : CarK5 s (s.putFork G) :=
  ⟨fun _ hg => (heard5_putFork s G).trans hg,
    fun F hF hs => ⟨G, First.S.fork_putFork s F G hF, fo_of_later (h F hF hs), (h F hF hs).sized hs⟩⟩

/-! ### from the hearing to a record that carries -/

variable {c : ParC}

/-- **Behind the kind's own decision, and on to every record that carries.** -/
theorem k5OkAt_behind {p : P.Par} {t t₁ u₀ : First.S} {rs : List Fmt.RoundView}
    (hd : P.decide P.seatSO p t rs = .ok t₁) (hz : ∀ F, P.seatSO.ledger t = some F → Road.Sized F)
    (gf : P.GeoFits c.geo p.own) (hc : CarK5 t₁ u₀) (zk : Array (Array E)) :
    ∃ F h G U, P.seatSO.ledger t = some F ∧ P.hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      u₀.fork? = some U ∧ u₀.heard5? = some h ∧ Later G U ∧ K5OkAt c zk h U := by
  obtain ⟨_, F, h, G, l1, hh, l2⟩ := (P.decide_lays P.seatSO p _ _ _).1 hd
  obtain ⟨a, _, rfl⟩ := P.seatSO_lay l2
  obtain ⟨_, _, _, _, _, zG, _⟩ := P.hear_said hh (hz F l1)
  obtain ⟨U, hU, lU, sU⟩ := hc.2 G rfl ⟨zG.vp, zG.mf, zG.got⟩
  have lU' : Later G U := later_of_fo lU fun _ => sU
  exact ⟨F, h, G, U, l1, hh, hU, hc.1 h rfl, lU', k5OkAt_of_hearing hh (hz F l1) gf lU' sU⟩

/-- **At the record in front of the segment's batching**, from a trace of the link's fold. -/
theorem k5OkAt_at_batch {Cl : Type} {Q : First.S → List Fmt.RoundView → First.S → List Cl → First.S → First.S → Prop}
    {L : Link First.S Cl} {h₁ : List (Block First.S Cl)} {b : Block First.S Cl} {ft : ℕ} {s : First.S}
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn} {t t₁ u₀ z u e : First.S} {cls : List Cl}
    (T : Traced CarK5 Q L h₁ b ft s rs cols t t₁ u₀ z u e cls) {p : P.Par}
    (hb : ∀ x rs' gs, b.decide x rs' gs = P.decide P.seatSO p x rs')
    (hz : ∀ F, P.seatSO.ledger t = some F → Road.Sized F) (gf : P.GeoFits c.geo p.own)
    (zk : Array (Array E)) :
    ∃ h U, u₀.fork? = some U ∧ u₀.heard5? = some h ∧ K5OkAt c zk h U := by
  obtain ⟨gs, hd⟩ := T.decided
  rw [hb] at hd
  obtain ⟨_, h, _, U, _, _, a1, a2, _, a3⟩ := k5OkAt_behind hd hz gf T.toBatch zk
  exact ⟨h, U, a1, a2, a3⟩

/-! ### who carries -/

/-- **Kind K1's later moment carries.** -/
theorem commitAtS_steps {Cl : Type} (P₁ : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) P₁ link moment arrays).Steps CarK5 := by
  intro s rs gs s' h
  obtain ⟨L, F, tl, y, _, hF, _, rfl, hs⟩ := VerifiableInference.Desc.K1.commitAtS_slots h
  have m : CarK5 s ((VerifiableInference.Desc.K1.laid s y.w).putLink y.L) :=
    carK5_same _ _ ((First.S.fork_putLink _ _).trans (First.S.fork_of_here _ _ rfl))
      ((heard5_putLink _ _).trans (heard5_of_here _ _ rfl))
  refine carK5_pre.trans _ _ _ m (carK5_putFork _ _ fun F' hF' _ => ?_)
  have e : some F' = some F := by
    rw [← hF', ← hF]
    exact (First.S.fork_putLink _ _).trans (First.S.fork_of_here _ _ rfl)
  rw [Option.some.inj e]
  exact hs.later

/-- **The step without a round that makes the tables of what was heard carries.** -/
theorem readsAtSO_carries {A : Attention.Plan} {s s' : First.S} (h : readsAtSO A s = .ok s') :
    CarK5 s s' := by
  obtain ⟨a, _, _, _, _, _, he, _, _, _, _, _, rfl⟩ := reads_next_o A s s' h
  refine carK5_same _ _ ?_ ?_
  · unfold First.S.fork?
    rw [he]
  · unfold First.S.heard5?
    rw [he]

theorem readsAtO_steps {Cl : Type} (W : Verify.Public) (l g : ℕ) (b : Block First.S Cl)
    (hb : readsAtO W l g = some b) : b.Steps CarK5 := by
  unfold readsAtO at hb
  obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun s _ _ s' h => readsAtSO_carries h

end K5Law

#print axioms K5Law.carK5_pre
#print axioms K5Law.k5OkAt_behind
#print axioms K5Law.k5OkAt_at_batch
#print axioms K5Law.commitAtS_steps
#print axioms K5Law.readsAtO_steps
