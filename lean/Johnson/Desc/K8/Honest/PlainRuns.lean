-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlainRuns.lean: RUNS OF CLAIMS THAT ARE FREE OF THE BATCHING ELEMENT.
Definitions, statements and proofs, on the runs' own texts or the library's equations on them. No
prover. Lemmas; none of the library's goals.

  `PlainRun f`      four things, each from a yes of f at a state t: a yes of f at t with the
      batching element replaced (`reChi`, Johnson/Desc/K8/Honest/FreeChi.lean) returns THE SAME
      CLAIMS, and the state that f returned with the element replaced; the claims are plain; the
      smallness test's data and the list of tables stay; the batching's lens still finds a part,
      with the ledger's sums as they were
  `PlainBehind f`   the like for a run that stands behind "K8.equations": with the smallness test's
      data replaced too (`reBoth`)
  `PlainRun.ofForward`   from the stronger form "f says yes at the replaced state"
  `plain_idle`, `plain_objects` (`plain_objectsCalls`, `plain_objectsDigits`), `plain_flRun` (the
      form of the lookup's "join" and "planes": `plain_join`, `plain_planes`, if the caller's keys |
      readers do not read the element), `plain_still` (a run of forms that hands the state back)
  `plain_front`, `behind_back`   the feed-forward kind's two runs
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FreeChi
import Johnson.Desc.K8.Honest.FallLayersLaw
import Johnson.Desc.First.Batch.BlindPlanes
import Johnson.Desc.First.Batch.ClaimsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.K.Kc
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Desc.First.K4 (frontAtC backAtC frontOf formsFrontWith formsFrontWith_some
  formsBack_some formsFrontWith_core formsBack_core claimOf Wrote blockAtC)

/-- A run of claims in front of "K8.equations" that is free of the batching element. -/
structure PlainRun (f : Nat → S → Except String (List Claim × S)) : Prop where
  free : ∀ n t θ y y', f n t = .ok y → f n (reChi θ t) = .ok y' → y' = (y.1, reChi θ y.2)
  plain : ∀ n t y, f n t = .ok y → ∀ cl ∈ y.1, cl.eqFirst = none
  data : ∀ n t y, f n t = .ok y → y.2.tl? = t.tl? ∧ y.2.funs? = t.funs?
  ledger : ∀ n t y a, f n t = .ok y → K9.atS.get? t = some a →
    ∃ b, K9.atS.get? y.2 = some b ∧ SameSums a.F b.F

/-- The like behind "K8.equations". -/
structure PlainBehind (f : Nat → S → Except String (List Claim × S)) : Prop where
  free : ∀ n t θ tl y y', f n t = .ok y → f n (reBoth θ tl t) = .ok y' →
    y' = (y.1, reBoth θ tl y.2)
  plain : ∀ n t y, f n t = .ok y → ∀ cl ∈ y.1, cl.eqFirst = none
  data : ∀ n t y, f n t = .ok y → y.2.tl? = t.tl?
  ledger : ∀ n t y a, f n t = .ok y → K9.atS.get? t = some a →
    ∃ b, K9.atS.get? y.2 = some b ∧ SameSums a.F b.F

theorem PlainRun.ofForward {f : Nat → S → Except String (List Claim × S)}
    (fw : ∀ n t θ y, f n t = .ok y → f n (reChi θ t) = .ok (y.1, reChi θ y.2))
    (plain : ∀ n t y, f n t = .ok y → ∀ cl ∈ y.1, cl.eqFirst = none)
    (data : ∀ n t y, f n t = .ok y → y.2.tl? = t.tl? ∧ y.2.funs? = t.funs?)
    (ledger : ∀ n t y a, f n t = .ok y → K9.atS.get? t = some a →
      ∃ b, K9.atS.get? y.2 = some b ∧ SameSums a.F b.F) : PlainRun f :=
  ⟨fun n t θ y _ h h' => (Except.ok.inj ((fw n t θ y h).symm.trans h')).symm, plain, data, ledger⟩

/-- A ledger laid by putFork, through the batching's lens. -/
theorem ledger_putFork (t : S) (a : K9.Part) (F G : Fork) (h : K9.atS.get? t = some a)
    (hF : t.fork? = some F) (hs : SameSums F G) :
    ∃ b, K9.atS.get? (t.putFork G) = some b ∧ SameSums a.F b.F := by
  obtain ⟨u, hb⟩ := K9.get_putFork' t a G h
  obtain rfl : a.F = F := Option.some.inj ((K9.get_fork t a h).symm.trans hF)
  exact ⟨_, hb, hs⟩

/-! ## The run that returns no claim -/

theorem plain_idle : PlainRun LinkJoin.idle0 :=
  PlainRun.ofForward
    (fun n t θ y h => by
      obtain rfl : (([] : List Claim), t) = y := Except.ok.inj h
      rfl)
    (fun n t y h => by
      obtain rfl : (([] : List Claim), t) = y := Except.ok.inj h
      intro cl hcl
      cases hcl)
    (fun n t y h => by
      obtain rfl : (([] : List Claim), t) = y := Except.ok.inj h
      exact ⟨rfl, rfl⟩)
    (fun n t y a h ha => by
      obtain rfl : (([] : List Claim), t) = y := Except.ok.inj h
      exact ⟨a, ha, SameSums.refl _⟩)

/-! ## The lookup's "objects" -/

theorem plain_objects (heard : S → Option Forest.Heard)
    (hh : ∀ θ s, heard (reChi θ s) = heard s) : PlainRun (K9.objectsBy heard) :=
  PlainRun.ofForward
    (fun n t θ y h => by
      obtain ⟨c, e⟩ := y
      obtain ⟨F, g, hF, hg, rfl, rfl⟩ := objectsBy_ok heard n t e c h
      unfold K9.objectsBy
      rw [reChi_fork, hF, hh, hg, reChi_putFork]
      rfl)
    (fun n t y h => by
      obtain ⟨c, e⟩ := y
      obtain ⟨F, g, hF, hg, rfl, rfl⟩ := objectsBy_ok heard n t e c h
      exact plainOf_plain _)
    (fun n t y h => by
      obtain ⟨c, e⟩ := y
      obtain ⟨F, g, hF, hg, rfl, rfl⟩ := objectsBy_ok heard n t e c h
      exact ⟨tl_putFork' _ _, funs_putFork _ _⟩)
    (fun n t y a h ha => by
      obtain ⟨c, e⟩ := y
      obtain ⟨F, g, hF, hg, rfl, rfl⟩ := objectsBy_ok heard n t e c h
      exact ledger_putFork t a F _ ha hF (SameSums.paid F _))

theorem plain_objectsCalls : PlainRun K9.objectsCalls := plain_objects _ reChi_look

theorem plain_objectsDigits : PlainRun K9.objectsDigits :=
  plain_objects _ fun θ s => by rw [reChi_tl]

/-! ## The form of the lookup's "join" and "planes" -/

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => exact absurd h (by simp [need])

theorem plain_flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim)
    (h1 : ∀ θ s, pre1 (reChi θ s) = pre1 s) (h2 : ∀ θ s, pre2 (reChi θ s) = pre2 s)
    (ht : ∀ b θ F, test b (reChiF θ F) = test b F) (hm : ∀ b c, FlOk (m b c))
    (ho : ∀ d, ∀ cl ∈ out d, cl.eqFirst = none) :
    PlainRun (K9.flRun e0 pre1 e1 test pre2 e2 m out) := by
  have cut : ∀ n t y, K9.flRun e0 pre1 e1 test pre2 e2 m out n t = .ok y →
      ∃ F b c x, t.fork? = some F ∧ pre1 t = .ok b ∧ test b F = true ∧ pre2 t = .ok c ∧
        m b c F [] = some x ∧ y = (out x.1, t.putFork x.2.1) := by
    intro n t y h
    unfold K9.flRun at h
    obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨b, hb, h⟩ := K9L.ok_bind h
    obtain ⟨_, hte, h⟩ := K9L.ok_bind h
    obtain ⟨c, hc, h⟩ := K9L.ok_bind h
    obtain ⟨x, hx, h⟩ := K9L.ok_bind h
    exact ⟨F, b, c, x, named_ok hF, hb, need_ok hte, hc, named_ok hx, (Except.ok.inj h).symm⟩
  refine PlainRun.ofForward ?_ ?_ ?_ ?_
  · intro n t θ y h
    obtain ⟨F, b, c, x, hF, hb, hte, hc, hx, rfl⟩ := cut n t y h
    simp only [K9.flRun, reChi_fork, hF, Option.map_some, h1, hb, h2, hc, ht, hte,
      (hm b c).free F [] x θ hx, named, bind, Except.bind, pure, Except.pure, reChi_putFork]
    rfl
  · intro n t y h
    obtain ⟨F, b, c, x, hF, hb, hte, hc, hx, rfl⟩ := cut n t y h
    exact ho _
  · intro n t y h
    obtain ⟨F, b, c, x, hF, hb, hte, hc, hx, rfl⟩ := cut n t y h
    exact ⟨tl_putFork' _ _, funs_putFork _ _⟩
  · intro n t y a h ha
    obtain ⟨F, b, c, x, hF, hb, hte, hc, hx, rfl⟩ := cut n t y h
    exact ledger_putFork t a F _ ha hF ((hm b c).same F [] x hx)

theorem joinF_ok (g : Forest.Heard) (KF : Array Aff) : FlOk (First.Look.joinF g KF) :=
  FlOk.bind (FlOk.must _) fun _ => FlOk.bind (FlOk.paid _) fun _ => FlOk.pure _

theorem planesAtF_ok (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Fl Aff)
    (hb : ∀ e col, FlOk (bit e col)) : FlOk (First.Look.planesAtF g lm e bit) :=
  FlOk.foldlM (fun _ col => FlOk.bind (hb e col) fun _ => FlOk.pure _) _ _

theorem leavesRowOwn_ok (p : Psc) (S0 : E) (kept : Aff) :
    FlOk (First.Look.leavesRowOwn p S0 kept) :=
  FlOk.bind (FlOk.must _) fun _ => FlOk.bind (FlOk.hideRun _ _ _) fun _ => FlOk.pure _

theorem planeClaimsOwn_ok (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) (hb : ∀ e col, FlOk (bit e col)) (hp : ∀ col, FlOk (pin col)) :
    FlOk (First.Look.planeClaimsOwn g lm bit pin) :=
  FlOk.bind (FlOk.must _) fun _ =>
    FlOk.bind (planesAtF_ok g lm 0 bit hb) fun _ =>
      FlOk.bind (planesAtF_ok g lm 1 bit hb) fun _ =>
        FlOk.bind (FlOk.foldlM (fun _ col => FlOk.bind (hp col) fun _ => FlOk.pure _) _ _)
          fun _ => FlOk.bind (leavesRowOwn_ok _ _ _) fun _ => FlOk.pure _

theorem planesProg_ok (lm : Nat) (g : Forest.Heard)
    (r : (Nat → Nat → Option Aff) × (Nat → Option Aff)) : FlOk (K9.planesProg lm g r) :=
  FlOk.bind (planeClaimsOwn_ok g lm _ _ (fun _ _ => FlOk.need _) fun _ => FlOk.need _) fun _ =>
    FlOk.bind (FlOk.paid _) fun _ => FlOk.pure _

/-- The lookup's "join", if the caller's keys do not read the batching element. -/
theorem plain_join (keys : S → Option (Array Aff)) (hk : ∀ θ s, keys (reChi θ s) = keys s) :
    PlainRun (K9.joinCalls keys) :=
  plain_flRun _ _ _ _ _ _ _ _ (fun θ s => by rw [reChi_look]) (fun θ s => by rw [hk])
    (fun _ _ _ => rfl) (fun g KF => joinF_ok g KF)
    (fun _ cl hcl => by
      obtain rfl : cl = _ := List.mem_singleton.1 hcl
      rfl)

/-- The lookup's "planes", if the caller's readers do not read the batching element. -/
theorem plain_planes (lm : Nat) (readers : K3.Readers S)
    (hr : ∀ θ s, readers (reChi θ s) = readers s) : PlainRun (K9.planesCalls lm readers) :=
  plain_flRun _ _ _ _ _ _ _ _ (fun θ s => by rw [reChi_look]) (fun θ s => by rw [hr])
    (fun _ _ _ => rfl) (fun g r => planesProg_ok lm g r)
    (fun _ cl hcl => by
      obtain ⟨f, -, rfl⟩ := List.mem_map.1 hcl
      rfl)

/-! ## A run of forms that hands the state back -/

theorem plain_still (nm : String) (K : S → Option (List Aff × S))
    (hK : ∀ t z, K t = some z → z.2 = t)
    (hre : ∀ θ t, (K (reChi θ t)).map (·.1) = (K t).map (·.1)) :
    PlainRun fun _ s => (named nm (K s)).map fun y => (y.1.map K9.ofForm, y.2) := by
  have cut : ∀ (t : S) (y : List Claim × S),
      ((named nm (K t)).map fun y => (y.1.map K9.ofForm, y.2)) = .ok y →
      ∃ l, K t = some (l, t) ∧ y = (l.map K9.ofForm, t) := by
    intro t y h
    cases hk : K t with
    | none =>
      rw [hk] at h
      exact absurd h (by simp [named, Except.map])
    | some z =>
      rw [hk] at h
      have e : (z.1.map K9.ofForm, z.2) = y := Except.ok.inj h
      obtain ⟨l, u⟩ := z
      obtain rfl : u = t := hK t _ hk
      exact ⟨l, rfl, e.symm⟩
  constructor
  · intro n t θ y y' h h'
    obtain ⟨l, hl, rfl⟩ := cut t y h
    obtain ⟨l', hl', rfl⟩ := cut (reChi θ t) y' h'
    have e := hre θ t
    rw [hl, hl'] at e
    obtain rfl : l' = l := Option.some.inj e
    rfl
  · intro n t y h
    obtain ⟨l, hl, rfl⟩ := cut t y h
    intro cl hcl
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hcl
    rfl
  · intro n t y h
    obtain ⟨l, hl, rfl⟩ := cut t y h
    exact ⟨rfl, rfl⟩
  · intro n t y a h ha
    obtain ⟨l, hl, rfl⟩ := cut t y h
    exact ⟨a, ha, SameSums.refl _⟩

/-! ## The feed-forward kind's two runs -/

theorem lay_reChi (θ : E) (t : S) (a : LayOwn) (h : t.here = .lay a) :
    (reChi θ t).here = .lay { a with F := reChiF θ a.F } := by
  unfold reChi
  rw [lay_fork t a h]
  exact lay_putFork t a _ h

theorem front_re {rows : Bool} {P : Layer.Pub} {g : Nat} {o : Layer.Own} {F G G' : Fork}
    {fs fs' : Array Aff} (θ : E) (h : formsFrontWith rows P g o F = some (fs, G))
    (h' : formsFrontWith rows P g o (reChiF θ F) = some (fs', G')) :
    fs' = fs ∧ G' = reChiF θ G := by
  obtain ⟨sh, pp, l, F1, F2, a1, a2, a3, rfl, r1, r2, rfl⟩ := formsFrontWith_some h
  obtain ⟨sh', pp', l', F1', F2', a1', a2', a3', rfl, r1', r2', rfl⟩ := formsFrontWith_some h'
  obtain rfl : sh = sh' := Option.some.inj (a1.symm.trans a1')
  obtain rfl : pp = pp' := Option.some.inj (a2.symm.trans a2')
  obtain rfl : l = l' := Option.some.inj (a3.symm.trans a3')
  obtain rfl : reChiF θ F1 = F1' := Option.some.inj ((hideRun_re θ r1).symm.trans r1')
  obtain rfl : reChiF θ F2 = F2' := Option.some.inj ((hideRun_re θ r2).symm.trans r2')
  refine ⟨rfl, ?_⟩
  cases rows <;> rfl

theorem back_re {o : Layer.Own} {F G G' : Fork} {fs fs' : Array Aff} (θ : E)
    (h : OnBytes.Desc.First.K4.formsBack o F = some (fs, G))
    (h' : OnBytes.Desc.First.K4.formsBack o (reChiF θ F) = some (fs', G')) :
    fs' = fs ∧ G' = reChiF θ G := by
  obtain ⟨F1, rfl, r1, rfl⟩ := formsBack_some h
  obtain ⟨F1', rfl, r1', rfl⟩ := formsBack_some h'
  obtain rfl : reChiF θ F1 = F1' := Option.some.inj ((hideRun_re θ r1).symm.trans r1')
  exact ⟨rfl, rfl⟩

/-- What a writing by the feed-forward kind's lens leaves. -/
theorem wrote_facts {t t' : S} {a : LayOwn} {G : Fork} (w : Wrote t a G t') (hs : SameSums a.F G) :
    t'.tl? = t.tl? ∧ t'.funs? = t.funs? ∧
      ∀ x, K9.atS.get? t = some x → ∃ b, K9.atS.get? t' = some b ∧ SameSums x.F b.F := by
  obtain ⟨h1, h2⟩ := wrote_here w
  refine ⟨by rw [lay_tl t a h1, lay_tl t' _ h2], by rw [lay_funs t a h1, lay_funs t' _ h2], ?_⟩
  intro x hx
  obtain ⟨b, hb, hbF⟩ := lay_part t' _ h2
  have hxF : x.F = a.F := Option.some.inj ((K9.get_fork t x hx).symm.trans (lay_fork t a h1))
  exact ⟨b, hb, by rw [hbF, hxF]; exact hs⟩

theorem plain_front (p : OnBytes.Desc.First.K4.Par)
    (r : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "front" = some r) : PlainRun r := by
  constructor
  · intro n t θ y y' h h'
    obtain ⟨c, e⟩ := y
    obtain ⟨c', e'⟩ := y'
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := frontAtC hr h
    obtain ⟨a', o', fs', G', ho', hf', rfl, w'⟩ := frontAtC hr h'
    obtain rfl : _ = a' := Here.lay.inj ((lay_reChi θ t a w.1).symm.trans w'.1)
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    rw [frontOf_eq] at hf hf'
    obtain ⟨rfl, rfl⟩ := front_re θ hf hf'
    obtain ⟨w1, rfl⟩ := w
    obtain ⟨-, rfl⟩ := w'
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := t
    obtain rfl : here = .lay a := w1
    rfl
  · intro n t y h
    obtain ⟨c, e⟩ := y
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := frontAtC hr h
    intro cl hcl
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hcl
    rfl
  · intro n t y h
    obtain ⟨c, e⟩ := y
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := frontAtC hr h
    rw [frontOf_eq] at hf
    have k := wrote_facts w (SameSums.ofCore (formsFrontWith_core hf))
    exact ⟨k.1, k.2.1⟩
  · intro n t y x h hx
    obtain ⟨c, e⟩ := y
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := frontAtC hr h
    rw [frontOf_eq] at hf
    exact (wrote_facts w (SameSums.ofCore (formsFrontWith_core hf))).2.2 x hx

theorem lay_reBoth (θ : E) (tl : HTailF2) (t : S) (a : LayOwn) (h : t.here = .lay a) :
    (reBoth θ tl t).here = .lay { a with F := reChiF θ a.F, tl := tl } := by
  unfold reBoth
  exact lay_putTl _ _ tl (lay_reChi θ t a h)

theorem behind_back (p : OnBytes.Desc.First.K4.Par)
    (r : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "back" = some r) : PlainBehind r := by
  constructor
  · intro n t θ tl y y' h h'
    obtain ⟨c, e⟩ := y
    obtain ⟨c', e'⟩ := y'
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := backAtC hr h
    obtain ⟨a', o', fs', G', ho', hf', rfl, w'⟩ := backAtC hr h'
    obtain rfl : _ = a' := Here.lay.inj ((lay_reBoth θ tl t a w.1).symm.trans w'.1)
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    obtain ⟨rfl, rfl⟩ := back_re θ hf hf'
    obtain ⟨w1, rfl⟩ := w
    obtain ⟨-, rfl⟩ := w'
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := t
    obtain rfl : here = .lay a := w1
    rfl
  · intro n t y h
    obtain ⟨c, e⟩ := y
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := backAtC hr h
    intro cl hcl
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hcl
    rfl
  · intro n t y h
    obtain ⟨c, e⟩ := y
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := backAtC hr h
    exact (wrote_facts w (SameSums.ofCore (formsBack_core hf))).1
  · intro n t y x h hx
    obtain ⟨c, e⟩ := y
    obtain ⟨a, o, fs, G, ho, hf, rfl, w⟩ := backAtC hr h
    exact (wrote_facts w (SameSums.ofCore (formsBack_core hf))).2.2 x hx

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.plain_objectsCalls
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_objectsDigits
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_join
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_planes
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_still
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_front
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_back
