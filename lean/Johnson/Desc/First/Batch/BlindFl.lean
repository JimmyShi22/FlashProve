-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/BlindFl.lean: A SMALL CALCULUS: WHICH PROGRAMS ON A LEDGER AND A TAPE (Fl:
OnBytes/K/Kc/Flat.lean) COMMUTE WITH THE ADDING OF CLAIMS, and: A RUN MADE OF SUCH A PROGRAM IS
BLIND (Johnson/Desc/First/Batch/ObjectsLaw.lean). No Mathlib.
  `Away m`: the program m and the adding commute: where claims cs can be added to the ledger in
      front of m, m behind that adding returns the same value and the same tape, or refuses alike,
      and cs can be added behind m, to the same end; whether a list can be added is not turned by m.
  Closed under `pure` and `bind`; `Fl.must`, `Fl.need` and the mark of a debt are Away.
  `flRun`: the form of the lookup's runs "join" and "planes": the ledger · what was heard · a test
      on the ledger's debts · what the caller hands in · a program · the claims and the ledger laid.
  `flRun_blind`: such a run is Blind to the real adding, if what it reads of the state beside the
      ledger is not turned by an adding (`Unturned`), its test reads the debts alone, and its
      program is Away.
  `joinCalls_is` | `joinCalls_blind`: the lookup's "join" at the calls' seat: under ONE premise: the
      caller's keys are not turned by an adding (`Unturned`).
Limits: a calculus on programs' commuting; "join" under one premise on the caller's keys. Nothing on
soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.BlindK3
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)

/-! ## the adding leaves the list of debts -/

theorem kapTake_owed (F : Fork) (c : Nat) (x : E × Fork) (h : F.kapTake c = some x) :
    x.2.owed = F.owed := by
  unfold Fork.kapTake at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨k, _, hk⟩ := map_some h
      rw [← hk]
    · split at h
      · obtain ⟨k, _, hk⟩ := map_some h
        rw [← hk]
      · simp at h

theorem kap_owed (F : Fork) (x : E × Fork) (h : F.kap = some x) : x.2.owed = F.owed := by
  unfold Fork.kap at h
  obtain ⟨y, hy, hx⟩ := map_some h
  rw [← hx]
  exact kapTake_owed F F.nClaim y hy

theorem push_owed (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) : G.owed = F.owed := by
  unfold Fork.push at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · injection h with h'
      rw [← h']
    · simp at h

theorem pushRuns_owed (F G : Fork) (k : E) (runs : Array Run2) (h : F.pushRuns k runs = some G) :
    G.owed = F.owed := by
  unfold Fork.pushRuns at h
  obtain ⟨tr, _, hG⟩ := map_some h
  rw [← hG]

theorem addClaim_owed (F G : Fork) (cl : Claim) (h : addClaim F cl = some G) :
    G.owed = F.owed := by
  unfold addClaim at h
  obtain ⟨x, hx, h1⟩ := bind_some h
  obtain ⟨k, _, h2⟩ := bind_some h1
  obtain ⟨P, hP, h3⟩ := bind_some h2
  rw [pushRuns_owed P G k cl.runs h3, push_owed x.2 P k cl.form hP, kap_owed F x hx]

theorem addAll_owed : ∀ (cs : List Claim) (F G : Fork), addAll F cs = some G → G.owed = F.owed := by
  intro cs
  induction cs with
  | nil =>
    intro F G h
    simp [addAll, pure] at h
    rw [h]
  | cons c l ih =>
    intro F G h
    unfold addAll at h
    rw [List.foldlM_cons] at h
    obtain ⟨H, hH, hl⟩ := bind_some h
    rw [ih H G hl, addClaim_owed F H c hH]

/-! ## programs that commute with the adding -/

/-- **The program and the adding commute.** -/
structure Away {α : Type} (m : Fl α) : Prop where
  moves : ∀ (F G : Fork) (cs : List Claim) (tp : Tape), addAll F cs = some G →
    match m F tp with
    | none => m G tp = none
    | some x => ∃ G', m G tp = some (x.1, G', x.2.2) ∧ addAll x.2.1 cs = some G'
  keeps : ∀ (F : Fork) (tp : Tape) (x : α × Fork × Tape) (cs : List Claim), m F tp = some x →
    (addAll x.2.1 cs).isSome = (addAll F cs).isSome

theorem Away.ofPure {α : Type} (a : α) : Away (pure a : Fl α) where
  moves := by
    intro F G cs tp h
    exact ⟨G, rfl, h⟩
  keeps := by
    intro F tp x cs h
    injection h with h'
    rw [← h']

theorem Away.ofBind {α β : Type} (m : Fl α) (f : α → Fl β) (hm : Away m)
    (hf : ∀ a, Away (f a)) : Away (m >>= f) where
  moves := by
    intro F G cs tp h
    have h1 := hm.moves F G cs tp h
    show match Fl.andThen m f F tp with
      | none => Fl.andThen m f G tp = none
      | some x => ∃ G', Fl.andThen m f G tp = some (x.1, G', x.2.2) ∧ addAll x.2.1 cs = some G'
    unfold Fl.andThen
    cases hx : m F tp with
    | none =>
      simp only [hx] at h1
      simp [h1]
    | some x =>
      simp only [hx] at h1
      obtain ⟨G', hG, hadd⟩ := h1
      obtain ⟨a, F', tp'⟩ := x
      simp only [hG]
      exact (hf a).moves F' G' cs tp' hadd
  keeps := by
    intro F tp y cs h
    have h' : Fl.andThen m f F tp = some y := h
    unfold Fl.andThen at h'
    cases hx : m F tp with
    | none => simp [hx] at h'
    | some x =>
      obtain ⟨a, F', tp'⟩ := x
      simp only [hx] at h'
      rw [(hf a).keeps F' tp' y cs h', hm.keeps F tp (a, F', tp') cs hx]

theorem Away.ofMust (b : Bool) : Away (Fl.must b) where
  moves := by
    intro F G cs tp h
    unfold Fl.must
    cases b with
    | false => simp
    | true => exact ⟨G, by simp, h⟩
  keeps := by
    intro F tp x cs h
    unfold Fl.must at h
    cases b with
    | false => simp at h
    | true =>
      simp at h
      rw [← h]

theorem Away.ofNeed {α : Type} (o : Option α) : Away (Fl.need o) where
  moves := by
    intro F G cs tp h
    unfold Fl.need
    cases o with
    | none => rfl
    | some a => exact ⟨G, rfl, h⟩
  keeps := by
    intro F tp x cs h
    unfold Fl.need at h
    cases o with
    | none => simp at h
    | some a =>
      simp at h
      rw [← h]

/-- The mark of a debt. -/
theorem Away.ofPaid (i : Nat) : Away (First.Look.paidF i) where
  moves := by
    intro F G cs tp h
    refine ⟨G.paid i, rfl, ?_⟩
    show addAll (F.paid i) cs = some (G.paid i)
    rw [addAll_paid, h]
    rfl
  keeps := by
    intro F tp x cs h
    have h' : some (((), F.paid i, tp) : Unit × Fork × Tape) = some x := h
    injection h' with h''
    rw [← h'']
    show (addAll (F.paid i) cs).isSome = _
    rw [addAll_paid]
    cases addAll F cs <;> rfl

/-! ## a run made of such a program -/

/-- The form of the lookup's runs "join" and "planes". -/
def flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim) : Fn S := fun _ s => do
  let F ← named e0 s.fork?
  let b ← pre1 s
  need e1 (test b F)
  let c ← pre2 s
  let x ← named e2 (m b c F [])
  pure (out x.1, s.putFork x.2.1)

/-- A ledger laid by putFork: the lens reads the part with it, but for "the slots taken". -/
theorem get_putFork' (t : S) (p : Part) (F₁ : Fork) (h : atS.get? t = some p) :
    ∃ u, atS.get? (t.putFork F₁) = some { p with F := F₁, used := u } := by
  cases hh : t.here with
  | between => simp [atS, S.link?, hh] at h
  | fin a => simp [atS, S.link?, hh] at h
  | mem a => simp [atS, S.link?, hh] at h
  | lay a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
    subst h
    exact ⟨a.tl.slotB, by simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, owedOf]⟩
  | att a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
    subst h
    exact ⟨F₁.next, by simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, owedOf]⟩
  | head a =>
    cases ho : a.opened with
    | false => simp [atS, S.link?, hh, ho] at h
    | true =>
      cases hsl : a.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h
      | some n =>
        simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h
        subst h
        exact ⟨n, by simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, ho, hsl, owedOf]⟩

/-- The lens's laying does not read "the slots taken". -/
theorem set_used (t : S) (p : Part) (H : Fork) (u : Nat) :
    atS.set t { p with F := H, used := u } = atS.set t { p with F := H } := rfl

/-- What is read of the state is not turned by an adding: by the lens's laying of the state's own
part with its ledger turned BY AN ADDING. (Asked of no other part: a reader that looks at the
ledger's shape could not meet it at an arbitrary ledger.) -/
def Unturned {α : Type} (read : S → α) : Prop :=
  ∀ (t : S) (p : Part) (cs : List Claim) (G : Fork), atS.get? t = some p →
    addAll p.F cs = some G → read (atS.set t { p with F := G }) = read t

/-- **A run of that form is Blind to the real adding.** -/
theorem flRun_blind {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim)
    (h1 : Unturned pre1) (h2 : Unturned pre2)
    (ht : ∀ (b : β) (F G : Fork), G.owed = F.owed → test b G = test b F)
    (hm : ∀ (b : β) (c : γ), Away (m b c)) :
    Blind (addsOf atS atS_ok) (flRun e0 pre1 e1 test pre2 e2 m out) where
  moves := by
    intro k t t' cs hadd
    obtain ⟨p, hp, hq⟩ := bind_some (show (atS.get? t).bind _ = some t' from hadd)
    obtain ⟨G, hG, ht'⟩ := map_some hq
    have hf := get_fork t p hp
    have hp' := atS_ok.getSet t p cs G hp hG
    have hf' := get_fork _ _ hp'
    subst ht'
    simp only [flRun, hf, hf', h1 t p cs G hp hG, h2 t p cs G hp hG, named, bind, Except.bind]
    cases pre1 t with
    | error e => rfl
    | ok b =>
      dsimp only
      rw [ht b p.F G (addAll_owed cs p.F G hG)]
      cases test b p.F with
      | false => simp [need]
      | true =>
        simp only [need, if_true]
        cases pre2 t with
        | error e => rfl
        | ok c =>
          dsimp only
          have hmv := (hm b c).moves p.F G cs [] hG
          cases hx : m b c p.F [] with
          | none =>
            simp only [hx] at hmv
            simp [hmv, named]
          | some x =>
            simp only [hx] at hmv
            obtain ⟨G', hG', hadd'⟩ := hmv
            simp only [hG', named, pure, Except.pure]
            refine ⟨_, rfl, ?_⟩
            show addAt atS (t.putFork x.2.1) cs = _
            unfold addAt
            obtain ⟨u, hu⟩ := get_putFork' t p x.2.1 hp
            rw [hu]
            simp only [Option.bind]
            rw [hadd']
            simp only [Option.map]
            rw [set_used, set_putFork t p x.2.1 G G']
  keeps := by
    intro n t y cs hy
    show (addAt atS y.2 cs).isSome = (addAt atS t cs).isSome
    unfold addAt
    simp only [flRun, bind, Except.bind] at hy
    cases hf : t.fork? with
    | none => simp [hf, named] at hy
    | some F =>
      simp only [hf, named] at hy
      cases hb : pre1 t with
      | error e => simp [hb] at hy
      | ok b =>
        simp only [hb] at hy
        cases htest : test b F with
        | false => simp [htest, need] at hy
        | true =>
          simp only [htest, need, if_true] at hy
          cases hc : pre2 t with
          | error e => simp [hc] at hy
          | ok c =>
            simp only [hc] at hy
            cases hx : m b c F [] with
            | none => simp [hx, named] at hy
            | some x =>
              simp only [hx, named, pure, Except.pure] at hy
              injection hy with hy'
              subst hy'
              cases hp : atS.get? t with
              | none =>
                rw [get_none_putFork t _ hp]
                rfl
              | some p =>
                have hfp := get_fork t p hp
                rw [hf] at hfp
                injection hfp with hfp'
                subst hfp'
                obtain ⟨u, hu⟩ := get_putFork' t p x.2.1 hp
                rw [hu]
                simp only [Option.bind]
                have hk := (hm b c).keeps p.F [] x cs hx
                cases ha : addAll x.2.1 cs with
                | none =>
                  rw [ha] at hk
                  cases hb' : addAll p.F cs with
                  | none => rfl
                  | some _ => simp [hb'] at hk
                | some _ =>
                  rw [ha] at hk
                  cases hb' : addAll p.F cs with
                  | none => simp [hb'] at hk
                  | some _ => rfl

/-! ## the lookup's "join" -/

theorem joinF_away (g : Forest.Heard) (KF : Array Aff) : Away (First.Look.joinF g KF) :=
  Away.ofBind _ _ (Away.ofMust _) fun _ =>
    Away.ofBind _ _ (Away.ofPaid _) fun _ => Away.ofPure _

/-- "join" at the calls' seat, in flRun's form. keys: the calling kind's. -/
def joinCalls (keys : S → Option (Array Aff)) : Fn S :=
  flRun "K3 join: no sub-proof is open"
    (fun s => named "K3 join: nothing was heard" s.lookHeard?)
    "K3 join: it is made once" (fun g F => K3.unpaid F g.owedJoin)
    (fun s => named "K3 join: the caller's keys" (keys s))
    "K3 join: one form and one weight a call" (fun g KF => First.Look.joinF g KF)
    (fun a => [({ form := a } : Claim)])

/-- It is K3's own run. -/
theorem joinCalls_is (keys : S → Option (Array Aff)) :
    K3.joinRun (K3.seatCalls fun a => ({ form := a } : Claim)) keys = joinCalls keys := rfl

/-- **K3's "join" at the calls is Blind to the real adding**, if an adding does not turn the
caller's keys. -/
theorem joinCalls_blind (keys : S → Option (Array Aff)) (hk : Unturned keys) :
    Blind (addsOf atS atS_ok) (joinCalls keys) :=
  flRun_blind _ _ _ _ _ _ _ _
    (fun t p _ G _ _ => by rw [(set_heard t { p with F := G }).1])
    (fun t p cs G hp hG => by rw [hk t p cs G hp hG])
    (fun g F G h => by unfold K3.unpaid; rw [h])
    (fun g KF => joinF_away g KF)

end VerifiableInference.Desc.K9
