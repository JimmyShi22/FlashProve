-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RespectsAtt.lean: MEMBERS OF
"Respects" (Johnson/Desc/K1/Law/ReadersStayAt.lean: a run of claims reads nothing of what a later
moment's sending of kind K1 writes): ALL SEVEN RUNS OF AN ATTENTION SEGMENT THAT ARE OPEN AT ITS
DIGITS' PLACE, at the kinds' own texts: K3's "objects", "guests", "planes"; K5's "first", "keys",
"second" and K3's "join" with K5's keys. Definitions, and statements with their proofs.
How. The runs' normal forms lie in Johnson/Desc/First/Batch/BlindK3.lean, BlindFl.lean,
BlindPlanes.lean, BlindAtt.lean, BlindAttO.lean, BlindClaims.lean (readRun, objectsBy, flRun; "it is
the kind's own run": first_is, keys_is, second_is, join_is, planesCalls_is), where they are shown
blind to the adding of claims. THIS FILE MIRRORS THAT CALCULUS, lemma for lemma, with "reads no
mark" (Markless) in the place of "commutes with the adding" (Away), and "reads the rest alone"
(ReadsRest) in the place of "is not turned by an adding" (Unturned).
Main names:
  (ReadsRest f: f (restOf s) = f s, at every state: Johnson/Desc/K1/Law/RestDef.lean.)
  retree, eq_retree, rest_retree. Markless m: the program on a ledger and a tape refuses alike, or
                      returns the same value and tape, at two ledgers that part in the marks alone.
  Markless.ofPure, ofBind, ofMust, ofNeed, ofChange, ofPaid, ofFoldlM; hideRun_markless.
  joinF_markless, planesProg_markless (with its four steps).
  respects_flRun      a run made of such a program. respects_joinCalls, respects_planesCalls.
  SeatRest seat       K5's claims' seat's five readers read the rest alone. seatCO_rest: the seat
                      that reads what was heard is such a seat.
  respects_firstAt, respects_keysAt, respects_secondAt.
  block_respects      K3's block at the calls. runsO_respects: **K5's list with K3's "join".**
  withCaller_respects: **K3's block at the calls with K5 as its caller.**
What is not claimed. That a real chain's link states these runs (the seat's guard:
respects_guarded). Anything on K3's block at the digits, whose runs are not open at the digits'
sending. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ReadersStayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.K.Kc Desc.Plain
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.First.Att.P (seatCO parCOf ParC)
open VerifiableInference.Desc.K9 (Fn RunOf readRun objectsBy guestsNone flRun joinCalls planesCalls
  planesProg firstAt keysAt secondAt asClaimsOf runOfForms ofForm)

/-! ## Programs on a ledger and a tape that read no mark -/

/-- The ledger with other arrays. -/
def retree (F : Fork) (T : Array HTree) : Fork := { F with trees := T }

theorem eq_retree {F F' : Fork} (h : forkRest F = forkRest F') : F' = retree F F'.trees := by
  cases F
  cases F'
  simp only [forkRest, Fork.mk.injEq] at h
  obtain ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem trees_rest {F F' : Fork} (h : forkRest F = forkRest F') :
    F.trees.map treeRest = F'.trees.map treeRest := by
  have := congrArg Fork.trees h
  exact this

theorem rest_retree (G : Fork) {T T' : Array HTree} (h : T.map treeRest = T'.map treeRest) :
    forkRest (retree G T) = forkRest (retree G T') := by
  unfold forkRest retree
  dsimp only
  rw [h]

/-- **The program reads no mark**: at two ledgers that part in the marks alone it refuses alike, or
returns the same value and tape and two such ledgers. -/
def Markless {α : Type} (m : Fl α) : Prop :=
  ∀ (F F' : Fork) (tp : Tape), forkRest F = forkRest F' →
    match m F tp with
    | none => m F' tp = none
    | some x => ∃ G', m F' tp = some (x.1, G', x.2.2) ∧ forkRest x.2.1 = forkRest G'

theorem Markless.ofPure {α : Type} (a : α) : Markless (pure a : Fl α) :=
  fun _ F' _ h => ⟨F', rfl, h⟩

theorem Markless.ofBind {α β : Type} (m : Fl α) (f : α → Fl β) (hm : Markless m)
    (hf : ∀ a, Markless (f a)) : Markless (m >>= f) := by
  intro F F' tp h
  have h1 := hm F F' tp h
  show match Fl.andThen m f F tp with
    | none => Fl.andThen m f F' tp = none
    | some x => ∃ G', Fl.andThen m f F' tp = some (x.1, G', x.2.2) ∧
        forkRest x.2.1 = forkRest G'
  unfold Fl.andThen
  cases hx : m F tp with
  | none =>
    simp only [hx] at h1
    simp [h1]
  | some x =>
    simp only [hx] at h1
    obtain ⟨G', hG, hr⟩ := h1
    obtain ⟨a, F₁, tp'⟩ := x
    simp only [hG]
    exact hf a F₁ G' tp' hr

theorem Markless.ofMust (b : Bool) : Markless (Fl.must b) := by
  intro F F' tp h
  unfold Fl.must
  cases b with
  | false => simp
  | true => exact ⟨F', by simp, h⟩

theorem Markless.ofNeed {α : Type} (o : Option α) : Markless (Fl.need o) := by
  intro F F' tp h
  unfold Fl.need
  cases o with
  | none => rfl
  | some a => exact ⟨F', rfl, h⟩

/-- A step on the ledger that goes past the arrays. -/
theorem Markless.ofChange (g : Fork → Option Fork)
    (hg : ∀ F T, g (retree F T) = (g F).map (retree · T)) : Markless (Fl.change g) := by
  intro F F' tp h
  have e := eq_retree h
  have hF : g F = (g F).map (retree · F.trees) := by
    have := hg F F.trees
    exact this
  unfold Fl.change
  rw [e, hg]
  cases hx : g F with
  | none => rfl
  | some G =>
    rw [hx] at hF
    have hG : G = retree G F.trees := Option.some.inj hF
    refine ⟨retree G F'.trees, rfl, ?_⟩
    show forkRest G = _
    rw [hG]
    exact rest_retree G (trees_rest h)

theorem Markless.ofPaid (i : Nat) : Markless (First.Look.paidF i) :=
  Markless.ofChange _ fun _ _ => rfl

theorem hide_retree (F : Fork) (T : Array HTree) (j : Nat) (y f : E) :
    (retree F T).hide j y f = (F.hide j y f).map (retree · T) := by
  rw [K9.hide_eq, K9.hide_eq]
  show (if decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true then _ else none) = _
  split <;> rfl

theorem hideSteps_retree (f : E) (T : Array HTree) : ∀ (v : List E) (j : Nat) (F : Fork),
    v.foldlM (Fork.hideStep f) (j, retree F T) =
      (v.foldlM (Fork.hideStep f) (j, F)).map fun x => (x.1, retree x.2 T)
  | [], _, _ => rfl
  | y :: v, j, F => by
    rw [List.foldlM_cons, List.foldlM_cons]
    have e1 : Fork.hideStep f (j, retree F T) y =
        ((F.hide j y f).map (retree · T)).map fun H => (j + 1, H) := by
      show ((retree F T).hide j y f).map _ = _
      rw [hide_retree]
    have e2 : Fork.hideStep f (j, F) y = (F.hide j y f).map fun H => (j + 1, H) := rfl
    rw [e1, e2]
    cases F.hide j y f with
    | none => rfl
    | some H => exact hideSteps_retree f T v (j + 1) H

theorem hideRun_markless (first : Nat) (v : Array E) (f : E) :
    Markless (Fl.change (·.hideRun first v f)) :=
  Markless.ofChange _ fun F T => by
    rw [K9.hideRun_list, K9.hideRun_list, hideSteps_retree]
    cases v.toList.foldlM (Fork.hideStep f) (first, F) <;> rfl

theorem Markless.ofFoldlM {α β : Type} (f : β → α → Fl β) (hf : ∀ b a, Markless (f b a)) :
    ∀ (l : List α) (b : β), Markless (l.foldlM f b) := by
  intro l
  induction l with
  | nil => intro b; exact Markless.ofPure b
  | cons a l ih =>
    intro b
    rw [List.foldlM_cons]
    exact Markless.ofBind _ _ (hf b a) fun b' => ih b'

/-! ### The lookup's two programs -/

theorem joinF_markless (g : Forest.Heard) (KF : Array Aff) : Markless (First.Look.joinF g KF) :=
  Markless.ofBind _ _ (Markless.ofMust _) fun _ =>
    Markless.ofBind _ _ (Markless.ofPaid _) fun _ => Markless.ofPure _

theorem planesAtF_markless (g : Forest.Heard) (lm e : Nat) (bit : Nat → Nat → Fl Aff)
    (hb : ∀ e col, Markless (bit e col)) : Markless (First.Look.planesAtF g lm e bit) :=
  Markless.ofFoldlM _ (fun _ col => Markless.ofBind _ _ (hb e col) fun _ => Markless.ofPure _) _ _

theorem leavesRowOwn_markless (p : Psc) (S0 : E) (kept : Aff) :
    Markless (First.Look.leavesRowOwn p S0 kept) :=
  Markless.ofBind _ _ (Markless.ofMust _) fun _ =>
    Markless.ofBind _ _ (hideRun_markless _ _ _) fun _ => Markless.ofPure _

theorem planeClaimsOwn_markless (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Fl Aff)
    (pin : Nat → Fl Aff) (hb : ∀ e col, Markless (bit e col)) (hp : ∀ col, Markless (pin col)) :
    Markless (First.Look.planeClaimsOwn g lm bit pin) :=
  Markless.ofBind _ _ (Markless.ofMust _) fun _ =>
    Markless.ofBind _ _ (planesAtF_markless g lm 0 bit hb) fun _ =>
      Markless.ofBind _ _ (planesAtF_markless g lm 1 bit hb) fun _ =>
        Markless.ofBind _ _
          (Markless.ofFoldlM _
            (fun _ col => Markless.ofBind _ _ (hp col) fun _ => Markless.ofPure _) _ _)
          fun _ => Markless.ofBind _ _ (leavesRowOwn_markless _ _ _) fun _ => Markless.ofPure _

theorem planesProg_markless (lm : Nat) (g : Forest.Heard)
    (r : (Nat → Nat → Option Aff) × (Nat → Option Aff)) : Markless (planesProg lm g r) :=
  Markless.ofBind _ _
    (planeClaimsOwn_markless g lm _ _ (fun _ _ => Markless.ofNeed _) fun _ => Markless.ofNeed _)
    fun _ => Markless.ofBind _ _ (Markless.ofPaid _) fun _ => Markless.ofPure _

/-! ## A run made of such a program -/

theorem respects_flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim) (h1 : ReadsRest pre1) (h2 : ReadsRest pre2)
    (ht : ∀ b F F', forkRest F = forkRest F' → test b F' = test b F)
    (hm : ∀ b c, Markless (m b c)) : Respects (flRun e0 pre1 e1 test pre2 e2 m out) := by
  intro s s' hA cl t e
  unfold flRun at e ⊢
  obtain ⟨F, hF, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨b, hb, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨_, hn, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨c, hc, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨x, hx, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  cases hF0 : s.fork? with
  | none => rw [hF0] at hF; cases hF
  | some F₀ =>
    rw [hF0] at hF
    obtain rfl : F₀ = F := Except.ok.inj hF
    obtain ⟨F', g1, g2⟩ := hA.fork hF0
    cases hm0 : m b c F₀ [] with
    | none => rw [hm0] at hx; cases hx
    | some x₀ =>
      rw [hm0] at hx
      obtain rfl : x₀ = x := Except.ok.inj hx
      have k := hm b c F₀ F' [] g2.symm
      rw [hm0] at k
      obtain ⟨G', k1, k2⟩ := k
      refine ⟨s'.putFork G', ?_, hA.putFork k2⟩
      rw [g1, h1.alike hA, h2.alike hA]
      show (Except.ok F' : Except String Fork).bind _ = _
      simp only [Except.bind]
      rw [hb]
      simp only [bind, Except.bind]
      rw [ht b F₀ F' g2.symm, hn, hc]
      simp only [k1]
      rfl

theorem unpaid_rest (i : Nat) (F F' : Fork) (h : forkRest F = forkRest F') :
    K3.unpaid F' i = K3.unpaid F i := by
  have e : F'.owed = F.owed := by
    have := congrArg Fork.owed h
    exact this.symm
  unfold K3.unpaid
  rw [e]

theorem readsRest_named {α : Type} (e : String) (f : S → Option α) (h : ReadsRest f) :
    ReadsRest fun s => named e (f s) := fun s => by
  show named e (f (restOf s)) = named e (f s)
  rw [h s]

/-- **K3's "join" at the calls**: where the caller's keys read the rest alone. -/
theorem respects_joinCalls (keys : S → Option (Array Aff)) (hk : ReadsRest keys) :
    Respects (joinCalls keys) :=
  respects_flRun _ _ _ _ _ _ _ _ (readsRest_named _ _ readsRest_lookHeard)
    (readsRest_named _ _ hk) (fun g F F' h => unpaid_rest g.owedJoin F F' h)
    fun g KF => joinF_markless g KF

/-- **K3's "planes" at the calls**: where the caller's readers read the rest alone. -/
theorem respects_planesCalls (lm : Nat) (readers : K3.Readers S) (hr : ReadsRest readers) :
    Respects (planesCalls lm readers) :=
  respects_flRun _ _ _ _ _ _ _ _ (readsRest_named _ _ readsRest_lookHeard)
    (readsRest_named _ _ hr) (fun g F F' h => unpaid_rest g.owedPlanes F F' h)
    fun g r => planesProg_markless lm g r

/-! ## K5's claims' seat -/

/-- A seat of K5's claims whose five readers read the rest alone. -/
structure SeatRest (seat : First.Att.P.SeatC S) : Prop where
  pts : ReadsRest seat.pts
  cols : ReadsRest seat.cols
  look : ReadsRest seat.look
  pad : ReadsRest seat.pad
  zk : ReadsRest seat.zk

theorem inOf_rest (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    ReadsRest (First.Att.P.inOf seat c) := by
  intro s
  unfold First.Att.P.inOf
  rw [h.pts s, h.look s, h.zk s, h.cols s]

theorem keysOfK_rest (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    ReadsRest (First.Att.P.keysOfK seat c) := by
  intro s
  unfold First.Att.P.keysOfK
  rw [inOf_rest seat h c s, h.pad s]

theorem readersOfK_rest (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    ReadsRest (First.Att.P.readersOfK seat c) := by
  intro s
  unfold First.Att.P.readersOfK
  rw [inOf_rest seat h c s]

theorem respects_firstAt (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    Respects (firstAt seat c) :=
  respects_readRest _ fun s => by
    unfold First.Att.P.firstK
    rw [inOf_rest seat h c s]
    cases First.Att.P.inOf seat c s with
    | none => rfl
    | some x =>
      obtain ⟨i, K⟩ := x
      cases hq : First.Att.P.Runs.firstRun i K <;>
        simp [hq, asClaimsOf, named, Except.map, bind, Option.bind]

theorem respects_keysAt (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    Respects (keysAt seat c) :=
  respects_readRest _ fun s => by
    unfold First.Att.P.keysK
    rw [keysOfK_rest seat h c s]
    cases First.Att.P.keysOfK seat c s <;> rfl

theorem respects_secondAt (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    Respects (secondAt seat c) :=
  respects_readRest _ fun s => by
    unfold First.Att.P.secondK
    rw [inOf_rest seat h c s]
    cases First.Att.P.inOf seat c s with
    | none => rfl
    | some x =>
      obtain ⟨i, K⟩ := x
      cases hq : First.Att.P.Runs.secondRun i K <;>
        simp [hq, asClaimsOf, named, Except.map, bind, Option.bind]

/-- **The seat that reads what was heard is such a seat.** -/
theorem seatCO_rest (c : ParC) : SeatRest (seatCO c) where
  pts := fun s => by
    have hpt : ∀ (F : Fork) (zk : Array (Array E)) (h : First.Att.P.Heard),
        First.Att.P.ptsFrom c.geo zk h (forkRest F) = First.Att.P.ptsFrom c.geo zk h F :=
      fun F => K9.ptsFrom_of_shown F (forkRest F) (K9.shown_of_quiet F (forkRest F) rfl) c.geo
    cases hh : s.here <;> simp [seatCO, restOf, hereRest, S.heard5?, hh, hpt]
  cols := fun s => by
    cases hh : s.here with
    | att a =>
      simp [seatCO, restOf, hereRest, forkRest, hh]
      rfl
    | _ => simp [seatCO, restOf, hereRest, hh]
  look := fun s => by cases hh : s.here <;> simp [seatCO, restOf, hereRest, hh]
  pad := fun s => by cases hh : s.here <;> simp [seatCO, restOf, hereRest, hh]
  zk := fun s => by cases hh : s.here <;> simp [seatCO, restOf, hereRest, hh]

/-! ## All that an attention segment's blocks state -/

theorem block_respects (digits : Bool) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) :
    ∀ r ∈ (K3.block (if digits then K3.seatDigits ofForm else K3.seatCalls ofForm) piece laid
      before p []).claims, digits = false → Respects r.2 := by
  intro r hr hd
  subst hd
  have hr' : r ∈ [("objects", K9.objectsCalls), ("guests", guestsNone)] := hr
  have : r = ("objects", K9.objectsCalls) ∨ r = ("guests", guestsNone) := by
    simpa using hr'
  cases this with
  | inl h => rw [h]; exact respects_objectsCalls
  | inr h => rw [h]; exact respects_guestsNone

theorem runsO_respects (A : Attention.Plan) :
    ∀ r ∈ (First.Att.P.runsO A).map runOfForms, Respects r.2 := by
  intro r hr
  have : r = runOfForms ("first", fun _ s => named "K5.first"
        (First.Att.P.firstK (seatCO (parCOf A)) (parCOf A) s)) ∨
      r = runOfForms ("keys", fun _ s => named "K5.keys"
        (First.Att.P.keysK (seatCO (parCOf A)) (parCOf A) s)) ∨
      r = runOfForms ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id)
        (First.Att.P.keysOfO A)) ∨
      r = runOfForms ("second", fun _ s => named "K5.second"
        (First.Att.P.secondK (seatCO (parCOf A)) (parCOf A) s)) := by
    simpa [First.Att.P.runsO, First.Att.P.runsK] using hr
  rcases this with h | h | h | h
  · rw [h, K9.first_is]; exact respects_firstAt _ (seatCO_rest _) _
  · rw [h, K9.keys_is]; exact respects_keysAt _ (seatCO_rest _) _
  · rw [h, K9.join_is]; exact respects_joinCalls _ (keysOfK_rest _ (seatCO_rest _) _)
  · rw [h, K9.second_is]; exact respects_secondAt _ (seatCO_rest _) _

/-- K3's block at the calls with K5 as its caller: "planes" is stated behind the block's own
runs. -/
theorem withCaller_respects (A : Attention.Plan) (b b₀ : Block S Claim) (p : First.Look.P)
    (h0 : ∀ r ∈ b₀.claims, Respects r.2)
    (hb : b = K3.withCaller (K3.seatCalls ofForm) p (First.Att.P.readersOfO A) b₀) :
    ∀ r ∈ b.claims, Respects r.2 := by
  intro r hr
  rw [hb] at hr
  have : r ∈ b₀.claims ∨ r = ("planes", planesCalls p.lm (First.Att.P.readersOfO A)) := by
    simpa [K3.withCaller, K9.planesCalls_is, ofForm] using hr
  cases this with
  | inl h' => exact h0 r h'
  | inr h' =>
    rw [h']
    exact respects_planesCalls p.lm _ (readersOfK_rest _ (seatCO_rest _) _)

end VerifiableInference.Desc.K1
