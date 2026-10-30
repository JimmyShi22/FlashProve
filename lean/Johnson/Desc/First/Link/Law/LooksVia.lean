-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksVia.lean: KIND K3 (the lookup), WHOLE: ITS DECISION WITH NO PREMISE
ON THE PLAN, AND ITS RUNS OF CLAIMS, STAND IN `KeepsLooks`
(Johnson/Desc/First/Link/Law/LooksWalk.lean).
A class, instances, theorems.

Why. `Meaning.K2.SeatKeeps` (Johnson/IMR/SeatKeeps.lean: a structure, general in a relation) asks of
each maker of the proof file's seat `Keeps.Whole R b`: the decision, every run of claims, every run
behind the batching; and of K3's `theStated` WITHOUT a yes of the test on the plan.
`theStated_steps` (LooksSeated.lean) goes through `blockVia_decide`, which takes that yes. Here the
hearing that `blockVia` itself calls is walked.
  `StaysHr x`: wherever x returns (a text of the type `K3.Law.Hr`), its ledger has THE ARRAYS of the
    ledger that it was handed. Instances for the type's own steps and for `drawsV`, `drawV`, `sumV`,
    `openV`, `tieV`, `partsV`, `keysV`, `messagesV` (Johnson/Desc/First/Look/Via/Rounds.lean).
  `msWhole_arrays` (the masked sumcheck's `whole`) · `level_arrays`, `run_arrays` (the grand
    product's levels, Johnson/Desc/First/ProdV/Level.lean) · `hearV_arrays`, `hearVia_arrays`.
  `keeps_putFork`: the tool for a run: a ledger with the same looks is laid where one is open.
  `viaW_calls`, `viaW_digits`: **Whole (KeepsLooks shOf) (blockVia (seatCalls | seatDigits claim)
    …)**.
  `planesRun_keeps`, `joinRun_keeps`: the runs "planes" and "join", at a seat whose `mark` is the
    laying of the ledger.
  `theOwn_whole`, `theWhole_whole`, `theStated_whole`: **so of K3's sub-protocol at an address.**
Limits. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.ViaL
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.ProdV (Hears level turn run Carried LevelOut)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.Law

variable {α β γ : Type}

theorem msWhole_arrays {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E}
    {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : G.trees = F.trees := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact (K5L.msRow_arrays hr).trans (K5L.msHear_arrays hh)

/-- One level of the grand product. -/
theorem level_arrays {m : ℕ} {z : Array E} {order : List ℕ} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    G.trees = F.trees := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact msWhole_arrays hw
      · exact nomatch h
    · exact nomatch h

theorem turn_arrays {order : List ℕ} {s s' : Carried} {m : ℕ} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) :
    G.trees = F.trees := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_arrays hx

theorem fold_arrays (m0 : ℕ) (orders : ℕ → List ℕ) : ∀ (l : List ℕ)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → y.2.1.trees = x.2.1.trees
  | [], x, y, h => by
    obtain rfl : x = y := Option.some.inj h
    rfl
  | i :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact (fold_arrays m0 orders l _ y h).trans (turn_arrays hz)

/-- A run of levels. -/
theorem run_arrays {m0 n : ℕ} {orders : ℕ → List ℕ} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : run m0 n orders s F rs = some (s', G, rest)) :
    G.trees = F.trees := fold_arrays m0 orders _ (s, F, rs) (s', G, rest) h

/-- Wherever x returns, its ledger has the arrays of the ledger that it was handed. -/
class StaysHr (x : Hr α) : Prop where
  same : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) →
    G.trees = F.trees

theorem bindHr_some {x : Hr α} {f : α → Hr β} {F : Fork} {rs : List Fmt.RoundView}
    {r : β × Fork × List Fmt.RoundView} (h : (x >>= f) F rs = some r) :
    ∃ a G rest, x F rs = some (a, G, rest) ∧ f a G rest = some r := by
  have h' : Hr.andThen x f F rs = some r := h
  unfold Hr.andThen at h'
  cases e : x F rs with
  | none =>
    rw [e] at h'
    exact nomatch h'
  | some y =>
    obtain ⟨a, G, rest⟩ := y
    rw [e] at h'
    exact ⟨a, G, rest, rfl, h'⟩

instance staysHr_pure (a : α) : StaysHr (pure a : Hr α) :=
  ⟨fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    exact (congrArg (fun y => y.2.1.trees) (Option.some.inj e')).symm⟩

theorem StaysHr.bind {x : Hr α} {f : α → Hr β} (hx : StaysHr x) (hf : ∀ a, StaysHr (f a)) :
    StaysHr (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysHr_bind (x : Hr α) (f : α → Hr β) [StaysHr x] [∀ a, StaysHr (f a)] :
    StaysHr (x >>= f) := StaysHr.bind inferInstance inferInstance

instance staysHr_ite (p : Prop) [Decidable p] (x y : Hr α) [StaysHr x] [StaysHr y] :
    StaysHr (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysHr" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysHr.bind ?_ ?_
    | intro _
    | split)

theorem staysHr_foldlM {f : β → γ → Hr β} (hf : ∀ s a, StaysHr (f s a)) :
    ∀ (l : List γ) (s : β), StaysHr (l.foldlM f s)
  | [], s => by
    show StaysHr (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show StaysHr (f s a >>= fun s' => l.foldlM f s')
    exact StaysHr.bind (hf s a) fun s' => staysHr_foldlM hf l s'

instance staysHr_must (b : Bool) : StaysHr (Hr.must b) :=
  ⟨fun {F G rs rest a} e => by
    unfold Hr.must at e
    split at e
    · exact (congrArg (fun y => y.2.1.trees) (Option.some.inj e)).symm
    · exact nomatch e⟩

instance staysHr_slot : StaysHr Hr.slot :=
  ⟨fun {F G rs rest a} e => by
    have e' : some (F.next, F, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => y.2.1.trees) (Option.some.inj e')).symm⟩

instance staysHr_owe (what : String) : StaysHr (Hr.owe what) :=
  ⟨fun {F G rs rest a} e => by
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => y.2.1.trees) (Option.some.inj e')).symm⟩

instance staysHr_run (m0 n : ℕ) (orders : ℕ → List ℕ) (s : Carried) :
    StaysHr (Hr.of (run m0 n orders s)) := ⟨fun e => run_arrays e⟩

instance staysHr_drawsV (n : ℕ) : StaysHr (drawsV n) :=
  ⟨fun {F G rs rest a} e => by
    unfold drawsV at e
    cases rs with
    | nil => exact nomatch e
    | cons r rs' =>
      dsimp only at e
      split at e
      · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
        exact (congrArg (fun y => y.2.1.trees) e).symm
      · exact nomatch e⟩

instance staysHr_drawV : StaysHr drawV :=
  ⟨fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact (staysHr_drawsV 1).same hx
      · exact nomatch e
    · exact nomatch e⟩

instance staysHr_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    StaysHr (sumV C k endTerm) :=
  ⟨fun {F G rs rest a} e => by
    unfold sumV at e
    split at e
    · exact nomatch e
    · split at e
      · rename_i h row G' hw
        split at e
        · exact nomatch e
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
          exact msWhole_arrays hw
      · exact nomatch e⟩

instance staysHr_openV (C : Aff) (vs : List MaskedSum.Var) : StaysHr (openV C vs) :=
  ⟨fun {F G rs rest a} e => by
    unfold openV at e
    split at e
    · exact nomatch e
    · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨h, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2.1) e
      exact K5L.msHear_arrays hx⟩

instance staysHr_tieV (w : ℕ) (a : E) : StaysHr (tieV w a) := by
  unfold tieV
  refine StaysHr.bind inferInstance fun x => ?_
  refine StaysHr.bind (staysHr_foldlM (fun s _ => by staysHr) _ _) fun _ => ?_
  infer_instance

theorem staysHr_partsV : ∀ (n : ℕ) (rows : Array Aff) (C : Aff), StaysHr (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine StaysHr.bind inferInstance fun w => ?_
    refine StaysHr.bind (staysHr_partsV n _ _) fun _ => ?_
    infer_instance

instance (n : ℕ) (rows : Array Aff) (C : Aff) : StaysHr (partsV n rows C) :=
  staysHr_partsV n rows C

theorem staysHr_keysV (f : Face) : ∀ (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff),
    StaysHr (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine StaysHr.bind inferInstance fun k => ?_
    refine StaysHr.bind (staysHr_keysV f xs Cs _) fun _ => ?_
    infer_instance

instance (f : Face) (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff) :
    StaysHr (keysV f xs Cs rows) := staysHr_keysV f xs Cs rows

/-- **The lookup's rounds, heard in order.** -/
instance staysHr_messagesV (f : Face) : StaysHr (messagesV f) := by
  unfold messagesV
  staysHr

theorem hearV_arrays {f : Face} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : G.trees = F.trees := by
  unfold hearV at h
  split at h
  · split at h
    · rename_i g' G' hm
      obtain rfl : G' = G := congrArg (·.2) (Option.some.inj h)
      exact (staysHr_messagesV f).same hm
    · exact nomatch h
  · exact nomatch h

theorem hearVia_arrays {p : First.Look.P} {F G : Fork} {rs : List Fmt.RoundView} {g : Forest.Heard}
    (h : hearVia p F rs = some (g, G)) : G.trees = F.trees := by
  unfold hearVia at h
  split at h
  · split at h
    · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨g', _, e⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨gv, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2) e
      exact hearV_arrays hx
    · exact nomatch h
  · exact nomatch h

end VerifiableInference.Desc.LinkJoin.ViaL

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look

instance stays_paidF (i : ℕ) : Stays (paidF i) :=
  Stays.change fun F G h => by
    rw [← Option.some.inj h]
    exact SameLooks.refl F

instance stays_planesAddedF (g : Forest.Heard) : Stays (planesAddedF g) := by
  unfold planesAddedF; infer_instance

instance stays_joinAddedF (g : Forest.Heard) : Stays (joinAddedF g) := by
  unfold joinAddedF; infer_instance

instance stays_joinF (g : Forest.Heard) (KF : Array Aff) : Stays (joinF g KF) := by
  unfold joinF; stays

instance stays_planesAtF (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff)
    [∀ a b, Stays (bit a b)] : Stays (planesAtF g lm e bit) := by
  unfold planesAtF
  exact stays_foldlM (fun _ _ => by stays) _ _

instance stays_leavesRowOwn (p : Psc) (S0 : E) (kept : Aff) : Stays (leavesRowOwn p S0 kept) := by
  unfold leavesRowOwn; stays

instance stays_planeClaimsOwn (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) [∀ a b, Stays (bit a b)] [∀ a, Stays (pin a)] :
    Stays (planeClaimsOwn g lm bit pin) := by
  unfold planeClaimsOwn
  refine Stays.bind inferInstance fun _ => ?_
  refine Stays.bind inferInstance fun _ => ?_
  refine Stays.bind inferInstance fun _ => ?_
  refine Stays.bind (stays_foldlM (fun _ _ => by stays) _ _) fun _ => ?_
  stays

end VerifiableInference.Desc.LinkJoin.FlL

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)

section
variable (shOf : ℕ → List Look)

/-- **The tool for a run**: a ledger with the same looks is laid where one is open. -/
theorem keeps_putFork {s : S} {F G : Fork} (hF : s.fork? = some F)
    (e : G.trees.map look = F.trees.map look) : KeepsLooks shOf s (s.putFork G) := by
  refine keeps_of_cases shOf fun G' L' e1 e2 => Or.inr ⟨F, L', hF, ?_, rfl, ?_⟩
  · rw [← link_putFork s G]
    exact e2
  · rw [fork_putFork s F hF] at e1
    rw [← Option.some.inj e1]
    exact e

/-- The decision of `blockVia`, with no premise on the plan. -/
theorem via_decides {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    Decides (KeepsLooks shOf) (K3.Law.blockVia seat piece laid before p guests) := by
  intro s rs gs s' h
  have h' : K3.Law.decideVia seat p s rs = .ok s' := h
  unfold K3.Law.decideVia at h'
  obtain ⟨F, hF, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, hn, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, hx, h'⟩ := K9L.ok_bind h'
  obtain rfl := Except.ok.inj h'
  have hF' := named_some hF
  have hn' : seat.heard s = none := by
    cases e : seat.heard s with
    | none => rfl
    | some g =>
      rw [e] at hn
      exact nomatch hn
  have e1 : (seat.put s x.1 x.2).fork? = some x.2 := by
    rw [← hf]
    exact hk s x.1 x.2 (by rw [hF']; rfl) hn'
  refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF'
  · rw [← hl s x.1 x.2]
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact congrArg (·.map look) (ViaL.hearVia_arrays (g := x.1) (G := x.2) (named_some hx))

/-- `blockVia`, whole, at a seat whose `mark` is the laying of the ledger. -/
theorem via_whole {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsLooks shOf) (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨via_decides shOf seat hf hk hl piece laid before p guests, fun c hc n s y h => ?_,
    (fun _ hc => nomatch hc)⟩
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p guests).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨g, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    show KeepsLooks shOf s (seat.mark s (F.paid g.owedObjects))
    rw [hm]
    exact keeps_putFork shOf (F := F) (by rw [← hf]; exact named_some hF) rfl
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (named_some h)
    rw [← e]
    exact keeps_refl shOf s

theorem viaW_calls {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsLooks shOf) (K3.Law.blockVia (seatCalls claim) piece laid before p guests) :=
  via_whole shOf _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) (fun _ _ => rfl)
    piece laid before p guests

theorem viaW_digits {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsLooks shOf) (K3.Law.blockVia (seatDigits claim) piece laid before p guests) :=
  via_whole shOf _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim)
    (fun _ _ => rfl) piece laid before p guests

/-- The run "planes". -/
theorem planesRun_keeps {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : ℕ) (readers : K3.Readers S) (n : ℕ) :
    FnCl (KeepsLooks shOf) (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨r, _, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsLooks shOf s (seat.mark s x.2.1)
  rw [hm]
  refine keeps_putFork shOf (by rw [← hf]; exact named_some hF) ?_
  have i : FlL.Stays (do
      let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
        fun col => Fl.need (r.2 col)
      First.Look.planesAddedF g
      pure fs : Fl (Array Aff)) := by
    refine FlL.Stays.bind inferInstance fun _ => ?_
    refine FlL.Stays.bind inferInstance fun _ => ?_
    infer_instance
  exact i.same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx)

/-- The run "join". -/
theorem joinRun_keeps {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) (n : ℕ) :
    FnCl (KeepsLooks shOf) (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨KF, _, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsLooks shOf s (seat.mark s x.2.1)
  rw [hm]
  exact keeps_putFork shOf (by rw [← hf]; exact named_some hF)
    ((FlL.stays_joinF g KF).same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx))

/-- K3's own sub-protocol at an address, whole. -/
theorem theOwn_whole {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole (KeepsLooks shOf) b := by
  unfold K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have W : Whole (KeepsLooks shOf) (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact viaW_digits shOf claim a.piece laid sent p []
        | false => exact viaW_calls shOf claim a.piece laid sent p []
      cases runs with
      | true => exact ⟨W.1, W.2.1, W.2.2⟩
      | false => exact ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- With the step without a round joined behind it. -/
theorem theWhole_whole {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole (KeepsLooks shOf) b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_whole shOf claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole (KeepsLooks shOf) (keeps_trans shOf) _ _ _ W
      ⟨steps_quiet _ _ _ _ f fun s t k => quietAt_keeps shOf hq k, (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩

/-- **K3's sub-protocol at an address, whole, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_whole {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole (KeepsLooks shOf) b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_whole shOf claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        refine ⟨W.1, fun c hc n => ?_, W.2.2⟩
        rcases List.mem_append.1 hc with hc | hc
        · exact W.2.1 c hc n
        · obtain rfl := List.mem_singleton.1 hc
          exact planesRun_keeps shOf _ (fun _ => rfl) (fun _ _ => rfl) _ _ n

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ViaL.hearVia_arrays
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putFork
#print axioms VerifiableInference.Desc.LinkJoin.viaW_calls
#print axioms VerifiableInference.Desc.LinkJoin.viaW_digits
#print axioms VerifiableInference.Desc.LinkJoin.planesRun_keeps
#print axioms VerifiableInference.Desc.LinkJoin.joinRun_keeps
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_whole
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_whole
#print axioms VerifiableInference.Desc.LinkJoin.theStated_whole
