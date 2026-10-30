-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrVia.lean: K3, THE LOOKUP, WHOLE: an accepting decision, and each of its runs of claims, is
`KeepsTr`.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. One direction: from a yes. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.ProofFile.Honest.K9.TrSeated
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.ViaT
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.ProdV (Hears level turn run Carried LevelOut)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.Law
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)

variable {α β γ : Type}

theorem msWhole_tr {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E}
    {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : tr G = tr F := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact (K5T.msRow_tr hr).trans (K5T.msHear_tr hh)

/-- One level of the grand product. -/
theorem level_tr {m : ℕ} {z : Array E} {order : List ℕ} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    tr G = tr F := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact msWhole_tr hw
      · exact nomatch h
    · exact nomatch h

theorem turn_tr {order : List ℕ} {s s' : Carried} {m : ℕ} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) :
    tr G = tr F := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_tr hx

theorem fold_tr (m0 : ℕ) (orders : ℕ → List ℕ) : ∀ (l : List ℕ)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → tr y.2.1 = tr x.2.1
  | [], x, y, h => by
    obtain rfl : x = y := Option.some.inj h
    rfl
  | i :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact (fold_tr m0 orders l _ y h).trans (turn_tr hz)

/-- A run of levels. -/
theorem run_tr {m0 n : ℕ} {orders : ℕ → List ℕ} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : run m0 n orders s F rs = some (s', G, rest)) :
    tr G = tr F := fold_tr m0 orders _ (s, F, rs) (s', G, rest) h

/-- Wherever x returns, its ledger has the reading of the ledger that it was handed. -/
class StaysHrT (x : Hr α) : Prop where
  same : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) →
    tr G = tr F

instance staysHr_pureT (a : α) : StaysHrT (pure a : Hr α) :=
  ⟨fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    exact (congrArg (fun y => tr y.2.1) (Option.some.inj e')).symm⟩

theorem StaysHrT.bind {x : Hr α} {f : α → Hr β} (hx : StaysHrT x) (hf : ∀ a, StaysHrT (f a)) :
    StaysHrT (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysHr_bindT (x : Hr α) (f : α → Hr β) [StaysHrT x] [∀ a, StaysHrT (f a)] :
    StaysHrT (x >>= f) := StaysHrT.bind inferInstance inferInstance

instance staysHr_iteT (p : Prop) [Decidable p] (x y : Hr α) [StaysHrT x] [StaysHrT y] :
    StaysHrT (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysHrT" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysHrT.bind ?_ ?_
    | intro _
    | split)

theorem staysHr_foldlMT {f : β → γ → Hr β} (hf : ∀ s a, StaysHrT (f s a)) :
    ∀ (l : List γ) (s : β), StaysHrT (l.foldlM f s)
  | [], s => by
    show StaysHrT (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show StaysHrT (f s a >>= fun s' => l.foldlM f s')
    exact StaysHrT.bind (hf s a) fun s' => staysHr_foldlMT hf l s'

instance staysHr_mustT (b : Bool) : StaysHrT (Hr.must b) :=
  ⟨fun {F G rs rest a} e => by
    unfold Hr.must at e
    split at e
    · exact (congrArg (fun y => tr y.2.1) (Option.some.inj e)).symm
    · exact nomatch e⟩

instance staysHr_slotT : StaysHrT Hr.slot :=
  ⟨fun {F G rs rest a} e => by
    have e' : some (F.next, F, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => tr y.2.1) (Option.some.inj e')).symm⟩

instance staysHr_oweT (what : String) : StaysHrT (Hr.owe what) :=
  ⟨fun {F G rs rest a} e => by
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => tr y.2.1) (Option.some.inj e')).symm⟩

instance staysHr_runT (m0 n : ℕ) (orders : ℕ → List ℕ) (s : Carried) :
    StaysHrT (Hr.of (run m0 n orders s)) := ⟨fun e => run_tr e⟩

instance staysHr_drawsVT (n : ℕ) : StaysHrT (drawsV n) :=
  ⟨fun {F G rs rest a} e => by
    unfold drawsV at e
    cases rs with
    | nil => exact nomatch e
    | cons r rs' =>
      dsimp only at e
      split at e
      · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
        exact (congrArg (fun y => tr y.2.1) e).symm
      · exact nomatch e⟩

instance staysHr_drawVT : StaysHrT drawV :=
  ⟨fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact (staysHr_drawsVT 1).same hx
      · exact nomatch e
    · exact nomatch e⟩

instance staysHr_sumVT (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    StaysHrT (sumV C k endTerm) :=
  ⟨fun {F G rs rest a} e => by
    unfold sumV at e
    split at e
    · exact nomatch e
    · split at e
      · rename_i h row G' hw
        split at e
        · exact nomatch e
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
          exact msWhole_tr hw
      · exact nomatch e⟩

instance staysHr_openVT (C : Aff) (vs : List MaskedSum.Var) : StaysHrT (openV C vs) :=
  ⟨fun {F G rs rest a} e => by
    unfold openV at e
    split at e
    · exact nomatch e
    · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨h, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2.1) e
      exact K5T.msHear_tr hx⟩

instance staysHr_tieVT (w : ℕ) (a : E) : StaysHrT (tieV w a) := by
  unfold tieV
  refine StaysHrT.bind inferInstance fun x => ?_
  refine StaysHrT.bind (staysHr_foldlMT (fun s _ => by staysHrT) _ _) fun _ => ?_
  infer_instance

theorem staysHr_partsVT : ∀ (n : ℕ) (rows : Array Aff) (C : Aff), StaysHrT (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine StaysHrT.bind inferInstance fun w => ?_
    refine StaysHrT.bind (staysHr_partsVT n _ _) fun _ => ?_
    infer_instance

instance (n : ℕ) (rows : Array Aff) (C : Aff) : StaysHrT (partsV n rows C) :=
  staysHr_partsVT n rows C

theorem staysHr_keysVT (f : Face) : ∀ (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff),
    StaysHrT (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine StaysHrT.bind inferInstance fun k => ?_
    refine StaysHrT.bind (staysHr_keysVT f xs Cs _) fun _ => ?_
    infer_instance

instance (f : Face) (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff) :
    StaysHrT (keysV f xs Cs rows) := staysHr_keysVT f xs Cs rows

/-- **The lookup's rounds, heard in order.** -/
instance staysHr_messagesVT (f : Face) : StaysHrT (messagesV f) := by
  unfold messagesV
  staysHrT

theorem hearV_tr {f : Face} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : tr G = tr F := by
  unfold hearV at h
  split at h
  · split at h
    · rename_i g' G' hm
      obtain rfl : G' = G := congrArg (·.2) (Option.some.inj h)
      exact (staysHr_messagesVT f).same hm
    · exact nomatch h
  · exact nomatch h

theorem hearVia_tr {p : First.Look.P} {F G : Fork} {rs : List Fmt.RoundView} {g : Forest.Heard}
    (h : hearVia p F rs = some (g, G)) : tr G = tr F := by
  unfold hearVia at h
  split at h
  · split at h
    · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨g', _, e⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨gv, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2) e
      exact hearV_tr hx
    · exact nomatch h
  · exact nomatch h

end VerifiableInference.Desc.LinkJoin.ViaT

namespace VerifiableInference.Desc.LinkJoin.FlT
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look

instance stays_paidFT (i : ℕ) : StaysT (paidF i) :=
  StaysT.change fun F G h => by
    rw [← Option.some.inj h]
    exact SameTr.refl F

instance stays_planesAddedFT (g : Forest.Heard) : StaysT (planesAddedF g) := by
  unfold planesAddedF; infer_instance

instance stays_joinAddedFT (g : Forest.Heard) : StaysT (joinAddedF g) := by
  unfold joinAddedF; infer_instance

instance stays_joinFT (g : Forest.Heard) (KF : Array Aff) : StaysT (joinF g KF) := by
  unfold joinF; staysT

instance stays_planesAtFT (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff)
    [∀ a b, StaysT (bit a b)] : StaysT (planesAtF g lm e bit) := by
  unfold planesAtF
  exact stays_foldlMT (fun _ _ => by staysT) _ _

instance stays_leavesRowOwnT (p : Psc) (S0 : E) (kept : Aff) : StaysT (leavesRowOwn p S0 kept) := by
  unfold leavesRowOwn; staysT

instance stays_planeClaimsOwnT (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) [∀ a b, StaysT (bit a b)] [∀ a, StaysT (pin a)] :
    StaysT (planeClaimsOwn g lm bit pin) := by
  unfold planeClaimsOwn
  refine StaysT.bind inferInstance fun _ => ?_
  refine StaysT.bind inferInstance fun _ => ?_
  refine StaysT.bind inferInstance fun _ => ?_
  refine StaysT.bind (stays_foldlMT (fun _ _ => by staysT) _ _) fun _ => ?_
  staysT

end VerifiableInference.Desc.LinkJoin.FlT

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)

section
/-- **The tool for a run**: a ledger with the same reading is laid where one is open. -/
theorem keeps_putForkT {s : S} {F G : Fork} (hF : s.fork? = some F)
    (e : tr G = tr F) : KeepsTr s (s.putFork G) := by
  refine keeps_of_casesT fun G' L' e1 e2 => ⟨F, L', hF, ?_, rfl, ?_⟩
  · rw [← link_putFork s G]
    exact e2
  · rw [fork_putFork s F hF] at e1
    rw [← Option.some.inj e1]
    exact e

/-- The decision of `blockVia`, with no premise on the plan. -/
theorem via_decidesT {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    Decides (KeepsTr) (K3.Law.blockVia seat piece laid before p guests) := by
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
  refine keeps_of_casesT fun G' L' hG hL' => ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF'
  · rw [← hl s x.1 x.2]
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact id (ViaT.hearVia_tr (g := x.1) (G := x.2) (named_some hx))

/-- `blockVia`, whole, at a seat whose `mark` is the laying of the ledger. -/
theorem via_wholeT {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsTr) (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨via_decidesT seat hf hk hl piece laid before p guests, fun c hc n s y h => ?_,
    (fun _ hc => nomatch hc)⟩
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p guests).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨g, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    show KeepsTr s (seat.mark s (F.paid g.owedObjects))
    rw [hm]
    exact keeps_putForkT (F := F) (by rw [← hf]; exact named_some hF) rfl
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (named_some h)
    rw [← e]
    exact keeps_reflT s

theorem viaW_callsT {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsTr) (K3.Law.blockVia (seatCalls claim) piece laid before p guests) :=
  via_wholeT _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) (fun _ _ => rfl)
    piece laid before p guests

theorem viaW_digitsT {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsTr) (K3.Law.blockVia (seatDigits claim) piece laid before p guests) :=
  via_wholeT _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim)
    (fun _ _ => rfl) piece laid before p guests

/-- The run "planes". -/
theorem planesRun_keepsT {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : ℕ) (readers : K3.Readers S) (n : ℕ) :
    FnCl (KeepsTr) (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨r, _, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsTr s (seat.mark s x.2.1)
  rw [hm]
  refine keeps_putForkT (by rw [← hf]; exact named_some hF) ?_
  have i : FlT.StaysT (do
      let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
        fun col => Fl.need (r.2 col)
      First.Look.planesAddedF g
      pure fs : Fl (Array Aff)) := by
    refine FlT.StaysT.bind inferInstance fun _ => ?_
    refine FlT.StaysT.bind inferInstance fun _ => ?_
    infer_instance
  exact i.same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx)

/-- The run "join". -/
theorem joinRun_keepsT {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) (n : ℕ) :
    FnCl (KeepsTr) (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨KF, _, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsTr s (seat.mark s x.2.1)
  rw [hm]
  exact keeps_putForkT (by rw [← hf]; exact named_some hF)
    ((FlT.stays_joinFT g KF).same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx))

/-- K3's own sub-protocol at an address, whole. -/
theorem theOwn_wholeT {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole (KeepsTr) b := by
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
      have W : Whole (KeepsTr) (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact viaW_digitsT claim a.piece laid sent p []
        | false => exact viaW_callsT claim a.piece laid sent p []
      cases runs with
      | true => exact ⟨W.1, W.2.1, W.2.2⟩
      | false => exact ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- With the step without a round joined behind it. -/
theorem theWhole_wholeT {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole (KeepsTr) b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_wholeT claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole (KeepsTr) (keeps_transT) _ _ _ W
      ⟨steps_quiet _ _ _ _ f fun s t k => quietAt_keepsT hq k, (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩

/-- **K3's sub-protocol at an address, whole, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_wholeT {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole (KeepsTr) b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_wholeT claim true X codes shape a h0
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
          exact planesRun_keepsT _ (fun _ => rfl) (fun _ _ => rfl) _ _ n

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ViaT.msWhole_tr
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.level_tr
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.turn_tr
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.fold_tr
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.run_tr
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_pureT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.StaysHrT.bind
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_bindT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_iteT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_foldlMT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_mustT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_slotT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_oweT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_runT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_drawsVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_drawVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_sumVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_openVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_tieVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_partsVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_keysVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.staysHr_messagesVT
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.hearV_tr
#print axioms VerifiableInference.Desc.LinkJoin.ViaT.hearVia_tr
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_paidFT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_planesAddedFT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_joinAddedFT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_joinFT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_planesAtFT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_leavesRowOwnT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_planeClaimsOwnT
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putForkT
#print axioms VerifiableInference.Desc.LinkJoin.via_decidesT
#print axioms VerifiableInference.Desc.LinkJoin.via_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.viaW_callsT
#print axioms VerifiableInference.Desc.LinkJoin.viaW_digitsT
#print axioms VerifiableInference.Desc.LinkJoin.planesRun_keepsT
#print axioms VerifiableInference.Desc.LinkJoin.joinRun_keepsT
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_wholeT
#print axioms VerifiableInference.Desc.LinkJoin.theStated_wholeT
