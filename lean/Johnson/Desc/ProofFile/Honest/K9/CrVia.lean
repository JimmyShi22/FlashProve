-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CrVia.lean: K3, THE LOOKUP, WHOLE: an accepting decision, and each of its runs of claims, is
`KeepsCr`.

One of nine files (Honest/K9/CrAre.lean, CrFl, CrWalk, CrK4, CrK5, CrK6, CrSeated, CrVia, CrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves what the batching's draw will test of the
ledger (`cr`) and of the segment's book-keeping (`lnk`). The walk through each sub-protocol's text is the library's own walk for
the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files Slots*.lean beside it), carried over by program
to the reading `cr`, name by name, and righted by hand where the ground fact is another.

Limits. One direction: from a yes. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.ProofFile.Honest.K9.CrSeated
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.ViaC
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.ProdV (Hears level turn run Carried LevelOut)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.Law
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)

variable {α β γ : Type}

theorem msWhole_cr {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E}
    {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : cr G = cr F := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact (K5C.msRow_cr hr).trans (K5C.msHear_cr hh)

/-- One level of the grand product. -/
theorem level_cr {m : ℕ} {z : Array E} {order : List ℕ} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    cr G = cr F := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact msWhole_cr hw
      · exact nomatch h
    · exact nomatch h

theorem turn_cr {order : List ℕ} {s s' : Carried} {m : ℕ} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) :
    cr G = cr F := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_cr hx

theorem fold_cr (m0 : ℕ) (orders : ℕ → List ℕ) : ∀ (l : List ℕ)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → cr y.2.1 = cr x.2.1
  | [], x, y, h => by
    obtain rfl : x = y := Option.some.inj h
    rfl
  | i :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact (fold_cr m0 orders l _ y h).trans (turn_cr hz)

/-- A run of levels. -/
theorem run_cr {m0 n : ℕ} {orders : ℕ → List ℕ} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : run m0 n orders s F rs = some (s', G, rest)) :
    cr G = cr F := fold_cr m0 orders _ (s, F, rs) (s', G, rest) h

/-- Wherever x returns, its ledger has the reading of the ledger that it was handed. -/
class StaysHrC (x : Hr α) : Prop where
  same : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) →
    cr G = cr F

instance staysHr_pureC (a : α) : StaysHrC (pure a : Hr α) :=
  ⟨fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    exact (congrArg (fun y => cr y.2.1) (Option.some.inj e')).symm⟩

theorem StaysHrC.bind {x : Hr α} {f : α → Hr β} (hx : StaysHrC x) (hf : ∀ a, StaysHrC (f a)) :
    StaysHrC (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysHr_bindC (x : Hr α) (f : α → Hr β) [StaysHrC x] [∀ a, StaysHrC (f a)] :
    StaysHrC (x >>= f) := StaysHrC.bind inferInstance inferInstance

instance staysHr_iteC (p : Prop) [Decidable p] (x y : Hr α) [StaysHrC x] [StaysHrC y] :
    StaysHrC (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysHrC" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysHrC.bind ?_ ?_
    | intro _
    | split)

theorem staysHr_foldlMC {f : β → γ → Hr β} (hf : ∀ s a, StaysHrC (f s a)) :
    ∀ (l : List γ) (s : β), StaysHrC (l.foldlM f s)
  | [], s => by
    show StaysHrC (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show StaysHrC (f s a >>= fun s' => l.foldlM f s')
    exact StaysHrC.bind (hf s a) fun s' => staysHr_foldlMC hf l s'

instance staysHr_mustC (b : Bool) : StaysHrC (Hr.must b) :=
  ⟨fun {F G rs rest a} e => by
    unfold Hr.must at e
    split at e
    · exact (congrArg (fun y => cr y.2.1) (Option.some.inj e)).symm
    · exact nomatch e⟩

instance staysHr_slotC : StaysHrC Hr.slot :=
  ⟨fun {F G rs rest a} e => by
    have e' : some (F.next, F, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => cr y.2.1) (Option.some.inj e')).symm⟩

instance staysHr_oweC (what : String) : StaysHrC (Hr.owe what) :=
  ⟨fun {F G rs rest a} e => by
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => cr y.2.1) (Option.some.inj e')).symm⟩

instance staysHr_runC (m0 n : ℕ) (orders : ℕ → List ℕ) (s : Carried) :
    StaysHrC (Hr.of (run m0 n orders s)) := ⟨fun e => run_cr e⟩

instance staysHr_drawsVC (n : ℕ) : StaysHrC (drawsV n) :=
  ⟨fun {F G rs rest a} e => by
    unfold drawsV at e
    cases rs with
    | nil => exact nomatch e
    | cons r rs' =>
      dsimp only at e
      split at e
      · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
        exact (congrArg (fun y => cr y.2.1) e).symm
      · exact nomatch e⟩

instance staysHr_drawVC : StaysHrC drawV :=
  ⟨fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact (staysHr_drawsVC 1).same hx
      · exact nomatch e
    · exact nomatch e⟩

instance staysHr_sumVC (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    StaysHrC (sumV C k endTerm) :=
  ⟨fun {F G rs rest a} e => by
    unfold sumV at e
    split at e
    · exact nomatch e
    · split at e
      · rename_i h row G' hw
        split at e
        · exact nomatch e
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
          exact msWhole_cr hw
      · exact nomatch e⟩

instance staysHr_openVC (C : Aff) (vs : List MaskedSum.Var) : StaysHrC (openV C vs) :=
  ⟨fun {F G rs rest a} e => by
    unfold openV at e
    split at e
    · exact nomatch e
    · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨h, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2.1) e
      exact K5C.msHear_cr hx⟩

instance staysHr_tieVC (w : ℕ) (a : E) : StaysHrC (tieV w a) := by
  unfold tieV
  refine StaysHrC.bind inferInstance fun x => ?_
  refine StaysHrC.bind (staysHr_foldlMC (fun s _ => by staysHrC) _ _) fun _ => ?_
  infer_instance

theorem staysHr_partsVC : ∀ (n : ℕ) (rows : Array Aff) (C : Aff), StaysHrC (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine StaysHrC.bind inferInstance fun w => ?_
    refine StaysHrC.bind (staysHr_partsVC n _ _) fun _ => ?_
    infer_instance

instance (n : ℕ) (rows : Array Aff) (C : Aff) : StaysHrC (partsV n rows C) :=
  staysHr_partsVC n rows C

theorem staysHr_keysVC (f : Face) : ∀ (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff),
    StaysHrC (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine StaysHrC.bind inferInstance fun k => ?_
    refine StaysHrC.bind (staysHr_keysVC f xs Cs _) fun _ => ?_
    infer_instance

instance (f : Face) (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff) :
    StaysHrC (keysV f xs Cs rows) := staysHr_keysVC f xs Cs rows

/-- **The lookup's rounds, heard in order.** -/
instance staysHr_messagesVC (f : Face) : StaysHrC (messagesV f) := by
  unfold messagesV
  staysHrC

theorem hearV_cr {f : Face} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : cr G = cr F := by
  unfold hearV at h
  split at h
  · split at h
    · rename_i g' G' hm
      obtain rfl : G' = G := congrArg (·.2) (Option.some.inj h)
      exact (staysHr_messagesVC f).same hm
    · exact nomatch h
  · exact nomatch h

theorem hearVia_cr {p : First.Look.P} {F G : Fork} {rs : List Fmt.RoundView} {g : Forest.Heard}
    (h : hearVia p F rs = some (g, G)) : cr G = cr F := by
  unfold hearVia at h
  split at h
  · split at h
    · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨g', _, e⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨gv, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2) e
      exact hearV_cr hx
    · exact nomatch h
  · exact nomatch h

end VerifiableInference.Desc.LinkJoin.ViaC

namespace VerifiableInference.Desc.LinkJoin.FlC
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look

instance stays_paidFC (i : ℕ) : StaysC (paidF i) :=
  StaysC.change fun F G h => by
    rw [← Option.some.inj h]
    exact SameCr.refl F

instance stays_planesAddedFC (g : Forest.Heard) : StaysC (planesAddedF g) := by
  unfold planesAddedF; infer_instance

instance stays_joinAddedFC (g : Forest.Heard) : StaysC (joinAddedF g) := by
  unfold joinAddedF; infer_instance

instance stays_joinFC (g : Forest.Heard) (KF : Array Aff) : StaysC (joinF g KF) := by
  unfold joinF; staysC

instance stays_planesAtFC (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff)
    [∀ a b, StaysC (bit a b)] : StaysC (planesAtF g lm e bit) := by
  unfold planesAtF
  exact stays_foldlMC (fun _ _ => by staysC) _ _

instance stays_leavesRowOwnC (p : Psc) (S0 : E) (kept : Aff) : StaysC (leavesRowOwn p S0 kept) := by
  unfold leavesRowOwn; staysC

instance stays_planeClaimsOwnC (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) [∀ a b, StaysC (bit a b)] [∀ a, StaysC (pin a)] :
    StaysC (planeClaimsOwn g lm bit pin) := by
  unfold planeClaimsOwn
  refine StaysC.bind inferInstance fun _ => ?_
  refine StaysC.bind inferInstance fun _ => ?_
  refine StaysC.bind inferInstance fun _ => ?_
  refine StaysC.bind (stays_foldlMC (fun _ _ => by staysC) _ _) fun _ => ?_
  staysC

end VerifiableInference.Desc.LinkJoin.FlC

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)

section
/-- **The tool for a run**: a ledger with the same reading is laid where one is open. -/
theorem keeps_putForkC {s : S} {F G : Fork} (hF : s.fork? = some F)
    (e : cr G = cr F) : KeepsCr s (s.putFork G) := by
  refine keeps_of_casesC fun G' L' e1 e2 => ⟨F, L', hF, ?_, rfl, ?_⟩
  · rw [← link_putFork s G]
    exact e2
  · rw [fork_putFork s F hF] at e1
    rw [← Option.some.inj e1]
    exact e

/-- The decision of `blockVia`, with no premise on the plan. -/
theorem via_decidesC {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    Decides (KeepsCr) (K3.Law.blockVia seat piece laid before p guests) := by
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
  refine keeps_of_casesC fun G' L' hG hL' => ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF'
  · rw [← hl s x.1 x.2]
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact id (ViaC.hearVia_cr (g := x.1) (G := x.2) (named_some hx))

/-- `blockVia`, whole, at a seat whose `mark` is the laying of the ledger. -/
theorem via_wholeC {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsCr) (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨via_decidesC seat hf hk hl piece laid before p guests, fun c hc n s y h => ?_,
    (fun _ hc => nomatch hc)⟩
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p guests).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨g, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    show KeepsCr s (seat.mark s (F.paid g.owedObjects))
    rw [hm]
    exact keeps_putForkC (F := F) (by rw [← hf]; exact named_some hF) rfl
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (named_some h)
    rw [← e]
    exact keeps_reflC s

theorem viaW_callsC {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsCr) (K3.Law.blockVia (seatCalls claim) piece laid before p guests) :=
  via_wholeC _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) (fun _ _ => rfl)
    piece laid before p guests

theorem viaW_digitsC {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsCr) (K3.Law.blockVia (seatDigits claim) piece laid before p guests) :=
  via_wholeC _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim)
    (fun _ _ => rfl) piece laid before p guests

/-- The run "planes". -/
theorem planesRun_keepsC {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : ℕ) (readers : K3.Readers S) (n : ℕ) :
    FnCl (KeepsCr) (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨r, _, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsCr s (seat.mark s x.2.1)
  rw [hm]
  refine keeps_putForkC (by rw [← hf]; exact named_some hF) ?_
  have i : FlC.StaysC (do
      let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
        fun col => Fl.need (r.2 col)
      First.Look.planesAddedF g
      pure fs : Fl (Array Aff)) := by
    refine FlC.StaysC.bind inferInstance fun _ => ?_
    refine FlC.StaysC.bind inferInstance fun _ => ?_
    infer_instance
  exact i.same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx)

/-- The run "join". -/
theorem joinRun_keepsC {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) (n : ℕ) :
    FnCl (KeepsCr) (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨KF, _, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsCr s (seat.mark s x.2.1)
  rw [hm]
  exact keeps_putForkC (by rw [← hf]; exact named_some hF)
    ((FlC.stays_joinFC g KF).same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx))

/-- K3's own sub-protocol at an address, whole. -/
theorem theOwn_wholeC {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole (KeepsCr) b := by
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
      have W : Whole (KeepsCr) (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact viaW_digitsC claim a.piece laid sent p []
        | false => exact viaW_callsC claim a.piece laid sent p []
      cases runs with
      | true => exact ⟨W.1, W.2.1, W.2.2⟩
      | false => exact ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- With the step without a round joined behind it. -/
theorem theWhole_wholeC {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole (KeepsCr) b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_wholeC claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole (KeepsCr) (keeps_transC) _ _ _ W
      ⟨steps_quiet _ _ _ _ f fun s t k => quietAt_keepsC hq k, (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩

/-- **K3's sub-protocol at an address, whole, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_wholeC {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole (KeepsCr) b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_wholeC claim true X codes shape a h0
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
          exact planesRun_keepsC _ (fun _ => rfl) (fun _ _ => rfl) _ _ n

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ViaC.msWhole_cr
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.level_cr
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.turn_cr
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.fold_cr
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.run_cr
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_pureC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.StaysHrC.bind
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_bindC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_iteC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_foldlMC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_mustC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_slotC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_oweC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_runC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_drawsVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_drawVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_sumVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_openVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_tieVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_partsVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_keysVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.staysHr_messagesVC
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.hearV_cr
#print axioms VerifiableInference.Desc.LinkJoin.ViaC.hearVia_cr
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_paidFC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_planesAddedFC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_joinAddedFC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_joinFC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_planesAtFC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_leavesRowOwnC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_planeClaimsOwnC
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putForkC
#print axioms VerifiableInference.Desc.LinkJoin.via_decidesC
#print axioms VerifiableInference.Desc.LinkJoin.via_wholeC
#print axioms VerifiableInference.Desc.LinkJoin.viaW_callsC
#print axioms VerifiableInference.Desc.LinkJoin.viaW_digitsC
#print axioms VerifiableInference.Desc.LinkJoin.planesRun_keepsC
#print axioms VerifiableInference.Desc.LinkJoin.joinRun_keepsC
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_wholeC
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_wholeC
#print axioms VerifiableInference.Desc.LinkJoin.theStated_wholeC
