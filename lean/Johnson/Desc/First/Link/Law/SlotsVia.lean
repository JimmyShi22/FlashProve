-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsVia.lean: K3, WHOLE.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksVia.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.First.Link.Law.SlotsSeated
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.ViaS
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.ProdV (Hears level turn run Carried LevelOut)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.Law
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)

variable {α β γ : Type}

theorem msWhole_slots {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E}
    {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : sl G = sl F := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact (K5S.msRow_slots hr).trans (K5S.msHear_slots hh)

/-- One level of the grand product. -/
theorem level_slots {m : ℕ} {z : Array E} {order : List ℕ} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    sl G = sl F := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact msWhole_slots hw
      · exact nomatch h
    · exact nomatch h

theorem turn_slots {order : List ℕ} {s s' : Carried} {m : ℕ} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) :
    sl G = sl F := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_slots hx

theorem fold_slots (m0 : ℕ) (orders : ℕ → List ℕ) : ∀ (l : List ℕ)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → sl y.2.1 = sl x.2.1
  | [], x, y, h => by
    obtain rfl : x = y := Option.some.inj h
    rfl
  | i :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact (fold_slots m0 orders l _ y h).trans (turn_slots hz)

/-- A run of levels. -/
theorem run_slots {m0 n : ℕ} {orders : ℕ → List ℕ} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : run m0 n orders s F rs = some (s', G, rest)) :
    sl G = sl F := fold_slots m0 orders _ (s, F, rs) (s', G, rest) h

/-- Wherever x returns, its ledger has the two numbers of the ledger that it was handed. -/
class StaysHrS (x : Hr α) : Prop where
  same : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) →
    sl G = sl F

instance staysHr_pureS (a : α) : StaysHrS (pure a : Hr α) :=
  ⟨fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    exact (congrArg (fun y => sl y.2.1) (Option.some.inj e')).symm⟩

theorem StaysHrS.bind {x : Hr α} {f : α → Hr β} (hx : StaysHrS x) (hf : ∀ a, StaysHrS (f a)) :
    StaysHrS (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance staysHr_bindS (x : Hr α) (f : α → Hr β) [StaysHrS x] [∀ a, StaysHrS (f a)] :
    StaysHrS (x >>= f) := StaysHrS.bind inferInstance inferInstance

instance staysHr_iteS (p : Prop) [Decidable p] (x y : Hr α) [StaysHrS x] [StaysHrS y] :
    StaysHrS (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysHrS" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysHrS.bind ?_ ?_
    | intro _
    | split)

theorem staysHr_foldlMS {f : β → γ → Hr β} (hf : ∀ s a, StaysHrS (f s a)) :
    ∀ (l : List γ) (s : β), StaysHrS (l.foldlM f s)
  | [], s => by
    show StaysHrS (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show StaysHrS (f s a >>= fun s' => l.foldlM f s')
    exact StaysHrS.bind (hf s a) fun s' => staysHr_foldlMS hf l s'

instance staysHr_mustS (b : Bool) : StaysHrS (Hr.must b) :=
  ⟨fun {F G rs rest a} e => by
    unfold Hr.must at e
    split at e
    · exact (congrArg (fun y => sl y.2.1) (Option.some.inj e)).symm
    · exact nomatch e⟩

instance staysHr_slotS : StaysHrS Hr.slot :=
  ⟨fun {F G rs rest a} e => by
    have e' : some (F.next, F, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => sl y.2.1) (Option.some.inj e')).symm⟩

instance staysHr_oweS (what : String) : StaysHrS (Hr.owe what) :=
  ⟨fun {F G rs rest a} e => by
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    exact (congrArg (fun y => sl y.2.1) (Option.some.inj e')).symm⟩

instance staysHr_runS (m0 n : ℕ) (orders : ℕ → List ℕ) (s : Carried) :
    StaysHrS (Hr.of (run m0 n orders s)) := ⟨fun e => run_slots e⟩

instance staysHr_drawsVS (n : ℕ) : StaysHrS (drawsV n) :=
  ⟨fun {F G rs rest a} e => by
    unfold drawsV at e
    cases rs with
    | nil => exact nomatch e
    | cons r rs' =>
      dsimp only at e
      split at e
      · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
        exact (congrArg (fun y => sl y.2.1) e).symm
      · exact nomatch e⟩

instance staysHr_drawVS : StaysHrS drawV :=
  ⟨fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact (staysHr_drawsVS 1).same hx
      · exact nomatch e
    · exact nomatch e⟩

instance staysHr_sumVS (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    StaysHrS (sumV C k endTerm) :=
  ⟨fun {F G rs rest a} e => by
    unfold sumV at e
    split at e
    · exact nomatch e
    · split at e
      · rename_i h row G' hw
        split at e
        · exact nomatch e
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
          exact msWhole_slots hw
      · exact nomatch e⟩

instance staysHr_openVS (C : Aff) (vs : List MaskedSum.Var) : StaysHrS (openV C vs) :=
  ⟨fun {F G rs rest a} e => by
    unfold openV at e
    split at e
    · exact nomatch e
    · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨h, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2.1) e
      exact K5S.msHear_slots hx⟩

instance staysHr_tieVS (w : ℕ) (a : E) : StaysHrS (tieV w a) := by
  unfold tieV
  refine StaysHrS.bind inferInstance fun x => ?_
  refine StaysHrS.bind (staysHr_foldlMS (fun s _ => by staysHrS) _ _) fun _ => ?_
  infer_instance

theorem staysHr_partsVS : ∀ (n : ℕ) (rows : Array Aff) (C : Aff), StaysHrS (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine StaysHrS.bind inferInstance fun w => ?_
    refine StaysHrS.bind (staysHr_partsVS n _ _) fun _ => ?_
    infer_instance

instance (n : ℕ) (rows : Array Aff) (C : Aff) : StaysHrS (partsV n rows C) :=
  staysHr_partsVS n rows C

theorem staysHr_keysVS (f : Face) : ∀ (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff),
    StaysHrS (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine StaysHrS.bind inferInstance fun k => ?_
    refine StaysHrS.bind (staysHr_keysVS f xs Cs _) fun _ => ?_
    infer_instance

instance (f : Face) (xs : List (ℕ × ℕ)) (Cs : List Aff) (rows : Array Aff) :
    StaysHrS (keysV f xs Cs rows) := staysHr_keysVS f xs Cs rows

/-- **The lookup's rounds, heard in order.** -/
instance staysHr_messagesVS (f : Face) : StaysHrS (messagesV f) := by
  unfold messagesV
  staysHrS

theorem hearV_slots {f : Face} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : sl G = sl F := by
  unfold hearV at h
  split at h
  · split at h
    · rename_i g' G' hm
      obtain rfl : G' = G := congrArg (·.2) (Option.some.inj h)
      exact (staysHr_messagesVS f).same hm
    · exact nomatch h
  · exact nomatch h

theorem hearVia_slots {p : First.Look.P} {F G : Fork} {rs : List Fmt.RoundView} {g : Forest.Heard}
    (h : hearVia p F rs = some (g, G)) : sl G = sl F := by
  unfold hearVia at h
  split at h
  · split at h
    · obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨g', _, e⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨gv, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2) e
      exact hearV_slots hx
    · exact nomatch h
  · exact nomatch h

end VerifiableInference.Desc.LinkJoin.ViaS

namespace VerifiableInference.Desc.LinkJoin.FlS
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look

instance stays_paidFS (i : ℕ) : StaysS (paidF i) :=
  StaysS.change fun F G h => by
    rw [← Option.some.inj h]
    exact SameSlots.refl F

instance stays_planesAddedFS (g : Forest.Heard) : StaysS (planesAddedF g) := by
  unfold planesAddedF; infer_instance

instance stays_joinAddedFS (g : Forest.Heard) : StaysS (joinAddedF g) := by
  unfold joinAddedF; infer_instance

instance stays_joinFS (g : Forest.Heard) (KF : Array Aff) : StaysS (joinF g KF) := by
  unfold joinF; staysS

instance stays_planesAtFS (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff)
    [∀ a b, StaysS (bit a b)] : StaysS (planesAtF g lm e bit) := by
  unfold planesAtF
  exact stays_foldlMS (fun _ _ => by staysS) _ _

instance stays_leavesRowOwnS (p : Psc) (S0 : E) (kept : Aff) : StaysS (leavesRowOwn p S0 kept) := by
  unfold leavesRowOwn; staysS

instance stays_planeClaimsOwnS (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) [∀ a b, StaysS (bit a b)] [∀ a, StaysS (pin a)] :
    StaysS (planeClaimsOwn g lm bit pin) := by
  unfold planeClaimsOwn
  refine StaysS.bind inferInstance fun _ => ?_
  refine StaysS.bind inferInstance fun _ => ?_
  refine StaysS.bind inferInstance fun _ => ?_
  refine StaysS.bind (stays_foldlMS (fun _ _ => by staysS) _ _) fun _ => ?_
  staysS

end VerifiableInference.Desc.LinkJoin.FlS

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)

section
variable (nsOf : ℕ → ℕ × ℕ)

/-- **The tool for a run**: a ledger with the same two numbers is laid where one is open. -/
theorem keeps_putForkS {s : S} {F G : Fork} (hF : s.fork? = some F)
    (e : sl G = sl F) : KeepsSlots nsOf s (s.putFork G) := by
  refine keeps_of_casesS nsOf fun G' L' e1 e2 => Or.inr ⟨F, L', hF, ?_, rfl, ?_⟩
  · rw [← link_putFork s G]
    exact e2
  · rw [fork_putFork s F hF] at e1
    rw [← Option.some.inj e1]
    exact e

/-- The decision of `blockVia`, with no premise on the plan. -/
theorem via_decidesS {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    Decides (KeepsSlots nsOf) (K3.Law.blockVia seat piece laid before p guests) := by
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
  refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF'
  · rw [← hl s x.1 x.2]
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact id (ViaS.hearVia_slots (g := x.1) (G := x.2) (named_some hx))

/-- `blockVia`, whole, at a seat whose `mark` is the laying of the ledger. -/
theorem via_wholeS {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsSlots nsOf) (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨via_decidesS nsOf seat hf hk hl piece laid before p guests, fun c hc n s y h => ?_,
    (fun _ hc => nomatch hc)⟩
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p guests).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨g, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    show KeepsSlots nsOf s (seat.mark s (F.paid g.owedObjects))
    rw [hm]
    exact keeps_putForkS nsOf (F := F) (by rw [← hf]; exact named_some hF) rfl
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (named_some h)
    rw [← e]
    exact keeps_reflS nsOf s

theorem viaW_callsS {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsSlots nsOf) (K3.Law.blockVia (seatCalls claim) piece laid before p guests) :=
  via_wholeS nsOf _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) (fun _ _ => rfl)
    piece laid before p guests

theorem viaW_digitsS {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsSlots nsOf) (K3.Law.blockVia (seatDigits claim) piece laid before p guests) :=
  via_wholeS nsOf _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim)
    (fun _ _ => rfl) piece laid before p guests

/-- The run "planes". -/
theorem planesRun_keepsS {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : ℕ) (readers : K3.Readers S) (n : ℕ) :
    FnCl (KeepsSlots nsOf) (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨r, _, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsSlots nsOf s (seat.mark s x.2.1)
  rw [hm]
  refine keeps_putForkS nsOf (by rw [← hf]; exact named_some hF) ?_
  have i : FlS.StaysS (do
      let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
        fun col => Fl.need (r.2 col)
      First.Look.planesAddedF g
      pure fs : Fl (Array Aff)) := by
    refine FlS.StaysS.bind inferInstance fun _ => ?_
    refine FlS.StaysS.bind inferInstance fun _ => ?_
    infer_instance
  exact i.same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx)

/-- The run "join". -/
theorem joinRun_keepsS {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) (n : ℕ) :
    FnCl (KeepsSlots nsOf) (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨KF, _, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsSlots nsOf s (seat.mark s x.2.1)
  rw [hm]
  exact keeps_putForkS nsOf (by rw [← hf]; exact named_some hF)
    ((FlS.stays_joinFS g KF).same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx))

/-- K3's own sub-protocol at an address, whole. -/
theorem theOwn_wholeS {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole (KeepsSlots nsOf) b := by
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
      have W : Whole (KeepsSlots nsOf) (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact viaW_digitsS nsOf claim a.piece laid sent p []
        | false => exact viaW_callsS nsOf claim a.piece laid sent p []
      cases runs with
      | true => exact ⟨W.1, W.2.1, W.2.2⟩
      | false => exact ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- With the step without a round joined behind it. -/
theorem theWhole_wholeS {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole (KeepsSlots nsOf) b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_wholeS nsOf claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole (KeepsSlots nsOf) (keeps_transS nsOf) _ _ _ W
      ⟨steps_quiet _ _ _ _ f fun s t k => quietAt_keepsS nsOf hq k, (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩

/-- **K3's sub-protocol at an address, whole, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_wholeS {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole (KeepsSlots nsOf) b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_wholeS nsOf claim true X codes shape a h0
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
          exact planesRun_keepsS nsOf _ (fun _ => rfl) (fun _ _ => rfl) _ _ n

end

end VerifiableInference.Desc.LinkJoin
