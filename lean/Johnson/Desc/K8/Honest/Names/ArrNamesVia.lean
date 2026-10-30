-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesVia.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: THE
LOOKUP (K3) AS THE SEAT LAYS IT: ITS DECISION AND ITS RUNS OF CLAIMS. MADE BY PROGRAM FROM THE
LIBRARY's Johnson/Desc/First/Link/Law/LooksVia.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
ITS FORM, AS ITS SOURCE's: 7 INSTANCES OF THE CLASS `StaysN` · ONE LOCAL MACRO, "staysN" (the
library's "stays" is global; this one is laid anew in each file that spends it).
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (17): stays_paidF → stays_paidFN · stays_planesAddedF → stays_planesAddedFN ·
stays_joinAddedF → stays_joinAddedFN · stays_joinF → stays_joinFN · stays_planesAtF →
stays_planesAtFN · stays_leavesRowOwn → stays_leavesRowOwnN · stays_planeClaimsOwn →
stays_planeClaimsOwnN · keeps_putFork → keeps_putForkN · via_decides → via_decidesN · via_whole →
via_wholeN · viaW_calls → viaW_callsN · viaW_digits → viaW_digitsN · planesRun_keeps →
planesRun_keepsN · joinRun_keeps → joinRun_keepsN · theOwn_whole → theOwn_wholeN · theWhole_whole →
theWhole_wholeN · theStated_whole → theStated_wholeN.
CALLED WHERE THEY LIE (26): msWhole_arrays · level_arrays · turn_arrays · fold_arrays · run_arrays ·
StaysHr · bindHr_some · staysHr_pure · StaysHr.bind · staysHr_bind · staysHr_ite · staysHr_foldlM ·
staysHr_must · staysHr_slot · staysHr_owe · staysHr_run · staysHr_drawsV · staysHr_drawV ·
staysHr_sumV · staysHr_openV · staysHr_tieV · staysHr_partsV · staysHr_keysV · staysHr_messagesV ·
hearV_arrays · hearVia_arrays.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.K8.Honest.Names.FlArrNames
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.ViaL
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.ProdV (Hears level turn run Carried LevelOut)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.Law

variable {α β γ : Type}

end VerifiableInference.Desc.LinkJoin.ViaL

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Look

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysN" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysN.bind ?_ ?_
    | intro _
    | split)

instance stays_paidFN (i : ℕ) : StaysN (paidF i) :=
  StaysN.change fun F G h => by
    rw [← Option.some.inj h]
    exact SameArrNames.refl F

instance stays_planesAddedFN (g : Forest.Heard) : StaysN (planesAddedF g) := by
  unfold planesAddedF; infer_instance

instance stays_joinAddedFN (g : Forest.Heard) : StaysN (joinAddedF g) := by
  unfold joinAddedF; infer_instance

instance stays_joinFN (g : Forest.Heard) (KF : Array Aff) : StaysN (joinF g KF) := by
  unfold joinF; staysN

instance stays_planesAtFN (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Fl Aff)
    [∀ a b, StaysN (bit a b)] : StaysN (planesAtF g lm e bit) := by
  unfold planesAtF
  exact stays_foldlMN (fun _ _ => by staysN) _ _

instance stays_leavesRowOwnN (p : Psc) (S0 : E) (kept : Aff) : StaysN (leavesRowOwn p S0 kept) := by
  unfold leavesRowOwn; staysN

instance stays_planeClaimsOwnN (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Fl Aff)
    (pin : ℕ → Fl Aff) [∀ a b, StaysN (bit a b)] [∀ a, StaysN (pin a)] :
    StaysN (planeClaimsOwn g lm bit pin) := by
  unfold planeClaimsOwn
  refine StaysN.bind inferInstance fun _ => ?_
  refine StaysN.bind inferInstance fun _ => ?_
  refine StaysN.bind inferInstance fun _ => ?_
  refine StaysN.bind (stays_foldlMN (fun _ _ => by staysN) _ _) fun _ => ?_
  staysN

end VerifiableInference.Desc.LinkJoin.FlL

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)

section
variable (shOf : ℕ → List String)

/-- **The tool for a run**: a ledger with the same names is laid where one is open. -/
theorem keeps_putForkN {s : S} {F G : Fork} (hF : s.fork? = some F)
    (e : G.trees.map treeName = F.trees.map treeName) : KeepsArrNames shOf s (s.putFork G) := by
  refine keeps_of_casesN shOf fun G' L' e1 e2 => Or.inr ⟨F, L', hF, ?_, rfl, ?_⟩
  · rw [← link_putFork s G]
    exact e2
  · rw [fork_putFork s F hF] at e1
    rw [← Option.some.inj e1]
    exact e

/-- The decision of `blockVia`, with no premise on the plan. -/
theorem via_decidesN {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?) (piece : ℕ)
    (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    Decides (KeepsArrNames shOf) (K3.Law.blockVia seat piece laid before p guests) := by
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
  refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨F, L', ?_, ?_, rfl, ?_⟩
  · rw [← hf]
    exact hF'
  · rw [← hl s x.1 x.2]
    exact hL'
  · rw [← Option.some.inj (e1.symm.trans hG)]
    exact congrArg (·.map treeName) (ViaL.hearVia_arrays (g := x.1) (G := x.2) (named_some hx))

/-- `blockVia`, whole, at a seat whose `mark` is the laying of the ledger. -/
theorem via_wholeN {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (hl : ∀ s g G, (seat.put s g G).link? = s.link?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsArrNames shOf) (K3.Law.blockVia seat piece laid before p guests) := by
  refine ⟨via_decidesN shOf seat hf hk hl piece laid before p guests, fun c hc n s y h => ?_,
    (fun _ hc => nomatch hc)⟩
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p guests).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · obtain ⟨F, hF, h⟩ := K9L.ok_bind h
    obtain ⟨g, _, h⟩ := K9L.ok_bind h
    obtain rfl := Except.ok.inj h
    show KeepsArrNames shOf s (seat.mark s (F.paid g.owedObjects))
    rw [hm]
    exact keeps_putForkN shOf (F := F) (by rw [← hf]; exact named_some hF) rfl
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 (named_some h)
    rw [← e]
    exact keeps_reflN shOf s

theorem viaW_callsN {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsArrNames shOf) (K3.Law.blockVia (seatCalls claim) piece laid before p guests) :=
  via_wholeN shOf _ (fun _ => rfl) (seatCalls_keeps claim) (calls_put_link claim) (fun _ _ => rfl)
    piece laid before p guests

theorem viaW_digitsN {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array ℕ)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole (KeepsArrNames shOf) (K3.Law.blockVia (seatDigits claim) piece laid before p guests) :=
  via_wholeN shOf _ (fun _ => rfl) (seatDigits_keeps claim) (digits_put_link claim)
    (fun _ _ => rfl) piece laid before p guests

/-- The run "planes". -/
theorem planesRun_keepsN {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : ℕ) (readers : K3.Readers S) (n : ℕ) :
    FnCl (KeepsArrNames shOf) (K3.planesRun seat lm readers n) := by
  intro s y h
  unfold K3.planesRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨r, _, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsArrNames shOf s (seat.mark s x.2.1)
  rw [hm]
  refine keeps_putForkN shOf (by rw [← hf]; exact named_some hF) ?_
  have i : FlL.StaysN (do
      let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
        fun col => Fl.need (r.2 col)
      First.Look.planesAddedF g
      pure fs : Fl (Array Aff)) := by
    refine FlL.StaysN.bind inferInstance fun _ => ?_
    refine FlL.StaysN.bind inferInstance fun _ => ?_
    infer_instance
  exact i.same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx)

/-- The run "join". -/
theorem joinRun_keepsN {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hm : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) (n : ℕ) :
    FnCl (KeepsArrNames shOf) (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨g, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨KF, _, h⟩ := K9L.ok_bind h
  obtain ⟨x, hx, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  show KeepsArrNames shOf s (seat.mark s x.2.1)
  rw [hm]
  exact keeps_putForkN shOf (by rw [← hf]; exact named_some hF)
    ((FlL.stays_joinFN g KF).same (a := x.1) (G := x.2.1) (u := x.2.2) (named_some hx))

/-- K3's own sub-protocol at an address, whole. -/
theorem theOwn_wholeN {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole (KeepsArrNames shOf) b := by
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
      have W : Whole (KeepsArrNames shOf) (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact viaW_digitsN shOf claim a.piece laid sent p []
        | false => exact viaW_callsN shOf claim a.piece laid sent p []
      cases runs with
      | true => exact ⟨W.1, W.2.1, W.2.2⟩
      | false => exact ⟨W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- With the step without a round joined behind it. -/
theorem theWhole_wholeN {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole (KeepsArrNames shOf) b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_wholeN shOf claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole (KeepsArrNames shOf) (keeps_transN shOf) _ _ _ W
      ⟨steps_quiet _ _ _ _ f fun s t k => quietAt_keepsN shOf hq k, (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩

/-- **K3's sub-protocol at an address, whole, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_wholeN {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole (KeepsArrNames shOf) b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_wholeN shOf claim true X codes shape a h0
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
          exact planesRun_keepsN shOf _ (fun _ => rfl) (fun _ _ => rfl) _ _ n

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keeps_putForkN
#print axioms VerifiableInference.Desc.LinkJoin.via_decidesN
#print axioms VerifiableInference.Desc.LinkJoin.via_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.viaW_callsN
#print axioms VerifiableInference.Desc.LinkJoin.viaW_digitsN
#print axioms VerifiableInference.Desc.LinkJoin.planesRun_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.joinRun_keepsN
#print axioms VerifiableInference.Desc.LinkJoin.theOwn_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.theWhole_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.theStated_wholeN
