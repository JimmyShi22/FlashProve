-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Pile/ReqMakers.lean: THE RELATION "THE REQUEST'S WORDS STAY, AND NO MARK IS TAKEN
OFF" ON THE VERIFIER'S STATE OF THE REQUEST'S OWN FIAT–SHAMIR HASH CHAIN (`First.S`), AT EVERY MAKER
OF A SUB-PROTOCOL THAT SENDS NOTHING. One definition; statements with their proofs.

Main names (namespace `Meaning.K2`).
  **`ReqStays s s'`**: `s'.req = s.req`, and `s'.failed = none → s.failed = none`. The second clause
    is there for the fold's fact: the chain's start at a request that fails its test is the blank
    state, which bears a mark and no words; since no mark is taken off, a reached state without a
    mark has come from the other start. `req_refl`, `req_trans`, `req_same` (both fields as they
    were).
  THE FIFTY of Johnson/Goal/Meaning/RecK3.lean … RecSeated.lean that name that family's relation
    `Quiet`, EACH BY THE SCRIPT OF ITS LIKE, at `ReqStays`: ported by a program from
    Johnson/Desc/First/Pile/PileMakers.lean (a line in front of each says from which file of the
    family). Names: `req_x`, `x_req`. Tops: `theStated_req` (K3), `blockAtC_req` (K4), `k5AtN_req`
    (K5), `seatedClaims_req` (K6), `k7Of_req` (K7), `k8Whole_req` (K8), `headMerge11_req` (K11).

Limits. A FRAME LAW: what these texts do not write. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.RecSeated
import Johnson.Goal.Meaning.RecK7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart decide_ok freeSlot_same runOf)

/-! ## The relation -/

/-- **The request's words stay, and no mark is taken off.** -/
def ReqStays (s s' : S) : Prop := s'.req = s.req ∧ (s'.failed = none → s.failed = none)

theorem req_refl (s : S) : ReqStays s s := ⟨rfl, fun h => h⟩

theorem req_trans (a b c : S) (h : ReqStays a b) (k : ReqStays b c) : ReqStays a c :=
  ⟨k.1.trans h.1, fun x => h.2 (k.2 x)⟩

/-- Where the words and the mark are as they were. -/
theorem req_same {s s' : S} (hr : s'.req = s.req) (hf : s'.failed = s.failed) : ReqStays s s' :=
  ⟨hr, fun h => hf ▸ h⟩

-- from RecK3.lean
theorem req_mark (s : S) (name : String) : ReqStays s (s.mark name) := by
  unfold S.mark
  split
  · exact req_refl s
  · exact ⟨rfl, fun h => nomatch h⟩

variable {Cl : Type}

/-- A tactic for a writer of State.lean that turns "here" inside one kind of link, or marks. -/
local macro "still" d:ident : tactic =>
  `(tactic| (unfold $d; repeat' split) <;> first
    | exact req_refl _
    | exact req_mark _ _
    | exact req_same rfl rfl)

-- from RecK3.lean
theorem req_putFork (s : S) (F : Fork) : ReqStays s (s.putFork F) := by
  still S.putFork

-- from RecK3.lean
theorem req_putTl (s : S) (tl : HTailF2) : ReqStays s (s.putTl tl) := by
  still S.putTl

-- from RecK3.lean
theorem req_hearLook (s : S) (g : Forest.Heard) : ReqStays s (s.hearLook g) := by
  still S.hearLook

-- from RecK3.lean
theorem seatCalls_put_req (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ReqStays s ((K3.seatCalls claim).put s g G) :=
  req_trans _ _ _ (req_putFork s G) (req_hearLook _ g)

-- from RecK3.lean
theorem seatCalls_mark_req (claim : Aff → Cl) (s : S) (G : Fork) :
    ReqStays s ((K3.seatCalls claim).mark s G) := req_putFork s G

-- from RecK3.lean
theorem seatDigits_put_req (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ReqStays s ((K3.seatDigits claim).put s g G) := by
  show ReqStays s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact req_trans _ _ _ (req_putTl s _) (req_putFork _ G)
  · exact req_mark s _

-- from RecK3.lean
theorem seatDigits_mark_req (claim : Aff → Cl) (s : S) (G : Fork) :
    ReqStays s ((K3.seatDigits claim).mark s G) := req_putFork s G

-- from RecK3.lean
theorem quietLook_req (fs : Forest.Shape) : Fn ReqStays (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact req_refl s

-- from RecK3.lean
theorem quietDigits_req (used claims : Nat) : Fn ReqStays (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact req_putFork s G

-- from RecK3.lean
theorem quietHead_req (X : Verify.Public) : Fn ReqStays (K3.quietHead X) := fun s s' h => by
  unfold K3.quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact req_same rfl rfl
  · cases h

-- from RecK3.lean
theorem quietAt_req (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn ReqStays f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_req X)
    | (cases h; exact quietLook_req _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_req _ _)
    | cases h

-- from RecK3More.lean
theorem withCallerCalls_req (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole ReqStays b) :
    Whole ReqStays (K3.withCaller (K3.seatCalls claim) p readers b) :=
  withCaller_whole ReqStays _ (seatCalls_mark_req claim) p readers W

-- from RecK3More.lean
theorem withCallerDigits_req (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole ReqStays b) :
    Whole ReqStays (K3.withCaller (K3.seatDigits claim) p readers b) :=
  withCaller_whole ReqStays _ (seatDigits_mark_req claim) p readers W

-- from RecK3More.lean
theorem blockViaCalls_req (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole ReqStays (K3.Law.blockVia (K3.seatCalls claim) piece laid before p guests) :=
  blockVia_whole ReqStays req_refl _ (seatCalls_put_req claim) (seatCalls_mark_req claim)
    _ _ _ _ _

-- from RecK3More.lean
theorem blockViaDigits_req (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole ReqStays (K3.Law.blockVia (K3.seatDigits claim) piece laid before p guests) :=
  blockVia_whole ReqStays req_refl _ (seatDigits_put_req claim) (seatDigits_mark_req claim)
    _ _ _ _ _

-- from RecK3More.lean
/-- Every block that lookClaims gives leaves the pile. -/
theorem lookClaims_req (W : Verify.Public) (l : Nat) {b : Block S Claim}
    (h : Kinds.Head.lookClaims W l = some b) : Whole ReqStays b := by
  unfold Kinds.Head.lookClaims at h
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact withCallerCalls_req _ p _ (blockViaCalls_req _ _ _ _ _ _)

-- from RecK3More.lean
/-- **Every block that theOwn gives leaves the pile.** -/
theorem theOwn_req (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole ReqStays b := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      have W : Whole ReqStays (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockViaCalls_req claim _ _ _ _ _
        · exact blockViaDigits_req claim _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

-- from RecK3More.lean
/-- **The block at an address, whole, leaves the pile.** -/
theorem theWhole_req (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole ReqStays b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_req claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole ReqStays req_trans _ _ _ W
      ⟨Keeps.quiet_decides ReqStays _ _ _ _ f (quietAt_req X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

-- from RecK4.lean
/-- Laid back into S, a part with the same link leaves the pile. -/
theorem setPart_req (t : S) (p x : OnBytes.Desc.First.K4.Part) (hp : part? t = some p)
    (e : SameL p x) : ReqStays t (setPart t x) := by
  unfold part? at hp
  split at hp
  · rename_i a ha
    cases hp
    exact req_same rfl rfl
  · cases hp

-- from RecK4.lean
/-- **K4's sub-protocol at the verifier's state leaves the pile.** -/
theorem k4_req (p : OnBytes.Desc.First.K4.Par) : Whole ReqStays (blockAtS p) :=
  whole_of_steps (stepsLiftPart part? setPart _ (k4_steps p) setPart_req)
    (runsLiftPart part? setPart _ (k4_runs p) setPart_req)
    (afterLiftPart part? setPart _ (k4_after p) setPart_req)

-- from RecK5K8.lean
/-- The three runs with "join" laid behind "keys". -/
theorem withJoin_keep_req (seat : Att.P.SeatC S) (c : Att.P.ParC) (keys : S → Option (Array Aff)) :
    ∀ x ∈ (Att.P.runsK seat c).flatMap (fun r =>
        if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)]
        else [r]), ∀ n, FnCl ReqStays (x.2 n) := by
  intro x hx n
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep ReqStays req_refl seat c _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep ReqStays _ (seatCalls_mark_req id) keys n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep ReqStays req_refl seat c _ hr n
    · cases hx

-- from RecK5K8.lean
theorem req_hear5 (s : S) (h : Att.P.Heard) : ReqStays s (s.hear5 h) := by
  unfold S.hear5
  split
  · rename_i a ha
    split
    · exact req_mark s _
    · exact req_same rfl rfl
  · exact req_mark s _

-- from RecK5K8.lean
theorem req_hear5? {s s' : S} {h : Att.P.Heard} (e : (s.hear5? h).toOption = some s') :
    ReqStays s s' := by
  unfold S.hear5? at e
  cases k : (s.hear5 h).unmarked with
  | error _ => rw [k] at e; cases e
  | ok t =>
    rw [k] at e
    cases e
    rw [quiet_unmarked k]
    exact req_hear5 s h

-- from RecK5K8.lean
theorem seatS_lay_req (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatS shape).lay s h G = some s') : ReqStays s s' := by
  simp only [Att.P.seatS] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact req_same rfl rfl
  · cases e

-- from RecK5K8.lean
theorem seatSH_lay_req (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatSH shape).lay s h G = some s') : ReqStays s s' := by
  have e' : ((Att.P.seatS shape).lay s h G).bind (fun t => (t.hear5? h).toOption) = some s' := e
  obtain ⟨t, h1, h2⟩ := Option.bind_eq_some_iff.1 e'
  exact req_trans _ _ _ (seatS_lay_req shape s h G t h1) (req_hear5? h2)

-- from RecK5K8.lean
theorem seatSO_lay_req (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : Att.P.seatSO.lay s h G = some s') : ReqStays s s' := by
  simp only [Att.P.seatSO] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    have q1 : ReqStays s ({ s with rowsOwed := none, here := .att { a with F := G } } : S) := by
      exact req_same rfl rfl
    exact req_trans _ _ _ q1 (req_hear5? e)
  · cases e

-- from RecK5K8.lean
theorem k5At_req {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Cl} (h : Att.P.k5At W l g before = some b) : Whole ReqStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k5_whole ReqStays _ (seatS_lay_req p.S) [] (fun _ hx => nomatch hx) _

-- from RecK5K8.lean
theorem k5AtW_req (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtW W l g before = some b) : Whole ReqStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole ReqStays _ (seatS_lay_req p.S) (Att.P.runsW p)
    (withJoin_keep_req _ _ _) _) rfl (fun _ hx => hx) rfl

-- from RecK5K8.lean
theorem k5AtH_req (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtH W l g before = some b) : Whole ReqStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole ReqStays _ (seatSH_lay_req p.S) (Att.P.runsH p)
    (withJoin_keep_req _ _ _) _) rfl (fun _ hx => hx) rfl

-- from RecK5K8.lean
theorem k5AtO_req (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtO W l g before = some b) : Whole ReqStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole ReqStays _ seatSO_lay_req (Att.P.runsO p)
    (withJoin_keep_req _ _ _) _) rfl (fun _ hx => hx) rfl

-- from RecK5K8.lean
theorem k8_lay_req (s : S) (m : Array Int) (first : Array Nat) (s' : S)
    (e : K8.atS.lay s m first = .ok s') : ReqStays s s' := by
  have e' : (match s.tl? with
    | some tl => Except.ok (s.putTl { tl with cfF := m, cfFirst := first })
    | none => .error "the smallness test: no link is open") = .ok s' := e
  split at e'
  · cases e'
    exact req_putTl s _
  · cases e'

-- from RecK5K8.lean
theorem k8_req {Cl : Type} (p : K8.Par) : Whole ReqStays (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p) :=
  k8_whole ReqStays _ k8_lay_req p

section
open VerifiableInference.Desc.Kinds.Head

-- from RecK6.lean
theorem seatAt_ledger_req (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : ReqStays s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact req_putFork s F
  · cases e'

-- from RecK6.lean
theorem seatAt_heard_req (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : ReqStays s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      exact req_same rfl rfl
    · cases e
  · cases e

-- from RecK6.lean
/-- **The output head's own sub-protocol at the verifier's state leaves the pile.** -/
theorem blockAt_req (h : Model.Head.Shape) (iU3 work l : Nat) :
    Whole ReqStays (Kinds.Head.blockAt h iU3 work l) :=
  k6Join_whole ReqStays req_refl req_trans _ (seatCalls_mark_req _) (seatAt h iU3)
    (seatAt_ledger_req h iU3) (seatAt_heard_req h iU3) (fun s _ => req_refl s)
    (fun s _ => req_refl s)
    l 4 (parOf h work)

-- from RecK6.lean
theorem blockOf_req {W : Verify.Public} {l : Nat} {b : Block S Unit}
    (hb : Kinds.Head.blockOf W l = some b) : Whole ReqStays b := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact blockAt_req _ _ _ _

end

section
open VerifiableInference.Desc.Kinds

-- from RecK7.lean
theorem seatAt_set_req (s : S) (h : E) : ReqStays s (Reply.seatAt.setReply s h) := by
  simp only [Reply.seatAt]
  exact req_same rfl rfl

-- from RecK7.lean
/-- **K7's sub-protocol at the verifier's state leaves the pile** (it writes `out.reply`). -/
theorem k7_req (l V : Nat) : Whole ReqStays (Reply.blockAt l V) :=
  entered_whole (k7_whole ReqStays _ seatAt_set_req l 1 V)

-- from RecK7.lean
theorem k7Of_req (W : Verify.Public) (l : Nat) : Whole ReqStays (Reply.blockOf W l) :=
  k7_req l W.hS.V

end

-- from RecSeated.lean
theorem theStated_req (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole ReqStays b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_req claim true X codes shape a h0
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
        exact withCallerCalls_req claim p _ W

-- from RecSeated.lean
theorem blockAtC_req (p : OnBytes.Desc.First.K4.Par) :
    Whole ReqStays (OnBytes.Desc.First.K4.blockAtC p) := atClaims_whole (k4_req p)

-- from RecSeated.lean
theorem k5AtN_req (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) : Whole ReqStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  have H : ∀ x ∈ Att.P.runsO p, ∀ n, FnCl ReqStays (x.2 n) := withJoin_keep_req _ _ _
  refine whole_same (k5_whole ReqStays _ seatSO_lay_req (Att.P.runsN p)
    (fun c hc n s y e => ?_) _) rfl
    (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := Att.P.runN_ok e
  exact H r hr n s _ e'

-- from RecSeated.lean
theorem kindJoinAt_req (claim : Aff → Cl) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) :
    Whole ReqStays
      (Kinds.Head.kindWithJoin (K3.seatCalls claim) (Kinds.Head.seatAt h iU3) l piece p) :=
  k6Join_whole ReqStays req_refl req_trans _ (seatCalls_mark_req _) (Kinds.Head.seatAt h iU3)
    (seatAt_ledger_req h iU3) (seatAt_heard_req h iU3) (fun s _ => req_refl s)
    (fun s _ => req_refl s)
    l piece p

-- from RecSeated.lean
theorem blockClaims_req {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole ReqStays b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact kindJoinAt_req _ _ _ _ _ _

-- from RecSeated.lean
/-- ONE TEXT FOR TWO FORMS OF A SEAT: in one the seated block's decision IS the block's; in the
other, this library's (Johnson/Stored/HeadSeatAt.lean: tested), it asks a test on the state in
front, and a yes of it is a yes of the block's. (Over either form one of
the two arms of "first" is not reached.) -/
theorem seatedClaims_req {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole ReqStays b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_req h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

-- from RecSeated.lean
theorem k8Set_req (s : S) (q : TailClaims.K8Part) : ReqStays s (TailClaims.k8PartP.set s q) := by
  show ReqStays s ((s.putTl q.tl).putFork q.F)
  exact req_trans _ _ _ (req_putTl s _) (req_putFork _ _)

-- from RecSeated.lean
theorem atRecord_req {α : Type} (f : TailClaims.K8Part → Except String (α × TailClaims.K8Part))
    {s : S} {y : α × S} (h : K8.atRecord f s = .ok y) : ReqStays s y.2 := by
  unfold K8.atRecord at h
  split at h
  · cases h
  · obtain ⟨x, -, rfl⟩ := Keeps.emap_ok h
    exact k8Set_req s _

-- from RecSeated.lean
theorem k8Whole_req (p : K8.ParW) : Whole ReqStays (K8.whole p) := by
  refine ⟨(k8_req (Cl := Claim) p.toPar).1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact atRecord_req _ h
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y, e, rfl⟩ := Keeps.emap_ok h
    exact atRecord_req _ e

-- from RecSeated.lean
open Johnson.Desc.First.ForkMerge in
theorem headMerge11_req (P : HeadMergeP) : Whole ReqStays (headClaimMergeKind P) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · have h' : headMergeDecide P s rs = .ok s' := h
    unfold headMergeDecide at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨⟨wo, F, t⟩, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      cases h'
      exact req_same rfl rfl
    · cases h'
  · obtain rfl := List.mem_singleton.1 hc
    have h' : headMergeClaim n s = .ok y := h
    unfold headMergeClaim at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨x, -, h'⟩ := bindE h'
      cases h'
      exact req_same rfl rfl
    · cases h'

#print axioms req_refl
#print axioms req_trans
#print axioms req_same
#print axioms req_mark
#print axioms req_putFork
#print axioms req_putTl
#print axioms req_hearLook
#print axioms seatCalls_put_req
#print axioms seatCalls_mark_req
#print axioms seatDigits_put_req
#print axioms seatDigits_mark_req
#print axioms quietLook_req
#print axioms quietDigits_req
#print axioms quietHead_req
#print axioms quietAt_req
#print axioms withCallerCalls_req
#print axioms withCallerDigits_req
#print axioms blockViaCalls_req
#print axioms blockViaDigits_req
#print axioms lookClaims_req
#print axioms theOwn_req
#print axioms theWhole_req
#print axioms setPart_req
#print axioms k4_req
#print axioms withJoin_keep_req
#print axioms req_hear5
#print axioms req_hear5?
#print axioms seatS_lay_req
#print axioms seatSH_lay_req
#print axioms seatSO_lay_req
#print axioms k5At_req
#print axioms k5AtW_req
#print axioms k5AtH_req
#print axioms k5AtO_req
#print axioms k8_lay_req
#print axioms k8_req
#print axioms seatAt_ledger_req
#print axioms seatAt_heard_req
#print axioms blockAt_req
#print axioms blockOf_req
#print axioms seatAt_set_req
#print axioms k7_req
#print axioms k7Of_req
#print axioms theStated_req
#print axioms blockAtC_req
#print axioms k5AtN_req
#print axioms kindJoinAt_req
#print axioms blockClaims_req
#print axioms seatedClaims_req
#print axioms k8Set_req
#print axioms atRecord_req
#print axioms k8Whole_req
#print axioms headMerge11_req

end Meaning.K2
