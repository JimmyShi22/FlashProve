-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Pile/PileMakers.lean: THE RELATION "THE PILE STAYS" ON THE VERIFIER'S STATE OF
THE REQUEST'S OWN FIAT–SHAMIR HASH CHAIN (`First.S`), AND THAT EVERY MAKER OF A SUB-PROTOCOL THAT
SENDS NOTHING KEEPS IT. One definition; statements with their proofs.

Why. Several facts that are wanted at every state which the verifier's fold can reach read just two
things of the state: the rows on the table (`First.S.rows`: the pile of pending rows; behind kind
K13's batching the one row) and the number of the index masks' message (`out.indexMasks`). One
induction along the fold on "who writes these" serves them all. This file is its first third.

Main names (namespace `Meaning.K2`, beside the family that they follow).
  **`PileStays s s'`**: `s'.rows = s.rows`, `s'.out.indexMasks = s.out.indexMasks`, and s' stands at
    the chain's end (`here = .mem _`) only if s did. NOT "`out` whole stays": kind K7 writes
    `out.reply`. `pile_refl`, `pile_trans`; `pile_here` ("here" and the two fields of `out` are as
    they were), `pile_of` (neither state stands at the chain's end), `rows_of_not_mem`.
  THE FIFTY: the theorems of Johnson/Goal/Meaning/RecK3.lean, RecK3More.lean, RecK4.lean,
    RecK5K8.lean, RecK6.lean, RecK7.lean, RecSeated.lean whose text names that family's relation
    `Quiet`, EACH BY THE SCRIPT OF ITS LIKE, at `PileStays`: ported by a program (a line in front of
    each says from which file); the family's lemmas that are general in the relation
    (`k3_block_whole`, `blockVia_whole`, `k5_whole`, `k6Join_whole`, `k7_whole`, `k8_whole`, …) are
    called as they lie. Names: `quiet_x` is `pile_x`; `x_quiet` is `x_pile`; any other name bears
    `_pile` behind it.
  The tops, one for each maker of the seat: **`theStated_pile`** (K3), **`blockAtC_pile`** (K4),
    **`k5AtN_pile`** (K5), **`seatedClaims_pile`** (K6), **`k7Of_pile`** (K7), **`k8Whole_pile`**
    (K8), **`headMerge11_pile`** (K11).

Every "there is": in `PileStays`' third clause alone: the state's own "here".
Limits. A FRAME LAW: it says what these texts do not write, not that accepting means a test: a
sub-protocol that rejects all meets it. Which maker stands at which place: not here. Nothing on
soundness or on hiding.
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

/-- **The pile stays**: the rows on the table and the index masks' message's number are as they
were, and the state behind stands at the chain's end only if the state in front did. -/
def PileStays (s s' : S) : Prop :=
  s'.rows = s.rows ∧ s'.out.indexMasks = s.out.indexMasks ∧
    ((∃ a, s'.here = .mem a) → ∃ a, s.here = .mem a)

theorem pile_refl (s : S) : PileStays s s := ⟨rfl, rfl, fun h => h⟩

theorem pile_trans (a b c : S) (h : PileStays a b) (k : PileStays b c) : PileStays a c :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, fun x => h.2.2 (k.2.2 x)⟩

/-- Where "here" is as it was, and of `out` the pile and the index masks' number. -/
theorem pile_here {s s' : S} (hh : s'.here = s.here) (hp : s'.out.pending = s.out.pending)
    (hi : s'.out.indexMasks = s.out.indexMasks) : PileStays s s' := by
  refine ⟨?_, hi, fun ⟨a, ha⟩ => ⟨a, hh ▸ ha⟩⟩
  unfold S.rows
  rw [hh, hp]

/-- In front of the chain's end the rows on the table are the pile. -/
theorem rows_of_not_mem {s : S} (h : ∀ a, s.here ≠ .mem a) : s.rows = s.out.pending := by
  unfold S.rows
  split
  · rename_i a ha
    exact absurd ha (h a)
  · rfl

/-- Where neither state stands at the chain's end, and of `out` these two are as they were. -/
theorem pile_of {s s' : S} (hp : s'.out.pending = s.out.pending)
    (hi : s'.out.indexMasks = s.out.indexMasks) (h1 : ∀ a, s.here ≠ .mem a)
    (h2 : ∀ a, s'.here ≠ .mem a) : PileStays s s' :=
  ⟨by rw [rows_of_not_mem h1, rows_of_not_mem h2, hp], hi, fun ⟨a, ha⟩ => absurd ha (h2 a)⟩

-- from RecK3.lean
theorem pile_mark (s : S) (name : String) : PileStays s (s.mark name) := by
  unfold S.mark
  split
  · exact pile_refl s
  · exact pile_here rfl rfl rfl

variable {Cl : Type}

/-- A tactic for a writer of State.lean that turns "here" inside one kind of link, or marks. -/
local macro "still" d:ident : tactic =>
  `(tactic| (unfold $d; repeat' split) <;> first
    | exact pile_refl _
    | exact pile_mark _ _
    | exact pile_of rfl rfl (by simp_all) (by simp))

-- from RecK3.lean
theorem pile_putFork (s : S) (F : Fork) : PileStays s (s.putFork F) := by
  still S.putFork

-- from RecK3.lean
theorem pile_putTl (s : S) (tl : HTailF2) : PileStays s (s.putTl tl) := by
  still S.putTl

-- from RecK3.lean
theorem pile_hearLook (s : S) (g : Forest.Heard) : PileStays s (s.hearLook g) := by
  still S.hearLook

-- from RecK3.lean
theorem seatCalls_put_pile (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    PileStays s ((K3.seatCalls claim).put s g G) :=
  pile_trans _ _ _ (pile_putFork s G) (pile_hearLook _ g)

-- from RecK3.lean
theorem seatCalls_mark_pile (claim : Aff → Cl) (s : S) (G : Fork) :
    PileStays s ((K3.seatCalls claim).mark s G) := pile_putFork s G

-- from RecK3.lean
theorem seatDigits_put_pile (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    PileStays s ((K3.seatDigits claim).put s g G) := by
  show PileStays s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact pile_trans _ _ _ (pile_putTl s _) (pile_putFork _ G)
  · exact pile_mark s _

-- from RecK3.lean
theorem seatDigits_mark_pile (claim : Aff → Cl) (s : S) (G : Fork) :
    PileStays s ((K3.seatDigits claim).mark s G) := pile_putFork s G

-- from RecK3.lean
theorem quietLook_pile (fs : Forest.Shape) : Fn PileStays (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact pile_refl s

-- from RecK3.lean
theorem quietDigits_pile (used claims : Nat) : Fn PileStays (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact pile_putFork s G

-- from RecK3.lean
theorem quietHead_pile (X : Verify.Public) : Fn PileStays (K3.quietHead X) := fun s s' h => by
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
    exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
  · cases h

-- from RecK3.lean
theorem quietAt_pile (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn PileStays f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_pile X)
    | (cases h; exact quietLook_pile _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_pile _ _)
    | cases h

-- from RecK3More.lean
theorem withCallerCalls_pile (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole PileStays b) :
    Whole PileStays (K3.withCaller (K3.seatCalls claim) p readers b) :=
  withCaller_whole PileStays _ (seatCalls_mark_pile claim) p readers W

-- from RecK3More.lean
theorem withCallerDigits_pile (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole PileStays b) :
    Whole PileStays (K3.withCaller (K3.seatDigits claim) p readers b) :=
  withCaller_whole PileStays _ (seatDigits_mark_pile claim) p readers W

-- from RecK3More.lean
theorem blockViaCalls_pile (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole PileStays (K3.Law.blockVia (K3.seatCalls claim) piece laid before p guests) :=
  blockVia_whole PileStays pile_refl _ (seatCalls_put_pile claim) (seatCalls_mark_pile claim)
    _ _ _ _ _

-- from RecK3More.lean
theorem blockViaDigits_pile (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole PileStays (K3.Law.blockVia (K3.seatDigits claim) piece laid before p guests) :=
  blockVia_whole PileStays pile_refl _ (seatDigits_put_pile claim) (seatDigits_mark_pile claim)
    _ _ _ _ _

-- from RecK3More.lean
/-- Every block that lookClaims gives leaves the pile. -/
theorem lookClaims_pile (W : Verify.Public) (l : Nat) {b : Block S Claim}
    (h : Kinds.Head.lookClaims W l = some b) : Whole PileStays b := by
  unfold Kinds.Head.lookClaims at h
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact withCallerCalls_pile _ p _ (blockViaCalls_pile _ _ _ _ _ _)

-- from RecK3More.lean
/-- **Every block that theOwn gives leaves the pile.** -/
theorem theOwn_pile (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole PileStays b := by
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
      have W : Whole PileStays (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockViaCalls_pile claim _ _ _ _ _
        · exact blockViaDigits_pile claim _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

-- from RecK3More.lean
/-- **The block at an address, whole, leaves the pile.** -/
theorem theWhole_pile (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole PileStays b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_pile claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole PileStays pile_trans _ _ _ W
      ⟨Keeps.quiet_decides PileStays _ _ _ _ f (quietAt_pile X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

-- from RecK4.lean
/-- Laid back into S, a part with the same link leaves the pile. -/
theorem setPart_pile (t : S) (p x : OnBytes.Desc.First.K4.Part) (hp : part? t = some p)
    (e : SameL p x) : PileStays t (setPart t x) := by
  unfold part? at hp
  split at hp
  · rename_i a ha
    cases hp
    exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
  · cases hp

-- from RecK4.lean
/-- **K4's sub-protocol at the verifier's state leaves the pile.** -/
theorem k4_pile (p : OnBytes.Desc.First.K4.Par) : Whole PileStays (blockAtS p) :=
  whole_of_steps (stepsLiftPart part? setPart _ (k4_steps p) setPart_pile)
    (runsLiftPart part? setPart _ (k4_runs p) setPart_pile)
    (afterLiftPart part? setPart _ (k4_after p) setPart_pile)

-- from RecK5K8.lean
/-- The three runs with "join" laid behind "keys". -/
theorem withJoin_keep_pile (seat : Att.P.SeatC S) (c : Att.P.ParC) (keys : S → Option (Array Aff)) :
    ∀ x ∈ (Att.P.runsK seat c).flatMap (fun r =>
        if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)]
        else [r]), ∀ n, FnCl PileStays (x.2 n) := by
  intro x hx n
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep PileStays pile_refl seat c _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep PileStays _ (seatCalls_mark_pile id) keys n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep PileStays pile_refl seat c _ hr n
    · cases hx

-- from RecK5K8.lean
theorem pile_hear5 (s : S) (h : Att.P.Heard) : PileStays s (s.hear5 h) := by
  unfold S.hear5
  split
  · rename_i a ha
    split
    · exact pile_mark s _
    · exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
  · exact pile_mark s _

-- from RecK5K8.lean
theorem pile_hear5? {s s' : S} {h : Att.P.Heard} (e : (s.hear5? h).toOption = some s') :
    PileStays s s' := by
  unfold S.hear5? at e
  cases k : (s.hear5 h).unmarked with
  | error _ => rw [k] at e; cases e
  | ok t =>
    rw [k] at e
    cases e
    rw [quiet_unmarked k]
    exact pile_hear5 s h

-- from RecK5K8.lean
theorem seatS_lay_pile (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatS shape).lay s h G = some s') : PileStays s s' := by
  simp only [Att.P.seatS] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
  · cases e

-- from RecK5K8.lean
theorem seatSH_lay_pile (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatSH shape).lay s h G = some s') : PileStays s s' := by
  have e' : ((Att.P.seatS shape).lay s h G).bind (fun t => (t.hear5? h).toOption) = some s' := e
  obtain ⟨t, h1, h2⟩ := Option.bind_eq_some_iff.1 e'
  exact pile_trans _ _ _ (seatS_lay_pile shape s h G t h1) (pile_hear5? h2)

-- from RecK5K8.lean
theorem seatSO_lay_pile (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : Att.P.seatSO.lay s h G = some s') : PileStays s s' := by
  simp only [Att.P.seatSO] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    have q1 : PileStays s ({ s with rowsOwed := none, here := .att { a with F := G } } : S) := by
      exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
    exact pile_trans _ _ _ q1 (pile_hear5? e)
  · cases e

-- from RecK5K8.lean
theorem k5At_pile {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Cl} (h : Att.P.k5At W l g before = some b) : Whole PileStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k5_whole PileStays _ (seatS_lay_pile p.S) [] (fun _ hx => nomatch hx) _

-- from RecK5K8.lean
theorem k5AtW_pile (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtW W l g before = some b) : Whole PileStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole PileStays _ (seatS_lay_pile p.S) (Att.P.runsW p)
    (withJoin_keep_pile _ _ _) _) rfl (fun _ hx => hx) rfl

-- from RecK5K8.lean
theorem k5AtH_pile (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtH W l g before = some b) : Whole PileStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole PileStays _ (seatSH_lay_pile p.S) (Att.P.runsH p)
    (withJoin_keep_pile _ _ _) _) rfl (fun _ hx => hx) rfl

-- from RecK5K8.lean
theorem k5AtO_pile (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtO W l g before = some b) : Whole PileStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole PileStays _ seatSO_lay_pile (Att.P.runsO p)
    (withJoin_keep_pile _ _ _) _) rfl (fun _ hx => hx) rfl

-- from RecK5K8.lean
theorem k8_lay_pile (s : S) (m : Array Int) (first : Array Nat) (s' : S)
    (e : K8.atS.lay s m first = .ok s') : PileStays s s' := by
  have e' : (match s.tl? with
    | some tl => Except.ok (s.putTl { tl with cfF := m, cfFirst := first })
    | none => .error "the smallness test: no link is open") = .ok s' := e
  split at e'
  · cases e'
    exact pile_putTl s _
  · cases e'

-- from RecK5K8.lean
theorem k8_pile {Cl : Type} (p : K8.Par) : Whole PileStays (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p) :=
  k8_whole PileStays _ k8_lay_pile p

section
open VerifiableInference.Desc.Kinds.Head

-- from RecK6.lean
theorem seatAt_ledger_pile (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : PileStays s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact pile_putFork s F
  · cases e'

-- from RecK6.lean
theorem seatAt_heard_pile (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : PileStays s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      exact pile_of rfl rfl (by rw [ho]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
    · cases e
  · cases e

-- from RecK6.lean
/-- **The output head's own sub-protocol at the verifier's state leaves the pile.** -/
theorem blockAt_pile (h : Model.Head.Shape) (iU3 work l : Nat) :
    Whole PileStays (Kinds.Head.blockAt h iU3 work l) :=
  k6Join_whole PileStays pile_refl pile_trans _ (seatCalls_mark_pile _) (seatAt h iU3)
    (seatAt_ledger_pile h iU3) (seatAt_heard_pile h iU3) (fun s _ => pile_refl s)
    (fun s _ => pile_refl s)
    l 4 (parOf h work)

-- from RecK6.lean
theorem blockOf_pile {W : Verify.Public} {l : Nat} {b : Block S Unit}
    (hb : Kinds.Head.blockOf W l = some b) : Whole PileStays b := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact blockAt_pile _ _ _ _

end

section
open VerifiableInference.Desc.Kinds

-- from RecK7.lean
theorem seatAt_set_pile (s : S) (h : E) : PileStays s (Reply.seatAt.setReply s h) := by
  simp only [Reply.seatAt]
  exact pile_here rfl rfl rfl

-- from RecK7.lean
/-- **K7's sub-protocol at the verifier's state leaves the pile** (it writes `out.reply`). -/
theorem k7_pile (l V : Nat) : Whole PileStays (Reply.blockAt l V) :=
  entered_whole (k7_whole PileStays _ seatAt_set_pile l 1 V)

-- from RecK7.lean
theorem k7Of_pile (W : Verify.Public) (l : Nat) : Whole PileStays (Reply.blockOf W l) :=
  k7_pile l W.hS.V

end

-- from RecSeated.lean
theorem theStated_pile (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole PileStays b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_pile claim true X codes shape a h0
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
        exact withCallerCalls_pile claim p _ W

-- from RecSeated.lean
theorem blockAtC_pile (p : OnBytes.Desc.First.K4.Par) :
    Whole PileStays (OnBytes.Desc.First.K4.blockAtC p) := atClaims_whole (k4_pile p)

-- from RecSeated.lean
theorem k5AtN_pile (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) : Whole PileStays b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  have H : ∀ x ∈ Att.P.runsO p, ∀ n, FnCl PileStays (x.2 n) := withJoin_keep_pile _ _ _
  refine whole_same (k5_whole PileStays _ seatSO_lay_pile (Att.P.runsN p)
    (fun c hc n s y e => ?_) _) rfl
    (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := Att.P.runN_ok e
  exact H r hr n s _ e'

-- from RecSeated.lean
theorem kindJoinAt_pile (claim : Aff → Cl) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) :
    Whole PileStays
      (Kinds.Head.kindWithJoin (K3.seatCalls claim) (Kinds.Head.seatAt h iU3) l piece p) :=
  k6Join_whole PileStays pile_refl pile_trans _ (seatCalls_mark_pile _) (Kinds.Head.seatAt h iU3)
    (seatAt_ledger_pile h iU3) (seatAt_heard_pile h iU3) (fun s _ => pile_refl s)
    (fun s _ => pile_refl s)
    l piece p

-- from RecSeated.lean
theorem blockClaims_pile {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole PileStays b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact kindJoinAt_pile _ _ _ _ _ _

-- from RecSeated.lean
/-- ONE TEXT FOR TWO FORMS OF A SEAT: in one the seated block's decision IS the block's; in the
other, this library's (Johnson/Stored/HeadSeatAt.lean: tested), it asks a test on the state in
front, and a yes of it is a yes of the block's. (Over either form one of
the two arms of "first" is not reached.) -/
theorem seatedClaims_pile {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole PileStays b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_pile h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

-- from RecSeated.lean
theorem k8Set_pile (s : S) (q : TailClaims.K8Part) : PileStays s (TailClaims.k8PartP.set s q) := by
  show PileStays s ((s.putTl q.tl).putFork q.F)
  exact pile_trans _ _ _ (pile_putTl s _) (pile_putFork _ _)

-- from RecSeated.lean
theorem atRecord_pile {α : Type} (f : TailClaims.K8Part → Except String (α × TailClaims.K8Part))
    {s : S} {y : α × S} (h : K8.atRecord f s = .ok y) : PileStays s y.2 := by
  unfold K8.atRecord at h
  split at h
  · cases h
  · obtain ⟨x, -, rfl⟩ := Keeps.emap_ok h
    exact k8Set_pile s _

-- from RecSeated.lean
theorem k8Whole_pile (p : K8.ParW) : Whole PileStays (K8.whole p) := by
  refine ⟨(k8_pile (Cl := Claim) p.toPar).1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact atRecord_pile _ h
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y, e, rfl⟩ := Keeps.emap_ok h
    exact atRecord_pile _ e

-- from RecSeated.lean
open Johnson.Desc.First.ForkMerge in
theorem headMerge11_pile (P : HeadMergeP) : Whole PileStays (headClaimMergeKind P) := by
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
      exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
    · cases h'
  · obtain rfl := List.mem_singleton.1 hc
    have h' : headMergeClaim n s = .ok y := h
    unfold headMergeClaim at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨x, -, h'⟩ := bindE h'
      cases h'
      exact pile_of rfl rfl (by rw [ha]; exact fun _ h => nomatch h) (fun _ h => nomatch h)
    · cases h'

#print axioms pile_refl
#print axioms pile_trans
#print axioms pile_here
#print axioms rows_of_not_mem
#print axioms pile_of
#print axioms pile_mark
#print axioms pile_putFork
#print axioms pile_putTl
#print axioms pile_hearLook
#print axioms seatCalls_put_pile
#print axioms seatCalls_mark_pile
#print axioms seatDigits_put_pile
#print axioms seatDigits_mark_pile
#print axioms quietLook_pile
#print axioms quietDigits_pile
#print axioms quietHead_pile
#print axioms quietAt_pile
#print axioms withCallerCalls_pile
#print axioms withCallerDigits_pile
#print axioms blockViaCalls_pile
#print axioms blockViaDigits_pile
#print axioms lookClaims_pile
#print axioms theOwn_pile
#print axioms theWhole_pile
#print axioms setPart_pile
#print axioms k4_pile
#print axioms withJoin_keep_pile
#print axioms pile_hear5
#print axioms pile_hear5?
#print axioms seatS_lay_pile
#print axioms seatSH_lay_pile
#print axioms seatSO_lay_pile
#print axioms k5At_pile
#print axioms k5AtW_pile
#print axioms k5AtH_pile
#print axioms k5AtO_pile
#print axioms k8_lay_pile
#print axioms k8_pile
#print axioms seatAt_ledger_pile
#print axioms seatAt_heard_pile
#print axioms blockAt_pile
#print axioms blockOf_pile
#print axioms seatAt_set_pile
#print axioms k7_pile
#print axioms k7Of_pile
#print axioms theStated_pile
#print axioms blockAtC_pile
#print axioms k5AtN_pile
#print axioms kindJoinAt_pile
#print axioms blockClaims_pile
#print axioms seatedClaims_pile
#print axioms k8Set_pile
#print axioms atRecord_pile
#print axioms k8Whole_pile
#print axioms headMerge11_pile

end Meaning.K2
