--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/LinkSeated.lean: THE SIX KINDS OF SUB-PROTOCOL THAT SEND NOTHING INSIDE A LINK
(K3, K4, K5, K6, K8, K11) LEAVE THE OPEN LINK's CONTEXT AS IT WAS, WHOLE (S.link?: the state of the
calls, the link's number, its arrays' names, the sub-proof's list of arrays, the count of moments
and the two marks "handed" and "done"). A third relation, beside Quiet
(Johnson/Goal/Meaning/RecQuiet.lean) and Outer (Johnson/Goal/Meaning/OuterSeated.lean). Theorems,
proved.

WHY. A public test that reads the link context stays true across a sub-protocol that leaves it.
Quiet holds four of its seven fields.

  SameLink s s'   s'.link? = s.link?. lk_refl, lk_trans.
  lk_mark, lk_putFork, lk_putTl, lk_hearLook, lk_hear5   the state's own writers that these kinds
    call.
  theStated_lk (K3), blockAtC_lk (K4), k5AtN_lk (K5), seatedClaims_lk (K6), k8Whole_lk (K8),
    headMerge11_lk (K11)   THE SIX MAKERS AS THEY ARE SEATED: Whole SameLink: the decision, the runs
    of claims and the runs behind the batching.

HOW. As at OuterSeated.lean: the walk of RecK3.lean, RecK3More.lean, RecK4.lean, RecK5K8.lean,
RecK6.lean and RecSeated.lean, theorem by theorem, at SameLink in Quiet's place; the rules that are
general in the relation are CALLED.

OBJECT: the landed makers' sub-protocols that are named above. USER:
Johnson/Goal/Meaning/QuietRide.lean. LETTERS: as at the theorems on Quiet.

What is not claimed. Anything on the ledger or on the approximate range proof's parameters: K3 and
K8 write both. Anything on another kind. No soundness.
-/
import Johnson.Goal.Meaning.RecSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Lnk

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart decide_ok freeSlot_same runOf)
open Meaning.K2

/-- **The open link's context is as it was, whole**; and where no link is open none is. -/
def SameLink (s s' : S) : Prop := s'.link? = s.link?

theorem lk_refl (s : S) : SameLink s s := rfl

theorem lk_trans (a b c : S) (h : SameLink a b) (k : SameLink b c) : SameLink a c := Eq.trans k h

variable {T Cl : Type}

/-! ## Out of RecK3.lean -/

theorem lk_mark (s : S) (name : String) : SameLink s (s.mark name) := by
  unfold S.mark
  split
  · exact lk_refl s
  · rfl

theorem lk_putFork (s : S) (F : Fork) : SameLink s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals simp [SameLink, S.link?, *]

theorem lk_putTl (s : S) (tl : HTailF2) : SameLink s (s.putTl tl) := by
  unfold S.putTl
  repeat' split
  all_goals simp [SameLink, S.link?, *]

theorem lk_hearLook (s : S) (g : Forest.Heard) : SameLink s (s.hearLook g) := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact lk_mark s _
    · simp [SameLink, S.link?, *]
  · rename_i a ha
    split
    · exact lk_mark s _
    · simp [SameLink, S.link?, *]
  · rename_i a ha
    split
    · exact lk_mark s _
    · split
      · exact lk_mark s _
      · simp [SameLink, S.link?, *]
  · exact lk_mark s _

theorem seatCalls_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    SameLink s ((K3.seatCalls claim).put s g G) :=
  lk_trans _ _ _ (lk_putFork s G) (lk_hearLook _ g)

theorem seatCalls_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    SameLink s ((K3.seatCalls claim).mark s G) := lk_putFork s G

theorem seatDigits_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    SameLink s ((K3.seatDigits claim).put s g G) := by
  show SameLink s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact lk_trans _ _ _ (lk_putTl s _) (lk_putFork _ G)
  · exact lk_mark s _

theorem seatDigits_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    SameLink s ((K3.seatDigits claim).mark s G) := lk_putFork s G

theorem quietLook_lk (fs : Forest.Shape) : Fn SameLink (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact lk_refl s

theorem quietDigits_lk (used claims : Nat) : Fn SameLink (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact lk_putFork s G

theorem quietHead_lk (X : Verify.Public) : Fn SameLink (K3.quietHead X) := fun s s' h => by
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
    simp [SameLink, S.link?, *]
  · cases h

theorem quietAt_lk (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn SameLink f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_lk X)
    | (cases h; exact quietLook_lk _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_lk _ _)
    | cases h

/-! ## Out of RecK3More.lean -/

theorem withCallerCalls_lk (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole SameLink b) :
    Whole SameLink (K3.withCaller (K3.seatCalls claim) p readers b) :=
  withCaller_whole SameLink _ (seatCalls_mark claim) p readers W

theorem withCallerDigits_lk (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole SameLink b) :
    Whole SameLink (K3.withCaller (K3.seatDigits claim) p readers b) :=
  withCaller_whole SameLink _ (seatDigits_mark claim) p readers W

theorem blockViaCalls_lk (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole SameLink (K3.Law.blockVia (K3.seatCalls claim) piece laid before p guests) :=
  blockVia_whole SameLink lk_refl _ (seatCalls_put claim) (seatCalls_mark claim) _ _ _ _ _

theorem blockViaDigits_lk (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole SameLink (K3.Law.blockVia (K3.seatDigits claim) piece laid before p guests) :=
  blockVia_whole SameLink lk_refl _ (seatDigits_put claim) (seatDigits_mark claim) _ _ _ _ _

/-- Every block that lookClaims gives is SameLink. -/
theorem lookClaims_lk (W : Verify.Public) (l : Nat) {b : Block S Claim}
    (h : Kinds.Head.lookClaims W l = some b) : Whole SameLink b := by
  unfold Kinds.Head.lookClaims at h
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact withCallerCalls_lk _ p _ (blockViaCalls_lk _ _ _ _ _ _)

/-- **Every block that theOwn gives is SameLink.** -/
theorem theOwn_lk (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole SameLink b := by
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
      have W : Whole SameLink (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockViaCalls_lk claim _ _ _ _ _
        · exact blockViaDigits_lk claim _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

/-- **The block at an address, whole, is SameLink.** -/
theorem theWhole_lk (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole SameLink b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_lk claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole SameLink lk_trans _ _ _ W
      ⟨Keeps.quiet_decides SameLink _ _ _ _ f (quietAt_lk X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

/-! ## Out of RecK4.lean -/

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- Laid back into S, a part with the same link gives a state with the same link context. ONE TEXT
FOR SameL (RecK4.lean): the equation on the link is its first clause.
(The two linters are off here alone: one of
the two arms of "first" is not reached.) -/
theorem setPart_lk (t : S) (p x : OnBytes.Desc.First.K4.Part) (hp : part? t = some p)
    (e : SameL p x) : SameLink t (setPart t x) := by
  unfold part? at hp
  split at hp
  · rename_i a ha
    cases hp
    have e' : x.1.L = a.L := by
      first
        | exact e.1
        | exact e
    simp [SameLink, S.link?, setPart, ha, e']
  · cases hp

/-- **K4's block at the state is SameLink.** -/
theorem k4_lk (p : OnBytes.Desc.First.K4.Par) : Whole SameLink (blockAtS p) :=
  whole_of_steps (stepsLiftPart part? setPart _ (k4_steps p) setPart_lk)
    (runsLiftPart part? setPart _ (k4_runs p) setPart_lk)
    (afterLiftPart part? setPart _ (k4_after p) setPart_lk)

/-! ## Out of RecK5K8.lean -/

/-- The three runs with "join" laid behind "keys". -/
theorem withJoin_keep (seat : Att.P.SeatC S) (c : Att.P.ParC) (keys : S → Option (Array Aff)) :
    ∀ x ∈ (Att.P.runsK seat c).flatMap (fun r =>
        if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)]
        else [r]), ∀ n, FnCl SameLink (x.2 n) := by
  intro x hx n
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep SameLink lk_refl seat c _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep SameLink _ (seatCalls_mark id) keys n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep SameLink lk_refl seat c _ hr n
    · cases hx

theorem lk_hear5 (s : S) (h : Att.P.Heard) : SameLink s (s.hear5 h) := by
  unfold S.hear5
  split
  · rename_i a ha
    split
    · exact lk_mark s _
    · simp [SameLink, S.link?, *]
  · exact lk_mark s _

theorem lk_hear5? {s s' : S} {h : Att.P.Heard} (e : (s.hear5? h).toOption = some s') :
    SameLink s s' := by
  unfold S.hear5? at e
  cases k : (s.hear5 h).unmarked with
  | error _ => rw [k] at e; cases e
  | ok t =>
    rw [k] at e
    cases e
    rw [quiet_unmarked k]
    exact lk_hear5 s h

theorem seatS_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatS shape).lay s h G = some s') : SameLink s s' := by
  simp only [Att.P.seatS] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 e
    simp [SameLink, S.link?, *]
  · cases e

theorem seatSH_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatSH shape).lay s h G = some s') : SameLink s s' := by
  have e' : ((Att.P.seatS shape).lay s h G).bind (fun t => (t.hear5? h).toOption) = some s' := e
  obtain ⟨t, h1, h2⟩ := Option.bind_eq_some_iff.1 e'
  exact lk_trans _ _ _ (seatS_lay shape s h G t h1) (lk_hear5? h2)

theorem seatSO_lay (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : Att.P.seatSO.lay s h G = some s') : SameLink s s' := by
  simp only [Att.P.seatSO] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    have q1 : SameLink s ({ s with rowsOwed := none, here := .att { a with F := G } } : S) := by
      simp [SameLink, S.link?, *]
    exact lk_trans _ _ _ q1 (lk_hear5? e)
  · cases e

theorem k5At_lk {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Cl} (h : Att.P.k5At W l g before = some b) : Whole SameLink b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k5_whole SameLink _ (seatS_lay p.S) [] (fun _ hx => nomatch hx) _

theorem k5AtW_lk (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtW W l g before = some b) : Whole SameLink b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole SameLink _ (seatS_lay p.S) (Att.P.runsW p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtH_lk (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtH W l g before = some b) : Whole SameLink b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole SameLink _ (seatSH_lay p.S) (Att.P.runsH p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtO_lk (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtO W l g before = some b) : Whole SameLink b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole SameLink _ seatSO_lay (Att.P.runsO p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k8_lay (s : S) (m : Array Int) (first : Array Nat) (s' : S)
    (e : K8.atS.lay s m first = .ok s') : SameLink s s' := by
  have e' : (match s.tl? with
    | some tl => Except.ok (s.putTl { tl with cfF := m, cfFirst := first })
    | none => .error "the smallness test: no link is open") = .ok s' := e
  split at e'
  · cases e'
    exact lk_putTl s _
  · cases e'

theorem k8_lk {Cl : Type} (p : K8.Par) : Whole SameLink (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p) :=
  k8_whole SameLink _ k8_lay p

/-! ## Out of RecK6.lean -/

section K6
open VerifiableInference.Desc.Kinds.Head

theorem seatAt_ledger (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : SameLink s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact lk_putFork s F
  · cases e'

theorem seatAt_heard (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : SameLink s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      simp [SameLink, S.link?, *]
    · cases e
  · cases e

/-- **The output head's own block at the state is SameLink.** -/
theorem blockAt_lk (h : Model.Head.Shape) (iU3 work l : Nat) :
    Whole SameLink (Kinds.Head.blockAt h iU3 work l) :=
  k6Join_whole SameLink lk_refl lk_trans _ (seatCalls_mark _) (seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => lk_refl s) (fun s _ => lk_refl s)
    l 4 (parOf h work)

theorem blockOf_lk {W : Verify.Public} {l : Nat} {b : Block S Unit}
    (hb : Kinds.Head.blockOf W l = some b) : Whole SameLink b := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact blockAt_lk _ _ _ _

end K6

/-! ## Out of RecSeated.lean -/

theorem theStated_lk (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole SameLink b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_lk claim true X codes shape a h0
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
        exact withCallerCalls_lk claim p _ W

theorem blockAtC_lk (p : OnBytes.Desc.First.K4.Par) :
    Whole SameLink (OnBytes.Desc.First.K4.blockAtC p) := atClaims_whole (k4_lk p)

theorem k5AtN_lk (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) : Whole SameLink b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  have H : ∀ x ∈ Att.P.runsO p, ∀ n, FnCl SameLink (x.2 n) := withJoin_keep _ _ _
  refine whole_same (k5_whole SameLink _ seatSO_lay (Att.P.runsN p) (fun c hc n s y e => ?_) _) rfl
    (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := Att.P.runN_ok e
  exact H r hr n s _ e'

theorem kindJoinAt_lk (claim : Aff → Cl) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) :
    Whole SameLink
      (Kinds.Head.kindWithJoin (K3.seatCalls claim) (Kinds.Head.seatAt h iU3) l piece p) :=
  k6Join_whole SameLink lk_refl lk_trans _ (seatCalls_mark _) (Kinds.Head.seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => lk_refl s) (fun s _ => lk_refl s)
    l piece p

theorem blockClaims_lk {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole SameLink b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact kindJoinAt_lk _ _ _ _ _ _

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- ONE TEXT FOR TWO ISSUES OF THE SEAT (Johnson/Stored/HeadSeatAt.lean: tested): in the elder the
seated block's decision IS the block's; in the newer it asks a test on the state in front, and a
yes of it is a yes of the block's. (The two linters are off here alone: over either issue one of
the two arms of "first" is not reached.) -/
theorem seatedClaims_lk {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole SameLink b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_lk h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

theorem k8Set_lk (s : S) (q : TailClaims.K8Part) : SameLink s (TailClaims.k8PartP.set s q) := by
  show SameLink s ((s.putTl q.tl).putFork q.F)
  exact lk_trans _ _ _ (lk_putTl s _) (lk_putFork _ _)

theorem atRecord_lk {α : Type} (f : TailClaims.K8Part → Except String (α × TailClaims.K8Part))
    {s : S} {y : α × S} (h : K8.atRecord f s = .ok y) : SameLink s y.2 := by
  unfold K8.atRecord at h
  split at h
  · cases h
  · obtain ⟨x, -, rfl⟩ := Keeps.emap_ok h
    exact k8Set_lk s _

theorem k8Whole_lk (p : K8.ParW) : Whole SameLink (K8.whole p) := by
  refine ⟨(k8_lk (Cl := Claim) p.toPar).1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact atRecord_lk _ h
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y, e, rfl⟩ := Keeps.emap_ok h
    exact atRecord_lk _ e

open Johnson.Desc.First.ForkMerge in
theorem headMerge11_lk (P : HeadMergeP) : Whole SameLink (headClaimMergeKind P) := by
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
      simp [SameLink, S.link?, *]
    · cases h'
  · obtain rfl := List.mem_singleton.1 hc
    have h' : headMergeClaim n s = .ok y := h
    unfold headMergeClaim at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨x, -, h'⟩ := bindE h'
      cases h'
      simp [SameLink, S.link?, *]
    · cases h'

#print axioms theStated_lk
#print axioms blockAtC_lk
#print axioms k5AtN_lk
#print axioms seatedClaims_lk
#print axioms k8Whole_lk
#print axioms headMerge11_lk

end Meaning.Lnk
