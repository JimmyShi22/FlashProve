-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/OuterSeated.lean: THE SIX KINDS OF SUB-PROTOCOL THAT SEND NOTHING INSIDE A LINK
(K3, K4, K5, K6, K8, K11) LEAVE THREE OF THE NINE FIELDS OF THE VERIFIER's STATE AS THEY WERE: what
goes on to the later chains (out), the state of the calls over the links (check) and the request's
public words (req). A second relation beside Quiet (Johnson/Goal/Meaning/RecQuiet.lean). Theorems,
proved.

WHY. A public test that reads "out" or the frame between segments (check.frame) stays true across a
sub-protocol that leaves these fields. Quiet holds the statement, the book, the count of roots and
parts of the open link; of the state's own field check it holds the rows' layout alone, and that
every copy of the frame behind is a copy in front; of "out" and of "req" it says nothing.

  Outer s s'   s'.out = s.out, s'.check = s.check, s'.req = s.req. outer_refl, outer_trans.
  outer_mark, outer_putFork, outer_putTl, outer_hearLook, outer_hear5   the state's own writers that
    these kinds call.
  theStated_outer (K3), blockAtC_outer (K4), k5AtN_outer (K5), seatedClaims_outer (K6),
    k8Whole_outer (K8), headMerge11_outer (K11)   THE SIX MAKERS AS THEY ARE SEATED: Whole Outer:
    the decision, the runs of claims and the runs behind the batching.

HOW. The walk of RecK3.lean, RecK3More.lean, RecK4.lean, RecK5K8.lean, RecK6.lean and
RecSeated.lean, theorem by theorem, at Outer in Quiet's place: their rules that are general in the
relation (k3_block_whole, withCaller_whole, blockG_whole, blockV_whole, blockVia_whole, k5_whole,
k6_whole, k6Join_whole, k8_whole, the lifts of a part) are CALLED; what is typed here is each rule's
premises at Outer.

The makers are the library's, as named above; the letters are as at the theorems on Quiet. Used by
Johnson/LPFGuard/Makers.lean.

What is not claimed. Anything on the open link's own fields (the link context, the ledger, the
approximate range proof's parameters), on the mark or on the debt of rows. Anything on another kind.
No soundness.

-/
import Johnson.Goal.Meaning.RecSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Out

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart decide_ok freeSlot_same runOf)
open Meaning.K2

/-- **What goes on to the later chains, the state of the calls over the links and the request's
public words are as they were.** -/
def Outer (s s' : S) : Prop := s'.out = s.out ∧ s'.check = s.check ∧ s'.req = s.req

theorem outer_refl (s : S) : Outer s s := ⟨rfl, rfl, rfl⟩

theorem outer_trans (a b c : S) (h : Outer a b) (k : Outer b c) : Outer a c :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

variable {T Cl : Type}

/-! ## Out of RecK3.lean -/

theorem outer_mark (s : S) (name : String) : Outer s (s.mark name) := by
  unfold S.mark
  split
  · exact outer_refl s
  · exact ⟨rfl, rfl, rfl⟩

theorem outer_putFork (s : S) (F : Fork) : Outer s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem outer_putTl (s : S) (tl : HTailF2) : Outer s (s.putTl tl) := by
  unfold S.putTl
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem outer_hearLook (s : S) (g : Forest.Heard) : Outer s (s.hearLook g) := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact outer_mark s _
    · exact ⟨rfl, rfl, rfl⟩
  · rename_i a ha
    split
    · exact outer_mark s _
    · exact ⟨rfl, rfl, rfl⟩
  · rename_i a ha
    split
    · exact outer_mark s _
    · split
      · exact outer_mark s _
      · exact ⟨rfl, rfl, rfl⟩
  · exact outer_mark s _

theorem seatCalls_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    Outer s ((K3.seatCalls claim).put s g G) :=
  outer_trans _ _ _ (outer_putFork s G) (outer_hearLook _ g)

theorem seatCalls_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    Outer s ((K3.seatCalls claim).mark s G) := outer_putFork s G

theorem seatDigits_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    Outer s ((K3.seatDigits claim).put s g G) := by
  show Outer s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact outer_trans _ _ _ (outer_putTl s _) (outer_putFork _ G)
  · exact outer_mark s _

theorem seatDigits_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    Outer s ((K3.seatDigits claim).mark s G) := outer_putFork s G

theorem quietLook_outer (fs : Forest.Shape) : Fn Outer (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact outer_refl s

theorem quietDigits_outer (used claims : Nat) : Fn Outer (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact outer_putFork s G

theorem quietHead_outer (X : Verify.Public) : Fn Outer (K3.quietHead X) := fun s s' h => by
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
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem quietAt_outer (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn Outer f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_outer X)
    | (cases h; exact quietLook_outer _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_outer _ _)
    | cases h

/-! ## Out of RecK3More.lean -/

theorem withCallerCalls_outer (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole Outer b) :
    Whole Outer (K3.withCaller (K3.seatCalls claim) p readers b) :=
  withCaller_whole Outer _ (seatCalls_mark claim) p readers W

theorem withCallerDigits_outer (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole Outer b) :
    Whole Outer (K3.withCaller (K3.seatDigits claim) p readers b) :=
  withCaller_whole Outer _ (seatDigits_mark claim) p readers W

theorem blockViaCalls_outer (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole Outer (K3.Law.blockVia (K3.seatCalls claim) piece laid before p guests) :=
  blockVia_whole Outer outer_refl _ (seatCalls_put claim) (seatCalls_mark claim) _ _ _ _ _

theorem blockViaDigits_outer (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole Outer (K3.Law.blockVia (K3.seatDigits claim) piece laid before p guests) :=
  blockVia_whole Outer outer_refl _ (seatDigits_put claim) (seatDigits_mark claim) _ _ _ _ _

/-- Every block that lookClaims gives is Outer. -/
theorem lookClaims_outer (W : Verify.Public) (l : Nat) {b : Block S Claim}
    (h : Kinds.Head.lookClaims W l = some b) : Whole Outer b := by
  unfold Kinds.Head.lookClaims at h
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact withCallerCalls_outer _ p _ (blockViaCalls_outer _ _ _ _ _ _)

/-- **Every block that theOwn gives is Outer.** -/
theorem theOwn_outer (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole Outer b := by
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
      have W : Whole Outer (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockViaCalls_outer claim _ _ _ _ _
        · exact blockViaDigits_outer claim _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

/-- **The block at an address, whole, is Outer.** -/
theorem theWhole_outer (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole Outer b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_outer claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole Outer outer_trans _ _ _ W
      ⟨Keeps.quiet_decides Outer _ _ _ _ f (quietAt_outer X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

/-! ## Out of RecK4.lean -/

/-- Laid back into S, a part with the same link gives an Outer state. -/
theorem setPart_outer (t : S) (p x : OnBytes.Desc.First.K4.Part) (hp : part? t = some p)
    (_ : SameL p x) : Outer t (setPart t x) := by
  unfold part? at hp
  split at hp
  · rename_i a ha
    cases hp
    exact ⟨rfl, rfl, rfl⟩
  · cases hp

/-- **K4's block at the state is Outer.** -/
theorem k4_outer (p : OnBytes.Desc.First.K4.Par) : Whole Outer (blockAtS p) :=
  whole_of_steps (stepsLiftPart part? setPart _ (k4_steps p) setPart_outer)
    (runsLiftPart part? setPart _ (k4_runs p) setPart_outer)
    (afterLiftPart part? setPart _ (k4_after p) setPart_outer)

/-! ## Out of RecK5K8.lean -/

/-- The three runs with "join" laid behind "keys". -/
theorem withJoin_keep (seat : Att.P.SeatC S) (c : Att.P.ParC) (keys : S → Option (Array Aff)) :
    ∀ x ∈ (Att.P.runsK seat c).flatMap (fun r =>
        if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)]
        else [r]), ∀ n, FnCl Outer (x.2 n) := by
  intro x hx n
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep Outer outer_refl seat c _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep Outer _ (seatCalls_mark id) keys n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep Outer outer_refl seat c _ hr n
    · cases hx

theorem outer_hear5 (s : S) (h : Att.P.Heard) : Outer s (s.hear5 h) := by
  unfold S.hear5
  split
  · rename_i a ha
    split
    · exact outer_mark s _
    · exact ⟨rfl, rfl, rfl⟩
  · exact outer_mark s _

theorem outer_hear5? {s s' : S} {h : Att.P.Heard} (e : (s.hear5? h).toOption = some s') :
    Outer s s' := by
  unfold S.hear5? at e
  cases k : (s.hear5 h).unmarked with
  | error _ => rw [k] at e; cases e
  | ok t =>
    rw [k] at e
    cases e
    rw [quiet_unmarked k]
    exact outer_hear5 s h

theorem seatS_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatS shape).lay s h G = some s') : Outer s s' := by
  simp only [Att.P.seatS] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ⟨rfl, rfl, rfl⟩
  · cases e

theorem seatSH_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatSH shape).lay s h G = some s') : Outer s s' := by
  have e' : ((Att.P.seatS shape).lay s h G).bind (fun t => (t.hear5? h).toOption) = some s' := e
  obtain ⟨t, h1, h2⟩ := Option.bind_eq_some_iff.1 e'
  exact outer_trans _ _ _ (seatS_lay shape s h G t h1) (outer_hear5? h2)

theorem seatSO_lay (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : Att.P.seatSO.lay s h G = some s') : Outer s s' := by
  simp only [Att.P.seatSO] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    have q1 : Outer s ({ s with rowsOwed := none, here := .att { a with F := G } } : S) := by
      exact ⟨rfl, rfl, rfl⟩
    exact outer_trans _ _ _ q1 (outer_hear5? e)
  · cases e

theorem k5At_outer {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Cl} (h : Att.P.k5At W l g before = some b) : Whole Outer b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k5_whole Outer _ (seatS_lay p.S) [] (fun _ hx => nomatch hx) _

theorem k5AtW_outer (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtW W l g before = some b) : Whole Outer b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole Outer _ (seatS_lay p.S) (Att.P.runsW p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtH_outer (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtH W l g before = some b) : Whole Outer b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole Outer _ (seatSH_lay p.S) (Att.P.runsH p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtO_outer (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtO W l g before = some b) : Whole Outer b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole Outer _ seatSO_lay (Att.P.runsO p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k8_lay (s : S) (m : Array Int) (first : Array Nat) (s' : S)
    (e : K8.atS.lay s m first = .ok s') : Outer s s' := by
  have e' : (match s.tl? with
    | some tl => Except.ok (s.putTl { tl with cfF := m, cfFirst := first })
    | none => .error "the smallness test: no link is open") = .ok s' := e
  split at e'
  · cases e'
    exact outer_putTl s _
  · cases e'

theorem k8_outer {Cl : Type} (p : K8.Par) : Whole Outer (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p) :=
  k8_whole Outer _ k8_lay p

/-! ## Out of RecK6.lean -/

section K6
open VerifiableInference.Desc.Kinds.Head

theorem seatAt_ledger (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : Outer s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact outer_putFork s F
  · cases e'

theorem seatAt_heard (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : Outer s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      exact ⟨rfl, rfl, rfl⟩
    · cases e
  · cases e

/-- **The output head's own block at the state is Outer.** -/
theorem blockAt_outer (h : Model.Head.Shape) (iU3 work l : Nat) :
    Whole Outer (Kinds.Head.blockAt h iU3 work l) :=
  k6Join_whole Outer outer_refl outer_trans _ (seatCalls_mark _) (seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => outer_refl s) (fun s _ => outer_refl s)
    l 4 (parOf h work)

theorem blockOf_outer {W : Verify.Public} {l : Nat} {b : Block S Unit}
    (hb : Kinds.Head.blockOf W l = some b) : Whole Outer b := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact blockAt_outer _ _ _ _

end K6

/-! ## Out of RecSeated.lean -/

theorem theStated_outer (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole Outer b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_outer claim true X codes shape a h0
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
        exact withCallerCalls_outer claim p _ W

theorem blockAtC_outer (p : OnBytes.Desc.First.K4.Par) :
    Whole Outer (OnBytes.Desc.First.K4.blockAtC p) := atClaims_whole (k4_outer p)

theorem k5AtN_outer (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) : Whole Outer b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  have H : ∀ x ∈ Att.P.runsO p, ∀ n, FnCl Outer (x.2 n) := withJoin_keep _ _ _
  refine whole_same (k5_whole Outer _ seatSO_lay (Att.P.runsN p) (fun c hc n s y e => ?_) _) rfl
    (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := Att.P.runN_ok e
  exact H r hr n s _ e'

theorem kindJoinAt_outer (claim : Aff → Cl) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) :
    Whole Outer
      (Kinds.Head.kindWithJoin (K3.seatCalls claim) (Kinds.Head.seatAt h iU3) l piece p) :=
  k6Join_whole Outer outer_refl outer_trans _ (seatCalls_mark _) (Kinds.Head.seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => outer_refl s) (fun s _ => outer_refl s)
    l piece p

theorem blockClaims_outer {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole Outer b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact kindJoinAt_outer _ _ _ _ _ _

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- One proof for two forms of the seat (Johnson/Stored/HeadSeatAt.lean: tested): one in which the
seated block's decision IS the block's, and the present one, in which it asks a test on the state in
front, and a yes of it is a yes of the block's. (The two linters are off here alone: at either form
one of the two arms of "first" is not reached.) -/
theorem seatedClaims_outer {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole Outer b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_outer h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

theorem k8Set_outer (s : S) (q : TailClaims.K8Part) : Outer s (TailClaims.k8PartP.set s q) := by
  show Outer s ((s.putTl q.tl).putFork q.F)
  exact outer_trans _ _ _ (outer_putTl s _) (outer_putFork _ _)

theorem atRecord_outer {α : Type} (f : TailClaims.K8Part → Except String (α × TailClaims.K8Part))
    {s : S} {y : α × S} (h : K8.atRecord f s = .ok y) : Outer s y.2 := by
  unfold K8.atRecord at h
  split at h
  · cases h
  · obtain ⟨x, -, rfl⟩ := Keeps.emap_ok h
    exact k8Set_outer s _

theorem k8Whole_outer (p : K8.ParW) : Whole Outer (K8.whole p) := by
  refine ⟨(k8_outer (Cl := Claim) p.toPar).1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact atRecord_outer _ h
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y, e, rfl⟩ := Keeps.emap_ok h
    exact atRecord_outer _ e

open Johnson.Desc.First.ForkMerge in
theorem headMerge11_outer (P : HeadMergeP) : Whole Outer (headClaimMergeKind P) := by
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
      exact ⟨rfl, rfl, rfl⟩
    · cases h'
  · obtain rfl := List.mem_singleton.1 hc
    have h' : headMergeClaim n s = .ok y := h
    unfold headMergeClaim at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨x, -, h'⟩ := bindE h'
      cases h'
      exact ⟨rfl, rfl, rfl⟩
    · cases h'

#print axioms theStated_outer
#print axioms blockAtC_outer
#print axioms k5AtN_outer
#print axioms seatedClaims_outer
#print axioms k8Whole_outer
#print axioms headMerge11_outer

end Meaning.Out
