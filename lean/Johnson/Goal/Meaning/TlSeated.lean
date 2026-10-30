--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/TlSeated.lean: FOUR OF THE SIX KINDS OF SUB-PROTOCOL THAT SEND NOTHING INSIDE A
LINK LEAVE THE OPEN SEGMENT's PARAMETERS OF THE APPROXIMATE RANGE PROOF AS THEY WERE, WHOLE (S.tl?):
K3 AT A PIECE IN FRONT OF THE DIGITS' LOOKUP (the lookup on the calls), K5, K6 AND K11. A fourth
relation, beside Quiet (RecQuiet.lean), Outer (OuterSeated.lean) and SameLink (LinkSeated.lean).
Theorems, proved.

WHY. The public item "linkFresh" reads these parameters and the link context; it is open from a
segment's opening to the lookup on the digits.

  SameTl s s'   s'.tl? = s.tl?. tl_refl, tl_trans.
  tl_mark, tl_putFork, tl_hearLook, tl_hear5   the state's own writers that these kinds call.
  theStated_tl (K3; under a.piece < 7: the digits' lookup stands at piece 7, at the head's link at
    8: K3.pieceAt), k5AtN_tl (K5), seatedClaims_tl (K6), headMerge11_tl (K11)   THE MAKERS AS THEY
    ARE SEATED: Whole SameTl.

NOT HERE, AND WHY. K3 at the digits' lookup and K8 WRITE that structure (S.putTl stands in the
digits' seat's laying and in K8's part's laying). K4: its block is typed at a part of the state and
lifted; that the part's own copy stays is not drawn here.

HOW. As at OuterSeated.lean: the walk of RecK3.lean, RecK3More.lean, RecK5K8.lean, RecK6.lean and
RecSeated.lean at SameTl in Quiet's place; the rules that are general in the relation are CALLED.

OBJECT: the landed makers' sub-protocols that are named above. USER:
Johnson/Goal/Meaning/QuietRide.lean. LETTERS: as at the theorems on Quiet.

What is not claimed. Anything on the ledger. Anything on another kind. No soundness.
-/
import Johnson.Goal.Meaning.RecSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Tl

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart decide_ok freeSlot_same runOf)
open Meaning.K2

/-- **The open segment's parameters of the approximate range proof are as they were, whole**; and
where no segment is open none is. -/
def SameTl (s s' : S) : Prop := s'.tl? = s.tl?

theorem tl_refl (s : S) : SameTl s s := rfl

theorem tl_trans (a b c : S) (h : SameTl a b) (k : SameTl b c) : SameTl a c := Eq.trans k h

variable {T Cl : Type}

/-! ## Out of RecK3.lean -/

theorem tl_mark (s : S) (name : String) : SameTl s (s.mark name) := by
  unfold S.mark
  split
  · exact tl_refl s
  · rfl

theorem tl_putFork (s : S) (F : Fork) : SameTl s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals simp [SameTl, S.tl?, *]

theorem tl_hearLook (s : S) (g : Forest.Heard) : SameTl s (s.hearLook g) := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact tl_mark s _
    · simp [SameTl, S.tl?, *]
  · rename_i a ha
    split
    · exact tl_mark s _
    · simp [SameTl, S.tl?, *]
  · rename_i a ha
    split
    · exact tl_mark s _
    · split
      · exact tl_mark s _
      · simp [SameTl, S.tl?, *]
  · exact tl_mark s _

theorem seatCalls_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    SameTl s ((K3.seatCalls claim).put s g G) :=
  tl_trans _ _ _ (tl_putFork s G) (tl_hearLook _ g)

theorem seatCalls_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    SameTl s ((K3.seatCalls claim).mark s G) := tl_putFork s G

theorem seatDigits_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    SameTl s ((K3.seatDigits claim).mark s G) := tl_putFork s G

theorem quietLook_tl (fs : Forest.Shape) : Fn SameTl (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact tl_refl s

theorem quietDigits_tl (used claims : Nat) : Fn SameTl (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact tl_putFork s G

theorem quietHead_tl (X : Verify.Public) : Fn SameTl (K3.quietHead X) := fun s s' h => by
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
    simp [SameTl, S.tl?, *]
  · cases h

theorem quietAt_tl (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn SameTl f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_tl X)
    | (cases h; exact quietLook_tl _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_tl _ _)
    | cases h

/-! ## Out of RecK3More.lean -/

theorem withCallerCalls_tl (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole SameTl b) :
    Whole SameTl (K3.withCaller (K3.seatCalls claim) p readers b) :=
  withCaller_whole SameTl _ (seatCalls_mark claim) p readers W

theorem withCallerDigits_tl (claim : Aff → Cl) (p : First.Look.P) (readers : K3.Readers S)
    {b : Block S Cl} (W : Whole SameTl b) :
    Whole SameTl (K3.withCaller (K3.seatDigits claim) p readers b) :=
  withCaller_whole SameTl _ (seatDigits_mark claim) p readers W

theorem blockViaCalls_tl (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Whole SameTl (K3.Law.blockVia (K3.seatCalls claim) piece laid before p guests) :=
  blockVia_whole SameTl tl_refl _ (seatCalls_put claim) (seatCalls_mark claim) _ _ _ _ _

/-- Every block that lookClaims gives leaves them. -/
theorem lookClaims_tl (W : Verify.Public) (l : Nat) {b : Block S Claim}
    (h : Kinds.Head.lookClaims W l = some b) : Whole SameTl b := by
  unfold Kinds.Head.lookClaims at h
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact withCallerCalls_tl _ p _ (blockViaCalls_tl _ _ _ _ _ _)

/-- **Every block that theOwn gives at a piece in front of the digits' lookup leaves them.** -/
theorem theOwn_tl (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (hc : a.piece < 7) (h : K3.theOwn claim runs X codes shape a = some b) : Whole SameTl b := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · rename_i hpc
      obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      have W : Whole SameTl (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockViaCalls_tl claim _ _ _ _ _
        · exfalso
          have e : a.piece = K3.pieceAt X i true := by simpa using hpc
          unfold K3.pieceAt at e
          split at e <;> simp at e <;> omega
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

/-- **The block at such an address, whole, leaves them.** -/
theorem theWhole_tl (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (hc : a.piece < 7) (h : K3.theWhole claim runs X codes shape a = some b) : Whole SameTl b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_tl claim runs X codes shape a hc h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole SameTl tl_trans _ _ _ W
      ⟨Keeps.quiet_decides SameTl _ _ _ _ f (quietAt_tl X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

/-! ## Out of RecK5K8.lean -/

/-- The three runs with "join" laid behind "keys". -/
theorem withJoin_keep (seat : Att.P.SeatC S) (c : Att.P.ParC) (keys : S → Option (Array Aff)) :
    ∀ x ∈ (Att.P.runsK seat c).flatMap (fun r =>
        if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)]
        else [r]), ∀ n, FnCl SameTl (x.2 n) := by
  intro x hx n
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep SameTl tl_refl seat c _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep SameTl _ (seatCalls_mark id) keys n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep SameTl tl_refl seat c _ hr n
    · cases hx

theorem tl_hear5 (s : S) (h : Att.P.Heard) : SameTl s (s.hear5 h) := by
  unfold S.hear5
  split
  · rename_i a ha
    split
    · exact tl_mark s _
    · simp [SameTl, S.tl?, *]
  · exact tl_mark s _

theorem tl_hear5? {s s' : S} {h : Att.P.Heard} (e : (s.hear5? h).toOption = some s') :
    SameTl s s' := by
  unfold S.hear5? at e
  cases k : (s.hear5 h).unmarked with
  | error _ => rw [k] at e; cases e
  | ok t =>
    rw [k] at e
    cases e
    rw [quiet_unmarked k]
    exact tl_hear5 s h

theorem seatS_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatS shape).lay s h G = some s') : SameTl s s' := by
  simp only [Att.P.seatS] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 e
    simp [SameTl, S.tl?, *]
  · cases e

theorem seatSH_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatSH shape).lay s h G = some s') : SameTl s s' := by
  have e' : ((Att.P.seatS shape).lay s h G).bind (fun t => (t.hear5? h).toOption) = some s' := e
  obtain ⟨t, h1, h2⟩ := Option.bind_eq_some_iff.1 e'
  exact tl_trans _ _ _ (seatS_lay shape s h G t h1) (tl_hear5? h2)

theorem seatSO_lay (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : Att.P.seatSO.lay s h G = some s') : SameTl s s' := by
  simp only [Att.P.seatSO] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    have q1 : SameTl s ({ s with rowsOwed := none, here := .att { a with F := G } } : S) := by
      simp [SameTl, S.tl?, *]
    exact tl_trans _ _ _ q1 (tl_hear5? e)
  · cases e

theorem k5At_tl {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Cl} (h : Att.P.k5At W l g before = some b) : Whole SameTl b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k5_whole SameTl _ (seatS_lay p.S) [] (fun _ hx => nomatch hx) _

theorem k5AtW_tl (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtW W l g before = some b) : Whole SameTl b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole SameTl _ (seatS_lay p.S) (Att.P.runsW p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtH_tl (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtH W l g before = some b) : Whole SameTl b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole SameTl _ (seatSH_lay p.S) (Att.P.runsH p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtO_tl (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtO W l g before = some b) : Whole SameTl b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole SameTl _ seatSO_lay (Att.P.runsO p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

/-! ## Out of RecK6.lean -/

section K6
open VerifiableInference.Desc.Kinds.Head

theorem seatAt_ledger (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : SameTl s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact tl_putFork s F
  · cases e'

theorem seatAt_heard (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : SameTl s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      simp [SameTl, S.tl?, *]
    · cases e
  · cases e

/-- **The output head's own block at the state leaves them.** -/
theorem blockAt_tl (h : Model.Head.Shape) (iU3 work l : Nat) :
    Whole SameTl (Kinds.Head.blockAt h iU3 work l) :=
  k6Join_whole SameTl tl_refl tl_trans _ (seatCalls_mark _) (seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => tl_refl s) (fun s _ => tl_refl s)
    l 4 (parOf h work)

theorem blockOf_tl {W : Verify.Public} {l : Nat} {b : Block S Unit}
    (hb : Kinds.Head.blockOf W l = some b) : Whole SameTl b := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact blockAt_tl _ _ _ _

end K6

/-! ## Out of RecSeated.lean -/

theorem theStated_tl (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (hc : a.piece < 7) (h : K3.theStated claim readers X codes shape a = some b) :
    Whole SameTl b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_tl claim true X codes shape a hc h0
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
        exact withCallerCalls_tl claim p _ W

theorem k5AtN_tl (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) : Whole SameTl b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  have H : ∀ x ∈ Att.P.runsO p, ∀ n, FnCl SameTl (x.2 n) := withJoin_keep _ _ _
  refine whole_same (k5_whole SameTl _ seatSO_lay (Att.P.runsN p) (fun c hc n s y e => ?_) _) rfl
    (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := Att.P.runN_ok e
  exact H r hr n s _ e'

theorem kindJoinAt_tl (claim : Aff → Cl) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) :
    Whole SameTl
      (Kinds.Head.kindWithJoin (K3.seatCalls claim) (Kinds.Head.seatAt h iU3) l piece p) :=
  k6Join_whole SameTl tl_refl tl_trans _ (seatCalls_mark _) (Kinds.Head.seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => tl_refl s) (fun s _ => tl_refl s)
    l piece p

theorem blockClaims_tl {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole SameTl b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact kindJoinAt_tl _ _ _ _ _ _

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- ONE TEXT FOR TWO ISSUES OF THE SEAT (Johnson/Stored/HeadSeatAt.lean: tested): in the elder the
seated block's decision IS the block's; in the newer it asks a test on the state in front, and a
yes of it is a yes of the block's. (The two linters are off here alone: over either issue one of
the two arms of "first" is not reached.) -/
theorem seatedClaims_tl {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole SameTl b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_tl h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

open Johnson.Desc.First.ForkMerge in
theorem headMerge11_tl (P : HeadMergeP) : Whole SameTl (headClaimMergeKind P) := by
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
      simp [SameTl, S.tl?, *]
    · cases h'
  · obtain rfl := List.mem_singleton.1 hc
    have h' : headMergeClaim n s = .ok y := h
    unfold headMergeClaim at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨x, -, h'⟩ := bindE h'
      cases h'
      simp [SameTl, S.tl?, *]
    · cases h'

#print axioms theStated_tl
#print axioms k5AtN_tl
#print axioms seatedClaims_tl
#print axioms headMerge11_tl

end Meaning.Tl
