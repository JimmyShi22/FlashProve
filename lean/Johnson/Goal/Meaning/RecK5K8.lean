-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK5K8.lean: kind K5's blocks (an attention segment's own rounds) and kind
K8's hearing (the draw of the smallness test's matrix) at the first chain's record write neither the
statement nor a copy of the frame of the links: they are Quiet (Johnson/Goal/Meaning/RecQuiet.lean).

K5 (Johnson/Desc/First/Att/K5AttentionKind.lean).
  k5_whole: A GENERAL RULE, at any record and seat: a relation that the seat's laying keeps, and
    that every run of claims which is handed in keeps, is kept by the block attentionKind seat claims p. It has
    no run behind the batching.
  runsK_keep: the kind's three named runs (RunsK.lean: "first", "keys", "second") hand the record
    back as it is, at any seat of the claims. joinRun_keep: the lookup's run "join"
    (Look/K3Runs.lean) lays through the lookup's seat's mark alone.
  seatS_lay, seatSH_lay, seatSO_lay: the three seats of the hearing at the record (SeatP.lean,
    SeatH.lean, SeatO.lean) lay Quietly: they write the debt of rows and, inside the attention
    link's own part, the ledger and what was heard: never the link.
  k5At_quiet, k5AtW_quiet, k5AtH_quiet, k5AtO_quiet: Whole Quiet of every block that the four makers
  give.
K8 (Johnson/Desc/First/K8/Hear.lean, AtS.lean).
  k8_whole: the like general rule for approximateRangeProofDrawKind seat p. k8_quiet: Whole Quiet (K8.approximateRangeProofDrawKind K8.atS p).
With whole_rec and whole_grows each gives Whole (RecRel cs sh) and Whole (GrowsBy fun s => s.st).
Not claimed: anything on the steps without a round around these blocks (the reads' block,
Att/ReadsBlock.lean; Johnson/Desc/K8/ReadsQuiet.lean), or on K8's claims, which are another text's
(Johnson/Desc/First/TailClaims).
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them yet. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecK3
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.First.K8.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Fn FnCl)

/-! ## K5 -/

/-- **A relation that the seat's laying and the runs handed in keep is kept by K5's block.** -/
theorem k5_whole {T Cl : Type} (R : T → T → Prop) (seat : Att.P.Seat T)
    (hlay : ∀ s h G s', seat.lay s h G = some s' → R s s')
    (claims : List (String × (Nat → T → Except String (List Cl × T))))
    (hc : ∀ c ∈ claims, ∀ n, FnCl R (c.2 n)) (p : Att.P.Par) :
    Whole R (Att.P.attentionKind seat claims p) := by
  refine ⟨fun s rs gs s' h => ?_, hc, (fun _ hx => nomatch hx)⟩
  have h' : Att.P.decide seat p s rs = .ok s' := h
  unfold Att.P.decide at h'
  obtain ⟨_, _, h'⟩ := bindE h'
  obtain ⟨F, _, h'⟩ := bindE h'
  obtain ⟨⟨hd, G, rest, k⟩, _, h'⟩ := bindE h'
  obtain ⟨_, _, h'⟩ := bindE h'
  exact hlay _ _ _ _ (Keeps.named_ok h')

/-- The kind's three named runs hand the record back as it is. -/
theorem runsK_keep {T : Type} (R : T → T → Prop) (hr : ∀ s, R s s) (seat : Att.P.SeatC T)
    (c : Att.P.ParC) : ∀ x ∈ Att.P.runsK seat c, ∀ n, FnCl R (x.2 n) := by
  intro x hx n s y h
  rcases List.mem_cons.1 hx with rfl | hx
  · have h' := Keeps.named_ok h
    unfold Att.P.firstK at h'
    obtain ⟨⟨i, K⟩, _, h'⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨_, _, h'⟩ := Option.bind_eq_some_iff.1 h'
    cases h'
    exact hr s
  · rcases List.mem_cons.1 hx with rfl | hx
    · have h' := Keeps.named_ok h
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 h'
      rw [← e]
      exact hr s
    · rcases List.mem_cons.1 hx with rfl | hx
      · have h' := Keeps.named_ok h
        unfold Att.P.secondK at h'
        obtain ⟨⟨i, K⟩, _, h'⟩ := Option.bind_eq_some_iff.1 h'
        obtain ⟨_, _, h'⟩ := Option.bind_eq_some_iff.1 h'
        cases h'
        exact hr s
      · cases hx

/-- The lookup's run "join" lays through the lookup's seat's mark alone. -/
theorem joinRun_keep {T Cl : Type} (R : T → T → Prop) (seat : K3.Seat T Cl)
    (hmark : ∀ s G, R s (seat.mark s G)) (keys : T → Option (Array Aff)) (n : Nat) :
    FnCl R (K3.joinRun seat keys n) := by
  intro s y h
  unfold K3.joinRun at h
  obtain ⟨F, _, h⟩ := bindE h
  obtain ⟨g, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨KF, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  cases h
  exact hmark _ _

/-- The three runs with "join" laid behind "keys". -/
theorem withJoin_keep (seat : Att.P.SeatC S) (c : Att.P.ParC) (keys : S → Option (Array Aff)) :
    ∀ x ∈ (Att.P.runsK seat c).flatMap (fun r =>
        if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)]
        else [r]), ∀ n, FnCl Quiet (x.2 n) := by
  intro x hx n
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep Quiet quiet_refl seat c _ hr n
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact joinRun_keep Quiet _ (seatCalls_mark id) keys n
      · cases hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact runsK_keep Quiet quiet_refl seat c _ hr n
    · cases hx

theorem quiet_hear5 (s : S) (h : Att.P.Heard) : Quiet s (s.hear5 h) := by
  unfold S.hear5
  split
  · rename_i a ha
    split
    · exact quiet_mark s _
    · refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
      by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
  · exact quiet_mark s _

theorem quiet_unmarked {s s' : S} (h : s.unmarked = .ok s') : s' = s := by
  unfold S.unmarked at h
  split at h
  · cases h
    rfl
  · cases h

theorem quiet_hear5? {s s' : S} {h : Att.P.Heard} (e : (s.hear5? h).toOption = some s') :
    Quiet s s' := by
  unfold S.hear5? at e
  cases k : (s.hear5 h).unmarked with
  | error _ => rw [k] at e; cases e
  | ok t =>
    rw [k] at e
    cases e
    rw [quiet_unmarked k]
    exact quiet_hear5 s h

theorem seatS_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatS shape).lay s h G = some s') : Quiet s s' := by
  simp only [Att.P.seatS] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 e
    refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
      by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun _ => rfl,
        fun _ e => e⟩
    unfold framesIn at hf ⊢
    rw [ha]
    exact hf
  · cases e

theorem seatSH_lay (shape : Attention.Shape) (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : (Att.P.seatSH shape).lay s h G = some s') : Quiet s s' := by
  have e' : ((Att.P.seatS shape).lay s h G).bind (fun t => (t.hear5? h).toOption) = some s' := e
  obtain ⟨t, h1, h2⟩ := Option.bind_eq_some_iff.1 e'
  exact quiet_trans _ _ _ (seatS_lay shape s h G t h1) (quiet_hear5? h2)

theorem seatSO_lay (s : S) (h : Att.P.Heard) (G : Fork) (s' : S)
    (e : Att.P.seatSO.lay s h G = some s') : Quiet s s' := by
  simp only [Att.P.seatSO] at e
  split at e
  · rename_i a ha
    obtain ⟨g, _, e⟩ := Option.bind_eq_some_iff.1 e
    have q1 : Quiet s ({ s with rowsOwed := none, here := .att { a with F := G } } : S) := by
      refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
        by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun _ => rfl,
        fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
    exact quiet_trans _ _ _ q1 (quiet_hear5? e)
  · cases e

theorem k5At_quiet {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Cl} (h : Att.P.k5At W l g before = some b) : Whole Quiet b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k5_whole Quiet _ (seatS_lay p.S) [] (fun _ hx => nomatch hx) _

theorem k5AtW_quiet (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtW W l g before = some b) : Whole Quiet b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole Quiet _ (seatS_lay p.S) (Att.P.runsW p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtH_quiet (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtH W l g before = some b) : Whole Quiet b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole Quiet _ (seatSH_lay p.S) (Att.P.runsH p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

theorem k5AtO_quiet (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Aff} (h : Att.P.k5AtO W l g before = some b) : Whole Quiet b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact whole_same (k5_whole Quiet _ seatSO_lay (Att.P.runsO p)
    (withJoin_keep _ _ _) _) rfl (fun _ hx => hx) rfl

/-! ## K8's hearing -/

/-- **A relation that the seat's laying keeps is kept by K8's hearing.** -/
theorem k8_whole {T Cl : Type} (R : T → T → Prop) (seat : K8.Seat T)
    (hlay : ∀ s m first s', seat.lay s m first = .ok s' → R s s') (p : K8.Par) :
    Whole R (K8.approximateRangeProofDrawKind (Cl := Cl) seat p) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
  simp only [K8.approximateRangeProofDrawKind] at h
  split at h
  · repeat' split at h
    all_goals first
      | exact hlay _ _ _ _ h
      | cases h
  · cases h

theorem k8_lay (s : S) (m : Array Int) (first : Array Nat) (s' : S)
    (e : K8.atS.lay s m first = .ok s') : Quiet s s' := by
  have e' : (match s.tl? with
    | some tl => Except.ok (s.putTl { tl with cfF := m, cfFirst := first })
    | none => .error "the smallness test: no link is open") = .ok s' := e
  split at e'
  · cases e'
    exact quiet_putTl s _
  · cases e'

theorem k8_quiet {Cl : Type} (p : K8.Par) : Whole Quiet (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p) :=
  k8_whole Quiet _ k8_lay p

#print axioms k5_whole
#print axioms runsK_keep
#print axioms joinRun_keep
#print axioms k5At_quiet
#print axioms k5AtW_quiet
#print axioms k5AtH_quiet
#print axioms k5AtO_quiet
#print axioms k8_whole
#print axioms k8_quiet

end Meaning.K2
