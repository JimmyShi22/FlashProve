-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/TablesWalkHead.lean: FROM THE OUTPUT HEAD's SEGMENT's OPENING TO ITS READS' PLACE
NO SUB-PROTOCOL LAYS THE READS' TABLES: the makers that stand there (K7's place with the front step
that enters the segment · the segment's frame's "opened" · K2's place with the step that opens the
segment · the lookup on the calls · K6) leave the field t of the verifier's state as it is. Typed for
the row "TablesOk along reached" (Johnson/Desc/K1/Law/TablesOk.lean).
Definitions, and statements with their proofs.

How. One relation, TK s s': "what tables are laid" (tOf: the field t inside the output head's segment;
none elsewhere) is the same at both states. The proofs MIRROR, lemma for lemma,
Johnson/Desc/First/Pile/ReqMakers.lean and ReqSeated.lean (the relation "the request's words stay"),
and call the laws that are general in the relation: Meaning.K2.k7_whole, entered_whole, k6Join_whole,
blockVia_whole, withCaller_whole, whole_same, whole_sub, guarded_whole; Keeps.andThen_whole,
Keeps.quiet_decides.
Main names:
  tOf · TK (tk_refl, tk_trans, tk_here) · NoTables · TK.no: TK carries NoTables.
  writers of the state: tk_mark, tk_putFork, tk_putTl, tk_hearLook, tk_enterLay, tk_enterAtt,
    tk_enterHead, tk_openHead.
  theStated_tk        **the lookup's sub-protocol at any address.**
  seatedClaims_tk     **K6's lot's sub-protocol.**
  k7Of_tk · headFrontQ_tk · k7Block_tk   **K7's place's sub-protocol as the lot lays it.**
  k2_tk · headOpenQ_tk · headOpened_tk · k2Is_tk   **K2's lot's sub-protocol at a place in a link.**
  opened_tk           **every row of the links' frames: "opened".**
  noTables_of         the form that the walk calls: Decides TK b → an accept of b carries NoTables.
What is not claimed. That the reads' quiet steps keep TK: they do not. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.TablesWalk
import Johnson.Goal.Meaning.RecSeated
import Johnson.Goal.Meaning.RecK7
import Johnson.Top.H0.Tw.K2C.LeavesOut
import Johnson.Desc.First.Pile.ReqSeated
import Johnson.IMR.K2Seat
import Johnson.IMR.K7Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (seatAt HeardAll)
open Johnson.Desc.First.Walk
open Meaning.K2 (bindE unmarked_eq quiet_unmarked k7_whole entered_whole k6Join_whole blockVia_whole
  withCaller_whole whole_same whole_sub guarded_whole mem_of_mapM_ok)

variable {Cl : Type}

/-! ## The relation -/

/-- What tables are laid: the field t inside the output head's segment; none elsewhere. -/
def tOf (s : S) : Option Head.Tables :=
  match s.here with
  | .head a => a.t
  | _ => none

/-- **What tables are laid stays.** -/
def TK (s s' : S) : Prop := tOf s' = tOf s

theorem tk_refl (s : S) : TK s s := rfl

theorem tk_trans (a b c : S) (h : TK a b) (k : TK b c) : TK a c := Eq.trans k h

theorem tk_here {s s' : S} (h : s'.here = s.here) : TK s s' := by
  unfold TK tOf
  rw [h]

/-- No tables are laid. -/
def NoTables (s : S) : Prop := ∀ a, s.here = .head a → a.t = none

theorem noTables_iff (s : S) : NoTables s ↔ tOf s = none := by
  unfold NoTables tOf
  cases h : s.here with
  | head a => exact ⟨fun k => k a rfl, fun k b e => by rw [← Here.head.inj e]; exact k⟩
  | _ => exact ⟨fun _ => rfl, fun _ b e => nomatch e⟩

theorem TK.no {s s' : S} (h : TK s s') (k : NoTables s) : NoTables s' :=
  (noTables_iff s').2 (Eq.trans h ((noTables_iff s).1 k))

/-- The form that the walk calls. -/
theorem noTables_of {b : Block S Cl} (D : Decides TK b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (e : b.decide s rs gs = .ok s') (k : NoTables s) :
    NoTables s' := (D s rs gs s' e).no k

/-- Where no tables are laid the invariant holds. -/
theorem tablesOk_of_no (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (s : S)
    (k : NoTables s) : TablesOk h L hp s := tablesOk_none h L hp s k

/-- Between two segments no tables are laid. -/
theorem noTables_between (s : S) (h : s.atBetween = true) : NoTables s := by
  intro a ha
  unfold S.atBetween at h
  rw [ha] at h
  cases h

/-! ## Writers of the state -/

theorem tk_mark (s : S) (name : String) : TK s (s.mark name) := by
  unfold S.mark
  split
  · exact tk_refl s
  · exact tk_here rfl

theorem tk_putFork (s : S) (F : Fork) : TK s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals first
    | exact tk_refl _
    | exact tk_mark _ _
    | (unfold TK tOf; simp [*])

theorem tk_putTl (s : S) (tl : HTailF2) : TK s (s.putTl tl) := by
  unfold S.putTl
  repeat' split
  all_goals first
    | exact tk_refl _
    | exact tk_mark _ _
    | (unfold TK tOf; simp [*])

theorem tk_hearLook (s : S) (g : Forest.Heard) : TK s (s.hearLook g) := by
  unfold S.hearLook
  repeat' split
  all_goals first
    | exact tk_refl _
    | exact tk_mark _ _
    | (unfold TK tOf; simp [*])

theorem tk_openHead (s : S) : TK s s.openHead := by
  unfold S.openHead
  repeat' split
  all_goals first
    | exact tk_refl _
    | exact tk_mark _ _
    | (unfold TK tOf; simp [*])

theorem tOf_between (s : S) (h : s.atBetween = true) : tOf s = none :=
  (noTables_iff s).1 (noTables_between s h)

theorem tk_enterLay (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : TK s (s.enterLay L F tl) := by
  unfold S.enterLay
  split
  · rename_i hb
    exact (tOf_between s hb).symm
  · exact tk_mark _ _

theorem tk_enterAtt (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) : TK s (s.enterAtt L F tl) := by
  unfold S.enterAtt
  split
  · rename_i hb
    exact (tOf_between s hb).symm
  · exact tk_mark _ _

theorem tk_enterHead (s : S) (tl : HTailF2) : TK s (s.enterHead tl) := by
  unfold S.enterHead
  split
  · rename_i hb
    exact (tOf_between s hb).symm
  · exact tk_mark _ _

/-! ## The lookup -/

theorem seatCalls_put_tk (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    TK s ((K3.seatCalls claim).put s g G) :=
  tk_trans _ _ _ (tk_putFork s G) (tk_hearLook _ g)

theorem seatCalls_mark_tk (claim : Aff → Cl) (s : S) (G : Fork) :
    TK s ((K3.seatCalls claim).mark s G) := tk_putFork s G

theorem seatDigits_put_tk (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    TK s ((K3.seatDigits claim).put s g G) := by
  show TK s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact tk_trans _ _ _ (tk_putTl s _) (tk_putFork _ G)
  · exact tk_mark s _

theorem seatDigits_mark_tk (claim : Aff → Cl) (s : S) (G : Fork) :
    TK s ((K3.seatDigits claim).mark s G) := tk_putFork s G

theorem quietLook_tk (fs : Forest.Shape) : Fn TK (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact tk_refl s

theorem quietDigits_tk (used claims : Nat) : Fn TK (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact tk_putFork s G

theorem quietHead_tk (X : Verify.Public) : Fn TK (K3.quietHead X) := fun s s' h => by
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
    unfold TK tOf
    simp [ha]
  · cases h

theorem quietAt_tk (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn TK f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_tk X)
    | (cases h; exact quietLook_tk _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_tk _ _)
    | cases h

theorem theOwn_tk (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole TK b := by
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
      have W : Whole TK (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockVia_whole TK tk_refl _ (seatCalls_put_tk claim) (seatCalls_mark_tk claim)
            _ _ _ _ _
        · exact blockVia_whole TK tk_refl _ (seatDigits_put_tk claim) (seatDigits_mark_tk claim)
            _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

theorem theWhole_tk (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole TK b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_tk claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole TK tk_trans _ _ _ W
      ⟨Keeps.quiet_decides TK _ _ _ _ f (quietAt_tk X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

/-- **The lookup's sub-protocol at any address.** -/
theorem theStated_tk (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole TK b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_tk claim true X codes shape a h0
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
        exact withCaller_whole TK _ (seatCalls_mark_tk claim) p _ W

/-! ## K6 -/

theorem seatAt_ledger_tk (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : TK s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact tk_putFork s F
  · cases e'

theorem seatAt_heard_tk (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : TK s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      unfold TK tOf
      simp [ho]
    · cases e
  · cases e

theorem blockClaims_tk {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole TK b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k6Join_whole TK tk_refl tk_trans _ (seatCalls_mark_tk _) (seatAt W.hS iU3)
    (seatAt_ledger_tk W.hS iU3) (seatAt_heard_tk W.hS iU3) (fun s _ => tk_refl s)
    (fun s _ => tk_refl s) l 4 _

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- **K6's lot's sub-protocol.** -/
theorem seatedClaims_tk {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole TK b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_tk h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

/-! ## K7's place -/

theorem k7Of_tk (W : Verify.Public) (l : Nat) : Whole TK (Reply.blockOf W l) :=
  entered_whole (k7_whole TK _ (fun _ _ => tk_here rfl) l 1 W.hS.V)

theorem headFrontQ_tk (tl : HTailF2) : Fn TK (K2.headFrontQ tl) := fun s s' h => by
  unfold K2.headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, _, h⟩ := K2.bindOk h
      obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
      cases K2.enterHeadQ h₁
      split at h
      · rename_i a ha
        cases h
        refine tk_trans _ _ _ (tk_enterHead s tl) ?_
        unfold TK tOf
        simp [ha]
      · cases h

/-- **K7's place's sub-protocol as the lot lays it**: the front step that enters the segment, then
K7's own. -/
theorem k7Block_tk (X : Verify.Public) (l : ℕ) : Whole TK (IM.k7Block X l) := by
  have D : Decides TK (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ X.H.tl) : Block S Unit) :=
    Keeps.quiet_decides TK _ _ _ _ _ (headFrontQ_tk X.H.tl)
  have W : Whole TK ({ (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ X.H.tl) : Block S Unit) with
      place := (Reply.blockOf X l).place }) :=
    ⟨D, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  exact Keeps.andThen_whole TK tk_trans _ _ _ (guarded_whole _ _ W) (k7Of_tk X l)

/-! ## K2's place -/

theorem k2_tk (p : K2.P2) : Whole TK (K2.codeSwitchKind p : Block S Unit) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h : K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s' := h
  unfold K2.decideWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · obtain ⟨x, _, h⟩ := bindE h
      obtain ⟨_, _, h⟩ := bindE h
      obtain ⟨_, _, h⟩ := bindE h
      cases h
      exact tk_here rfl
    · obtain ⟨_, _, h⟩ := bindE h
      obtain ⟨x, _, h⟩ := bindE h
      obtain ⟨_, _, h⟩ := bindE h
      cases h
      unfold TK tOf
      simp [*]
    · obtain ⟨_, _, h⟩ := bindE h
      obtain ⟨_, _, h⟩ := bindE h
      obtain ⟨x, _, h⟩ := bindE h
      obtain ⟨_, _, h⟩ := bindE h
      cases h
      unfold TK tOf
      simp [*]
    · cases h

theorem headOpenQ_tk (P : K2.HeadPar) : Fn TK (K2.headOpenQ P) := fun s s' h => by
  unfold K2.headOpenQ at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := K2.bindOk h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hf, h⟩ := K2.bindOk h
        dsimp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
                cases K2.openHeadQ h₁
                split at h
                · rename_i b hb'
                  cases h
                  refine tk_trans _ _ _ (tk_openHead s) ?_
                  unfold TK tOf
                  simp [hb']
                · cases h
        · cases h
  · cases h

theorem headOpened_tk (name : String) (place : Place) (P : K2.HeadPar) :
    Whole TK (K2.headOpened name place P : Block S Unit) := by
  have D : Decides TK (roundlessBlock (name ++ ": opened") place.chain place.link place.piece
      (K2.headOpenQ P) : Block S Unit) := Keeps.quiet_decides TK _ _ _ _ _ (headOpenQ_tk P)
  exact ⟨D, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **K2's lot's sub-protocol at a place in a link.** -/
theorem k2Is_tk {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : IM.K2Is Z G a nm x) {l : ℕ} (hl : a.link = some l) : Decides TK x := by
  rcases h with ⟨-, hm⟩ | ⟨P, n, -, -, h | h | h⟩
  · intro s rs gs s' e
    obtain ⟨er, he⟩ := hm s rs gs
    rw [he] at e
    cases e
  · rw [hl] at h
    exact nomatch h.1
  · obtain ⟨l', HP, -, -, rfl⟩ := h
    exact (Keeps.andThen_whole TK tk_trans _ _ _ (k2_tk _) (headOpened_tk _ _ _)).1
  · obtain ⟨l', -, rfl⟩ := h
    exact (k2_tk _).1

/-! ## The links' frames' "opened" -/

theorem openAtt_tk (P : AttPar) : Fn TK (openAtt P) := fun s t h => by
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  rw [unmarked_eq h]
  exact tk_enterAtt ({ s with out := a.out } : S) _ _ _

theorem openLay_tk (P : LayPar) : Fn TK (openLay P) := fun s t h => by
  unfold openLay at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  rw [unmarked_eq h]
  exact tk_enterLay ({ s with out := a.out } : S) _ _ _

theorem openLayZero_tk (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn TK (openLayZero P fvs kCol) := fun s t h => by
  unfold openLayZero at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  rw [unmarked_eq h]
  exact tk_enterLay ({ s with out := a.out } : S) _ _ _

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the links' frames: "opened".** -/
theorem opened_tk {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, Fn TK f.opened := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact fun s t k => by cases k; exact tk_refl s
  · split at e
    · split at e
      · cases e
      · cases e
        exact openLayZero_tk _ _ _
    · split at e
      · cases e
      · cases e
        exact openAtt_tk _
      · cases e
        exact openLay_tk _

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.noTables_iff
#print axioms VerifiableInference.Desc.K1.TK.no
#print axioms VerifiableInference.Desc.K1.noTables_of
#print axioms VerifiableInference.Desc.K1.noTables_between
#print axioms VerifiableInference.Desc.K1.tk_putFork
#print axioms VerifiableInference.Desc.K1.tk_putTl
#print axioms VerifiableInference.Desc.K1.tk_hearLook
#print axioms VerifiableInference.Desc.K1.tk_openHead
#print axioms VerifiableInference.Desc.K1.tk_enterHead
#print axioms VerifiableInference.Desc.K1.theStated_tk
#print axioms VerifiableInference.Desc.K1.seatedClaims_tk
#print axioms VerifiableInference.Desc.K1.k7Of_tk
#print axioms VerifiableInference.Desc.K1.headFrontQ_tk
#print axioms VerifiableInference.Desc.K1.k7Block_tk
#print axioms VerifiableInference.Desc.K1.k2_tk
#print axioms VerifiableInference.Desc.K1.headOpenQ_tk
#print axioms VerifiableInference.Desc.K1.headOpened_tk
#print axioms VerifiableInference.Desc.K1.k2Is_tk
#print axioms VerifiableInference.Desc.K1.opened_tk
