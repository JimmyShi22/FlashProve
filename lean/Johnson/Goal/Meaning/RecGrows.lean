-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecGrows.lean: "the statement only grows" (Johnson/Desc/Grows.lean;
Johnson/Desc/StatementGrows.lean's owed premise) at the link's frame's first steps, the quiet steps
behind the reads, the marking of a segment and kind K9's blocks, at the first chain's record.

Two forms, the stronger that each text bears.
  QUIET (Johnson/Goal/Meaning/RecQuiet.lean: the statement stays; no new copy of the frame comes in;
    so RecAll is handed on and every reflexive relation on statements is kept): layFront_quiet,
    openAtt_enters, openLay_enters, openLayZero_enters (over enterLay_enters, enterAtt_enters),
    still_putLink, shut_still, layers_quiet, headReads_quiet, readsAtSO_quiet, readsAtO_quiet.
  FOR EVERY RELATION THAT THE GROUND's PLAIN FUNCTIONS KEEP (GroundKeeps R,
    Johnson/Desc/GroundKeeps.lean), read at the record's statement (ByS R): drawAlone_by (a
    reflexive R is enough), adds_by (for a function of claims that keeps it), batch_by,
    oneEquation_by (over takeN_by, asRow_by, door_by).
NOT TYPED HERE: the closing of a link (its batching begins a test, which is no field of
GroundKeeps); the clearing of a link (it writes one message's ledger by itself, through no plain
function of the ground); the head's and the finish's fronts.
Not claimed: that the other kinds' runs of claims keep a relation.
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them yet. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecK9
import Johnson.Goal.Meaning.RecReads
import Johnson.Goal.Meaning.RecReadsAtt
import Johnson.Goal.Meaning.RecQuiet
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundKeeps By groundKeeps_grows)
open VerifiableInference.Desc.K9
open Johnson.Desc.First.Walk

variable {Cl : Type} {R : Statement → Statement → Prop}

/-- The relation R, read at the record's statement. -/
abbrev ByS (R : Statement → Statement → Prop) : S → S → Prop := By R fun s : S => s.st

/-! ## Quiet steps -/

theorem layFront_quiet (l : Nat) : Fn Quiet (layFront l) := fun s t h => by
  rw [(Law.layFront_ok h).1]
  exact quiet_refl s

theorem unmarked_eq {s s' : S} (h : s.unmarked = .ok s') : s' = s :=
  ((S.unmarked_ok _ _).1 h).1.symm

/-- Entering a link with the walk's own state of the calls brings no new copy. -/
theorem enterLay_enters (s : S) (o : Proof.LinksResult) {L : LinkCtx} (hL : L.check = s.check)
    (F : Fork) (tl : HTailF2) : Enters s (S.enterLay { s with out := o } L F tl) := by
  unfold S.enterLay
  split
  · refine ⟨rfl, fun f hf => ?_, rfl, rfl⟩
    have e : f = s.check.frame := by
      simpa [framesIn, hL] using hf
    rw [e]
    exact List.mem_cons_self
  · unfold S.mark
    split
    · exact ⟨rfl, fun _ h => h, rfl, rfl⟩
    · exact ⟨rfl, fun _ h => h, rfl, rfl⟩

theorem enterAtt_enters (s : S) (o : Proof.LinksResult) {L : LinkCtx} (hL : L.check = s.check)
    (F : Fork) (tl : HTailF2) : Enters s (S.enterAtt { s with out := o } L F tl) := by
  unfold S.enterAtt
  split
  · refine ⟨rfl, fun f hf => ?_, rfl, rfl⟩
    have e : f = s.check.frame := by
      simpa [framesIn, hL] using hf
    rw [e]
    exact List.mem_cons_self
  · unfold S.mark
    split
    · exact ⟨rfl, fun _ h => h, rfl, rfl⟩
    · exact ⟨rfl, fun _ h => h, rfl, rfl⟩

theorem openAtt_enters (P : AttPar) : Fn Enters (openAtt P) := fun s t h => by
  obtain ⟨hB, -, -, -, hl, -⟩ := Law.openAtt_ok h
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := unmarked_eq h
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterAtt_ok (L := a.L) (F := a.F) (tl := a.tl) hB').1
  rw [← e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  rw [e]
  exact enterAtt_enters s a.out eL _ _

theorem openLay_enters (P : LayPar) : Fn Enters (openLay P) := fun s t h => by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLay_ok h
  unfold openLay at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := unmarked_eq h
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [← e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  rw [e]
  exact enterLay_enters s a.out eL _ _

theorem openLayZero_enters (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn Enters (openLayZero P fvs kCol) := fun s t h => by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLayZero_ok h
  unfold openLayZero at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := unmarked_eq h
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [← e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  rw [e]
  exact enterLay_enters s a.out eL _ _

/-- Laying a link's record whose frame, rows, number and list of arrays are the open link's brings
no new copy and leaves what ctxOf reads. -/
theorem still_putLink {s : S} {L L' : LinkCtx} (h : s.link? = some L)
    (e : L'.check.frame = L.check.frame) (e1 : L'.check.rows = L.check.rows)
    (e2 : L'.link = L.link) (e3 : L'.arrayOf = L.arrayOf) : Still s (s.putLink L') := by
  unfold S.link? at h
  unfold S.putLink
  split
  · rename_i a ha
    rw [ha] at h
    obtain rfl := Option.some.inj h
    exact ⟨⟨rfl, fun f hf => by simpa [framesIn, ha, e] using hf, rfl, rfl⟩,
      by first | rfl | simp [ctxOf, *]⟩
  · rename_i a ha
    rw [ha] at h
    obtain rfl := Option.some.inj h
    exact ⟨⟨rfl, fun f hf => by simpa [framesIn, ha, e] using hf, rfl, rfl⟩,
      by first | rfl | simp [ctxOf, *]⟩
  · rename_i a ha
    rw [ha] at h
    split
    · rename_i ho
      have h' : (if a.opened = true then some a.L else none) = some L := h
      rw [if_pos ho] at h'
      obtain rfl := Option.some.inj h'
      exact ⟨⟨rfl, fun f hf => by simpa [framesIn, ha, e] using hf, rfl, rfl⟩,
      by first | rfl | simp [ctxOf, *]⟩
    · exact (quiet_refl s).still
  · exact (quiet_refl s).still

/-- K9's marking behind the closing: IT WRITES THE OPEN LINK's STATE OF THE CALLS (no link is under
way): so it is Still, not Quiet. -/
theorem shut_still (p : Where) (piece : Nat) : Whole Still (shut (Cl := Cl) p piece) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨L, hL, h⟩ := bindE h
  cases h
  exact still_putLink (there_some hL) rfl rfl rfl rfl

theorem layers_quiet (P : K8.ReadsQuiet.PG) : Whole Quiet (K8.ReadsQuiet.layers P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, own, tl', ha, -, -, rfl⟩ := K8.ReadsQuiet.layers_ok h
  refine ⟨⟨rfl, fun f hm => ?_, rfl, rfl⟩,
    by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
  unfold framesIn at hm ⊢
  rw [ha]
  exact hm

theorem headReads_quiet (P : K8.ReadsQuiet.PH) : Whole Quiet (K8.ReadsQuiet.head P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, cov, x, t, tl', ha, -, -, -, -, -, rfl⟩ := K8.ReadsQuiet.head_ok h
  refine ⟨⟨rfl, fun f hm => ?_, rfl, rfl⟩,
    by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
  unfold framesIn at hm ⊢
  rw [ha]
  exact hm

theorem readsAtSO_quiet (A : Attention.Plan) : Fn Quiet (Att.readsAtSO A) := fun s s' h => by
  obtain ⟨a, t, tl, ha, rfl⟩ := readsAtSO_eq h
  refine ⟨⟨rfl, fun f hm => ?_, rfl, rfl⟩,
    by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
  unfold framesIn at hm ⊢
  rw [ha]
  exact hm

theorem readsAtO_quiet {W : Verify.Public} {l g : Nat} {b : Block S Cl}
    (h : Att.readsAtO W l g = some b) : Whole Quiet b := by
  unfold Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨fun s _ _ s' e => readsAtSO_quiet A s s' e, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

/-! ## K9's blocks -/

/-- The statement that the lens lays back. -/
theorem atS_set_st (s : S) (p : K9.Part) : (atS.set s p).st = p.d.st := rfl

theorem drawAlone_by (hr : ∀ T, R T T) (p : Where) :
    Decides (ByS R) (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨chi, _, h⟩ := bindE h
    obtain ⟨o, ho, h⟩ := bindE h
    cases h
    show R s.st q.d.st
    rw [(atS_get (there_some hq)).2]
    exact hr _
  · cases h

theorem adds_by (p : Where) (piece : Nat) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Decides (ByS R) (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, hx, h⟩ := bindE h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨F, _, h⟩ := bindE h
  cases h
  show R s.st q.d.st
  rw [(atS_get (there_some hq)).2]
  exact hcl s x hx

theorem batch_by (H : GroundKeeps R) (p : Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Decides (ByS R) (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  exact H.trans (drawAlone_by H.refl p s rs gs t₁ h1)
    (adds_by p p.piece "the segment's" hcl t₁ [] [] s' h)

theorem takeN_by {X : Type} (H : GroundKeeps R) (o : Nat) : ∀ (n : Nat) (d : St X)
    (acc : List Nat) (y : List Nat × St X), takeN o n d acc = .ok y → R d.st y.2.st
  | 0, d, acc, y, h => by
    cases h
    exact H.refl _
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact H.trans (H.takeMask d x.2 o x.1 (there_some hx)) (takeN_by H o n x.2 _ y h)

theorem asRow_by {X : Type} (H : GroundKeeps R) {Rw : ReqRows} {f : ReqFrame} {q : Equation}
    {d : St X} {y : Row × St X} (h : asRow Rw f q d = .ok y) : R d.st y.2.st := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    exact H.refl _
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_by H o _ d [] x hx

theorem door_by {X : Type} (H : GroundKeeps R) {owed : RowsOwed} {laid : Option Nat}
    {L : LinkCtx} {F : Fork} {d : St X} {o : Out X} (h : door owed laid L F d = .ok o) :
    R d.st o.d.st := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact H.trans (asRow_by H hy) (H.addRow y.2 d' _ y.1 (there_some hd))

theorem oneEquation_by (H : GroundKeeps R) (p : Where) :
    Decides (ByS R) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  show R s.st o.d.st
  rw [← (atS_get (there_some hq)).2]
  exact door_by H ho

#print axioms openLay_enters
#print axioms shut_still
#print axioms readsAtO_quiet
#print axioms batch_by
#print axioms oneEquation_by

end Meaning.K2
