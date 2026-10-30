-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Keeps.lean (kind K9; the joint place with K10): THEOREMS: WHAT K9's
BLOCKS LEAVE AS IT IS. Frame laws: nothing on soundness.
First, general in the state: a block of K9's writes through its lens alone:
  drawAlone_writes · oneEquation_writes   a yes returns X.set t a for some part a.
  adds_writes · batch_writes              the like, behind the function of claims that it is handed.
Then at the state S of the proof file's first chain, through the lens atS, FOR ANY READER f OF THE
RECORD THAT READS BESIDE WHAT K9 AND THE CLOSING WRITE:
  Beside f       f does not see: the segment's book-keeping (putLink) · its ledger (putFork) · the
                 statement and the rows owed · the walk's record.
  beside_out · beside_tl · beside_funs · beside_tlFuns   four such readers: what the chain hands out
                 (S.out: the heard reply among it) · the smallness test's record (S.tl?) · the
                 tables with their weights (S.funs?; at a layers' segment: of what its own rounds
                 returned) · the smallness test's record's own list of tables (S.tl?.map (·.funs)).
  atS_set_keeps  f (atS.set s a) = f s.
  drawAlone_keeps · oneEquation_keeps · shut_keeps · closing_keeps · joint_keeps · closeOf_keeps
                 decide s rs gs = .ok s' → f s' = f s. NO PREMISE BUT Beside f.
  adds_keeps · batch_keeps   the same WHERE THE FUNCTION OF CLAIMS KEEPS f (a premise: the hearing
                 kinds' runs are left to these kinds' files).
  batch_front    a yes of the batching at s: the function of claims was called at atS.set s a, and
                 f (atS.set s a) = f s: so what holds of f where the runs begin holds at the
                 batching's front.
AT A REAL SEGMENT THE FUNCTION OF CLAIMS HOLDS K8's RUN OF EQUATIONS, WHICH WRITES THE SMALLNESS
TEST's RECORD: SO AT f := S.tl? THE PREMISE IS FALSE THERE, AND adds_keeps | batch_keeps CANNOT BE
CALLED AT THE BATCHING THAT RUNS: of that block, for that reader, this file gives the _writes
lemmas, atS_set_keeps and batch_front alone. For a reader that every run keeps they can be called;
which readers these are is left to the files of the runs' kinds.

-/
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.StateOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

variable {T Cl : Type}

theorem drawAlone_writes (X : Lens T) (p : Where) {t t' : T} {rs gs}
    (h : (drawAlone (Cl := Cl) X p).decide t rs gs = .ok t') : ∃ a, t' = X.set t a := by
  simp only [drawAlone] at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first
      | exact ⟨_, (Except.ok.inj h).symm⟩
      | cases h
  · cases h

theorem oneEquation_writes (X : Lens T) (p : Where) {t t' : T} {rs gs}
    (h : (oneEquation (Cl := Cl) X p).decide t rs gs = .ok t') : ∃ a, t' = X.set t a := by
  simp only [oneEquation, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | cases h

theorem adds_writes (X : Lens T) (p : Where) (piece : Nat) (what : String)
    (claims : T → Except String (List Claim × T)) {t t' : T} {rs gs}
    (h : (adds (Cl := Cl) X p piece what claims).decide t rs gs = .ok t') :
    ∃ x a, claims t = .ok x ∧ t' = X.set x.2 a := by
  simp only [adds, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | exact ⟨_, _, by assumption, (Except.ok.inj h).symm⟩
    | cases h

theorem batch_writes (X : Lens T) (p : Where) (claims : T → Except String (List Claim × T))
    {t t' : T} {rs gs} (h : (batch X p claims).decide t rs gs = .ok t') :
    ∃ a x b, claims (X.set t a) = .ok x ∧ t' = X.set x.2 b := by
  simp only [batch, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i t₁ h₁
    obtain ⟨a, rfl⟩ := drawAlone_writes X p h₁
    obtain ⟨x, b, hx, hb⟩ := adds_writes X p p.piece _ claims h
    exact ⟨a, x, b, hx, hb⟩

/-! ## At S -/

/-- A reader of the record that does not see what K9's blocks and the closing write. Its four fields
are cut to these texts as they stand: the four ways in which they write. -/
structure Beside {α : Type} (f : S → α) : Prop where
  link : ∀ (s : S) (L : LinkCtx), f (s.putLink L) = f s
  fork : ∀ (s : S) (F : Fork), f (s.putFork F) = f s
  rows : ∀ (s : S) (st : Statement) (owed : Option Nat),
    f { s with st := st, rowsOwed := owed } = f s
  walk : ∀ (s : S) (c : ChainCheck), f { s with check := c } = f s

theorem tl_putFork (s : S) (F : Fork) : (s.putFork F).tl? = s.tl? := by
  unfold S.putFork
  split
  · rename_i a h
    simp [S.tl?, h]
  · rename_i a h
    simp [S.tl?, h]
  · rename_i a h
    split
    · rename_i ho
      simp [S.tl?, h, ho]
    · rfl
  · rfl

theorem tl_putLink (s : S) (L : LinkCtx) : (s.putLink L).tl? = s.tl? := by
  unfold S.putLink
  split
  · rename_i a h
    simp [S.tl?, h]
  · rename_i a h
    simp [S.tl?, h]
  · rename_i a h
    split
    · rename_i ho
      simp [S.tl?, h, ho]
    · rfl
  · rfl

theorem funs_putFork (s : S) (F : Fork) : (s.putFork F).funs? = s.funs? := by
  unfold S.putFork
  split
  · rename_i a h
    simp [S.funs?, h]
  · rename_i a h
    simp [S.funs?, h]
  · rename_i a h
    split
    · rename_i ho
      simp [S.funs?, h, ho]
    · rfl
  · rfl

theorem funs_putLink (s : S) (L : LinkCtx) : (s.putLink L).funs? = s.funs? := by
  unfold S.putLink
  split
  · rename_i a h
    simp [S.funs?, h]
  · rename_i a h
    simp [S.funs?, h]
  · rename_i a h
    split
    · rename_i ho
      simp [S.funs?, h, ho]
    · rfl
  · rfl

theorem beside_out : Beside (·.out) :=
  ⟨S.out_putLink, S.out_putFork, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem beside_tl : Beside (·.tl?) :=
  ⟨tl_putLink, tl_putFork, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem beside_funs : Beside (·.funs?) :=
  ⟨funs_putLink, funs_putFork, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- A reader that goes through such a one is such a one. -/
theorem Beside.map {α β : Type} {f : S → α} (h : Beside f) (g : α → β) : Beside fun s => g (f s) :=
  ⟨fun s L => congrArg g (h.link s L), fun s F => congrArg g (h.fork s F),
   fun s st o => congrArg g (h.rows s st o), fun s c => congrArg g (h.walk s c)⟩

theorem beside_tlFuns : Beside fun s => s.tl?.map (·.funs) := beside_tl.map _

variable {α : Type} {f : S → α}

theorem atS_set_keeps (hf : Beside f) (s : S) (a : Part) : f (atS.set s a) = f s :=
  (hf.rows _ _ _).trans ((hf.fork _ _).trans (hf.link _ _))

theorem drawAlone_keeps (hf : Beside f) (p : Where) {s s' : S} {rs gs}
    (h : (drawAlone (Cl := Cl) atS p).decide s rs gs = .ok s') : f s' = f s := by
  obtain ⟨a, rfl⟩ := drawAlone_writes atS p h
  exact atS_set_keeps hf s a

theorem oneEquation_keeps (hf : Beside f) (p : Where) {s s' : S} {rs gs}
    (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok s') : f s' = f s := by
  obtain ⟨a, rfl⟩ := oneEquation_writes atS p h
  exact atS_set_keeps hf s a

theorem adds_keeps (hf : Beside f) (p : Where) (piece : Nat) (what : String)
    (claims : S → Except String (List Claim × S))
    (hc : ∀ s x, claims s = .ok x → f x.2 = f s) {s s' : S} {rs gs}
    (h : (adds (Cl := Cl) atS p piece what claims).decide s rs gs = .ok s') : f s' = f s := by
  obtain ⟨x, a, hx, rfl⟩ := adds_writes atS p piece what claims h
  exact (atS_set_keeps hf _ a).trans (hc s x hx)

theorem batch_keeps (hf : Beside f) (p : Where) (claims : S → Except String (List Claim × S))
    (hc : ∀ s x, claims s = .ok x → f x.2 = f s) {s s' : S} {rs gs}
    (h : (batch atS p claims).decide s rs gs = .ok s') : f s' = f s := by
  obtain ⟨a, x, b, hx, rfl⟩ := batch_writes atS p claims h
  exact (atS_set_keeps hf _ b).trans ((hc _ x hx).trans (atS_set_keeps hf s a))

theorem batch_front (hf : Beside f) (p : Where) (claims : S → Except String (List Claim × S))
    {s s' : S} {rs gs} (h : (batch atS p claims).decide s rs gs = .ok s') :
    ∃ a x, claims (atS.set s a) = .ok x ∧ f (atS.set s a) = f s := by
  obtain ⟨a, x, _, hx, _⟩ := batch_writes atS p claims h
  exact ⟨a, x, hx, atS_set_keeps hf s a⟩

theorem shut_keeps (hf : Beside f) (p : Where) (piece : Nat) {s s' : S} {rs gs}
    (h : (shut (Cl := Cl) p piece).decide s rs gs = .ok s') : f s' = f s := by
  simp only [shut, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rw [← Except.ok.inj h]
    exact hf.link s _

theorem putLive_keeps (hf : Beside f) (s : S) (c : ChainCheck) : f (s.putLive c) = f s := by
  simp only [S.putLive]
  split
  · exact hf.link s _
  · exact hf.walk s c

theorem putRec_keeps (hf : Beside f) (s : S) (r : First.Close.Rec) : f (putRec s r) = f s :=
  (hf.rows _ _ _).trans (putLive_keeps hf s _)

theorem closing_keeps (hf : Beside f) (P : Par) {s s' : S} {rs gs}
    (h : (closing (Cl := Cl) P).decide s rs gs = .ok s') : f s' = f s := by
  simp only [closing, Block.lift, Except.map] at h
  split at h
  · cases h
  · rw [← Except.ok.inj h]
    exact putRec_keeps hf s _

theorem joint_keeps (hf : Beside f) (p : Where) (P : Par) {s s' : S} {rs gs}
    (h : (joint (Cl := Cl) p P).decide s rs gs = .ok s') : f s' = f s := by
  simp only [joint, Block.andThen, Except.bind] at h
  split at h
  · cases h
  · rename_i s₂ h₂
    split at h₂
    · cases h₂
    · rename_i s₁ h₁
      exact (shut_keeps hf p _ h).trans
        ((closing_keeps hf P h₂).trans (oneEquation_keeps hf p h₁))

theorem closeOf_keeps (hf : Beside f) (p : Where) (P : Par) {b : Block S Cl}
    (hb : b ∈ closeOf p P) {s s' : S} {rs gs} (h : b.decide s rs gs = .ok s') : f s' = f s := by
  simp only [closeOf, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact oneEquation_keeps (Cl := Cl) (rs := rs) (gs := gs) hf p h
  · exact closing_keeps hf P h
  · exact shut_keeps hf p _ h

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.beside_out
#print axioms VerifiableInference.Desc.K9.beside_tl
#print axioms VerifiableInference.Desc.K9.beside_funs
#print axioms VerifiableInference.Desc.K9.beside_tlFuns
#print axioms VerifiableInference.Desc.K9.atS_set_keeps
#print axioms VerifiableInference.Desc.K9.drawAlone_keeps
#print axioms VerifiableInference.Desc.K9.oneEquation_keeps
#print axioms VerifiableInference.Desc.K9.adds_keeps
#print axioms VerifiableInference.Desc.K9.batch_keeps
#print axioms VerifiableInference.Desc.K9.batch_front
#print axioms VerifiableInference.Desc.K9.shut_keeps
#print axioms VerifiableInference.Desc.K9.closing_keeps
#print axioms VerifiableInference.Desc.K9.joint_keeps
#print axioms VerifiableInference.Desc.K9.closeOf_keeps
