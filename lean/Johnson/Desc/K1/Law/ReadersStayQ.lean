-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersStayQ.lean: OVER AN ACCEPT OF EITHER LATER SUB-PROTOCOL OF KIND K1 (a
segment's digits' place: a commitment; its reads' place: a commitment with the reads' quiet step
joined behind) THE STATE BEHIND PARTS FROM THE STATE IN FRONT IN NOTHING BUT WHAT Q.restOf TAKES OFF
(Johnson/Desc/K1/Law/RestQDef.lean). K1's HALF, PROVED; and the members of Q.Respects by the form of
the run that Johnson/Desc/K1/Law/ReadersStayAt.lean has at the narrower cut. Statements with their
proofs.

Main names (namespace VerifiableInference.Desc.K1.Q):
  QuietQ q            an accept of q leaves the rest. quietQ_layers | _head | _att | _blockAt |
                      _readsQuietAt | _orLoud: **the reads' quiet step, at each sort of segment.**
  LaterAlike B        an accept of B, on any rounds, leaves the rest. laterAlike_commitAtS |
                      _laterAt | _joined | _k1Reads: **both later sub-protocols.**
  respects_readRun, respects_guestsNone, respects_objectsBy, respects_objectsCalls;
  sameReply_alike     the lookup's "objects" and "guests"; the first chain's seat's test, for
                      respects_guarded.
What is not claimed. Q.Respects of another run. That a real chain's link states these runs. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RestQDef
import Johnson.Desc.K1.Law.ReadersStayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.Q
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Here Pub PubData pubAll)
open VerifiableInference.Desc.K9 (Read Readers RunOf Fn readerOf lateOf ownRow LinkHoles
  statesOfLink readersOfLink readRun objectsBy guestsNone)
open OnBytes.Model.Stages (LinkH)

variable {Cl : Type}

/-! ## The reads' quiet step leaves the rest -/

/-- An accept of q leaves the rest. -/
def QuietQ (q : Block S Cl) : Prop := ∀ s s' rs gs, q.decide s rs gs = .ok s' → RestAlike s s'

theorem quietQ_layers (P : K8.ReadsQuiet.PG) : QuietQ (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  simp [RestAlike, restOf, blank, blankHere, K1.restOf, hereRest, ha]

theorem quietQ_head (P : K8.ReadsQuiet.PH) : QuietQ (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  simp [RestAlike, restOf, blank, blankHere, K1.restOf, hereRest, ha]

theorem quietQ_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietQ q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  simp [RestAlike, restOf, blank, blankHere, K1.restOf, hereRest, ha]

theorem quietQ_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietQ q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact quietQ_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact quietQ_head _
    · cases h

theorem quietQ_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (h : ProofFile.readsQuietAt G l X piece = some q) : QuietQ q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact quietQ_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact quietQ_blockAt h
    · rw [if_neg h2] at h
      cases h

/-- The quiet step as the lot joins it (where none could be made, the refuser never accepts). -/
theorem quietQ_orLoud (name : String) (p : Place) (what : String) (G : ProofFile.Ground) (l : Nat)
    (X : LinkH) (piece : Nat) :
    QuietQ (ProofFile.orLoud name p what (ProofFile.readsQuietAt G l X piece)) := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact quietQ_readsQuietAt l X _ q hq

/-! ## Both later sub-protocols leave the rest -/

/-- An accept of B, on any rounds, leaves the rest. -/
def LaterAlike (B : Block S Cl) : Prop := ∀ s s' rs gs, B.decide s rs gs = .ok s' → RestAlike s s'

theorem laterAlike_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterAlike (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs h => alike_of (commitAtS_alike P link moment arrays s s' rs gs h)

/-- **A segment's digits' place.** -/
theorem laterAlike_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    LaterAlike (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterAlike_commitAtS _ _ _ _

theorem laterAlike_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietQ q) :
    LaterAlike (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h
  have h' : ((commitAtS P link moment arrays : Block S Cl).decide s
      (rs.take (commitAtS P link moment arrays : Block S Cl).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl).openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS P link moment arrays : Block S Cl).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  exact (laterAlike_commitAtS P link moment arrays _ _ _ _ h1).trans (hq _ _ _ _ h2)

/-- **A segment's reads' place.** -/
theorem laterAlike_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) : LaterAlike (IM.k1Reads Z G l X pr reads) :=
  laterAlike_joined _ _ _ _ _ _ (quietQ_orLoud _ _ _ G l X _)

/-! ## Members, by the form of the run -/

/-- A run that reads the state, lays claims and leaves the state. -/
theorem respects_readRun (read : S → Except String (List Claim))
    (h : ∀ s s', RestAlike s s' → read s' = read s) : Respects (readRun read) :=
  respects_read read h

/-- K3's "guests" where no guest is handed. -/
theorem respects_guestsNone : Respects guestsNone := respects_readRun _ fun _ _ _ => rfl

/-- The lookup's run "objects", general in where what was heard is read. -/
theorem respects_objectsBy (heard : S → Option Forest.Heard)
    (h : ∀ s s', RestAlike s s' → heard s' = heard s) : Respects (objectsBy heard) := by
  intro s s' hA cl t e
  unfold objectsBy at e ⊢
  obtain ⟨F, hF, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨g, hg, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  cases hF0 : s.fork? with
  | none => rw [hF0] at hF; cases hF
  | some F₀ =>
    rw [hF0] at hF
    obtain rfl : F₀ = F := Except.ok.inj hF
    obtain ⟨F', g1, g2⟩ := hA.fork hF0
    refine ⟨s'.putFork (F'.paid g.owedObjects), ?_, hA.putFork (paid_rest g2.symm _)⟩
    rw [g1, h s s' hA]
    show (Except.ok F' : Except String Fork).bind _ = _
    simp only [Except.bind]
    rw [hg]
    rfl

/-- **K3's "objects" at the lookup on the calls.** -/
theorem respects_objectsCalls : Respects K9.objectsCalls :=
  respects_objectsBy _ fun _ _ hA => hA.lookHeard.symm

/-- The first chain's seat's test: "the two states hold the same reply". -/
theorem sameReply_alike (s s' t t' : S) (h : RestAlike s s') (k : RestAlike t t') :
    ProofFile.sameReply s' t' = ProofFile.sameReply s t := by
  unfold ProofFile.sameReply
  rw [h.out, k.out]

end VerifiableInference.Desc.K1.Q

#print axioms VerifiableInference.Desc.K1.Q.quietQ_layers
#print axioms VerifiableInference.Desc.K1.Q.quietQ_head
#print axioms VerifiableInference.Desc.K1.Q.quietQ_att
#print axioms VerifiableInference.Desc.K1.Q.quietQ_orLoud
#print axioms VerifiableInference.Desc.K1.Q.laterAlike_commitAtS
#print axioms VerifiableInference.Desc.K1.Q.laterAlike_laterAt
#print axioms VerifiableInference.Desc.K1.Q.laterAlike_k1Reads
#print axioms VerifiableInference.Desc.K1.Q.respects_guestsNone
#print axioms VerifiableInference.Desc.K1.Q.respects_objectsBy
#print axioms VerifiableInference.Desc.K1.Q.respects_objectsCalls
#print axioms VerifiableInference.Desc.K1.Q.sameReply_alike
