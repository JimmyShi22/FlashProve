-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/SeatsTies.lean: THE SEATS' TIES FOR K4's BLOCK AND FOR THE LOOKUP ARGUMENT's
BLOCK ON THE CALLS, AT A LINK IN WHICH EACH STANDS IN THE DRIVER's SEATED FORM: behind the guard on
the reply and the guard on the mark, under another name and place (SeatedAs: to the letter the
clause of k04_sits_desc, Johnson/Road/K4/K04Sits.lean, which is not imported). What comes out: for
K4's block the sentence StatesAt at both of its runs of claims, at every state
(Johnson/Road/K4/InT/Statement.lean); for the lookup's block the four premises on its runs of the
structure ObjAsks (Johnson/Road/K4/Riders/ObjectsAtMeans.lean). Statements and proofs: a join.

  `hsame_reply`: the driver's test ProofFile.sameReply says yes at two states with one field out.
  `SeatedAs but b b' nm a`: b is b' in the seated form.
  `seated_claims`: then b's runs of claims are b''s, name by name, each behind the guard.
  `k4C_front`, `k4C_back`: K4's block at the one type of a claim states its two runs.
  **`st_at_seat`**: l.hear[2]? = some b, b the lot's block ProofFile.k4Block x in the seated form:
    StatesAt at "front" and at "back", at every state.
  **`runs_at_seat`**: l.hear[1]? = some b, b in the seated form a block b' that the lookups' make
    K3.theStated returns at the calls' place of a link without a caller's readers: "objects" and
    "guests" are found in K9.statesOfLink l 1, an ObjRun and a GuestRun.
No new argument: statesAt_guarded (Johnson/Road/K4/InT/SeatTie.lean), runs_at_guarded, stated_runs.
**Limits.** PREMISES: hb (the block's number among the link's hearing blocks) and he (the seated
form). For K4's block both are clauses of k04_sits_desc, at the proof file's description, in the
goals' scope, where the description's make returns: NOT CALLED HERE. For the lookup's block: THAT IT
STANDS ALONE IN THE SEATED FORM AT NUMBER 1 OF A LAYERS' LINK IS OTHER FILES' LAW: NOT READ AND
NOT CALLED HERE; if the driver joins a further block to it there, he is false and the tie wants
another form. l IS A LETTER: that the readers which a table's meaning takes at a segment
(K9.readersOfLink at some link) are made of THE VERY LINK in which the description's law finds b is
said by nobody here: one tie for whoever composes the meaning. Nothing on soundness. K04_law, the
law of K4's block itself, IS NOT PROVED.


-/
import Johnson.Road.K4.InT.SeatTie
import Johnson.Road.K4.Riders.ObjectsGuarded
import Johnson.Road.K4.Riders.ObjectsAtLot
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par blockAtC blockAtS block seatOwn part? setPart liftPart_run
  block_front block_back claimOf)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun guardRun runs_at_guarded stated_runs lit)
open OnBytes.Road.K4.InT (StatesAt statesAt_guarded lookup_mapSnd)
open VerifiableInference.Desc (Claim Block Link Place seatSame K9.statesOfLink K3.theStated
  K3.pieceAt K3.Readers)
open VerifiableInference.Desc.First (S)

/-- The driver's test on the reply says yes at two states with one field out. -/
theorem hsame_reply (t s : S) (h : s.out = t.out) : ProofFile.sameReply t s = true := by
  unfold ProofFile.sameReply
  rw [h]
  exact beq_self_eq_true _

/-- b is b' in the driver's seated form: the guard on the mark, another name and place, the guard on
the reply. -/
def SeatedAs (but : Place → Bool) (b b' : Block S Claim) (nm : String) (a : Place) : Prop :=
  b = Block.guarded ProofFile.sameReply but { { ProofFile.guardMark b' with name := nm } with place := a }

variable {but : Place → Bool} {b b' : Block S Claim} {nm : String} {a : Place}

/-- The seated block's runs of claims are b''s, name by name, each behind the guard. -/
theorem seated_claims (h : SeatedAs but b b' nm a) :
    b.claims = b'.claims.map fun c => (c.1, guardRun ProofFile.sameReply c.2) := by
  unfold SeatedAs at h
  subst h
  rfl

/-- K4's block at the one type of a claim states the run "front". -/
theorem k4C_front (p : Par) : ∃ runC, (blockAtC p).claims.lookup "front" = some runC := by
  have e := liftPart_run part? setPart (block seatOwn p) "front"
  rw [block_front] at e
  have k := lookup_mapSnd (α := ℕ → S → Except String (List Aff × S))
    (β := ℕ → S → Except String (List Claim × S))
    (fun r n s => (r n s).map fun y => (y.1.map claimOf, y.2)) (blockAtS p).claims "front" _ e
  exact ⟨_, k⟩

/-- And the run "back". -/
theorem k4C_back (p : Par) : ∃ runC, (blockAtC p).claims.lookup "back" = some runC := by
  have e := liftPart_run part? setPart (block seatOwn p) "back"
  rw [block_back] at e
  have k := lookup_mapSnd (α := ℕ → S → Except String (List Aff × S))
    (β := ℕ → S → Except String (List Claim × S))
    (fun r n s => (r n s).map fun y => (y.1.map claimOf, y.2)) (blockAtS p).claims "back" _ e
  exact ⟨_, k⟩

/-- **K4's block.** UNDER: block number 2 of the link's hearing blocks is b; b is the lot's block at
x in the seated form: at every state both runs of claims that the link states at number 2 answer as
K4's own block's at the parameters x.2 with k3Runs := true. -/
theorem st_at_seat {l : Link S Claim} {x : Bool × Par} (hb : l.hear[2]? = some b)
    (he : SeatedAs but b (ProofFile.k4Block x) nm a) (s : S) :
    StatesAt (K9.statesOfLink l) 2 { x.2 with k3Runs := true } "front" s ∧
      StatesAt (K9.statesOfLink l) 2 { x.2 with k3Runs := true } "back" s := by
  have hcl : b.claims = (blockAtC { x.2 with k3Runs := true }).claims.map fun c =>
      (c.1, fun n t => (c.2 n t).bind fun y => (seatSame ProofFile.sameReply t y.2).map fun _ => y) := by
    have h0 := seated_claims he
    exact h0
  obtain ⟨rF, hF⟩ := k4C_front { x.2 with k3Runs := true }
  obtain ⟨rB, hB⟩ := k4C_back { x.2 with k3Runs := true }
  exact ⟨statesAt_guarded hb hcl hsame_reply (Or.inl rfl) hF s,
    statesAt_guarded hb hcl hsame_reply (Or.inr rfl) hB s⟩

/-- **The lookup's block on the calls.** UNDER: block number 1 of the link's hearing blocks is b; b
is b' in the seated form; b' is what the lookups' make returns at the calls' place of link i; no
caller's readers are handed at i: both runs are found under their names, an ObjRun and a GuestRun.
-/
theorem runs_at_seat {l : Link S Claim} {readers : ℕ → Option (K3.Readers S)} {X : Verify.Public}
    {codes : Codes} {shape : Params.ReqShape} {a' : Place} {i : ℕ} (hb : l.hear[1]? = some b)
    (he : SeatedAs but b b' nm a) (h : K3.theStated lit readers X codes shape a' = some b')
    (hl : a'.link = some i) (hp : a'.piece = K3.pieceAt X i false) (hr : readers i = none) :
    ∃ runO runG,
      (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some ("objects", runO) ∧
      ObjRun runO ∧
      (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some ("guests", runG) ∧
      GuestRun runG :=
  runs_at_guarded hb (seated_claims he) hsame_reply (stated_runs h hl hp hr)

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.hsame_reply
#print axioms OnBytes.Road.K4.Riders.seated_claims
#print axioms OnBytes.Road.K4.Riders.k4C_front
#print axioms OnBytes.Road.K4.Riders.k4C_back
#print axioms OnBytes.Road.K4.Riders.st_at_seat
#print axioms OnBytes.Road.K4.Riders.runs_at_seat
