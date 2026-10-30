-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Cut.lean: THE PROOF FILE's FIRST CHAIN CUT IN SEGMENTS: nFrameA
(Johnson/Desc/First/Link/RowsRun.lean:123-159) is its segments one behind the other. Definitions and
theorems. A law file; no running text imports it.
  `closedOf z g gs`   nFrameA's own «closed» (:154-156): the group that a segment hands to the next.
  `segA`          A SECOND TEXT of nFrameA's lines at g :: gs, without the last (the call of
                  itself).
  `framePieces`   the segments as a list; it ends behind a segment without a link, as nFrameA does.
  `nFrameA_seq`   nFrameA … = seqN (framePieces …).
  `proof0R`, `proof0Tail`, `proof0R_seq` callsFrom's routine at «proof 0» (:188-194), by name, as
  its pieces.
  `fr_framePieces`, `fr_proof0Tail`   each piece reads no round.
Limits. segA will have to be turned with nFrameA; nFrameA_seq would then fail. No closed fact is
here. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem seqN_append : ∀ (a b : List (N Unit)), seqN (a ++ b) = seqN a >>= fun _ => seqN b
  | [], b => by
    simp only [List.nil_append, seqN, pure_bind]
  | x :: a, b => by
    simp only [List.cons_append, seqN, bind_assoc, seqN_append a b]

theorem seqN_one (x : N Unit) : seqN [x] = x := by
  simp only [seqN, bind_pure_unit]

theorem ite_bindN {α β : Type} (c : Prop) [Decidable c] (a b : N α) (f : α → N β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- The group that a segment hands to the next. -/
def closedOf (z : ProofSized) (g : ReqGroup) (gs : List ReqGroup) : GroupSize :=
  { z.link.group with
    k := g.k, h := g.h,
    slots := 2 ^ clog2 (1 + sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))) }

/-- One segment: nFrameA's lines at g :: gs, without the call of itself. -/
def segA (A : Nat → Arm) (z : ProofSized) (l : Nat) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (open_ : List Nat) (before : GroupSize) : N Unit := do
  let S := z.request
  let link := links.head?
  let msgs := (link.map (·.messages)).getD []
  let members : List OracleNotice :=
    (if 0 < l then [⟨g.target.shape, g.target.leafClass⟩] else []) ++
    (keptOf g).map (fun k => ⟨k.shape, k.leafClass⟩) ++
    (msgs.filter fun m => m.moment == 0).map (fun m => ⟨m.shape, m.leafClass⟩) ++
    [foldMaskNotice (ioppFoldShape ⟨S.code, S.maskCode, g.k, g.h⟩ {})]
  let sampleRows := sumT (members.map (·.shape.answers))
  let sent := if l == 0 then members ++ S.atStart else members
  if (link.map (·.plain)).getD 0 != 0 then
    note (.scalars ((link.map (·.plain)).getD 0))
    note .reply
  nReqSend z.codes sent (if link.isSome then z.link.group else z.last.first) z.batch.own.first
    (if l == 0 then S.atStart.length else 0) (l == 0)
  let carried ← if 0 < l then do
      let t ← noteV (.loc before) (planLoc before)
      pure (1 + sumT ((keptOf g).map (·.shape.answers)) +
        t * (3 + sumT ((keptOf g).map (·.shape.mainRows))))
    else pure 0
  match link with
  | none => nIopp z.last.stages (carried + sampleRows) 0 S.choice.masksRide
  | some _ =>
    nArm (A l) 0
    note (.scope .request)
    let moments := (msgs.getLast?.map (·.moment + 1)).getD 0
    let more ← nMomentsA A z l msgs (moments - 1) 1
    note (.bat [closedOf z g gs] (open_.headD 0 + carried + sampleRows + more))
    note (.fold (closedOf z g gs) 0)

/-- The segments as a list. -/
def framePieces (A : Nat → Arm) (z : ProofSized) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → List (N Unit)
  | _, [], _, _, _ => []
  | l, g :: gs, links, open_, before =>
    segA A z l g gs links open_ before ::
      (match links.head? with
       | none => []
       | some _ => framePieces A z (l + 1) gs (links.drop 1) (open_.drop 1) (closedOf z g gs))

/-- **The frame is its segments, one behind the other.** -/
theorem nFrameA_seq (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    nFrameA A z l gs links open_ before = seqN (framePieces A z l gs links open_ before)
  | [], _, _, _, _ => by
    unfold nFrameA framePieces
    rfl
  | g :: gs, l, links, open_, before => by
    have ih := nFrameA_seq A z gs (l + 1) (links.drop 1) (open_.drop 1) (closedOf z g gs)
    unfold framePieces
    unfold seqN
    unfold nFrameA segA
    cases links.head? with
    | none =>
      simp only [seqN, bind_assoc, bind_pure_unit, ite_bindN, pure_bind]
      try rfl
    | some lk =>
      simp only [← ih, bind_assoc, ite_bindN, pure_bind]
      try rfl

theorem fr_segA (A : Nat → Arm) (z : ProofSized) (l : Nat) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (open_ : List Nat) (before : GroupSize) :
    Fr (segA A z l g gs links open_ before) := by
  unfold segA
  cases links.head? with
  | none => frn
  | some lk => frn

theorem fr_framePieces (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    ∀ x ∈ framePieces A z l gs links open_ before, Fr x
  | [], _, _, _, _, x, hx => by
    unfold framePieces at hx
    cases hx
  | g :: gs, l, links, open_, before, x, hx => by
    unfold framePieces at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact fr_segA A z l g gs links open_ before
    · cases h : links.head? with
      | none =>
        rw [h] at hx
        cases hx
      | some lk =>
        rw [h] at hx
        exact fr_framePieces A z gs _ _ _ _ x hx

/-- callsFrom's routine at «proof 0», by name. -/
def proof0R (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    N Unit := do
  nFrameA A c.sized.proof 0 (reqGroups c.sized.proof.request).toList
    c.sized.proof.request.link openRows
    c.sized.proof.link.group
  note (.scope .request)
  if 1 < pendingRows then note (.batt pendingRows c.sized.proof.batch.shape.kCol)
  nLinFirst c.sized.proof.codes c.sized.proof.batch
  note .seal

/-- What stands behind the frame in it. -/
def proof0Tail (c : Configured) (pendingRows : Nat) : N Unit := do
  note (.scope .request)
  if 1 < pendingRows then note (.batt pendingRows c.sized.proof.batch.shape.kCol)
  nLinFirst c.sized.proof.codes c.sized.proof.batch
  note .seal

/-- The pieces of «proof 0». -/
def proof0Pieces (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    List (N Unit) :=
  framePieces A c.sized.proof 0 (reqGroups c.sized.proof.request).toList c.sized.proof.request.link
    openRows c.sized.proof.link.group ++ [proof0Tail c pendingRows]

theorem proof0R_seq (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    proof0R c openRows pendingRows A = seqN (proof0Pieces c openRows pendingRows A) := by
  unfold proof0R proof0Pieces
  rw [seqN_append, seqN_one, nFrameA_seq]
  rfl

theorem fr_proof0Tail (c : Configured) (pendingRows : Nat) : Fr (proof0Tail c pendingRows) := by
  have := fr_nLinFirst c.sized.proof.codes c.sized.proof.batch
  unfold proof0Tail
  frn

theorem fr_proof0Pieces (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    ∀ x ∈ proof0Pieces c openRows pendingRows A, Fr x := by
  intro x hx
  unfold proof0Pieces at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact fr_framePieces _ _ _ _ _ _ _ x hx
  · rcases List.mem_singleton.1 hx with rfl
    exact fr_proof0Tail c pendingRows

theorem faith_proof0R (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Faith (proof0R c openRows pendingRows A) := by
  have := faith_nFrameA A c.sized.proof (reqGroups c.sized.proof.request).toList 0
    c.sized.proof.request.link openRows c.sized.proof.link.group
  have := faith_nLinFirst c.sized.proof.codes c.sized.proof.batch
  unfold proof0R
  fth

theorem fr_proof0R (c : Configured) (openRows : List Nat) (pendingRows : Nat) (A : Nat → Arm) :
    Fr (proof0R c openRows pendingRows A) := by
  rw [proof0R_seq]
  exact fr_seqN (fr_proof0Pieces c openRows pendingRows A)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.nFrameA_seq
#print axioms VerifiableInference.Desc.LinkJoin.proof0R_seq
#print axioms VerifiableInference.Desc.LinkJoin.fr_proof0Pieces
#print axioms VerifiableInference.Desc.LinkJoin.faith_proof0R
#print axioms VerifiableInference.Desc.LinkJoin.fr_proof0R
