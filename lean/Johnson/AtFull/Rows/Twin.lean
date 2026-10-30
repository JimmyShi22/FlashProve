-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Twin.lean: TWO LIGHT TWINS, TO READ WHAT THE TWO LONG CHAINS' CALLS
SAY OF SAMPLES. packFrom reads of a chain its file, its number and what its calls say of samples
(`Like`, Law/RowsNoArms.lean). The arms of «proof 0» and the lookups of «key 0» note no call with a
sample (nArm_quiet · nLookup_quiet). So the same routines with «pure ()» in the arms' and in the
lookups' place say the same of samples, wherever both return.
Definitions and theorems. A law file; no running text imports it.
  `nMomentsL`, `nFrameL`   SECOND TEXTS of nMomentsA | nFrameA (RowsRun.lean:110-159) with «pure ()»
                           for «nArm (A l) …».
  `proof0L`       callsFrom's routine at «proof 0» over nFrameL.
  `nRangesL`, `key0L`   SECOND TEXTS of nRanges (Calls.lean:372-380) and of «key 0»'s routine, with
                  «pure ()» for the loop of the lookups.
  `proof0L_sim`, `key0L_sim`   Sim Any (the real routine) (its twin).   `fr_proof0L`, `fr_key0L`.
Limits. THE TWINS ARE NO PART OF THE PROTOCOL AND WRITE OTHER PLANS THAN THE PLANNER's: they serve
to read samples alone.
A conditional on returns. No closed fact is here. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.TableC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- nMomentsA with «pure ()» in the arm's place. -/
def nMomentsL (z : ProofSized) (msgs : List ReqMessage) : Nat → Nat → N Nat
  | 0, _ => pure 0
  | fuel + 1, moment => do
    let sent : List OracleNotice :=
      (msgs.filter fun m => m.moment == moment).map fun m => ⟨m.shape, m.leafClass⟩
    nReqSend z.codes sent z.link.group z.batch.own.first 0 true
    (pure () : N Unit)
    note (.scope .request)
    let more ← nMomentsL z msgs fuel (moment + 1)
    pure (sumT (sent.map (·.shape.answers)) + more)

/-- nFrameA with «pure ()» in the arm's place. -/
def nFrameL (z : ProofSized) :
    Nat → List ReqGroup → List ReqLink → List Nat → GroupSize → N Unit
  | _, [], _, _, _ => pure ()
  | l, g :: gs, links, open_, before => do
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
      (pure () : N Unit)
      note (.scope .request)
      let moments := (msgs.getLast?.map (·.moment + 1)).getD 0
      let more ← nMomentsL z msgs (moments - 1) 1
      let keptRows := sumT (((gs.head?.map keptOf).getD []).map (·.shape.mainRows))
      let closed : GroupSize :=
        { z.link.group with k := g.k, h := g.h, slots := 2 ^ clog2 (1 + keptRows) }
      note (.bat [closed] (open_.headD 0 + carried + sampleRows + more))
      note (.fold closed 0)
      nFrameL z (l + 1) gs (links.drop 1) (open_.drop 1) closed

theorem nMomentsL_sim (A : Nat → Arm) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment, Sim Any (nMomentsA A z l msgs fuel moment) (nMomentsL z msgs fuel moment)
  | 0, _ => sim_pure trivial
  | fuel + 1, moment => by
    unfold nMomentsA nMomentsL
    dsimp only
    exact sim_bind (nReqSend_sim _ _ _ _ _ _) fun _ _ _ =>
      sim_bind (sim_quiet (nArm_quiet _ _) (quiet_pure _)) fun _ _ _ =>
        sim_bind (sim_note rfl) fun _ _ _ =>
          sim_bind (nMomentsL_sim A z l msgs fuel (moment + 1)) fun _ _ _ => sim_pure trivial

/-- Steps through the frame and its light twin. -/
macro "simstepL" : tactic => `(tactic| repeat' first
  | with_reducible apply sim_ite
  | with_reducible apply sim_bind
  | ((with_reducible refine sim_note ?_) <;> rfl)
  | ((with_reducible refine sim_noteV _ _ ?_) <;> rfl)
  | with_reducible exact sim_pure (R := Any) trivial
  | with_reducible exact nReqSend_sim _ _ _ _ _ _
  | with_reducible exact sim_quiet (nArm_quiet _ _) (quiet_pure _)
  | with_reducible exact nIopp_sim _ _ _ _ _
  | with_reducible exact nMomentsL_sim _ _ _ _ _ _
  | with_reducible assumption
  | with_reducible intro _)

theorem nFrameL_sim (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    Sim Any (nFrameA A z l gs links open_ before) (nFrameL z l gs links open_ before)
  | [], _, _, _, _ => by
    unfold nFrameA nFrameL
    exact sim_pure trivial
  | g :: gs, l, links, open_, before => by
    have ih := fun c => nFrameL_sim A z gs (l + 1) (links.drop 1) (open_.drop 1) c
    unfold nFrameA nFrameL
    cases links.head? with
    | none =>
      dsimp only
      simstepL
    | some lk =>
      dsimp only
      simstepL
      all_goals exact ih _

/-- callsFrom's routine at «proof 0», over the light frame. -/
def proof0L (c : Configured) (openRows : List Nat) (pendingRows : Nat) : N Unit := do
  nFrameL c.sized.proof 0 (reqGroups c.sized.proof.request).toList
    c.sized.proof.request.link openRows
    c.sized.proof.link.group
  note (.scope .request)
  if 1 < pendingRows then note (.batt pendingRows c.sized.proof.batch.shape.kCol)
  nLinFirst c.sized.proof.codes c.sized.proof.batch
  note .seal

/-- **«proof 0» and its light twin say the same of samples.** -/
theorem proof0L_sim (c : Configured) (o : List Nat) (n : Nat) (A : Nat → Arm) :
    Sim Any (proof0R c o n A) (proof0L c o n) := by
  have := nFrameL_sim A c.sized.proof (reqGroups c.sized.proof.request).toList 0
    c.sized.proof.request.link o c.sized.proof.link.group
  have := nLinFirst_sim c.sized.proof.codes c.sized.proof.batch
  unfold proof0R proof0L
  simstepL

theorem fr_nMomentsL (z : ProofSized) (msgs : List ReqMessage) :
    ∀ fuel moment, Fr (nMomentsL z msgs fuel moment)
  | 0, _ => fr_pure _
  | fuel + 1, moment => by
    have := fr_nMomentsL z msgs fuel (moment + 1)
    unfold nMomentsL
    frn

theorem fr_nFrameL (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    Fr (nFrameL z l gs links open_ before)
  | [], _, _, _, _ => by
    unfold nFrameL
    exact fr_pure _
  | g :: gs, l, links, open_, before => by
    have ih := fun c => fr_nFrameL z gs (l + 1) (links.drop 1) (open_.drop 1) c
    have hm := fun msgs fuel moment => fr_nMomentsL z msgs fuel moment
    unfold nFrameL
    cases links.head? with
    | none =>
      frn
    | some lk =>
      frn
      all_goals first | exact ih _ | exact hm _ _ _

theorem fr_proof0L (c : Configured) (o : List Nat) (n : Nat) : Fr (proof0L c o n) := by
  have := fr_nFrameL c.sized.proof (reqGroups c.sized.proof.request).toList 0
    c.sized.proof.request.link o c.sized.proof.link.group
  have := fr_nLinFirst c.sized.proof.codes c.sized.proof.batch
  unfold proof0L
  frn

open OnBytes.Plan in
/-- nRanges with «pure ()» in the place of the loop of the lookups. -/
def nRangesL (codes : Codes) (z : RangesSized) : N Unit := do
  let x := z.x
  let roots ← (must (treesOf codes (Wf.messageOf x)) : Planning Nat)
  note (.send [⟨cubeBitsOf codes x.message.shape, [z.test.first]⟩] roots true)
  (pure PUnit.unit : N PUnit)
  (needs (sizedFits codes x.stages z.test.stages) : Planning Unit)
  nIopp z.test.stages (Wf.rowsBatched x z.matrix) (if x.choice.masksRide then 0 else 1)
    x.choice.masksRide
  if 1 < z.pending then note (.batt z.pending z.matrix.kCol)

open OnBytes.Plan in
theorem nRangesL_sim (codes : Codes) (z : RangesSized) :
    Sim Any (nRanges codes z) (nRangesL codes z) := by
  unfold nRanges nRangesL
  dsimp only
  refine sim_bind (sim_must _ _) fun a a' e => ?_
  subst e
  refine sim_bind (sim_note rfl) fun _ _ _ => ?_
  refine sim_bind (sim_quiet (quiet_forIn (fun p r => ?_) _ _) (quiet_pure _)) fun _ _ _ => ?_
  · have := nLookup_quiet p
    quiet
  refine sim_bind (sim_quiet (quiet_lift _) (quiet_lift _)) fun _ _ _ => ?_
  refine sim_bind (nIopp_sim _ _ _ _ _) fun _ _ _ => ?_
  exact sim_ite (sim_note rfl) (sim_pure trivial)

open OnBytes.Plan in
theorem fr_nRangesL (codes : Codes) (z : RangesSized) : Fr (nRangesL codes z) := by
  unfold nRangesL
  frn

/-- «key 0»'s routine over the light ranges. -/
def key0L (c : Configured) : N Unit := do
  note (.record c.sized.key.once.table)
  note (.send
    [⟨cubeBitsOf c.sized.key.codes c.sized.key.once.input.shape, [c.sized.key.once.own.first]⟩] 1
    true)
  nRangesL c.sized.key.codes c.sized.key.ranges
  nLinFirst c.sized.key.codes c.sized.key.once
  note .seal

/-- **«key 0» and its light twin say the same of samples.** -/
theorem key0L_sim (c : Configured) : Sim Any (key0R c) (key0L c) := by
  have := nRangesL_sim c.sized.key.codes c.sized.key.ranges
  have := nLinFirst_sim c.sized.key.codes c.sized.key.once
  unfold key0R key0L
  simstepL

theorem fr_key0L (c : Configured) : Fr (key0L c) := by
  have := fr_nRangesL c.sized.key.codes c.sized.key.ranges
  have := fr_nLinFirst c.sized.key.codes c.sized.key.once
  unfold key0L
  frn

/-- The seven chains, the two long ones by their light twins. -/
def twinsL (c : Configured) (o : List Nat) (n : Nat) : List Johnson.G.Chain :=
  [twinOf c.sized.set "key" 0 .once (key0L c),
   twinOf c.sized.set "key" 1 (scOf c.sized.key.once .shared) (key1R c),
   twinOf c.sized.set "key" 2 (scOf c.sized.key.once .request) (key2R c),
   twinOf c.sized.set "entry" 0 .once (entryR c),
   twinOf c.sized.set "proof" 0 .request (proof0L c o n),
   twinOf c.sized.set "proof" 1 (scOf c.sized.proof.batch .shared) (proof1R c),
   twinOf c.sized.set "proof" 2 (scOf c.sized.proof.batch .request) (proof2R c)]

theorem like_of_sim {s : Setting} {file : String} {ch : Nat} {scope sc' : Scope} {y y' : N Unit}
    {truth : Planned} (hs : Sim Any y y') (hy : Faith y) (hf : Fr y')
    (g : Good s truth.rounds (⟨scope, 0, 0, 0⟩, 0) y)
    (t : endOf s ⟨scope, 0, 0, 0⟩ y' = some ⟨sc', 0, 0, 0⟩) :
    Like (twinOf s file ch scope y) (twinOf s file ch scope y') := by
  obtain ⟨⟨P, hn⟩, _⟩ := one_twin (file := file) (ch := ch) hy g
  exact ⟨(rfl : file = file), (rfl : ch = ch), noted_trace hs hn (noted_of_runs (runs_of_end hf t))⟩

/-- **From «the key and the proof have three plans each» (hk | hp), seven walks (g0 … g6), the two
light twins' ends (t0 | t4) and one closed fact on the tail (ht): rowsFrom returns.** -/
theorem rows_of_partsL {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm}
    {k0 k1 k2 p0 p1 p2 : Planned} {sc0 sc4 : Scope}
    (hk : c.key = [k0, k1, k2]) (hp : c.proof = [p0, p1, p2])
    (g0 : Good c.sized.set k0.rounds (⟨.once, 0, 0, 0⟩, 0) (key0R c))
    (g1 : Good c.sized.set k1.rounds (⟨scOf c.sized.key.once .shared, 0, 0, 0⟩, 0) (key1R c))
    (g2 : Good c.sized.set k2.rounds (⟨scOf c.sized.key.once .request, 0, 0, 0⟩, 0) (key2R c))
    (g3 : Good c.sized.set c.entry.rounds (⟨.once, 0, 0, 0⟩, 0) (entryR c))
    (g4 : Good c.sized.set p0.rounds (⟨.request, 0, 0, 0⟩, 0) (proof0R c o n A))
    (g5 : Good c.sized.set p1.rounds (⟨scOf c.sized.proof.batch .shared, 0, 0, 0⟩, 0) (proof1R c))
    (g6 : Good c.sized.set p2.rounds (⟨scOf c.sized.proof.batch .request, 0, 0, 0⟩, 0) (proof2R c))
    (t0 : endOf c.sized.set ⟨.once, 0, 0, 0⟩ (key0L c) = some ⟨sc0, 0, 0, 0⟩)
    (t4 : endOf c.sized.set ⟨.request, 0, 0, 0⟩ (proof0L c o n) = some ⟨sc4, 0, 0, 0⟩)
    (ht : (tailFrom c c.sized.set (twinsL c o n)).toOption.isSome = true) :
    (rowsFrom c o n A).toOption.isSome = true := by
  have F2 : List.Forall₂ Like (twinsAt c o n A) (twinsL c o n) :=
    .cons (like_of_sim (key0L_sim c) (faith_key0R c) (fr_key0L c) g0 t0)
      (.cons (like_refl _) (.cons (like_refl _) (.cons (like_refl _)
        (.cons (like_of_sim (proof0L_sim c o n A) (faith_proof0R c o n A) (fr_proof0L c o n) g4 t4)
          (.cons (like_refl _) (.cons (like_refl _) .nil))))))
  rw [rowsFrom_eq (calls_of_goods hk hp g0 g1 g2 g3 g4 g5 g6), tail_congr c c.sized.set F2]
  exact ht

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.nFrameL_sim
#print axioms VerifiableInference.Desc.LinkJoin.proof0L_sim
#print axioms VerifiableInference.Desc.LinkJoin.key0L_sim
#print axioms VerifiableInference.Desc.LinkJoin.fr_proof0L
#print axioms VerifiableInference.Desc.LinkJoin.fr_key0L
#print axioms VerifiableInference.Desc.LinkJoin.like_of_sim
#print axioms VerifiableInference.Desc.LinkJoin.rows_of_partsL
