-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Tail.lean: FROM SEVEN WALKS AND ONE CLOSED FACT ON THE TAIL TO
«rowsFrom RETURNS». Definitions and theorems. A law file; no running text imports it.
  `key0R` … `proof2R`, `scOf`   callsFrom's seven routines and its local «sc», by name
                                (RowsRun.lean:174-197).
  `callsFrom_eq`  callsFrom, where the key and the proof have three plans each, as seven `oneAt`.
  `tailFrom`      A SECOND TEXT of what packFrom and rowsFrom (Law/RowsFrom.lean:108-142) do behind
                  callsFrom.
  `rowsFrom_eq`, `tail_congr`   rowsFrom is that tail at callsFrom's value; the tail reads of a
                                chain what
                  `Like` (Law/RowsNoArms.lean) says (file, chain, what its calls say of samples) and
                  no more.
  `twinOf`        a chain with the calls of a routine run once from nothing (`callsAt`).
SUPERSEDED IN USE: proof0R_sim serves Parts.lean's like_twins alone.
Limits. NO CLOSED FACT IS HERE. tailFrom will have to be turned with packFrom and
rowsFrom. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

theorem good_one {s : Setting} {truth : List PlanRound} {st : SmallSt × Nat} {sc' : Scope}
    {x : N Unit}
    (hx : Fr x) (h : pieceB s truth st x = some (⟨sc', 0, 0, 0⟩, truth.length)) :
        Good s truth st x := by
  obtain ⟨cs, rs, hr, e2, hs⟩ := step_runs hx h
  refine ⟨cs, rs, sc', hr, ?_⟩
  have e2' : truth.length = st.2 + rs.size := e2
  have e : (truth.drop st.2).take rs.size = truth.drop st.2 :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  rw [e] at hs
  exact hs

theorem callsAt_of_runs {s : Setting} {σ σ' : SmallSt} {x : N Unit} {cs : Array Call}
    {rs : Array PlanRound} (h : RunsN s σ x () cs rs σ') : callsAt s σ x = cs := by
  unfold callsAt outAt
  unfold RunsN at h
  rw [h]
  rfl

/-- A chain with the calls of a routine run once from nothing. -/
def twinOf (s : Setting) (file : String) (ch : Nat) (scope : Scope) (y : N Unit) :
    Johnson.G.Chain :=
  ⟨file, ch, scope, (callsAt s ⟨scope, 0, 0, 0⟩ y).toList⟩

/-- `one_of_good`, with the calls by name. -/
theorem one_twin {s : Setting} {file : String} {ch : Nat} {scope : Scope} {y : N Unit}
    {truth : Planned} (hy : Faith y) (g : Good s truth.rounds (⟨scope, 0, 0, 0⟩, 0) y) :
    (∃ P, noted s scope y = .ok ((callsAt s ⟨scope, 0, 0, 0⟩ y).toList, P)) ∧
      oneAt s file ch scope y truth = .ok (twinOf s file ch scope y) := by
  have g' := g
  obtain ⟨cs, rs, sc', hr, _⟩ := g'
  obtain ⟨calls, P, hn, ho⟩ := one_of_good (file := file) (ch := ch) hy g
  have e : calls = (callsAt s ⟨scope, 0, 0, 0⟩ y).toList := by
    rw [callsAt_of_runs hr]
    have := hn.symm.trans (noted_of_runs hr)
    exact congrArg Prod.fst (Except.ok.inj this)
  subst e
  exact ⟨⟨P, hn⟩, ho⟩

/-- callsFrom's local «sc», by name. -/
def scOf (x : LinSized) (other : Scope) : Scope := if x.lines.oneTime then .once else other

def key0R (c : Configured) : N Unit := do
  note (.record c.sized.key.once.table)
  note (.send
    [⟨cubeBitsOf c.sized.key.codes c.sized.key.once.input.shape, [c.sized.key.once.own.first]⟩] 1
    true)
  nRanges c.sized.key.codes c.sized.key.ranges
  nLinFirst c.sized.key.codes c.sized.key.once
  note .seal
def key1R (c : Configured) : N Unit := do nLinShared c.sized.key.codes c.sized.key.once; note .seal
def key2R (c : Configured) : N Unit := nLinSecond c.sized.key.once
def entryR (c : Configured) : N Unit := nLinkPlan c.sized.link
def proof1R (c : Configured) : N Unit := do
  nLinShared c.sized.proof.codes c.sized.proof.batch; note .seal
def proof2R (c : Configured) : N Unit := nLinSecond c.sized.proof.batch

theorem callsFrom_eq {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm}
    {k0 k1 k2 p0 p1 p2 : Planned} (hk : c.key = [k0, k1, k2]) (hp : c.proof = [p0, p1, p2]) :
    callsFrom c o n A =
      ([oneAt c.sized.set "key" 0 .once (key0R c) k0,
        oneAt c.sized.set "key" 1 (scOf c.sized.key.once .shared) (key1R c) k1,
        oneAt c.sized.set "key" 2 (scOf c.sized.key.once .request) (key2R c) k2,
        oneAt c.sized.set "entry" 0 .once (entryR c) c.entry,
        oneAt c.sized.set "proof" 0 .request (proof0R c o n A) p0,
        oneAt c.sized.set "proof" 1 (scOf c.sized.proof.batch .shared) (proof1R c) p1,
        oneAt c.sized.set "proof" 2 (scOf c.sized.proof.batch .request) (proof2R c) p2].mapM id >>=
        fun l => pure (c.sized.set, l)) := by
  unfold callsFrom
  rw [hk, hp]
  rfl

theorem fr_key0R (c : Configured) : Fr (key0R c) := by
  have := fr_nRanges c.sized.key.codes c.sized.key.ranges
  have := fr_nLinFirst c.sized.key.codes c.sized.key.once
  unfold key0R
  frn
theorem fr_key1R (c : Configured) : Fr (key1R c) := by
  have := fr_nLinShared c.sized.key.codes c.sized.key.once
  unfold key1R
  frn
theorem fr_key2R (c : Configured) : Fr (key2R c) := fr_nLinSecond _
theorem fr_entryR (c : Configured) : Fr (entryR c) := fr_nLinkPlan _
theorem fr_proof1R (c : Configured) : Fr (proof1R c) := by
  have := fr_nLinShared c.sized.proof.codes c.sized.proof.batch
  unfold proof1R
  frn
theorem fr_proof2R (c : Configured) : Fr (proof2R c) := fr_nLinSecond _

theorem faith_key0R (c : Configured) : Faith (key0R c) := by
  have := faith_nRanges c.sized.key.codes c.sized.key.ranges
  have := faith_nLinFirst c.sized.key.codes c.sized.key.once
  unfold key0R
  fth
theorem faith_key1R (c : Configured) : Faith (key1R c) := by
  have := faith_nLinShared c.sized.key.codes c.sized.key.once
  unfold key1R
  fth
theorem faith_key2R (c : Configured) : Faith (key2R c) := faith_nLinSecond _
theorem faith_entryR (c : Configured) : Faith (entryR c) := faith_nLinkPlan _
theorem faith_proof1R (c : Configured) : Faith (proof1R c) := by
  have := faith_nLinShared c.sized.proof.codes c.sized.proof.batch
  unfold proof1R
  fth
theorem faith_proof2R (c : Configured) : Faith (proof2R c) := faith_nLinSecond _

/-- What packFrom and rowsFrom do behind callsFrom. -/
def tailFrom (c : Configured) (s : Setting) (chains : List Johnson.G.Chain) :
    Except String (List SendRow) := do
  let sends ← sendsFrom c
  let pack ← (do
    let sends ← sendsFrom c
    let per ← (chains.zip sends).mapM fun (c, d) => do
      let smp := c.calls.flatMap Call.sendSamples
      unless smp.length == d.sends.length do
        throw s!"{c.file} {c.chain}: the calls and the list have not as many sendings"
      (smp.zip d.sends).mapM fun (o, x) => do
        let at_ := s!"{c.file} {c.chain}, entry {x.entry} ({x.label})"
        let sampled := (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)
        let o' :=
          if o.length == sampled.length then o
          else if o.length == 1 then List.replicate sampled.length (o.headD ⟨0, []⟩) else []
        unless o'.length == sampled.length do
          throw s!"{at_}: the sampled messages and the samples are not as many"
        let l ← (sampled.zip o').mapM fun (sh, sm) => do
          pure (sh, ← radiusFor s d.codes at_ sh sm)
        unless x.behind.answers == l.length * s.samples do
          throw s!"{at_}: (p3) the entry behind takes in another number of answers"
        unless x.seed.drawE == s.samples * (Johnson.Pack.bMax d.codes l + 1) do
          throw s!"{at_}: (p4) the entry draws another number of elements"
        pure (d.codes, l)
    pure per.flatten : Except String (List (Codes × List (OracleShape × Nat))))
  let flat := sends.flatMap fun c => c.sends.map fun s => (c, s)
  unless flat.length == pack.length do throw "the two lists have not as many sendings"
  pure ((flat.zip pack).map fun ((c, s), p) =>
    ⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
      (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩)

theorem rowsFrom_eq {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm} {s : Setting}
    {chains : List Johnson.G.Chain} (h : callsFrom c o n A = .ok (s, chains)) :
    rowsFrom c o n A = tailFrom c s chains := by
  unfold rowsFrom packFrom tailFrom
  rw [h]
  rfl

theorem tail_congr (c : Configured) (s : Setting) {chains chains' : List Johnson.G.Chain}
    (F2 : List.Forall₂ Like chains chains') : tailFrom c s chains = tailFrom c s chains' := by
  unfold tailFrom
  generalize sendsFrom c = E
  cases E with
  | error e => rfl
  | ok sends =>
    show (Except.ok sends >>= fun sends => _) = (Except.ok sends >>= fun sends => _)
    simp only [bind, Except.bind]
    rw [mapM_zip_like _ (fun a a' d (e : Like a a') => by
      obtain ⟨e1, e2, e3⟩ := e
      try dsimp only
      rw [e1, e2, e3]) F2 sends]

theorem mapM_id_oks {ε α : Type} :
    ∀ l : List α, (l.map (Except.ok : α → Except ε α)).mapM id = .ok l
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, mapM_id_oks l]
    rfl

theorem proof0R_sim (c : Configured) (o : List Nat) (n : Nat) (A A' : Nat → Arm) :
    Sim Any (proof0R c o n A) (proof0R c o n A') := by
  have := nFrameA_sim A A' c.sized.proof (reqGroups c.sized.proof.request).toList 0
    c.sized.proof.request.link o c.sized.proof.link.group
  have := nLinFirst_sim c.sized.proof.codes c.sized.proof.batch
  unfold proof0R
  simstep

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.callsFrom_eq
#print axioms VerifiableInference.Desc.LinkJoin.rowsFrom_eq
#print axioms VerifiableInference.Desc.LinkJoin.tail_congr
#print axioms VerifiableInference.Desc.LinkJoin.proof0R_sim
#print axioms VerifiableInference.Desc.LinkJoin.one_twin
