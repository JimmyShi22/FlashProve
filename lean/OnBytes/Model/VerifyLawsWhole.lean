-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyLawsWhole.lean: what has happened if a whole call ends with a yes or with a
result within limits.

`wholeCall` (OnBytes/Model/Verify.lean) is the pure function that the program runs for the command
`verify` on a request. This file unfolds it, as OnBytes/Model/VerifyLaws.lean unfolds the calls on
one file alone.

Main theorems.
- `cpStagesRun_passed`: if the result of a call is a passing one, every stage has passed.
- `readCall_ok`: the files that the first tests of a whole call return are the bytes of the call's
  files.
- `requestRun_ok`: the verdict in what `requestRun` returns is that of `Proof.check` on the proof
  file.
- `keyCheck_table`, `readTable_same`, `entryCheck_table`: the table that one check returns is the
  table against which the next one checks.
- `wholeCall_passed`: if the tests before the entry is read returned a number, and `wholeCall` on
  the same files with the entry returns a passing result, then the entry was there; `planned` on the
  three configuration files returned a value p; `Key.check` said yes on the key file under the key's
  three chains in p; `Entry.check` said yes on the entry file, under the parameter bytes of the
  entry's chain in p and against the table that `Key.check` returned; and `Proof.check` said
  `accepted` on the proof file, under the proof's three chains in p and against the table that
  `Entry.check` returned.

What is not claimed. Nothing on soundness: the theorems say which functions said yes, not what such
a yes is worth. The tables that the checks share are values of `Params.TableName`: a root and the
answers of a record. Each check reads them under the shape and the digest in the chains that it is
given for its file; that the chains under which the three checks run hold the same shape and digest
is not stated here: see OnBytes/Tie/SameChains.lean. A passing result (`CallEnd.passing`) is a yes,
a result within limits, or that a part passed; the theorems do not say which, nor that a whole call
never returns the third. Much of what a whole call tests is in no conclusion here: the tests before
the stages, beyond that they returned the files; what `planned` tests; the stages' accounting, so
whether the plans in p meet a target, and proof of work; the commitment ID; the acceptance policy;
the conditions of the standard parameter form; that the statement's item fits what the sub-proofs
use; and what the result is about. How request and reply enter is stated only as far as the
arguments of `Proof.check` show it. Of the links that `Proof.check` is given, only their form is
stated. The converse is not stated. Nothing says that some files make a call pass. For proofs only;
the program does not import this file.
-/
import OnBytes.Model.VerifyLaws

set_option autoImplicit false

namespace OnBytes.Model

open OnBytes.Params (exc_bind exc_guard exc_either)

namespace Stages

/-! ## From the result of the call to the ends of its stages -/

/-- A stage whose result shows no fault of the program, as `stageFault` looks for them, has not
refused. -/
theorem stageFault_no {asked : Nat} {own : Bool} {x : StageOut} {name : String}
    (h : stageFault asked own x = none) : x.ending ≠ .no name := by
  intro he
  unfold stageFault at h
  rw [he] at h
  dsimp only at h
  split at h
  · cases h
  · split at h <;> cases h

/-- If the stages' results show no fault of the program, no stage has refused. -/
theorem firstFault_no {asked : Nat} {single : Bool} : ∀ (l : List StageOut),
    firstFault asked single l = none → ∀ x ∈ l, ∀ name, x.ending ≠ .no name
  | [], _, _, hx, _ => by cases hx
  | [y], h, x, hx, name => by
    have e : x = y := by simpa using hx
    subst e
    exact stageFault_no h
  | y :: z :: zs, h, x, hx, name => by
    unfold firstFault at h
    split at h
    · cases h
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact stageFault_no hy
      · exact firstFault_no (z :: zs) h x hx' name

/-- If the stages name no cause, no stage has ended as not a verification. -/
theorem stageCauses_nil {l : List StageOut} (h : stageCauses l = []) :
    ∀ x ∈ l, ∀ causes, x.ending ≠ .notVer causes := by
  intro x hx causes he
  unfold stageCauses at h
  have hx0 := List.flatMap_eq_nil_iff.1 h x hx
  rw [he] at hx0
  cases causes <;> simp at hx0

/-- If the result of a call is a passing one, every stage has passed, and the flag `belowBar` is not
set. -/
theorem cpStagesRun_passed {stages : List StageOut} {part : Option StageName} {belowBar : Bool}
    {asked : Nat} {id : CpId} {about : Option (Array UInt32 × PolicyLines)}
    (h : (cpStagesRun stages part belowBar asked id about).passing = true) :
    (∀ x ∈ stages, x.ending = .passed) ∧ belowBar = false := by
  unfold cpStagesRun at h
  dsimp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hfault
        have hno := firstFault_no _ hfault
        clear hfault
        repeat' split at h
        all_goals first
          | (cases h; done)
          | skip
        all_goals
          have hc : stageCauses (stages.map StageOut.asRead) = [] ∧ belowBar = false := by simp_all
          refine ⟨fun x hx => ?_, hc.2⟩
          have hm : x.asRead ∈ stages.map StageOut.asRead := List.mem_map_of_mem hx
          have he : x.asRead.ending = x.ending := rfl
          cases hend : x.ending with
          | passed => rfl
          | no name => exact absurd (he.trans hend) (hno _ hm name)
          | notVer causes => exact absurd (he.trans hend) (stageCauses_nil hc.1 _ hm causes)

end Stages

namespace Verify

open OnBytes.Model.Stages

/-! ## The first tests of a whole call -/

/-- The first tests of a whole call do not look at the entry. -/
theorem readCall_entry (o : Options) (f : Files) (entry : FileIn) :
    readCall o { f with entry := entry } = readCall o f := rfl

/-- If the first tests of a whole call return the files, these are the bytes of the call's files. -/
theorem readCall_ok {o : Options} {f : Files} {r : Read} (h : readCall o f = .ok r) :
    f.policy = some r.pol ∧ f.KL = some r.KL ∧ f.layout = r.layout.map some ∧
      f.key = some r.key ∧ f.request = some r.request ∧ f.y = some r.y ∧
      f.proof = some r.proof := by
  unfold readCall at h
  replace h := exc_guard h
  obtain ⟨r0, h0, h⟩ := exc_bind h
  obtain ⟨e1, e2, e3, e4⟩ := readFirst_ok h0
  extract_lets next at h
  have hj : next () = .ok r := by
    split at h
    · obtain ⟨_, h⟩ := exc_either h
      exact h
    · obtain ⟨_, _, h⟩ := exc_bind h
      exact h
  obtain ⟨_, _, hj⟩ := exc_bind hj
  obtain ⟨request, q1, hj⟩ := exc_bind hj
  obtain ⟨y, q2, hj⟩ := exc_bind hj
  obtain ⟨_, hj⟩ := exc_either hj
  obtain ⟨proof, q3, hj⟩ := exc_bind hj
  obtain ⟨k, _, hj⟩ := exc_bind hj
  cases hj
  exact ⟨e1, e2, e3, e4, needBytes_ok q1, needBytes_ok q2, needBytes_ok q3⟩

/-! ## The stage request -/

/-- A value that `named` returns was there. -/
theorem named_ok {α : Type} {x : Except String α} {a : α} (h : named x = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok a0 =>
    cases h
    rfl

/-- The verdict in what `requestRun` returns is that of `Proof.check` on the proof file: under the
proof's three chains, against the table that `entryTable` read from the entry file, with the number
of the entry that the proof names, the statement's item that `Proof.requestItem` forms from the
parameter file, the scale file and the request, the request file's own bytes, the reply of the call,
and the links as built, each with the check that knows the request. -/
theorem requestRun_ok {C : Common} {o : Options} {r : Read} {entry : ByteArray} {x : RequestRun}
    (h : requestRun C o r entry = .ok x) :
    ∃ so cov further item links,
      Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
      Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      entryTable C.chains.link entry = .ok further ∧
      Proof.requestItem r.pol r.KL r.request = some item ∧
      linksOf C.X cov = .ok links ∧
      x.verdict = Proof.check C.chains.proof further r.entry item r.request (ofNat so.y)
        (runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
          C.chains.proof.first C.X.layers.wsLay) r.proof := by
  unfold requestRun at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨so, h1, h⟩ := exc_bind h
  obtain ⟨cov, h2, h⟩ := exc_bind h
  obtain ⟨further, h3, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases hi : Proof.requestItem r.pol r.KL r.request with
  | none =>
    rw [hi] at h
    cases h
  | some item =>
    rw [hi] at h
    obtain ⟨_, hp, h⟩ := exc_bind h
    cases hp
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨links, h4, h⟩ := exc_bind h
    cases h
    exact ⟨so, cov, further, item, links, h1, h2, h3, rfl, h4, rfl⟩

/-- If the stage request refuses nothing, `requestRun` has returned a value whose verdict on the
proof file is `accepted`. -/
theorem requestStage_ok {C : Common} {o : Options} {r : Read} {entry : ByteArray} {y : Found}
    (h : requestStage C o r entry = .ok y) :
    ∃ x, requestRun C o r entry = .ok x ∧ x.verdict = .accepted := by
  unfold requestStage at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  split at h
  · cases h
  · rename_i hv
    exact ⟨x, named_ok hx, hv⟩

/-! ## The tables that the three checks share -/

/-- The table that `Key.check` returns is the one that `Key.readTable` reads from the key file,
under the shape and the digest in the key's one-time chain. -/
theorem keyCheck_table {k : Params.KeyChains} {file : ByteArray} {table : Params.TableName}
    (h : Key.check k file = .ok table) :
    ∃ j, Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i t j ht
        split at h
        · cases h
        · split at h
          · cases h
          · cases h
            exact ⟨j, ht⟩

/-- If `Key.readTable` returns a table under each of two digests, under one shape and on one file,
the two tables are equal. Whether it returns one can depend on the digest. -/
theorem readTable_same {s : Params.IndexShape} {cfg cfg' file : ByteArray}
    {t t' : Params.TableName} {j j' : Nat} (h : Key.readTable s cfg file = .ok (t, j))
    (h' : Key.readTable s cfg' file = .ok (t', j')) : t = t' := by
  unfold Key.readTable at h h'
  split at h
  · cases h
  · rename_i hs
    rw [if_neg hs] at h'
    split at h
    · cases h
    · rename_i i hi
      rw [hi] at h'
      dsimp only at h'
      split at h
      · cases h
      · rename_i table k ht
        rw [ht] at h'
        dsimp only at h'
        split at h
        · split at h'
          · cases h
            cases h'
            rfl
          · cases h'
        · cases h

/-- The table that `Entry.check` returns is the one that `entryTable` reads from the entry file,
under the same parameter bytes as read. -/
theorem entryCheck_table {params file : ByteArray} {q : Params.Link}
    {first further t : Params.TableName} (h : Entry.check params first file = .ok further)
    (hq : Params.Link.read params = some q) (ht : entryTable q file = .ok t) : t = further := by
  unfold Entry.check at h
  rw [hq] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    have hf : r.further = further := by
      split at h
      · cases h
        rfl
      · cases h
    unfold Entry.read at hr
    unfold entryTable at ht
    dsimp only at hr ht
    split at hr
    · cases hr
    · rename_i i hi
      rw [hi] at ht
      dsimp only at ht
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · rename_i fu j hj
          rw [hj] at ht
          dsimp only at ht
          have e : r.further = fu := by
            repeat' split at hr
            all_goals first
              | (cases hr; rfl)
              | cases hr
          split at ht
          · cases ht
            rw [← hf, e]
          · cases ht

/-! ## The whole call -/

/-- The whole call. If the tests before the entry is read returned the number k, and `wholeCall` on
the same files with the entry returns a passing result, then: these tests returned the files r, in
which the proof names the entry k; the entry was there; `planned` on the three configuration files
returned p, and the common beginning of the stages returned C, which holds p's chains. `Key.check`
said yes on the key file, under the key's three chains in p, and returned `table`. `Entry.check`
said yes on the entry file, under the parameter bytes of the entry's chain in p and against `table`,
and returned `further`. `Proof.check` said `accepted` on the proof file, under the proof's three
chains in p and against `further`, with the number k, the item that `Proof.requestItem` forms, the
request file's own bytes, the reply of the call, and the links as built, each with the check that
knows the request. The call asked for no fewer bits than the threshold. -/
theorem wholeCall_passed {o : Options} {f : Files} {k : Nat} {entry : FileIn}
    (hk : entryNumber o f = .ok k)
    (h : (wholeCall o { f with entry := entry }).passing = true) :
    ∃ (r : Read) (ent : ByteArray) (p : Planned) (C : Common) (table further : Params.TableName),
      readCall o f = .ok r ∧ r.entry = k ∧ entry = some ent ∧
      planned r.pol r.KL r.layout = .ok p ∧ commonOfCall r = .ok C ∧ C.chains = p.chains ∧
      Key.check p.chains.key r.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table ent = .ok further ∧
      (∃ so cov item links,
        Head.stFromCall (words32 r.request) (words32 r.y) C.X.T = .ok so ∧
        Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
        Proof.requestItem r.pol r.KL r.request = some item ∧
        linksOf C.X cov = .ok links ∧
        Proof.check p.chains.proof further k item r.request (ofNat so.y)
          (runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) r.proof = .accepted) ∧
      askedBelowBar o.bits = false := by
  unfold entryNumber at hk
  cases hr : readCall o f with
  | error e =>
    rw [hr] at hk
    cases hk
  | ok r =>
    rw [hr] at hk
    have hk' : r.entry = k := by
      cases hk
      rfl
    unfold wholeCall at h
    rw [readCall_entry, hr] at h
    dsimp only at h
    cases entry with
    | none => cases h
    | some ent =>
      dsimp only at h
      unfold stagesOf at h
      cases hC : commonOfCall r with
      | error e =>
        rw [hC] at h
        have h1 := (cpStagesRun_passed h).1 _ (List.mem_cons_self)
        cases h1
      | ok C =>
        rw [hC] at h
        obtain ⟨h1, h2⟩ := cpStagesRun_passed h
        obtain ⟨_, _, a1⟩ := stageOut_passed
          (h1 (C.oneTimeOut .key (keyStage C o.bits r.key)) (by simp))
        obtain ⟨_, _, a2⟩ := stageOut_passed
          (h1 (C.oneTimeOut .leaf (leafStage C o.bits ent)) (by simp))
        obtain ⟨_, _, a3⟩ := stageOut_passed
          (h1 (stageOut .request C.idHex (requestStage C o r ent)) (by simp))
        obtain ⟨p, j, k1, k2, k3⟩ := commonOfCall_ok hC
        obtain ⟨table, b1⟩ := keyStage_ok a1
        obtain ⟨further, b2⟩ := leafStage_ok a2
        obtain ⟨x, b3, b4⟩ := requestStage_ok a3
        obtain ⟨so, cov, t, item, links, c1, c2, c3, c4, c5, c6⟩ := requestRun_ok b3
        rw [k2] at b1 b2 c3 c6
        obtain ⟨j', d1⟩ := keyCheck_table b1
        have e1 : C.first = table := readTable_same k3 d1
        have e2 : t = further := entryCheck_table b2 (planned_read k1).2.1 c3
        rw [e1] at b2
        rw [e2, hk', b4] at c6
        exact ⟨r, ent, p, C, table, further, rfl, hk', rfl, k1, hC, k2, b1, b2,
          ⟨so, cov, item, links, c1, c2, c4, c5, c6.symm⟩, h2⟩

end Verify

end OnBytes.Model

#print axioms OnBytes.Model.Verify.wholeCall_passed
#print axioms OnBytes.Model.Verify.requestRun_ok
#print axioms OnBytes.Model.Verify.readCall_ok
