-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyLaws.lean: what has happened if a call on one file alone ends with the result
that the part passed.

`keyCall` and `leafCall` (OnBytes/Model/Verify.lean) are the pure functions that the program runs
for the commands `verify -key` and `verify -leaf`. This file unfolds them.

Main definition: `Stages.CallEnd.passing`. Main theorems.
- `leafCall_passed`: if `leafCall` returns `partPassed`, then the five files were there; `planned`
  on the three configuration files returned a value p; `Key.readTable` read a table from the first
  bytes of the key file; and `Entry.check` said yes on the entry file, under the parameter bytes
  `p.chains.bytes .link` and against that table.
- `keyCall_passed`: if `keyCall` returns `partPassed`, then the four files were there, `planned`
  returned a value p, and `Key.check` said yes on the key file, under the three chains
  `p.chains.key`.
- `planned_read`: the chains in p that the checks use are read back from the parameter bytes in p.
- `planned_bytes`: these parameter bytes are those that the function `planBytes` lists, if it
  returns a list.

What is not claimed. Nothing on soundness: the theorems say which functions said yes, not what such
a yes is worth. `partPassed` is the result of a call on one file alone, which is never a
verification. In `leafCall_passed` the table is taken from the key file on its form alone: none of
the key's proofs is read, so nothing is known of that table. Nothing is said on what `planned`
tests, or on whether the plans in p meet a target: the stages' accounting is in no statement here.
The commitment ID is in no statement. The table is read under the shape in the key's one-time chain
and checked under the shape in the entry's chain; that the two agree is not stated. Nothing is said
on the command `plan`, which prints digests: `planned_bytes` is on the function behind it. No step
to the compiled verifier (a term of the library's Lean theory, not machine code) is made here: see
OnBytes/Tie/. The converse is not stated: a yes of `Entry.check` or `Key.check` is not enough for
the call to pass. Nothing says that some files make a call pass. For proofs only; the program does
not import this file.
-/
import OnBytes.Model.Verify
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false

namespace OnBytes.Model

open OnBytes.Params (exc_bind)

/-! ## Two steps in a row -/

/-- If two steps in a row fail, the first has failed so, or it returned a value on which the second
failed so. -/
theorem bind_error {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε}
    (h : (x >>= f) = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error e0 =>
    cases h
    exact Or.inl rfl
  | ok a => exact Or.inr ⟨a, rfl, h⟩

namespace Stages

/-! ## From the result of the call to the end of its one stage -/

/-- True for the three results that say that a call passed: a yes, a result within limits, and that
a part passed. The third is no verification. -/
def CallEnd.passing : CallEnd → Bool
  | .yes _ _ => true
  | .withinLimits _ _ => true
  | .partPassed _ _ => true
  | _ => false

/-- If a call with one stage ends with the result that a part passed, the stage has passed, the part
is the one that the call names, and the flag `belowBar` is not set. -/
theorem cpStagesRun_part {out : StageOut} {part s : StageName} {belowBar : Bool} {asked : Nat}
    {id : CpId} {about : Option (Array UInt32 × PolicyLines)} {c : Closing}
    (h : cpStagesRun [out] (some part) belowBar asked id about = .partPassed s c) :
    out.ending = .passed ∧ s = part ∧ belowBar = false := by
  unfold cpStagesRun at h
  dsimp only [List.map] at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hfault
        have he : out.asRead.ending = out.ending := rfl
        have hno : ∀ name, out.ending ≠ .no name := by
          intro name hend
          unfold firstFault stageFault at hfault
          rw [he, hend] at hfault
          dsimp only at hfault
          split at hfault
          · cases hfault
          · split at hfault <;> cases hfault
        have hnv : ∀ causes, out.ending = .notVer causes → stageCauses [out.asRead] ≠ [] := by
          intro causes hend hc
          unfold stageCauses at hc
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
          rw [he, hend] at hc
          cases causes <;> simp at hc
        clear hfault
        repeat' split at h
        all_goals first
          | (cases h; done)
          | skip
        all_goals
          injection h with h1 _
          have hc : stageCauses [out.asRead] = [] ∧ belowBar = false := by simp_all
          refine ⟨?_, h1.symm, hc.2⟩
          cases hend : out.ending with
          | passed => rfl
          | no name => exact absurd hend (hno name)
          | notVer causes => exact absurd hc.1 (hnv causes hend)

end Stages

namespace Verify

open OnBytes.Model.Stages

/-! ## The first tests of a call -/

/-- If `callNeeds` ends the call, the result is not a passing one. -/
theorem callNeeds_error {ok : Bool} {name : String} {e : CallEnd}
    (h : callNeeds ok name = .error e) : e.passing = false := by
  unfold callNeeds at h
  split at h
  · cases h
  · cases h
    rfl

/-- If `needBytes` ends the call, the result is not a passing one. -/
theorem needBytes_error {f : FileIn} {role : Role} {e : CallEnd}
    (h : needBytes f role = .error e) : e.passing = false := by
  cases f with
  | none =>
    cases h
    rfl
  | some b => cases h

/-- The bytes that `needBytes` returns are the file's. -/
theorem needBytes_ok {f : FileIn} {role : Role} {b : ByteArray}
    (h : needBytes f role = .ok b) : f = some b := by
  cases f with
  | none => cases h
  | some b0 =>
    cases h
    rfl

/-- If `callNamed` ends the call, the result is not a passing one. -/
theorem callNamed_error {α : Type} {x : Except String α} {e : CallEnd}
    (h : callNamed x = .error e) : e.passing = false := by
  cases x with
  | ok a => cases h
  | error n =>
    cases h
    rfl

/-- If `policyEnd` ends the call, the result is not a passing one. -/
theorem policyEnd_error {kind place : Nat} {e : CallEnd}
    (h : policyEnd kind place = .error e) : e.passing = false := by
  unfold policyEnd at h
  split at h <;> cases h <;> rfl

/-- If `cpPolicySays` ends the call, the result is not a passing one. -/
theorem cpPolicySays_error {p : Option PolicyNamed} {n T : Nat} {e : CallEnd}
    (h : cpPolicySays p n T = .error e) : e.passing = false := by
  cases p with
  | none => cases h
  | some p => exact policyEnd_error h

/-- If `cpPolicyWord` ends the call, the result is not a passing one. -/
theorem cpPolicyWord_error {pol : ByteArray} {e : CallEnd}
    (h : cpPolicyWord pol = .error e) : e.passing = false := by
  unfold cpPolicyWord at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    rfl

/-- If `cpKeyHead` ends the call, the result is not a passing one. -/
theorem cpKeyHead_error {b : ByteArray} {e : CallEnd}
    (h : cpKeyHead b = .error e) : e.passing = false := by
  unfold cpKeyHead at h
  rcases bind_error h with h1 | ⟨_, _, h1⟩
  · exact callNeeds_error h1
  · exact callNeeds_error h1

/-- What `cpConfRead` returns is the bytes of the parameter file, of the scale file and, if there is
one, of the layout file. -/
theorem cpConfRead_ok {policy KL : FileIn} {layout : Option FileIn} {pol kl : ByteArray}
    {lay : Option ByteArray} (h : cpConfRead policy KL layout = .ok (pol, kl, lay)) :
    policy = some pol ∧ KL = some kl ∧ layout = lay.map some := by
  unfold cpConfRead at h
  obtain ⟨a, h1, h⟩ := exc_bind h
  obtain ⟨b, h2, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases layout with
  | none =>
    cases h
    exact ⟨needBytes_ok h1, needBytes_ok h2, rfl⟩
  | some l0 =>
    cases l0 with
    | none => cases h
    | some x =>
      cases h
      exact ⟨needBytes_ok h1, needBytes_ok h2, rfl⟩

/-- If `cpConfRead` ends the call, the result is not a passing one. -/
theorem cpConfRead_error {policy KL : FileIn} {layout : Option FileIn} {e : CallEnd}
    (h : cpConfRead policy KL layout = .error e) : e.passing = false := by
  unfold cpConfRead at h
  rcases bind_error h with h1 | ⟨_, _, h⟩
  · exact needBytes_error h1
  rcases bind_error h with h1 | ⟨_, _, h⟩
  · exact needBytes_error h1
  rcases bind_error h with h1 | ⟨_, _, h⟩
  · exact callNeeds_error h1
  cases layout with
  | none => cases h
  | some l0 =>
    cases l0 with
    | none =>
      cases h
      rfl
    | some x => cases h

/-- If the first tests of a call return the files, these are the bytes of the call's parameter,
scale, layout and key files. -/
theorem readFirst_ok {o : Options} {f : Files} {needed : Bool} {r : Read}
    (h : readFirst o f needed = .ok r) :
    f.policy = some r.pol ∧ f.KL = some r.KL ∧ f.layout = r.layout.map some ∧
      f.key = some r.key := by
  unfold readFirst at h
  dsimp only at h
  (split at h <;> try split at h) <;>
  · obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨⟨pol, kl, lay⟩, h1, h⟩ := exc_bind h
    dsimp only at h
    obtain ⟨key, h2, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    obtain ⟨e1, e2, e3⟩ := cpConfRead_ok h1
    exact ⟨e1, e2, e3, needBytes_ok h2⟩

/-- If the first tests of a call end it, the result is not a passing one. -/
theorem readFirst_error {o : Options} {f : Files} {needed : Bool} {e : CallEnd}
    (h : readFirst o f needed = .error e) : e.passing = false := by
  unfold readFirst at h
  dsimp only at h
  (split at h <;> try split at h) <;>
  · rcases bind_error h with h1 | ⟨_, _, h⟩
    · cases h1 <;> rfl
    rcases bind_error h with h1 | ⟨_, _, h⟩
    · exact callNeeds_error h1
    rcases bind_error h with h1 | ⟨_, _, h⟩
    · exact cpPolicySays_error h1
    rcases bind_error h with h1 | ⟨⟨pol, kl, lay⟩, _, h⟩
    · exact cpConfRead_error h1
    dsimp only at h
    rcases bind_error h with h1 | ⟨_, _, h⟩
    · exact needBytes_error h1
    rcases bind_error h with h1 | ⟨_, _, h⟩
    · exact callNamed_error h1
    rcases bind_error h with h1 | ⟨_, _, h⟩
    · exact cpPolicyWord_error h1
    rcases bind_error h with h1 | ⟨_, _, h⟩
    · exact cpKeyHead_error h1
    · cases h

/-! ## The common beginning of the stages -/

/-- Without a layout file `shapesOf` returns no value. -/
theorem shapesOf_none {X : Public} {y : Array LinkH × Params.Shapes} :
    shapesOf X none ≠ .ok y := by
  intro h
  unfold shapesOf at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨_, _⟩, _, h⟩ := exc_bind h
  cases h

/-- What is planned was planned with a layout file. -/
theorem planned_layout {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) : ∃ lay, layout = some lay := by
  cases layout with
  | some lay => exact ⟨lay, rfl⟩
  | none =>
    exfalso
    unfold planned at h
    obtain ⟨X, _, h⟩ := exc_bind h
    dsimp only at h
    obtain ⟨_, h1, _⟩ := exc_bind h
    unfold chainsOf at h1
    obtain ⟨_, h2, _⟩ := exc_bind h1
    exact shapesOf_none h2

/-- The chains of a plan as read back, those of the key, of the entry and of the proof, are read
from the plan's own parameter bytes. -/
theorem planned_read {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) :
    Params.KeyChains.read (p.chains.bytes .keyOneTime) (p.chains.bytes .keyShared)
        (p.chains.bytes .keySecond) = some p.chains.key ∧
      Params.Link.read (p.chains.bytes .link) = some p.chains.link ∧
      Params.ProofChains.read (p.chains.bytes .proofFirst) (p.chains.bytes .proofShared)
        (p.chains.bytes .proofSecond) = some p.chains.proof := by
  unfold planned at h
  obtain ⟨X, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨chains, h1, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  unfold chainsOf at h1
  obtain ⟨⟨_, _⟩, _, h1⟩ := exc_bind h1
  dsimp only at h1
  obtain ⟨_, _, h1⟩ := exc_bind h1
  obtain ⟨_, _, h1⟩ := exc_bind h1
  obtain ⟨made, _, h1⟩ := exc_bind h1
  split at h1
  · rename_i key link proof e1 e2 e3
    cases h1
    exact ⟨e1, e2, e3⟩
  · cases h1

/-- If the common beginning of the stages returns a value C, `planned` has returned a value p on the
configuration files in r, C holds that plan's chains, and its first table was read from the key
file's first bytes. -/
theorem commonOfCall_ok {r : Read} {C : Common} (h : commonOfCall r = .ok C) :
    ∃ (p : Planned) (j : Nat), planned r.pol r.KL r.layout = .ok p ∧ C.chains = p.chains ∧
      Key.readTable p.chains.tableShape p.cfg r.key = .ok (C.first, j) := by
  unfold commonOfCall at h
  cases hp : planned r.pol r.KL r.layout with
  | error n =>
    rw [hp] at h
    cases h
  | ok p =>
    rw [hp] at h
    have h1 : commonOf p.X p.cfg p.chains p.built r.key r.id.asked = .ok C := h
    unfold commonOf at h1
    dsimp only at h1
    split at h1
    · rename_i x hx
      obtain ⟨first, h2, h1⟩ := exc_bind h1
      cases h2
      obtain ⟨_, _, h1⟩ := exc_bind h1
      cases h1
      exact ⟨p, x.2, rfl, rfl, hx⟩
    · obtain ⟨_, h2, _⟩ := exc_bind h1
      cases h2

/-! ## The two stages -/

/-- A stage's result that has passed comes from findings that have passed. -/
theorem stageOut_passed {name : StageName} {idHex : String} {x : Except Refused Found}
    (h : (stageOut name idHex x).ending = .passed) :
    ∃ acct work, x = .ok (.passed, acct, work) := by
  match x, h with
  | .error _, h => cases h
  | .ok (e, a, w), h =>
    have h1 : e = .passed := h
    subst h1
    exact ⟨a, w, rfl⟩

/-- If the stage leaf refuses nothing, `Entry.check` has said yes on the entry file. -/
theorem leafStage_ok {C : Common} {asked : Nat} {entry : ByteArray} {y : Found}
    (h : leafStage C asked entry = .ok y) :
    ∃ further, Entry.check C.chains.made.entryLink C.first entry = .ok further := by
  unfold leafStage at h
  obtain ⟨_, _, h⟩ := exc_bind h
  split at h
  · cases h
  · rename_i further hf
    exact ⟨further, hf⟩

/-- If the stage key refuses nothing, `Key.check` has said yes on the key file. -/
theorem keyStage_ok {C : Common} {asked : Nat} {key : ByteArray} {y : Found}
    (h : keyStage C asked key = .ok y) : ∃ table, Key.check C.chains.key key = .ok table := by
  unfold keyStage at h
  obtain ⟨_, _, h⟩ := exc_bind h
  split at h
  · cases h
  · rename_i table hf
    exact ⟨table, hf⟩

/-! ## The calls on one file alone -/

/-- If a call on one file alone ends with the result that a part passed, its first tests returned
the files, the common beginning returned a value, and the stage passed on these. The part is the one
that the call names, and the call asked for no fewer bits than the threshold. -/
theorem partCall_passed {o : Options} {f : Files} {part s : StageName}
    {run : Common → Read → Except Refused Found} {c : Closing}
    (h : partCall o f part run = .partPassed s c) :
    ∃ r C acct work, readFirst o f false = .ok r ∧ commonOfCall r = .ok C ∧
      run C r = .ok (.passed, acct, work) ∧ s = part ∧ askedBelowBar o.bits = false := by
  unfold partCall at h
  split at h
  · cases h
  · split at h
    · rename_i e he
      have hn := readFirst_error he
      rw [h] at hn
      cases hn
    · rename_i r hr
      dsimp only at h
      obtain ⟨h1, h2, h3⟩ := cpStagesRun_part h
      cases hC : commonOfCall r with
      | error x =>
        rw [hC] at h1
        cases h1
      | ok C =>
        rw [hC] at h1
        obtain ⟨acct, work, h4⟩ := stageOut_passed h1
        exact ⟨r, C, acct, work, hr, hC, h4, h2, h3⟩

/-- The call on an entry file alone. If it ends with the result that a part passed, then: the five
files were there; `planned` on the three configuration files returned p; `Key.readTable`, under the
tables' shape and the digest in p, read the table `first` from the first bytes of the key file, on
its form alone; and `Entry.check` said yes on the entry file, under the parameter bytes of the
entry's chain in p and against `first`. The part is the stage leaf, and the call asked for no fewer
bits than the threshold. -/
theorem leafCall_passed {o : Options} {f : Files} {s : StageName} {c : Closing}
    (h : leafCall o f = .partPassed s c) :
    ∃ (pol KL lay key entry : ByteArray) (p : Planned) (first further : Params.TableName) (j : Nat),
      f.policy = some pol ∧ f.KL = some KL ∧ f.layout = some (some lay) ∧ f.key = some key ∧
      f.entry = some entry ∧ planned pol KL (some lay) = .ok p ∧
      Key.readTable p.chains.tableShape p.cfg key = .ok (first, j) ∧
      Entry.check (p.chains.bytes .link) first entry = .ok further ∧
      s = .leaf ∧ askedBelowBar o.bits = false := by
  unfold leafCall at h
  split at h
  · split at h <;> cases h
  · rename_i x entry hne
    obtain ⟨r, C, _, _, h1, h2, h3, h4, h5⟩ := partCall_passed h
    obtain ⟨e1, e2, e3, e4⟩ := readFirst_ok h1
    obtain ⟨p, j, k1, k2, k3⟩ := commonOfCall_ok h2
    obtain ⟨lay, hl⟩ := planned_layout k1
    obtain ⟨further, hf⟩ := leafStage_ok h3
    rw [hl] at e3 k1
    rw [k2] at hf
    cases he : f.entry with
    | none => exact absurd he (fun he => hne r h1 he)
    | some ent =>
      rw [he] at hf
      exact ⟨r.pol, r.KL, lay, r.key, ent, p, C.first, further, j, e1, e2, e3, e4, rfl, k1, k3, hf,
        h4, h5⟩

/-- The call on a key file alone. If it ends with the result that a part passed, then: the four
files were there; `planned` on the three configuration files returned p; and `Key.check` said yes on
the key file, under the key's three chains in p. The part is the stage key, and the call asked for
no fewer bits than the threshold. -/
theorem keyCall_passed {o : Options} {f : Files} {s : StageName} {c : Closing}
    (h : keyCall o f = .partPassed s c) :
    ∃ (pol KL lay key : ByteArray) (p : Planned) (table : Params.TableName),
      f.policy = some pol ∧ f.KL = some KL ∧ f.layout = some (some lay) ∧ f.key = some key ∧
      planned pol KL (some lay) = .ok p ∧ Key.check p.chains.key key = .ok table ∧
      s = .key ∧ askedBelowBar o.bits = false := by
  obtain ⟨r, C, _, _, h1, h2, h3, h4, h5⟩ := partCall_passed h
  obtain ⟨e1, e2, e3, e4⟩ := readFirst_ok h1
  obtain ⟨p, j, k1, k2, _⟩ := commonOfCall_ok h2
  obtain ⟨lay, hl⟩ := planned_layout k1
  obtain ⟨table, hf⟩ := keyStage_ok h3
  rw [hl] at e3 k1
  rw [k2] at hf
  exact ⟨r.pol, r.KL, lay, r.key, p, table, e1, e2, e3, e4, k1, hf, h4, h5⟩

/-- The parameter bytes of a plan are those that `planBytes` lists, the function behind the command
`plan`, which prints a digest of each: if `planBytes` returns a list on the same three files, it
pairs each chain's name with that chain's bytes in p. -/
theorem planned_bytes {bits : Nat} {pol KL lay : ByteArray} {p : Planned}
    {l : List (String × ByteArray)} (hp : planned pol KL (some lay) = .ok p)
    (h : planBytes bits (some pol) (some KL) (some (some lay)) = .ok l) :
    l = allChains.map fun c => (c.text, p.chains.bytes c) := by
  unfold planBytes at h
  obtain ⟨⟨a, b, d⟩, h1, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨e1, e2, e3⟩ := cpConfRead_ok h1
  cases e1
  cases e2
  cases d with
  | none => cases e3
  | some d0 =>
    cases e3
    rw [hp] at h
    obtain ⟨q, h2, h⟩ := exc_bind h
    cases h2
    obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    rfl

end Verify

end OnBytes.Model

#print axioms OnBytes.Model.Verify.leafCall_passed
#print axioms OnBytes.Model.Verify.keyCall_passed
#print axioms OnBytes.Model.Verify.planned_bytes
#print axioms OnBytes.Model.Verify.planned_read
