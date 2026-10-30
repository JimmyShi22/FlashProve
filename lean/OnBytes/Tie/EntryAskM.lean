-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAskM.lean: a check of the entry file that asks.

For `LinkE` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean). The check (`checkBy`) asks the record's seeds of both
tables and the chain's strict reader at a way of asking. With the law (`checkBy_det`): its result at
an oracle f is `checkAskR` at the function that f induces.

It asks every string on which the library's strict reader (`Fmt.readChainX`) and `recordSeedsW` call
their hash, being these texts at the asking hash: by reading; no theorem speaks of its log.

Not claimed. The program's `readIn` and `recordSeeds` are other texts, tied to these in their values
alone. That the program hashes no further string on the file is neither proved nor read off the
texts here. So this file does not show that the check asks all that the program hashes.
OnBytes/Tie/EntryTwin.lean asks by a twin of the port's own text: as the asking text this file is
overtaken. No part; no count; nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAskRec
import OnBytes.Slice.ChainChkAsk

set_option autoImplicit false

namespace OnBytes.Tie
open ZKCP

/-! ## The seeds, at any way of asking -/

/-- The text of `recordSeeds` at the hash that asks by `ask` (`Slice.recordSeedsW`; `readBy`'s
like). The program does not call it. -/
def seedsBy (ask : ByteArray → OComp 256 ByteArray) (fl : Fmt.Fld) (name : ByteArray)
    (bits count : Nat) : OComp 256 (Option (List (List E × E))) :=
  Slice.recordSeedsW (Fmt.HM ask) fl name bits count

/-- If at the oracle f every `ask s` gives `O s`, the hash that asks by `ask`, read through "run at
f", is the hash that O induces. (The first step of `readBy_det`.) -/
theorem detHom_on_ask (f : ZKCP.Oracle 256) (ask : ByteArray → OComp 256 ByteArray)
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det f = O s) :
    (Run.detHom f).on (Fmt.HM ask) = Fmt.HO O := by
  funext number tree index start bytes
  have e : (fun s => (Run.detHom f).app (ask s)) = O := funext h
  exact ((Run.detHom f).HM ask number tree index start bytes).trans
    ((congrArg (fun a => Fmt.HM (m := Id) a number tree index start bytes) e).trans
      (Fmt.HM_id _ number tree index start bytes))

/-- If at the oracle f every `ask s` gives `O s`, the result at f of the seeds that ask by `ask`
is the seeds at O. -/
theorem seedsBy_det (f : ZKCP.Oracle 256) (ask : ByteArray → OComp 256 ByteArray)
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det f = O s) (fl : Fmt.Fld) (name : ByteArray)
    (bits count : Nat) : (seedsBy ask fl name bits count).det f = seedsAt O fl name bits count := by
  have e1 : (Run.detHom f).app (Fmt.recordFirstW (Fmt.HM ask) name) =
      Fmt.recordFirstW (m := Id) (Fmt.HO O) name :=
    congrFun (congrFun (congrFun (congrFun (congrFun (detHom_on_ask f ask O h) 160) 0)
      Fmt.recordLabel) Fmt.zero32) (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none)
  rw [← Run.detHom_app f]
  unfold seedsBy seedsAt Slice.recordSeedsW
  simp only [(Run.detHom f).app_bind, (Run.detHom f).app_pure, Run.Hom.queryW,
    detHom_on_ask f ask O h, e1]

/-! ## `checkWithR` hangs on its two functions at the places that it uses alone -/

/-- If two functions for the seeds give one place, and two readers one reading at that place,
`checkWithR` has one value. -/
theorem checkWithR_congr (rd rd' : Fmt.SpecX → ByteArray → Nat → InSession ChainRead)
    (sd sd' : Seeds) (params : ByteArray) (first : Params.TableName) (file : ByteArray)
    (hsd : ∀ q, Params.Link.read params = some q →
      entryPlaceR sd q first file = entryPlaceR sd' q first file)
    (hrd : ∀ q P, Params.Link.read params = some q → entryPlaceR sd' q first file = some P →
      (rd P.spec file P.byte).run = (rd' P.spec file P.byte).run) :
    checkWithR rd sd params first file = checkWithR rd' sd' params first file := by
  unfold checkWithR
  cases hq : Params.Link.read params with
  | none => rfl
  | some q =>
    dsimp only
    have e : readWithR rd sd q first file = readWithR rd' sd' q first file := by
      unfold readWithR
      rw [hsd q hq]
      cases hP : entryPlaceR sd' q first file with
      | none => rfl
      | some P =>
        dsimp only
        rw [hrd q P hq hP]
    rw [e]

/-! ## The check that asks -/

/-- The name of a table under parameters q: what `keyWith` hands to the function for the seeds. -/
def nameUnder (q : Params.Link) (t : Params.TableName) : ByteArray :=
  Fmt.tableName t.root q.given.cfg q.link.table.code.logN q.link.table.code.ell
    q.link.table.code.r q.link.table.v q.link.table.answers q.link.table.saltBytes

/-- Two asked values as a function for the seeds: the first at the first table's name, the second
elsewhere. -/
def seedsOf (q : Params.Link) (first : Params.TableName)
    (s0 s1 : Option (List (List E × E))) : Seeds :=
  fun _ n _ _ => if n = nameUnder q first then s0 else s1

/-- One asked reading as a reader. -/
def readerOf (S : Fmt.SpecX) (x : Option (Fmt.ChainOut × Nat)) :
    Fmt.SpecX → ByteArray → Nat → InSession ChainRead :=
  fun _ _ _ _ => x.map fun y => (⟨y.1, viewOf S y.1, y.2⟩, ⟨y.1.seen⟩)

/-- The check of an entry file that asks by `ask`. It reads the
parameters and the copy's table off the bytes (no hash); asks the seeds of the first table's record
and of the copy's (ALSO AT `answers = 0`); finds the place of
the chain; asks the chain's strict reader; and lets `checkWithR` decide on what was asked. The leaf
and vertex strings of the stored tables' openings are hashed within the strict reader (the head of
OnBytes/Iop/Link.lean; `HomX.app_readStored`); a block calls no hash (the head of
OnBytes/Iop/Foldeq.lean): by these heads' word; no theorem. The program does not call it. -/
def checkBy (ask : ByteArray → OComp 256 ByteArray) (params : ByteArray)
    (first : Params.TableName) (file : ByteArray) : OComp 256 (Option Params.TableName) :=
  match Params.Link.read params with
  | none => pure none
  | some q => do
    let s0 ← seedsBy ask q.given.plan.field (nameUnder q first) q.link.table.cubeBits
      q.link.table.answers
    let s1 ← seedsBy ask q.given.plan.field
      (nameUnder q ((furtherAt q.link.table file).getD ⟨ByteArray.empty, []⟩))
      q.link.table.cubeBits q.link.table.answers
    match entryPlaceR (seedsOf q first s0 s1) q first file with
    | none => pure none
    | some P => do
      let x ← readBy ask P.spec Session.start.seen file P.byte
      pure (checkWithR (readerOf P.spec x) (seedsOf q first s0 s1) params first file)

/-- `entryPlaceR` hangs on the function for the seeds through its values at the two tables' names
alone: the first table's and that of the table which `furtherAt` reads off the file. -/
theorem entryPlaceR_two {sd sd' : Seeds} {q : Params.Link} {first : Params.TableName}
    {file : ByteArray}
    (h0 : sd q.given.plan.field (nameUnder q first) q.link.table.cubeBits q.link.table.answers =
      sd' q.given.plan.field (nameUnder q first) q.link.table.cubeBits q.link.table.answers)
    (h1 : ∀ t, furtherAt q.link.table file = some t →
      sd q.given.plan.field (nameUnder q t) q.link.table.cubeBits q.link.table.answers =
        sd' q.given.plan.field (nameUnder q t) q.link.table.cubeBits q.link.table.answers) :
    entryPlaceR sd q first file = entryPlaceR sd' q first file := by
  have k0 : keyWith sd q.given.plan.field q.given.cfg q.link.table first 0 =
      keyWith sd' q.given.plan.field q.given.cfg q.link.table first 0 := by
    unfold keyWith
    unfold nameUnder at h0
    rw [h0]
  unfold entryPlaceR
  dsimp only
  rw [k0]
  cases hi : Proof.readHead q.given.plan.field .entry file with
  | error e => rfl
  | ok i =>
    dsimp only
    split
    · rfl
    · rename_i hf
      have e2 : q.given.plan.field = .two :=
        Classical.byContradiction fun hne => hf (by simp [bne_iff_ne, hne])
      cases ht : readTable q.given.plan.field (q.link.table.rows * q.link.table.answers) file i with
      | error e => rfl
      | ok x =>
        obtain ⟨further, j⟩ := x
        dsimp only
        have hfa : furtherAt q.link.table file = some further := by
          unfold furtherAt
          rw [e2] at hi ht
          rw [hi]
          dsimp only
          rw [ht]
        have k1 : keyWith sd q.given.plan.field q.given.cfg q.link.table further 1 =
            keyWith sd' q.given.plan.field q.given.cfg q.link.table further 1 := by
          have := h1 further hfa
          unfold keyWith
          unfold nameUnder at this
          rw [this]
        rw [k1]

/-- THE LAW. If at the oracle f every `ask s` gives `O s`, the result at f of the check that asks
by `ask` is `checkAskR O`: the plain check with the strict reader and the record's seeds at O. No
condition on the parameter bytes, the first table or the file. An equation
between two results; both may be "refused". The law cannot tell whether a plain step computes with
the format's own hash: such a call would stand on both sides. -/
theorem checkBy_det (f : ZKCP.Oracle 256) (ask : ByteArray → OComp 256 ByteArray)
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det f = O s) (params : ByteArray)
    (first : Params.TableName) (file : ByteArray) :
    (checkBy ask params first file).det f = checkAskR O params first file := by
  rw [← Run.detHom_app f]
  unfold checkBy
  cases hq : Params.Link.read params with
  | none =>
    dsimp only
    rw [(Run.detHom f).app_pure]
    unfold checkAskR checkWithR
    rw [hq]
    rfl
  | some q =>
    dsimp only
    have a : ∀ n, (Run.detHom f).app (seedsBy ask q.given.plan.field n q.link.table.cubeBits
        q.link.table.answers) =
          seedsAt O q.given.plan.field n q.link.table.cubeBits q.link.table.answers :=
      fun n => (Run.detHom_app f _).trans (seedsBy_det f ask O h _ n _ _)
    rw [(Run.detHom f).app_bind, a]
    show (Run.detHom f).app (_ >>= _) = _
    rw [(Run.detHom f).app_bind, a]
    generalize hs0 : seedsAt O q.given.plan.field (nameUnder q first) q.link.table.cubeBits
      q.link.table.answers = s0
    generalize hs1 : seedsAt O q.given.plan.field
      (nameUnder q ((furtherAt q.link.table file).getD ⟨ByteArray.empty, []⟩))
      q.link.table.cubeBits q.link.table.answers = s1
    have hpl : entryPlaceR (seedsOf q first s0 s1) q first file =
        entryPlaceR (seedsAt O) q first file := by
      refine entryPlaceR_two ?_ ?_
      · unfold seedsOf
        rw [if_pos rfl, hs0]
      · intro t ht
        unfold seedsOf
        split
        · rename_i e
          rw [e, hs0]
        · rw [ht] at hs1
          exact hs1.symm
    show (Run.detHom f).app (match entryPlaceR (seedsOf q first s0 s1) q first file with
      | none => pure none
      | some P => _) = _
    cases hP : entryPlaceR (seedsOf q first s0 s1) q first file with
    | none =>
      dsimp only
      rw [(Run.detHom f).app_pure]
      unfold checkAskR checkWithR readWithR
      rw [hq]
      dsimp only
      rw [← hpl, hP]
      rfl
    | some P =>
      dsimp only
      rw [(Run.detHom f).app_bind, Run.detHom_app, readBy_det f ask O h]
      show (Run.detHom f).app (pure _) = _
      rw [(Run.detHom f).app_pure]
      refine checkWithR_congr _ _ _ _ params first file ?_ ?_
      · intro q' hq'
        obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
        exact hpl
      · intro q' P' hq' hP'
        obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
        obtain rfl : P = P' := Option.some.inj (hP.symm.trans (hpl.trans hP'))
        unfold InSession.run readerOf readInAt
        cases Fmt.readChainX (m := Id) (Fmt.HO O) P.spec Session.start.seen file P.byte <;> rfl

/-! ## Every string asked; the generic language of trees; from the entry function -/

/-- The check that asks every string, the digest of the parameter bytes among them: `checkBy` at
`Run.askB`. -/
def checkAsks (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    OComp 256 (Option Params.TableName) :=
  checkBy Run.askB params first file

/-- Its result at f is `checkAskR` at the function that f induces on byte strings. -/
theorem checkAsks_det (f : ZKCP.Oracle 256) (params : ByteArray) (first : Params.TableName)
    (file : ByteArray) :
    (checkAsks params first file).det f = checkAskR (Run.oB f) params first file :=
  checkBy_det f Run.askB (Run.oB f) (fun _ => rfl) params first file

/-- The same as a tree in the library's generic language, over the family with one oracle: the type
of a part's checker. -/
def checkAsksR (params : ByteArray) (first : Params.TableName) (file : ByteArray) :
    Rom.OComp (Rom.rom 256) (Option Params.TableName) :=
  Rom.toRom (checkAsks params first file)

/-- Its result at a family g with one oracle. -/
theorem checkAsksR_det (g : Rom.Fam (Rom.rom 256)) (params : ByteArray)
    (first : Params.TableName) (file : ByteArray) :
    (checkAsksR params first file).det g = checkAskR (Run.oB (g ())) params first file :=
  (OComp.det_toRom g (checkAsks params first file)).trans (checkAsks_det (g ()) params first file)

/-- FROM THE ENTRY FUNCTION. Under `ZeroFacts` and `SaysRecordLines`, at c := the digest of the
three configuration files as read: THE CHECK THAT ASKS, run at the oracle on bit strings that is
made from the format's hash, on `recordBytesAt c`, the table that `Key.check` returned and the entry
file's bytes, returns the table that `Entry.check` returned. One fixed oracle: no bound over a
drawn oracle says anything of it. At that oracle, under 32 bytes for the digest and the first root
and a file within smallFX, it is equivalent to the program's yes: a form, no news. c is a constant
in the parameter bytes, BLAKE2b's. AT Run.oBits, NOT AT THE PATCHED HASH OF (b) IN
OnBytes/TypedOracleCompiler/Slice/Shapes.lean: that step wants that no asked string is one of the second hash
function's codes: unproved, since nothing here speaks of the log. -/
theorem zero_record_asks {args : List String} {s s' : OnBytes.Shell.World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : SaysRecordLines w.r.pol) :
    (checkAsksR (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table
      w.ent).det Run.oBits = some w.further :=
  (checkAsksR_det Run.oBits _ _ _).trans (zero_record_ask h hs)

end OnBytes.Tie
