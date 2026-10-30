-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAsked.lean: the asking half of the entry's typing.

The asking half (`askedE`) is the twin of `Entry.read`, asking; then both tables' seeds, asked by
the text of `recordSeeds` (`Slice.recordSeedsW`) at the tables' names. It returns the two tables,
both lists of seeds and what was read of the chain. No decision is taken: the typed verifier
decides.

With: its value at every oracle (`askedE_det`); and from main, at any ground with a record, at
`Run.oBits` (`EntryGround.zero_asked`): it returns a value, whose tables are those that `Key.check`
and `Entry.check` returned and whose seeds are the program's.

Not claimed. Values alone: of what it asks nothing is said here. The seeds' strings are asked twice
(once within the twin's `tableKey`, once here): harmless for a value. No part; nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryGroundTwin
import OnBytes.Tie.EntryAskM

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World)
open OnBytes.TwoPort
open ZKCP

/-- What the typing's asking half returns. -/
structure AskedE where
  /-- the first table: root and answers -/
  first : Params.TableName
  /-- the copy's table, read off the entry file -/
  further : Params.TableName
  /-- the seeds of the first table's record -/
  l0 : List (List E × E)
  /-- the seeds of the copy's record -/
  l1 : List (List E × E)
  /-- what the reader has read of the chain -/
  out : Fmt.ChainOut

/-- The seeds of a table's record under parameters q, at a function for the seeds. -/
def seedsUnder (sd : Seeds) (q : Params.Link) (t : Params.TableName) :
    Option (List (List E × E)) :=
  sd q.given.plan.field (nameUnder q t) q.link.table.cubeBits q.link.table.answers

/-- THE ASKING HALF. The program does not call it. -/
def askedE (q : Params.Link) (first : Params.TableName) (ent : ByteArray) :
    OComp 256 (Option AskedE) := do
  match ← M.Entry.read (Fmt.HM Run.askB) q first ent with
  | .error _ => pure none
  | .ok r => do
    let l0 ← seedsBy Run.askB q.given.plan.field (nameUnder q first) q.link.table.cubeBits
      q.link.table.answers
    let l1 ← seedsBy Run.askB q.given.plan.field (nameUnder q r.further) q.link.table.cubeBits
      q.link.table.answers
    pure (l0.bind fun a => l1.map fun b => ⟨first, r.further, a, b, r.chain.out⟩)

/-- Its value at a function O in the place of the hash: plain. -/
def askedAt (O : ByteArray → ByteArray) (q : Params.Link) (first : Params.TableName)
    (ent : ByteArray) : Option AskedE :=
  (readWithR (readInAt O) (seedsAt O) q first ent).bind fun r =>
    (seedsUnder (seedsAt O) q first).bind fun a =>
      (seedsUnder (seedsAt O) q r.further).map fun b => ⟨first, r.further, a, b, r.chain.out⟩

/-- The twin's reading, asking, run at f, is the twin's at the identity monad and the hash that f
induces. -/
theorem twin_read_det (f : ZKCP.Oracle 256) (q : Params.Link) (first : Params.TableName)
    (ent : ByteArray) :
    (Run.detHom f).app (M.Entry.read (Fmt.HM Run.askB) q first ent) =
      M.Entry.read (m := Id) (Fmt.HO (Run.oB f)) q first ent := by
  have e := M.RoadHom.app_read (Run.detHom f) (Fmt.HM Run.askB) q first ent
  rw [Run.detHom_on_HM] at e
  exact e

/-- The shape of `askedE` and of `askedAt`, with letters in the place of the reading (X, X'), of the
seeds that ask (S), of the names (N) and of the seeds' values (T), read through a morphism φ to the
identity monad. All are letters: nothing is computed. -/
theorem asked_shape (φ : Run.Hom (OComp 256) Id)
    (X : OComp 256 (Except Refusal Entry.EntryRead)) (X' : Except Refusal Entry.EntryRead)
    (hX : φ.app X = X')
    (S : ByteArray → Nat → Nat → OComp 256 (Option (List (List E × E))))
    (N : Params.TableName → ByteArray) (T : Params.TableName → Option (List (List E × E)))
    (bits count : Nat) (hS : ∀ t, φ.app (S (N t) bits count) = T t) (first : Params.TableName) :
    φ.app (do
      match ← X with
      | .error _ => pure none
      | .ok r => do
        let l0 ← S (N first) bits count
        let l1 ← S (N r.further) bits count
        pure (l0.bind fun a => l1.map fun b => (⟨first, r.further, a, b, r.chain.out⟩ : AskedE))) =
      X'.toOption.bind fun r =>
        (T first).bind fun a =>
          (T r.further).map fun b => (⟨first, r.further, a, b, r.chain.out⟩ : AskedE) := by
  rw [φ.app_bind, hX]
  cases X' with
  | error e =>
    show φ.app (pure none) = _
    rw [φ.app_pure]
    rfl
  | ok r =>
    show φ.app (S (N first) bits count >>= _) = _
    rw [φ.app_bind, hS]
    show φ.app (S (N r.further) bits count >>= _) = _
    rw [φ.app_bind, hS]
    show φ.app (pure _) = _
    rw [φ.app_pure]
    rfl

/-- `seedsUnder`, unfolded, for a letter sd. Where `seedsUnder recordSeeds q t` (or the same at
`seedsAt O`) has to meet the seeds' function at its four arguments, proofs go by this equation, not
by unfolding: left to compare the two by itself, a checker may unfold the seeds' function first,
then the match in it, and then compute the round. -/
theorem seedsUnder_eq (sd : Seeds) (q : Params.Link) (t : Params.TableName) :
    seedsUnder sd q t =
      sd q.given.plan.field (nameUnder q t) q.link.table.cubeBits q.link.table.answers := rfl

/-- The seeds that ask, under parameters q, run at f, are the seeds at the function that f induces.
-/
theorem seedsBy_under (f : ZKCP.Oracle 256) (q : Params.Link) (t : Params.TableName) :
    (Run.detHom f).app (seedsBy Run.askB q.given.plan.field (nameUnder q t) q.link.table.cubeBits
      q.link.table.answers) = seedsUnder (seedsAt (Run.oB f)) q t :=
  (Run.detHom_app f _).trans
    ((seedsBy_det f Run.askB (Run.oB f) (Run.det_askB f) q.given.plan.field (nameUnder q t)
      q.link.table.cubeBits q.link.table.answers).trans
        (seedsUnder_eq (seedsAt (Run.oB f)) q t).symm)

/-- THE LAW: at every oracle f the asking half's result is `askedAt` at the function that f
induces. NO HYPOTHESIS. -/
theorem askedE_det (f : ZKCP.Oracle 256) (q : Params.Link) (first : Params.TableName)
    (ent : ByteArray) : (askedE q first ent).det f = askedAt (Run.oB f) q first ent := by
  -- by `asked_shape`, which is proved for letters: written so that no checker need compute a seed
  rw [← Run.detHom_app f, askedE, askedAt, ← twin_read (Run.oB f) q first ent]
  exact asked_shape (Run.detHom f) (M.Entry.read (Fmt.HM Run.askB) q first ent)
    (M.Entry.read (m := Id) (Fmt.HO (Run.oB f)) q first ent) (twin_read_det f q first ent)
    (seedsBy Run.askB q.given.plan.field) (nameUnder q) (seedsUnder (seedsAt (Run.oB f)) q)
    q.link.table.cubeBits q.link.table.answers (seedsBy_under f q) first

/-! ## The asking half, then any plain map -/

/-- A typing: the asking half, then a plain map `asm` from what was asked to a typed value. All
questions are the asking half's. -/
def typedE {Out : Type} (asm : AskedE → Option Out) (q : Params.Link) (first : Params.TableName)
    (ent : ByteArray) : OComp 256 (Option Out) := do
  let a ← askedE q first ent
  pure (a.bind asm)

/-- Its value at every oracle. -/
theorem typedE_det {Out : Type} (asm : AskedE → Option Out) (f : ZKCP.Oracle 256)
    (q : Params.Link) (first : Params.TableName) (ent : ByteArray) :
    (typedE asm q first ent).det f = (askedAt (Run.oB f) q first ent).bind asm := by
  rw [← Run.detHom_app f]
  unfold typedE
  rw [(Run.detHom f).app_bind, Run.detHom_app, askedE_det]
  show (Run.detHom f).app (pure _) = _
  rw [(Run.detHom f).app_pure]
  rfl

/-- The same as a tree in the library's generic language, over the family with one oracle: the type
that a part's typing has. -/
def typedER {Out : Type} (asm : AskedE → Option Out) (q : Params.Link)
    (first : Params.TableName) (ent : ByteArray) : Rom.OComp (Rom.rom 256) (Option Out) :=
  Rom.toRom (typedE asm q first ent)

/-- Its value at every family of oracle functions: that of the asking half at the one oracle, then
the plain map. -/
theorem typedER_det {Out : Type} (asm : AskedE → Option Out) (g : Rom.Fam (Rom.rom 256))
    (q : Params.Link) (first : Params.TableName) (ent : ByteArray) :
    (typedER asm q first ent).det g = (askedAt (Run.oB (g ())) q first ent).bind asm :=
  (OComp.det_toRom g (typedE asm q first ent)).trans (typedE_det asm (g ()) q first ent)

/-! ## From the entry function -/

/-- At the oracle on bit strings made from the format's hash the value is that at the format's own
oracle. -/
theorem askedAt_oBits : askedAt (Run.oB (Run.oBits ())) = askedAt Fmt.oracle := by
  have e : readInAt (Run.oB (Run.oBits ())) = readInAt Fmt.oracle := by
    funext S b i s
    unfold readInAt
    rw [HO_oBits]
  unfold askedAt
  rw [e, seedsAt_oBits]

/-- With a record, a key comes from seeds: if `keyWith sd` returns k at a shape with answers, sd
returned a list l at the table's name, and k is made of the table's answers and l. -/
theorem keyWith_seeds {sd : Seeds} {f : Fmt.Fld} {cfg : ByteArray} {s : Params.IndexShape}
    {table : Params.TableName} {item : Nat} {k : TableKey}
    (h : keyWith sd f cfg s table item = some k) (hA : (s.answers == 0) = false) :
    ∃ l, sd f (Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers
        s.saltBytes) s.cubeBits s.answers = some l ∧
      k = { item := item, record := table.answers.toArray,
            seeds := l.map fun x => ⟨x.1, x.2⟩ } := by
  unfold keyWith at h
  simp only [hA, Bool.false_eq_true, if_false] at h
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨l, hl, ?_⟩
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- FROM THE ENTRY FUNCTION, AT ANY GROUND WHOSE TABLES HAVE A RECORD, AT Run.oBits. Under
`ZeroFacts` and `SaysLines`, at q := the ground's parameters at the digest of the three
configuration files as read: THE ASKING HALF RETURNS A VALUE: the table that `Key.check` returned,
the table that `Entry.check` returned, THE PROGRAM's OWN SEEDS at both tables' names, and what THE
PROGRAM's `Entry.read` read of the chain; and the program's two keys are made of these tables'
answers and these seeds; its block is `linkVerify` at them; its decision on the view says yes. One
fixed oracle. `SaysLines` is proved of no file; no file is shown a yes. Values alone. -/
theorem EntryGround.zero_asked (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) (hs : G.SaysLines w.r.pol) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)),
      Entry.read (linkAtCfg G.q (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table
        w.ent = .ok r ∧ r.further = w.further ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
        w.table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
        w.further = some l1 ∧
      r.block = linkVerify G.q.link
        { item := 0, record := w.table.answers.toArray, seeds := l0.map fun x => ⟨x.1, x.2⟩ }
        { item := 1, record := w.further.answers.toArray, seeds := l1.map fun x => ⟨x.1, x.2⟩ } ∧
      r.block.decides
        (Entry.start (linkAtCfg G.q (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])))
        r.chain.view = true ∧
      (askedE (linkAtCfg G.q (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) w.table
        w.ent).det (Run.oBits ()) = some ⟨w.table, w.further, l0, l1, r.chain.out⟩ := by
  have hc32 := Params.configurationDigest_size [w.r.pol, w.lay, w.r.KL]
  have eb := zero_entry_bytes h (G.saysLines_bytes hs w.lay w.r.KL)
  have hy : Entry.check (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = .ok w.further := by
    rw [← eb]
    exact h.entryYes
  generalize Params.configurationDigest [w.r.pol, w.lay, w.r.KL] = c at hc32 hy ⊢
  obtain ⟨q', r, hq', hr, hf, hd⟩ := (entry_check_iff _ _ _ _).1 hy
  obtain rfl : linkAtCfg G.q c = q' := Option.some.inj ((G.read_at c hc32).symm.trans hq')
  have hsm : ∀ P, entryPlaceR recordSeeds (linkAtCfg G.q c) w.table w.ent = some P →
      P.spec.ok = true → smallFX P.spec w.ent = true := by
    intro P hP hokP
    obtain ⟨_, ⟨rs2, h2, eP⟩, _⟩ := entryPlaceR_spec_any hP
    obtain rfl : G.rs = rs2 := Option.some.inj ((G.rounds_at c).symm.trans h2)
    rw [eP] at hokP ⊢
    exact smallFX_of_withinX _ hokP (G.within_at c hc32 _ (specX_base _ hokP)) w.ent
      (zero_entry_small h)
  have key := (readWithR_reader (q := linkAtCfg G.q c) (first := w.table) (file := w.ent)
    (readInAt Fmt.oracle) (fun S i hs => readInAt_oracle S w.ent i Session.start hs)
    (fun S i y hx => readX_ok _ _ _ w.ent i _ (readInAt_read _ _ _ _ _ y.2 y.1 hx).1) hc32
    (zero_table_root h) hsm r).2 hr
  have hr' : readWithR readIn recordSeeds (linkAtCfg G.q c) w.table w.ent = some r := by
    rw [readWithR_readIn, hr]
    rfl
  obtain ⟨P, hP, _, _, hPf, hPb⟩ := (readWithR_iff _ _ _ _ _ _).1 hr'
  obtain ⟨⟨k0, k1, hk0, hk1, hb⟩, _, h32⟩ := entryPlaceR_spec_any hP
  obtain ⟨l0, hl0, rfl⟩ := keyWith_seeds hk0 hA
  obtain ⟨l1, hl1, rfl⟩ := keyWith_seeds hk1 hA
  rw [← hPf, hf] at hl1 hb h32
  have H := seedsSame_oracle (linkAtCfg G.q c) hc32
  -- from here on by named equations, not by unfolding: see `seedsUnder_eq`
  have b0 : seedsUnder recordSeeds (linkAtCfg G.q c) w.table = some l0 :=
    (seedsUnder_eq _ _ _).trans hl0
  have b1 : seedsUnder recordSeeds (linkAtCfg G.q c) w.further = some l1 :=
    (seedsUnder_eq _ _ _).trans hl1
  have a0 : seedsUnder (seedsAt Fmt.oracle) (linkAtCfg G.q c) w.table = some l0 :=
    (seedsUnder_eq _ _ _).trans ((H w.table.root (zero_table_root h)).trans hl0)
  have a1 : seedsUnder (seedsAt Fmt.oracle) (linkAtCfg G.q c) w.further = some l1 :=
    (seedsUnder_eq _ _ _).trans ((H w.further.root h32).trans hl1)
  refine ⟨r, l0, l1, hr, hf, b0, b1, hPb.trans hb, hd, ?_⟩
  rw [askedE_det, askedAt_oBits, askedAt, key, Option.bind_some, a0, Option.bind_some, hf, a1,
    Option.map_some]

end OnBytes.Tie
