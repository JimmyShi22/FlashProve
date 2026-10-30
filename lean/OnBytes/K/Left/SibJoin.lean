-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SibJoin.lean: what the tie between the entry's arm at the link over pairs of records
(`linkSibFull`, `linkSibSmall`, OnBytes/Flat/LinkSibAt.lean) and a run of the program asks on the
letters, the number of blocks, the answers and the decision, at the two grounds.

Main names (small for full at the small example):
  `sibLetters_full`: kit, rounds' data, depth and stored openings as written are those of
    `entryXD recordGround c`, at every c; the written side stands on the left.
  `sibK_full`: 140 (small: 99) is that description's number of blocks.
  `chalP_heq`, `sibChal_full`: the way from blocks to verifier messages at the written field and
    number is the description's.
  `sibSpec`: the description under which the strict reader reads is the typed description's own
    part with the statement put in, and its stored openings, by unfolding.
  `sibSalt`: the description's length of salts is that of the ground's parameters, at every c.
  `sibAns_full`: at every yes of the program the answers of the two records read off the two
    tables, written as triples of words, are the tables' answers.
  `sibDec2_full`: there the decision in `linkSibFull` at the two records is the decision of a run at
    the run's instance.
  `sibDec_full`: there the decision of a run, at the written numbers, says yes on the view of what
    the strict reader read.

Limits: values alone. Nothing on soundness; no probability. That some files meet `PortYesAt` is not
shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.SibLetters
import OnBytes.Flat.LinkSibRun

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left
open OnBytes.Tie OnBytes.Slice OnBytes.Flat TypedOracleCompiler.Slice
open _root_.Run (ckP chalP)

/-- The way from blocks to verifier messages hangs on the field and the number of blocks alone. -/
theorem chalP_heq {f f' : Fmt.Fld} {K K' : ℕ} (hf : f = f') (hK : K = K') :
    HEq (chalP f K) (chalP f' K') := by
  subst hf hK
  rfl

/-- The description under which the strict reader reads, at a statement st, is the typed
description's own part with st put in, and its stored openings. -/
theorem sibSpec (G : EntryGround) (c st : ByteArray) :
    TypedOracleCompiler.Run.PQ.withStatement (specAt G c) st =
      ⟨{ (entryXD G c).base with statement := st }, (entryXD G c).stored⟩ := rfl

/-- The description's length of salts is that of the ground's parameters. -/
theorem sibSalt (G : EntryGround) (c : ByteArray) :
    G.q.given.plan.salt = (entryXD G c).base.plan.salt := rfl

/-! ## The full size -/

/-- The four written letters are the description's, written side first. -/
theorem sibLetters_full (c : ByteArray) :
    ckP .two = (entryXD recordGround c).C ∧ dsFull = (entryXD recordGround c).ds ∧
      frS.P.T.a = (entryXD recordGround c).a ∧ frD.xs = (entryXD recordGround c).xs :=
  ⟨(letters_full c).1.symm, (letters_full c).2.1.symm, (letters_full c).2.2.1.symm,
    (letters_full c).2.2.2.symm⟩

/-- The written number of blocks is the description's. -/
theorem sibK_full (c : ByteArray) : 140 = (entryXD recordGround c).K := (full_K c).symm

/-- The written way from blocks to verifier messages is the description's. -/
theorem sibChal_full (c : ByteArray) :
    HEq (chalP .two 140) (chalP (entryXD recordGround c).base.plan.field (entryXD recordGround c).K)
        :=
  chalP_heq (full_four c).1.symm (sibK_full c)

section
variable {F : Files} {id : String} {table further : Params.TableName}
  (h : PortYesAt F id table further) (hl : recordGround.SaysLines F.pol)

include h hl in
/-- The answers of the two records, written as triples of words, are the two tables'. -/
theorem sibAns_full (l0 l1 : List (List E × E)) (o : Fmt.ChainOut) :
    trAns (recsOf frS.P.v 29 1 ⟨table, further, l0, l1, o⟩).1.2 = table.answers.map E.triple ∧
      trAns (recsOf frS.P.v 29 1 ⟨table, further, l0, l1, o⟩).2.2 =
        further.answers.map E.triple := by
  obtain ⟨h0, h1, k0, k1⟩ := answers_at recordGround record_answers record_field h hl
  rw [numbers_full.1, numbers_full.2.2] at h0 h1
  exact ⟨trAns_anT _ _ _ h0 k0, trAns_anT _ _ _ h1 k1⟩

include h hl in
/-- The decision in `linkSibFull` at the two records is the decision of a run at the run's
instance. -/
theorem sibDec2_full (c : ByteArray) (l0 l1 : List (List E × E)) (o : Fmt.ChainOut) :
    decFullX (recX (recsOf frS.P.v 29 1 ⟨table, further, l0, l1, o⟩)) =
      decRun (linkAtCfg Params.recordRead c) frS.P.v 29 1
        (xOfAskedC 29 1 ⟨table, further, l0, l1, o⟩) := by
  rw [recX_full h hl, decRun_full]

include h hl in
/-- The decision of a run, at the written numbers, says yes on the view of what the strict reader
read. -/
theorem sibDec_full :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)) (i : ℕ),
      Entry.read (linkAtCfg recordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table
        F.ent = .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds
        (linkAtCfg recordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table = some l0
            ∧
      seedsUnder recordSeeds
        (linkAtCfg recordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL])) further =
          some l1 ∧
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
        (TypedOracleCompiler.Run.PQ.withStatement
          (specAt recordGround (Params.configurationDigest [F.pol, F.lay, F.KL]))
          (stmAt table.answers further.answers table.root further.root))
        Session.start.seen F.ent i = some (r.chain.out, r.chain.next) ∧
      decRun (linkAtCfg recordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL])) frS.P.v
        29 1 (xOfAskedC 29 1 ⟨table, further, l0, l1, r.chain.out⟩)
        (Fmt.viewX
          (TypedOracleCompiler.Run.PQ.withStatement
            (specAt recordGround (Params.configurationDigest [F.pol, F.lay, F.KL]))
            (stmAt table.answers further.answers table.root further.root)) r.chain.out) = true :=
  dec_yes recordGround record_answers record_field numbers_full.1 numbers_full.2.1 numbers_full.2.2
      h hl

end

/-! ## The small example -/

/-- The four written letters are the description's, written side first. -/
theorem sibLetters_small (c : ByteArray) :
    ckP .two = (entryXD smallRecordGround c).C ∧ dsSmall = (entryXD smallRecordGround c).ds ∧
      srS.P.T.a = (entryXD smallRecordGround c).a ∧ srD.xs = (entryXD smallRecordGround c).xs :=
  ⟨(letters_small c).1.symm, (letters_small c).2.1.symm, (letters_small c).2.2.1.symm,
    (letters_small c).2.2.2.symm⟩

/-- The written number of blocks is the description's. -/
theorem sibK_small (c : ByteArray) : 99 = (entryXD smallRecordGround c).K := (small_K c).symm

/-- The written way from blocks to verifier messages is the description's. -/
theorem sibChal_small (c : ByteArray) :
    HEq (chalP .two 99) (chalP (entryXD smallRecordGround c).base.plan.field (entryXD
        smallRecordGround c).K) :=
  chalP_heq (small_four c).1.symm (sibK_small c)

section
variable {F : Files} {id : String} {table further : Params.TableName}
  (h : PortYesAt F id table further) (hl : smallRecordGround.SaysLines F.pol)

include h hl in
/-- The answers of the two records, written as triples of words, are the two tables'. -/
theorem sibAns_small (l0 l1 : List (List E × E)) (o : Fmt.ChainOut) :
    trAns (recsOf srS.P.v 19 1 ⟨table, further, l0, l1, o⟩).1.2 = table.answers.map E.triple ∧
      trAns (recsOf srS.P.v 19 1 ⟨table, further, l0, l1, o⟩).2.2 =
        further.answers.map E.triple := by
  obtain ⟨h0, h1, k0, k1⟩ := answers_at smallRecordGround small_record_answers small_record_field h
      hl
  rw [numbers_small.1, numbers_small.2.2] at h0 h1
  exact ⟨trAns_anT _ _ _ h0 k0, trAns_anT _ _ _ h1 k1⟩

include h hl in
/-- The decision in `linkSibSmall` at the two records is the decision of a run at the run's
instance. -/
theorem sibDec2_small (c : ByteArray) (l0 l1 : List (List E × E)) (o : Fmt.ChainOut) :
    decSmallX (recX (recsOf srS.P.v 19 1 ⟨table, further, l0, l1, o⟩)) =
      decRun (linkAtCfg Params.smallRecordRead c) srS.P.v 19 1
        (xOfAskedC 19 1 ⟨table, further, l0, l1, o⟩) := by
  rw [recX_small h hl, decRun_small]

include h hl in
/-- The decision of a run, at the written numbers, says yes on the view of what the strict reader
read. -/
theorem sibDec_small :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)) (i : ℕ),
      Entry.read (linkAtCfg smallRecordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
          table
        F.ent = .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds
        (linkAtCfg smallRecordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table =
            some l0 ∧
      seedsUnder recordSeeds
        (linkAtCfg smallRecordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL])) further =
          some l1 ∧
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
        (TypedOracleCompiler.Run.PQ.withStatement
          (specAt smallRecordGround (Params.configurationDigest [F.pol, F.lay, F.KL]))
          (stmAt table.answers further.answers table.root further.root))
        Session.start.seen F.ent i = some (r.chain.out, r.chain.next) ∧
      decRun (linkAtCfg smallRecordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
          srS.P.v
        19 1 (xOfAskedC 19 1 ⟨table, further, l0, l1, r.chain.out⟩)
        (Fmt.viewX
          (TypedOracleCompiler.Run.PQ.withStatement
            (specAt smallRecordGround (Params.configurationDigest [F.pol, F.lay, F.KL]))
            (stmAt table.answers further.answers table.root further.root)) r.chain.out) = true :=
  dec_yes smallRecordGround small_record_answers small_record_field numbers_small.1
      numbers_small.2.1 numbers_small.2.2 h hl

end

end OnBytes.K.Left
