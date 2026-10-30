-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxChain.lean: the chain's half of the entry's tie at a ground: what
OnBytes/TypedOracleCompiler/Slice/EntryChain.lean asks of one reading of an entry's chain (`EntryRead`, fifteen
fields), from the strict reader's yes at the format's own oracle; and so the typed chain's run under
the family that a run evaluates.

Main names:
  `ho_oBits`: the hash made of the realised oracle on bits is the hash made of the format's oracle.
  `entryRead_of`: `EntryRead` at `entryXD G c`, the pins' digest `pdOf`, the oracle `oBits`, the two
    tables' roots as digests, and the program's own description at the two tables.
  `fitL_mem`, `fitsE_of`, `descr_of`, `within_of`: what the chain's half and the lax verifier's
    clauses on numbers ask of the description (`RowsE2.FitsE`; no round has more than 64 bits of
    work; the stored openings are in order), from the line's limits test and two tests on the
    ground's rounds.
  `famOf_famP`: the family that a run evaluates is the one that is read out of `oBits` through the
    page.
  `ChainYes`: under `EntryRunTop.famOf`, at a typed string, the typed chain returns; what it draws
    is what the reader drew; all tests of work pass; its last phase is local.
  `chain_of`: `ChainYes` at the string that the typing makes of what was read, by
    `entry_chain_run`.
  `chain_full`, `chain_small`: at the two grounds.

Hypotheses of `entryRead_of`: the reader's equation; the limits of OnBytes/TypedOracleCompiler at the description;
both roots have 32 bytes; the ground has a round; the parameter bytes lie in the hash's domain; the
run value and the typed plain parts of what was read; fewer than 2 ^ 32 answers at each table.
Hypotheses left in `chain_full`, `chain_small`: the digest and both roots have 32 bytes; the
parameter bytes lie in the hash's domain; the reader's equation; the typing's yes; the run value has
32 bytes; fewer than 2 ^ 32 answers at each table.

Limits: values alone. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryChain
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Run.RowsH
import OnBytes.TypedOracleCompiler.Slice.PartEntryFull
import OnBytes.TypedOracleCompiler.Slice.EntryHomeFull
import OnBytes.TypedOracleCompiler.Slice.EntryHomeSmall
import OnBytes.TypedOracleCompiler.Slice.EntryDescOk

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom OnBytes.Tie TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Slice.EntryChain
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run.RowsE2
open TypedOracleCompiler.Slice.EntryFill
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry)
open _root_.Run.PQ (View)
open _root_.Run (bytesToDig digToBytes oBits oB bytesToBits rootsB)

/-- The hash made of the realised oracle on bits is the hash made of the format's oracle. -/
theorem ho_oBits : Fmt.HO (oB (oBits ())) = Fmt.HO Fmt.oracle := by
  funext n t i st bs
  unfold Fmt.HO
  split
  · rw [RowsH.oB_oBits 0 (by decide), RowsH.oB_oBits 1 (by decide)]
  · rw [RowsH.oB_oBits 0 (by decide)]

/-- What the chain's half asks, at a ground. -/
theorem entryRead_of (G : EntryGround) (c : ByteArray)
    (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (first further : Params.TableName) (h0 : first.root.size = 32) (h1 : further.root.size = 32)
    (hrs : G.rs ≠ [])
    (hd : Fmt.hDom 169 0 1 Fmt.zero32 (entryXD G c).base.params = true)
    (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : Fmt.ChainOut)
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) seen b i =
        some (o, j))
    (run : ByteArray) (hrun : o.run = some run) (h32 : run.size = 32)
    (pls : Plains (PQ.uL (entryXD G c).C (entryXD G c).ds))
    (hpl : PQ.plainsSL (entryXD G c).C (entryXD G c).ds o.rounds.toList = some pls)
    (f0 : first.answers.length < 2 ^ 32) (f1 : further.answers.length < 2 ^ 32) :
    EntryRead (entryXD G c) (EntryRunTop.pdOf (entryXD G c)) oBits first further
      (bytesToDig first.root) (bytesToDig further.root)
      (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) o run
      pls where
  read := ⟨seen, b, i, j, by rw [ho_oBits]; exact e⟩
  label := rfl
  stm := rfl
  fit := PQ.fit_rds (entryXD G c).base hok
  room := _root_.Run.PQ.room_kOf (entryXD G c).base
  hasRound := fun h => hrs (List.map_eq_nil_iff.1 h)
  kit := _root_.Run.PQ.kit_pull _ _
  pdIs := by
    obtain ⟨-, x, i0, hd', s, -, -, -, rfl, -⟩ := readX_stages (Fmt.HO Fmt.oracle) _ seen b i o j e
    show Fmt.HO Fmt.oracle 169 0 1 Fmt.zero32 (entryXD G c).base.params = _
    rw [Fmt.HO_oracle _ _ _ _ _ hd]
    exact (_root_.Run.TieTree.dig_bytes _ (Fmt.size_H 169 0 1 _ _)).symm
  runIs := hrun
  run32 := h32
  plains := hpl
  root₀ := (_root_.Run.TieTree.dig_bytes _ h0).symm
  root₁ := (_root_.Run.TieTree.dig_bytes _ h1).symm
  few₀ := f0
  few₁ := f1

/-! ## The description -/

/-- Each of the rounds' data goes with a round of the description. -/
theorem fitL_mem : ∀ (ds : List PQ.RD) (rs : List Fmt.Round), PQ.FitL ds rs → ∀ d ∈ ds,
    ∃ r ∈ rs, d.entry = r.entry ∧ d.kind = r.kind ∧ d.items = r.items ∧
      d.trees.length = r.entry.roots ∧ Fmt.countItem .root r.items = r.entry.roots
  | [], [], _, _, hd => absurd hd List.not_mem_nil
  | _ :: ds, r0 :: rs, h, d, hd => by
      rcases List.mem_cons.1 hd with rfl | hd'
      · exact ⟨r0, List.mem_cons_self, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
      · obtain ⟨r, hr, x⟩ := fitL_mem ds rs h.2.2.2.2.2.2 d hd'
        exact ⟨r, List.mem_cons_of_mem _ hr, x⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

section
variable (G : EntryGround) (c : ByteArray)
  (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)

include hw in
/-- No round has more than 64 bits of work; the stored openings are in order. -/
theorem descr_of : (∀ d ∈ (entryXD G c).ds, d.entry.work ≤ 64) ∧
    PQ.okX (entryXD G c).ds (entryXD G c).a (entryXD G c).xs = true :=
  ⟨workT_of_within _ (fun _ _ => ByteArray.empty) hw,
    okxT_of_within _ (fun _ _ => ByteArray.empty) hw⟩

include hw in
/-- What the chain's half asks of the rounds' data. -/
theorem fitsE_of (hok : PQ.ok (entryXD G c).base = true)
    (hseal : (G.rs.all fun r => decide (r.1.kind ≠ .sealed)) = true)
    (hlen : G.rs.length + 1 < 2 ^ 64) : FitsE (entryXD G c) where
  work := (descr_of G c hw).1
  plain := fun d hd => by
    obtain ⟨r, hr, -, hk, -⟩ := fitL_mem _ _ (PQ.fit_rds _ hok) d hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    exact Or.inr (hk ▸ of_decide_eq_true (List.all_eq_true.1 hseal x hx))
  roots := fun d hd => by
    obtain ⟨r, -, -, -, hi, ht, hc⟩ := fitL_mem _ _ (PQ.fit_rds _ hok) d hd
    rw [ht, hi, hc]
  few := by
    rw [fitL_length _ _ (PQ.fit_rds _ hok)]
    show (G.rs.map (·.1)).length + 1 < 2 ^ 64
    rw [List.length_map]
    exact hlen

end

/-- The description at an empty statement is within the line's limits test, at every digest of 32
bytes, if the ground's own description is in order there. -/
theorem within_of (G : EntryGround)
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true) (c : ByteArray)
    (hc : c.size = 32) :
    withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true :=
  G.within_at c hc ByteArray.empty (by
    rw [baseOk_linkAtCfg G.q c G.rs ByteArray.empty (hc.trans G.cfg32.symm) G.spelled]
    exact hb)

/-! ## The chain -/

section
variable {lg s : ℕ} (D : PQ.XD) (hok : PQ.ok D.base = true) (hcfg : D.base.cfg.size = 32)
  (d₁ : Sd1 lg s) (sh : Params.IndexShape)

include hok in
/-- The family that a run evaluates is the one that is read out of `oBits` through the page. -/
theorem famOf_famP (dec : XE (List T3) lg s → View → Bool) :
    EntryRunTop.famOf D hcfg d₁ sh =
      famP D d₁ (EntryRunTop.cfgOf D) hcfg (EntryRunTop.pdOf D) (EntryRunTop.restAt D sh)
        (8 * EntryRunTop.saltOf D) (EntryRunTop.backOf D d₁) oBits := by
  rw [EntryRunTop.famOf_eq D hok hcfg d₁ sh dec]
  exact congrArg (fun m => readBlocks m oBits) (EntryFillRun.pageRunE_eq _ _ _ _ _ _ _ _)

end

/-- Under the family that a run evaluates, the typed chain of the written link, at the two tables'
roots, both tables' answers in the instance and the typed string π, returns; what it draws is what
was read in o; all tests of work pass; its last phase is local. -/
def ChainYes {lg s : ℕ} (G : EntryGround) (c : ByteArray) (hc : c.size = 32) (d₁ : Sd1 lg s)
    (sh : Params.IndexShape) (dec : XE (List T3) lg s → View → Bool)
    (first further : Params.TableName) (o : Fmt.ChainOut)
    (π : OneProtocolProof 256 (PSXE (entryXD G c) dec).up) (σ : Sd1 lg s × Sd1 lg s) : Prop :=
  ∃ (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds))) (v : Bits),
    (recomputeChainOfProof (L := Ls (entryXD G c) d₁) .link (PSXE (entryXD G c) dec).up
        (wqXE (entryXD G c) dec)
        (embPXE (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
          (TSE (entryXD G c) (seedEntry lg s))) some
        [bytesToDig first.root, bytesToDig further.root]
        ((first.answers.map E.triple, further.answers.map E.triple), σ) π).det
        (EntryRunTop.famOf (entryXD G c) hc d₁ sh) =
      some (ρ, ((none, some []), PQ.rtSL (entryXD G c).C (entryXD G c).ds o.rounds.toList),
        Phase.loc v) ∧
    PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
    PQ.passSL (entryXD G c).C (entryXD G c).ds ρ.2 = true

section
variable {lg s : ℕ} (c : ByteArray) (hc : c.size = 32) (d₁ : Sd1 lg s) (sh : Params.IndexShape)
  (dec : XE (List T3) lg s → View → Bool) (first further : Params.TableName)
  (h0 : first.root.size = 32) (h1 : further.root.size = 32)
  (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : Fmt.ChainOut)
  (h32 : ∀ run, o.run = some run → run.size = 32)
  (f0 : first.answers.length < 2 ^ 32) (f1 : further.answers.length < 2 ^ 32)
  (σ : Sd1 lg s × Sd1 lg s)

include h0 h1 h32 f0 f1 in
/-- The chain, at a ground, at the string that the typing makes of what the strict reader read.
-/
theorem chain_of (G : EntryGround) (hok : PQ.ok (entryXD G c).base = true)
    (F : FitsE (entryXD G c)) (hK : (entryXD G c).K + 1 < 2 ^ 48) (hrs : G.rs ≠ [])
    (hd : Fmt.hDom 169 0 1 Fmt.zero32 (entryXD G c).base.params = true)
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) seen b i =
        some (o, j))
    (π : OneProtocolProof 256 (PSXE (entryXD G c) dec).up) (hπ : assembleS (entryXD G c) dec o = some π) :
    ChainYes G c hc d₁ sh dec first further o π σ := by
  obtain ⟨run, pl, -, -, hrun, hpl, -, -, hsalt, hroots, hplains, -⟩ := assembleS_some _ _ hπ
  unfold ChainYes
  rw [famOf_famP (entryXD G c) hok hc d₁ sh dec]
  exact entry_chain_run (entryXD G c) d₁ _ hc _ _ _ _ oBits F hK dec first further _ _ _ o run pl
    (entryRead_of G c hok first further h0 h1 hrs hd seen b i j o e run hrun (h32 run hrun) pl hpl
      f0 f1) σ π [] hsalt (by rw [hroots, List.append_nil]) hplains

include h0 h1 h32 f0 f1 in
/-- The chain at the full size. -/
theorem chain_full
    (hd : Fmt.hDom 169 0 1 Fmt.zero32 (entryXD recordGround c).base.params = true)
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (Params.entrySpecOf (linkAtCfg recordGround.q c) recordGround.rs
        (Params.Link.statement first further)) seen b i = some (o, j))
    (π : OneProtocolProof 256 (PSXE (entryXD recordGround c) dec).up)
    (hπ : assembleS (entryXD recordGround c) dec o = some π) :
    ChainYes recordGround c hc d₁ sh dec first further o π σ :=
  chain_of c hc d₁ sh dec first further h0 h1 seen b i j o h32 f0 f1 σ recordGround
    (record_ok c hc)
    (fitsE_of recordGround c (within_of recordGround full_base_ok c hc) (record_ok c hc)
      Params.record_no_seal.1
      (by
        show Params.recordRounds.length + 1 < 2 ^ 64
        rw [Params.record_rounds_length]
        decide))
    (by rw [full_K]; decide)
    (fun h => by
      have h2 := Params.record_rounds_length
      rw [show Params.recordRounds = [] from h] at h2
      cases h2) hd e π hπ

include h0 h1 h32 f0 f1 in
/-- The chain at the small example. -/
theorem chain_small
    (hd : Fmt.hDom 169 0 1 Fmt.zero32 (entryXD smallRecordGround c).base.params = true)
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (Params.entrySpecOf (linkAtCfg smallRecordGround.q c) smallRecordGround.rs
        (Params.Link.statement first further)) seen b i = some (o, j))
    (π : OneProtocolProof 256 (PSXE (entryXD smallRecordGround c) dec).up)
    (hπ : assembleS (entryXD smallRecordGround c) dec o = some π) :
    ChainYes smallRecordGround c hc d₁ sh dec first further o π σ :=
  chain_of c hc d₁ sh dec first further h0 h1 seen b i j o h32 f0 f1 σ smallRecordGround
    (small_record_ok c hc)
    (fitsE_of smallRecordGround c (within_of smallRecordGround small_base_ok c hc)
      (small_record_ok c hc) Params.record_no_seal.2
      (by
        show Params.smallRecordRounds.length + 1 < 2 ^ 64
        rw [Params.small_record_rounds_length]
        decide))
    (by rw [small_K]; decide)
    (fun h => by
      have h2 := Params.small_record_rounds_length
      rw [show Params.smallRecordRounds = [] from h] at h2
      cases h2) hd e π hπ

end

end OnBytes.K.Left
