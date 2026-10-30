-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryChain.lean: THE CHAIN's HALF OF AN ENTRY's TIE: under the family that is read
out of one oracle g through the page of an entry's judge, the typed chain of the written link, at
the typed string that is made of what the strict reader read, computes round by round what that
reader drew at the hash over g; all tests of work pass.

The tie between the program's yes on an entry file and the yes of the typed checker has a chain's
half: the typed verifier recomputes its messages by typed chain queries; the program's reader
recomputes them by hashes. OnBytes/TypedOracleCompiler/Run/ChainERead.lean (`chain_one_read`) draws the typed
chain's value from ONE yes of the library's strict reader, under two laws on the family: one on the
first query, one on the written rounds. OnBytes/TypedOracleCompiler/Run/RowsE2.lean shows both laws at the page of
OnBytes/TypedOracleCompiler/Run/EntryPage.lean. This file joins them, and ties the first query's value to what the
reader computed (OnBytes/Tie/TraceStrict.lean: `readX_head`). The sibling is a second form of
the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `head_first`: what the format's start of a chain returns: its first value is the format's first
   value at its run value;
 - `EntryRead`: most of what is asked, as one structure of fifteen fields: the strict reader's yes
   at the hash over g; of the description under which it read: label, statement at two tables,
   rounds that fit the typed rounds' data, room, a round, a field that fits the typed challenges;
   the parameter digest that was read is the pins'; a run value of 32 bytes was read; the typed
   plain parts are those of the rounds read; the tables' roots are two digests' bytes; fewer than 2
   ^ 32 answers each. ASKED BESIDE IT by both theorems: `RowsE2.FitsE D` (four conditions on the
   typed rounds' data) and D.K + 1 < 2 ^ 48;
 - `entry_chain`: THE JOIN: the evaluable chain `chainP` at the page's family returns; what it draws
   is what the reader drew; all tests of work pass; the last phase is local;
 - `entry_chain_run`: the same of the road's own chain `recomputeChainOfProof`, run under the page's family, at
   the skeleton at which the judge's lax verifier is said (OnBytes/TypedOracleCompiler/Slice/EntryPS.lean).

Main definition: `EntryRead`.
Main theorems: `head_first`, `entry_chain`, `entry_chain_run`.

Not claimed. NOTHING BEHIND THE CHAIN: no opening, no view, no decision. No statement here has the
judge's verifier on its left: `entry_chain_run` is of the chain's half alone; the join with
`EntryPS.ZXE_verifier` is unwritten. No field of `EntryRead` or of `FitsE` is shown at any
description, AND THERE IS NO GUARD: nothing shows all twenty conditions together at one description
and one file: that the reader's yes is the twin's is not shown here;
what is asked of the description is owed by whoever gives the description as a function of sizes and
tables; plain parts, salt and instance are the typing's. Nothing on soundness. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ChainERead
import OnBytes.TypedOracleCompiler.Run.RowsE2
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Slice.EntryPS

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.EntryChain
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage
open TypedOracleCompiler.Run.RowsE TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- What the format's start of a chain returns: its first value is the format's first value at
its run value, with an empty record. -/
theorem head_first (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (lab : ℕ)
    (pd stm : ByteArray) (x : Option ByteArray) (hd : _root_.Fmt.ChainHead)
    (e : _root_.Fmt.startChainW (m := Id) h lab pd stm x = some hd) :
    hd.rho0 = _root_.Fmt.firstValueW (m := Id) h lab pd stm ByteArray.empty hd.run := by
  unfold _root_.Fmt.startChainW at e
  split_ifs at e with h1
  · cases x with
    | none =>
      have e' : some (⟨none, _root_.Fmt.firstValueW (m := Id) h lab pd stm ByteArray.empty none⟩ :
          _root_.Fmt.ChainHead) = some hd := e
      rw [← Option.some.inj e']
    | some b =>
      have e1 : (if b.size = 32 then
          (if _root_.Fmt.runOk (_root_.Fmt.runValueW (m := Id) h lab pd b) then
            some (⟨some (_root_.Fmt.runValueW (m := Id) h lab pd b),
              _root_.Fmt.firstValueW (m := Id) h lab pd stm ByteArray.empty
                (some (_root_.Fmt.runValueW (m := Id) h lab pd b))⟩ : _root_.Fmt.ChainHead)
            else none) else none) = some hd := e
      split_ifs at e1
      rw [← Option.some.inj e1]

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest : ByteArray) (n : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁))) (g : Fam (rom 256))

/-- The family that is read out of g through the page. -/
abbrev famP : Fam (typedOracleFamily 256 (D.K + 1) (Ls D d₁)) :=
  readBlocks (pageForE D d₁ cfg hcfg pd rest n back) g

/-- WHAT IS ASKED, of one reading of an entry's chain at the hash over g. first, further: the
two tables; c₀, c₁: their roots as digests; S: the description under which the chain was read; o:
what was read; run: its run value; pls: the typed plain parts. -/
structure EntryRead (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (S : _root_.Fmt.SpecX) (o : _root_.Fmt.ChainOut) (run : ByteArray)
    (pls : Plains (PQ.uL D.C D.ds)) : Prop where
  /-- the strict reader's yes, at the hash over g -/
  read : ∃ seen b i j,
    _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO (oB (g ()))) S seen b i = some (o, j)
  /-- the description's label is the port's label of a link's chain -/
  label : S.base.label = OnBytes.Params.labelLink
  /-- its statement is the program's, at the two tables -/
  stm : S.base.statement = OnBytes.Params.Link.statement first further
  /-- its rounds fit the typed rounds' data -/
  fit : PQ.FitL D.ds S.base.rounds
  /-- no round wants more than D.K blocks -/
  room : ∀ r ∈ S.base.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ D.K
  /-- it has a round -/
  hasRound : S.base.rounds ≠ []
  /-- the kit and the wire fit the description's field -/
  kit : _root_.Run.PQ.KitFits S.base.plan.field D.C D.K (chalP D.base.plan.field D.K)
  /-- the parameter digest that was read is the pins' -/
  pdIs : o.pd = digToBytes pd
  /-- the run value that was read -/
  runIs : o.run = some run
  /-- it has 32 bytes -/
  run32 : run.size = 32
  /-- the typed plain parts are those of the rounds read -/
  plains : PQ.plainsSL D.C D.ds o.rounds.toList = some pls
  /-- the tables' roots -/
  root₀ : first.root = digToBytes c₀
  /-- the further table's -/
  root₁ : further.root = digToBytes c₁
  /-- fewer than 2 ^ 32 answers -/
  few₀ : first.answers.length < 2 ^ 32
  /-- the further table's -/
  few₁ : further.answers.length < 2 ^ 32

/-- THE CHAIN's HALF. If `EntryRead` holds, the typed rounds' data meet `RowsE2.FitsE`, and
D.K + 1 < 2 ^ 48: under the page's family the typed chain of the written link, with the two
roots as outer roots, both tables' answers in the instance, the run value's bits as the salt, the
roots that were read and the typed plain parts of the rounds read, returns; what it draws is what
the reader drew; all tests of work pass; the last phase is local. σ: whatever stands in the seeds'
place of the instance. -/
theorem entry_chain (F : FitsE D) (hK : D.K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (S : _root_.Fmt.SpecX)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ S o run pls) (σ : Sd1 lg s × Sd1 lg s)
    (rtreq : Dig 256) (more : List (Dig 256)) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds))) (v' : Bits),
      TypedOracleCompiler.Run.Thin.chainP (fun _ : Unit => Ls D d₁) (famP D d₁ cfg hcfg pd rest n back g)
          (earlyTwo (A := List T3 × List T3) d₁) none .link [c₀, c₁]
          (some ((first.answers.map OnBytes.E.triple, further.answers.map OnBytes.E.triple), σ))
          (bytesToBits run) rtreq (PQ.SOf D.C D.ds) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds))
          (PQ.wire0S D.C D.K (chalP D.base.plan.field D.K),
            PQ.wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
          (wayB D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)) 0 .first
          ((_root_.Run.rootsB o).map bytesToDig ++ more) ((), pls) =
        some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList),
          TypedOracleCompiler.Compile.Batch.Phase.loc v') ∧
      PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
      PQ.passSL D.C D.ds ρ.2 = true := by
  obtain ⟨seen, b, i, j, e⟩ := A.read
  obtain ⟨x, i0, hd, -, hst, hrun, hrho⟩ := OnBytes.Tie.readX_head _ S seen b i o j e
  have hl : (bytesToBits run).length = 256 := by rw [length_bytesToBits, A.run32]
  have hv : runOf (bytesToBits run) = some run :=
    runOf_saltOf (some run) fun r e0 => by rw [← Option.some.inj e0]; exact A.run32
  have hs : _root_.Fmt.tableItem "the first table" (digToBytes c₀) (first.answers.map OnBytes.E.triple) ++
      _root_.Fmt.tableItem "the further table" (digToBytes c₁) (further.answers.map OnBytes.E.triple) =
      S.base.statement := by
    rw [A.stm]
    unfold OnBytes.Params.Link.statement
    rw [A.root₀, A.root₁]
  have h0 := s0B (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) D.K
    (KeyLeaves.leavesAt (EntryFill.L0 D d₁) n cfg) back g c₀ c₁ (first.answers.map OnBytes.E.triple)
    (further.answers.map OnBytes.E.triple) (bytesToBits run)
    (by rw [List.length_map]; exact A.few₀) (by rw [List.length_map]; exact A.few₁) (Or.inr hl)
  have hf := head_first _ _ _ _ _ hd hst
  rw [hrun, A.runIs, hrho, A.label, A.pdIs] at hf
  rw [hs, hv] at h0
  refine PQ.chain_one_read (fun _ : Unit => Ls D d₁) D.C D.K
    (famP D d₁ cfg hcfg pd rest n back g) (earlyTwo (A := List T3 × List T3) d₁) none .link
    [c₀, c₁] (some ((first.answers.map OnBytes.E.triple, further.answers.map OnBytes.E.triple), σ))
    (bytesToBits run) (oB (g ())) D.ds
    (wayB D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)) rtreq
    (fun t => size_digToBytes _) (chalP D.base.plan.field D.K) pls S o more A.kit
    ⟨⟨seen, b, i, j, e⟩, A.fit, A.room, A.hasRound, A.plains, ?_, ?_, fun _ _ h => by cases h⟩
  · rw [A.label]
    exact rowEndB (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) D.K
      (KeyLeaves.leavesAt (EntryFill.L0 D d₁) n cfg) back g F hK
  · rw [hf]
    exact h0

/-- THE SAME OF THE ROAD's OWN CHAIN, under the same three hypotheses: the chain's half of the
compiled lax verifier, at the skeleton `PSXE` of the written link with instances
(OnBytes/TypedOracleCompiler/Slice/EntryPS.lean: `ZXE_verifier` says that the judge's verifier is the lax verifier
there), run under the page's family, at a typed string π whose salt is the run value's bits, whose
roots begin with the roots that were read and whose plain parts are those of the rounds read. -/
theorem entry_chain_run (F : FitsE D) (hK : D.K + 1 < 2 ^ 48)
    (dec : XE (List T3) lg s → _root_.Run.PQ.View → Bool)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (S : _root_.Fmt.SpecX)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ S o run pls) (σ : Sd1 lg s × Sd1 lg s)
    (π : OneProtocolProof 256 (PSXE D dec).up) (more : List (Dig 256)) (hsalt : π.salt = bytesToBits run)
    (hroots : π.roots = (_root_.Run.rootsB o).map bytesToDig ++ more)
    (hpl : π.plains = ((), pls)) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds))) (v' : Bits),
      (recomputeChainOfProof (L := Ls D d₁) .link (PSXE D dec).up (wqXE D dec)
          (embPXE D (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s))) some [c₀, c₁]
          ((first.answers.map OnBytes.E.triple, further.answers.map OnBytes.E.triple), σ) π).det
          (famP D d₁ cfg hcfg pd rest n back g) =
        some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList),
          TypedOracleCompiler.Compile.Batch.Phase.loc v') ∧
      PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn) ∧
      PQ.passSL D.C D.ds ρ.2 = true := by
  obtain ⟨ρ, v', e, hd, hp⟩ := entry_chain D d₁ cfg hcfg pd rest n back g F hK first further c₀ c₁
    S o run pls A σ π.rtreq more
  refine ⟨ρ, v', ?_, hd, hp⟩
  rw [chainP_det, hsalt, hroots, hpl]
  exact e

end TypedOracleCompiler.Slice.EntryChain
