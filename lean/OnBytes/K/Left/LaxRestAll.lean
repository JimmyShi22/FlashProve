-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxRestAll.lean: the five fields that the lax verifier's yes asks at a ground
(`LaxRest`, OnBytes/K/Left/LaxAt.lean), at every yes of the program on bytes (`RestAll`,
OnBytes/K/Left/LaxEnd.lean), from the two of them that are shown in files of their own.

`rows`, `cols` and `listed` are paid here, by OnBytes/K/Left/LaxRestAt.lean at the equation on the
strict reader that the program's yes gives (`ground`, OnBytes/K/Left/LaxGround.lean). `walks` and
`accept` are premises, each in the field's own letters.

Main names:
  `WalksAt G c hc hok a`, `AcceptAt G c a π`: the two fields, by themselves.
  `restAll_of`: `RestAll G hok` from these two at every yes of the program, and two tests on the
    ground.

Not claimed. The two premises. `RestAll` speaks under `PortYesAt` and `G.SaysLines F.pol`: that the
parameter file's lines as read are the setting's is shown of no file here. An implication between
yeses, at one fixed oracle: nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxEnd
import OnBytes.K.Left.LaxRestAt

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.EntryFill
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf wX bodyS RowsT RowsL)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround linkAtCfg AskedE seedsUnder)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

section
variable (G : EntryGround) (c : ByteArray) (hc : c.size = 32)
  (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- The field `walks` of `LaxRest` (OnBytes/K/Left/LaxAt.lean), by itself. -/
abbrev WalksAt (a : AskedE) : Prop :=
  ∃ (vert : ByteArray → ByteArray → ByteArray)
      (e1 : Enc1 (Body (Ls (entryXD G c) (d1Run G.q.link.table.cubeBits G.q.link.table.answers))))
      (Fm : ℕ → _root_.Fmt.Shape → Prop) (Rt : ℕ → Dig 256 → Prop),
    NodeLaw (famAt G c hc) vert ∧
    (∀ q z, (ownES (entryXD G c) hok).emb (.inr q) z =
      embLS (entryXD G c).C (liftT e1) (entryXD G c).ds q z) ∧
    FormsOn Fm 0 (entryXD G c).ds ∧
    (∀ run, a.out.run = some run → ∀ op ∈ ownOps a.out,
      OwnOkE (famAt G c hc) vert e1 run Fm Rt op) ∧
    (∀ op ∈ stoOps a.out,
      StoOkE (famAt G c hc) vert (bodyS (entryXD G c).a (entryXD G c).base.plan.salt).embE
        (entryXD G c).a (entryXD G c).base.cfg
        [bytesToDig a.first.root, bytesToDig a.further.root] (entryXD G c) op) ∧
    RtsL Rt (entryXD G c).C 0 (entryXD G c).ds
      (PQ.rtSL (entryXD G c).C (entryXD G c).ds a.out.rounds.toList)

/-- The field `accept` of `LaxRest`, by itself. -/
abbrev AcceptAt (a : AskedE) (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up) : Prop :=
  ∀ ρ : Rho (_root_.Run.Twin.up (SOf (entryXD G c).C (entryXD G c).ds)),
    PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn) →
    PQ.passSL (entryXD G c).C (entryXD G c).ds ρ.2 = true →
    (PSXE (entryXD G c) (decAt G c)).up.loc.accept (xOfAskedC _ _ a)
      ((wqXE (entryXD G c) (decAt G c)).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE (entryXD G c) (decAt G c)).up.loc.shape (PSXE (entryXD G c) (decAt G c)).up.ann
        (wqXE (entryXD G c) (decAt G c)).sh (rtsAt G c a.out) π.plains ρ π.opens) = true

end

/-- The five fields at every yes of the program, from the two that are shown elsewhere: for
every reading r of the entry file that the program's reader returns, with the program's seeds l0, l1
and the typed string π. hA, hb: two tests on the ground. -/
theorem restAll_of (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (hA : (G.q.link.table.answers == 0) = false)
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (hW : ∀ (F : Files) (id : String) (table further : Params.TableName),
      PortYesAt F id table further → G.SaysLines F.pol →
      ∀ (r : Entry.EntryRead) (l0 l1 : List (List E × E)),
        Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
          .ok r → r.further = further →
        WalksAt G (Params.configurationDigest [F.pol, F.lay, F.KL])
          (Params.configurationDigest_size _) (hok _ (Params.configurationDigest_size _))
          ⟨table, further, l0, l1, r.chain.out⟩)
    (hAc : ∀ (F : Files) (id : String) (table further : Params.TableName),
      PortYesAt F id table further → G.SaysLines F.pol →
      ∀ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
        (π : OneProtocolProof 256 (PSXE (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
                      (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))).up),
        Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
          .ok r → r.further = further →
        seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
          table = some l0 →
        seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
          further = some l1 →
        assembleS (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
          (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])) r.chain.out = some π →
        AcceptAt G (Params.configurationDigest [F.pol, F.lay, F.KL])
          ⟨table, further, l0, l1, r.chain.out⟩ π) :
    RestAll G hok := by
  intro F id table further h hl r l0 l1 π hr hf e0 e1 hπ
  obtain ⟨r', -, -, i, hr', -, -, -, -, -, e, -, -⟩ := ground G hA h hl
  obtain rfl : r' = r := Except.ok.inj (hr'.symm.trans hr)
  have hc := Params.configurationDigest_size [F.pol, F.lay, F.KL]
  exact ⟨fun ρ hd => rows_rest G _ (hok _ hc) ⟨table, further, l0, l1, r'.chain.out⟩ _ _ _ _ e π ρ
      hd,
    cols_rest G _ (hok _ hc) ⟨table, further, l0, l1, r'.chain.out⟩ _ _ _ _ e,
    fun ρ hd => listed_rest G _ (hok _ hc) ⟨table, further, l0, l1, r'.chain.out⟩ _ _ _ _ e
      (within_of G hb _ hc) ρ hd,
    hW F id table further h hl r' l0 l1 hr hf,
    hAc F id table further h hl r' l0 l1 π hr hf e0 e1 hπ⟩

end OnBytes.K.Left
