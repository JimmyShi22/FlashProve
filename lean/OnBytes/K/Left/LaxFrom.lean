-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxFrom.lean: from the exit code 0 to the first premises of `lax_at`
(OnBytes/K/Left/LaxAt.lean), at both grounds, at one value a of the converter and one typed string
π.

Main names:
  `conv_eq`: the strict converter `convE` returns a := the two tables that the program threads, the
    program's seeds at both names, and what `Entry.read` read of the chain.
  `from_port_of`: at a ground G whose chain is shown (a premise in the form of
    `chain_full` | `chain_small`, OnBytes/K/Left/LaxChain.lean) and whose description at an empty
    statement is within the limits: there are r, l0, l1 and π with: `conv_eq`'s equation; the
    typing makes π of what was read; `ChainYes` at a and π; no round has more than 64 bits of work
    and the stored openings are in order; and the decision of a run at the typed instance says yes
    on the view of what was read.
  `from_port_full`, `from_port_small`: that at the two grounds. Hypotheses: `PortYesAt` and
    `G.SaysLines F.pol`, no other.

Limits: values alone. Nothing on soundness; no probability. The five fields of `LaxRest` are not
here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxKeys
import OnBytes.K.Left.AsmAt
import OnBytes.K.Left.LaxAt

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Run (PQ.okX)
open _root_.Run (bytesToDig)

/-- The strict converter's value, from what `read_at` names. -/
theorem conv_eq {q : Params.Link} {table further : Params.TableName} {ent : ByteArray}
    {r : Entry.EntryRead} {l0 l1 : List (List E × E)}
    (hr : Entry.read q table ent = .ok r) (hf : r.further = further)
    (a0 : seedsUnder recordSeeds q table = some l0)
    (a1 : seedsUnder recordSeeds q further = some l1) :
    convE q table ent = some ⟨table, further, l0, l1, r.chain.out⟩ := by
  simp only [convE, hr, hf, a0, a1, Option.bind_some, Option.map_some]

/-- What is concluded, at a ground G, files F and the two tables. c: the three public files' digest.
-/
def FromPort (G : EntryGround) (F : Files) (table further : Params.TableName) : Prop :=
  ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
    (π : OneProtocolProof 256 (PSXE (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
                  (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))).up),
    convE (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
      some ⟨table, further, l0, l1, r.chain.out⟩ ∧
    assembleS (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
      (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])) r.chain.out = some π ∧
    ChainYes G (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) (d1Run _ _) G.q.link.table
      (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])) table further r.chain.out π
      (xOfAskedC _ _ ⟨table, further, l0, l1, r.chain.out⟩).2 ∧
    ((∀ d ∈ (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL])).ds, d.entry.work ≤ 64) ∧
      TypedOracleCompiler.Run.PQ.okX (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL])).ds
        (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL])).a
        (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL])).xs = true) ∧
    decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])
      (xOfAskedC _ _ ⟨table, further, l0, l1, r.chain.out⟩)
      (Fmt.viewX (Params.entrySpecOf
        (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) G.rs
        (Params.Link.statement table further)) r.chain.out) = true

/-- From the exit code 0, at a ground whose chain is shown. -/
theorem from_port_of (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two)
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    {F : Files} {id : String} {table further : Params.TableName}
    (hchain : ∀ (seen : Fmt.Seen) (i j : ℕ) (o : Fmt.ChainOut) σ,
      (∀ run, o.run = some run → run.size = 32) →
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
        (Params.entrySpecOf (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) G.rs
          (Params.Link.statement table further)) seen F.ent i = some (o, j) →
      ∀ π, assembleS (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
          (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])) o = some π →
        ChainYes G (Params.configurationDigest [F.pol, F.lay, F.KL])
          (Params.configurationDigest_size _) (d1Run _ _) G.q.link.table
          (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])) table further o π σ)
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    FromPort G F table further := by
  obtain ⟨r, l0, l1, i, hr, hf, a0, a1, e, hd⟩ := dec_yes G hA hF rfl rfl rfl h hl
  obtain ⟨π, hπ⟩ := asm G hA h hl hr
    (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))
  rw [specAt_with] at e hd
  have h32 : ∀ run, r.chain.out.run = some run → run.size = 32 := by
    intro run hrun
    obtain ⟨run', h1, h2⟩ := run_of_read (_root_.Run.PQ.size_HO Fmt.oracle Fmt.size_oracle) e
      (fun h => by cases h)
    obtain rfl : run' = run := Option.some.inj (h1.symm.trans hrun)
    exact h2
  exact ⟨r, l0, l1, π, conv_eq hr hf a0 a1, hπ, hchain _ _ _ _ _ h32 e π hπ,
    descr_of G _ (within_of G hb _ (Params.configurationDigest_size _)), hd⟩

/-- At the full size. -/
theorem from_port_full {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : recordGround.SaysLines F.pol) :
    FromPort recordGround F table further := by
  obtain ⟨-, -, -, -, -, -, -, -, h0, h1, -⟩ := ground recordGround record_answers h hl
  obtain ⟨hd, f0, f1, -⟩ := ground_bounds recordGround record_answers h hl
  exact from_port_of recordGround record_answers record_field full_base_ok
    (fun seen i j o σ h32 e π hπ => chain_full _ _ _ _ _ table further h0 h1 seen F.ent i j o h32
      f0 f1 σ hd e π hπ) h hl

/-- At the small example. -/
theorem from_port_small {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : smallRecordGround.SaysLines F.pol) :
    FromPort smallRecordGround F table further := by
  obtain ⟨-, -, -, -, -, -, -, -, h0, h1, -⟩ := ground smallRecordGround small_record_answers h hl
  obtain ⟨hd, f0, f1, -⟩ := ground_bounds smallRecordGround small_record_answers h hl
  exact from_port_of smallRecordGround small_record_answers small_record_field small_base_ok
    (fun seen i j o σ h32 e π hπ => chain_small _ _ _ _ _ table further h0 h1 seen F.ent i j o h32
      f0 f1 σ hd e π hπ) h hl

end OnBytes.K.Left
