-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/CallInstAt.lean: `inst_port` (Johnson/Maker/Page/CallInst.lean) with three public
files pol, lay, KL given as parameters. The plan, the sizes and the record of how an instance holds
the public input are taken at these three files, and the call's three public files are assumed to be
equal to them.

  `inst_port_at`: if `K.PortYesAt` holds at the files F, F.pol = pol, F.lay = lay, F.KL = KL,
    `sizesAt pol = .ok P` and `planned pol KL (some lay) = .ok pl`, and the vocabulary is not empty
    (hV), then there is an instance i with `insOf P (K.stmOf F o) = some i`; whatever the program's
    plan and its three computations return at the call, `(pubOf pl P hV).block i = blockAt pl' links
    so.y`; i holds the call's five files; and whatever item the program forms, `reqX (withoutReply
    hV i) = item`.
  `block_of_ins`, `item_of_ins`: the second and the fourth clause, for whatever `insOf` returns at a
    call at which `K.PortYesAt` holds and whose statement meets a predicate Sv ("served") that gives
    x.pol = pol, x.lay = lay, x.KL = KL (hSv), under the same hV, `sizesAt pol = .ok P` and
    `planned pol KL (some lay) = .ok pl₀`, as universally quantified statements
    (Johnson/Flat/BigIns.lean and BigThrough.lean apply them; no theorem takes either as a
    hypothesis in this form). The item is the first half of the pair that the premise `hq` asks
    (Johnson/Maker/Page/PortProofV.lean). The description's block, the function for the item and the
    function that takes an instance's early part are variables, each fixed by an equation. Of Sv
    only these three equations are used.

Limits: nothing where `sizesAt` refuses the parameter file: the exit code 0 can occur there. One
direction only. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Maker.Page.CallInst
import Johnson.Maker.Page.BlockAtEq

set_option autoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Maker OnBytes.Flat Inst.Model OnBytes.Model OnBytes.Model.Verify

/-- **The typed instance of a call, at a plan, sizes and a record taken at three given files.** -/
theorem inst_port_at {F : K.Files} {id : String} {table further : OnBytes.Params.TableName}
    (h : K.PortYesAt F id table further) (o : Options) {P : Params} (hV : 0 < P.V)
    (pol lay KL : ByteArray) (e1 : F.pol = pol) (e2 : F.lay = lay) (e3 : F.KL = KL)
    (hP : sizesAt pol = .ok P) {pl : Planned} (hpl : planned pol KL (some lay) = .ok pl) :
    ∃ i : Instance' P, insOf P (K.stmOf F o) = some i ∧
      (∀ (pl' : Planned) (so : Head.StOwn) (cov : Head.Covered) (links : Array Stages.LinkH),
        planned F.pol F.KL (some F.lay) = .ok pl' →
        Head.stFromCall (words32 F.request) (words32 F.y) pl'.X.T = .ok so →
        Head.coveredOf so pl'.X.T pl'.X.P.h.V = .ok cov → linksOf pl'.X cov = .ok links →
        (pubOf pl P hV).block i = blockAt pl' links so.y) ∧
      (holdsIns hV pol lay KL).pub i = ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ ∧
      ∀ item, Proof.requestItem F.pol F.KL F.request = some item →
        (holdsIns hV pol lay KL).reqX (withoutReply hV i) = item := by
  subst e1 e2 e3
  obtain ⟨i, p, so', cov', item', links', _, _, _, _, hi, hRw, hQw, hpub, h1, hf, hb, h3, hreq,
    -⟩ := inst_port h o hP hV
  obtain rfl : p = pl := Except.ok.inj (h1.symm.trans hpl)
  rw [hRw, hQw] at hf
  refine ⟨i, hi, ?_, hpub, ?_⟩
  · intro pl' so cov links hp' hso hcov hl
    obtain rfl : p = pl' := Except.ok.inj (h1.symm.trans hp')
    obtain ⟨rfl, rfl, rfl⟩ := CallFacts.unique hf ⟨hso, hcov, hl⟩
    exact hb.trans (blockAt_eq p links' so'.y).symm
  · intro item hit
    obtain rfl : item' = item := Option.some.inj (h3.symm.trans hit)
    exact hreq

/-- **The block at the instance of a served call**, quantified over all calls. Sv: what "served"
says of a user's statement; only its three equations on pol, lay, KL are used. blk: the
description's block, a variable fixed by eB. -/
theorem block_of_ins {P : Params} (hV : 0 < P.V) (pol lay KL : ByteArray)
    (hP : sizesAt pol = .ok P) {pl₀ : Planned} (hpl : planned pol KL (some lay) = .ok pl₀)
    (Sv : K.UserStm → Prop) (hSv : ∀ x, Sv x → x.pol = pol ∧ x.lay = lay ∧ x.KL = KL)
    (blk : Instance' P → Blk Proof.FirstEnd) (eB : blk = (pubOf pl₀ P hV).block) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (i : Instance' P) (pl : Planned) (so : Head.StOwn) (cov : Head.Covered)
      (links : Array Stages.LinkH),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insOf P (K.stmOf F o) = some i →
      planned F.pol F.KL (some F.lay) = .ok pl →
      Head.stFromCall (words32 F.request) (words32 F.y) pl.X.T = .ok so →
      Head.coveredOf so pl.X.T pl.X.P.h.V = .ok cov → linksOf pl.X cov = .ok links →
      blk i = blockAt pl links so.y := by
  intro F o id table further i pl so cov links h hs hi hp hso hcov hl
  obtain ⟨e1, e2, e3⟩ := hSv _ hs
  obtain ⟨i', hi', hb, -, -⟩ := inst_port_at h o hV pol lay KL e1 e2 e3 hP hpl
  obtain rfl : i' = i := Option.some.inj (hi'.symm.trans hi)
  rw [eB]
  exact hb pl so cov links hp hso hcov hl

/-- **The request's item at the instance of a served call**, likewise. sp: the function that reads
the item off an instance; ear: which part of an instance is fixed first: variables, fixed by eS and
eE. -/
theorem item_of_ins {P : Params} (hV : 0 < P.V) (pol lay KL : ByteArray)
    (hP : sizesAt pol = .ok P) {pl₀ : Planned} (hpl : planned pol KL (some lay) = .ok pl₀)
    (Sv : K.UserStm → Prop) (hSv : ∀ x, Sv x → x.pol = pol ∧ x.lay = lay ∧ x.KL = KL)
    (sp : Instance' P → ByteArray) (eS : sp = (holdsIns hV pol lay KL).reqX)
    (ear : Instance' P → Instance' P) (eE : ear = withoutReply hV) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (i : Instance' P) (item : ByteArray),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insOf P (K.stmOf F o) = some i →
      Proof.requestItem F.pol F.KL F.request = some item → sp (ear i) = item := by
  intro F o id table further i item h hs hi hit
  obtain ⟨e1, e2, e3⟩ := hSv _ hs
  obtain ⟨i', hi', -, -, hq⟩ := inst_port_at h o hV pol lay KL e1 e2 e3 hP hpl
  obtain rfl : i' = i := Option.some.inj (hi'.symm.trans hi)
  rw [eS, eE]
  exact hq item hit

end Johnson.Session
