-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/TableClosed.lean: IN THE GOALS' SCOPE, WHERE THE PROOF FILE's
TEST ON WHAT THE PLANNER MADE ACCEPTS (madePinnedAt), THE CODE SWITCH's TYPED TABLE
(K2Caller.tableOf, Johnson/Top/H0/K2Caller/Table.lean) IS THE WRITTEN ONE (tableFullLit), WHEREVER
IT RETURNS. THE PIN FORCES THE VALUE, NOT THE RETURN: a yes of the named test tableWrittenB says
both "tableOf returns" and "its value is the written table": here the second follows from the pin;
the first is shown nowhere here. Definitions, closed facts by Lean's kernel AT WRITTEN VALUES (no
file is read), and theorems. A law file; no running text imports it. WHY IT IS SO. tableOf =
tableFrom z sub R (tableOf_iff). z: the planner's sizes: pinned. sub: at
most its open rows are read (tableFrom_sub), and by the text they are one a link. R: the rows of the
sendings: of them tableFrom reads linkRows alone, which keeps the first proof chain's rows; and
these are a block made of the first chain's sendings (pinned) and their radii
(radii_written, by the kernel).
  `first_rows_block`  where the rows are made: the first proof chain's rows ARE blockOf p0 q.
                    first_block (Johnson/HB/LLHARD/RadiiFirstBlock.lean) WITH ITS
                    LAST STEP LEFT OUT: its proof, line for line; its statement keeps one column,
                    this one the rows.
  `blockOf_snd`, `blockOf_congr`   a block reads of its share the second column alone.
  `rowsFirstW`        the first proof chain's rows at the written sendings and the written radii.
  `first_rows_written`   in scope, under the pin: wherever sendRowsOf returns R: P5T.firstRows R =
                    rowsFirstW.
  `linkRows_of_first`, `tableFrom_first`   tableFrom reads of R the first proof chain's rows alone.
  `subOpenW`          a stand-in for the sub-proofs: one open row a link.
  `table_closed`      BY THE KERNEL: swRowsB (tableFrom proofSizedFull subOpenW rowsFirstW)
                    tableFullLit = true: all ten fields of all 25 rows.
  `table_closed_rad`, `table_closed_label`, `table_closed_kept`, `table_closed_radius`   THE
                    CONTROLS, BY THE KERNEL, EACH TURNING ONE FIELD: a row of the sendings with its
                    radii one more; with its label turned; the written table's first row with its
                    kept places emptied; with its radius one more: the comparison says no.
  `table_in_scope`    InScope W · pubPlain secondHashFunction W.pol W.lay W.KL = .ok Z · madePinnedAt … =
                    true · tableOf W.pol W.lay W.KL = .ok t ⊢ t = tableFullLit.
  `row_in_scope`      so: ∀ m r, ProofFile.rowAtK2 Z.pol W.lay Z.KL m = some r → tableFullLit[m]? =
                    some r.
  `row_at_laid`       the same where the verifier's own value is laid (P5J.LaidAt).
  `hr_at_laid`        so the five public equations on that row (RowPubAt.lean beside this file:
                    the premise hr of K10's premise on the carried claim), from the scope and "the
                    value is laid": the pin comes by pins_of_laid, so with the entry tests that the
                    verifier asks where the value is laid; no further named test is left.

This file does not show that "the pin forces its yes".


Limits. THAT tableOf RETURNS is not said: where it does not, the ends are idle; a spender that wants
a row to BE there (not only: whatever row is there is the written one) wants that return from
elsewhere. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.Opts.TableOne
import Johnson.Top.H0.K2Caller.TableWritten
import Johnson.HB.LLHARD.RadiiInScope
import Johnson.Desc.ProofFile.Law.CarryAtLaw
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.LPFE1R.RowPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.G.MadeFree
open VerifiableInference.Number (sendsFrom)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (writtenMade made_in_scope sends_in_scope)
open VerifiableInference.Desc.First.K2Caller (SwRow tableOf tableFrom tableOf_iff tableFrom_sub
  older_sized_written tableFullLit swRowsB swRowsB_eq)

/-- **The first proof chain's rows are the fifth block**: the rows, not one column. -/
theorem first_rows_block {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm}
    {R : List SendRow} (h : rowsFrom c o n A = .ok R)
    (hA : ∀ s ch, callsFrom c o n A = .ok (s, ch) → s = c.sized.set ∧
      ∃ a0 a1 a2 a3 a4 a5 a6, ch = [a0, a1, a2, a3, a4, a5, a6] ∧ a4.file = "proof" ∧
        a4.chain = 0 ∧ a4.calls.flatMap Call.sendSamples = samplesP0 c.sized.proof) :
    ∃ k0 k1 k2 e p0 p1 p2 q, sendsFrom c = .ok [k0, k1, k2, e, p0, p1, p2] ∧
      packChain c.sized.set "proof" 0 (samplesP0 c.sized.proof) p0 = .ok q ∧
      P5T.firstRows R = blockOf p0 q := by
  unfold rowsFrom at h
  obtain ⟨sends, hs, h⟩ := exc_bind h
  obtain ⟨pack, hp, h⟩ := exc_bind h
  obtain ⟨k0, k1, k2, e, p0, p1, p2, rfl, t0, t1, t2, t3, t4, t5, t6⟩ := sends_tags hs
  unfold packFrom at hp
  obtain ⟨⟨s, ch⟩, hc, hp⟩ := exc_bind hp
  obtain ⟨rfl, a0, a1, a2, a3, a4, a5, a6, rfl, f4, c4, s4⟩ := hA s ch hc
  dsimp only at hp
  obtain ⟨sends', hs', hp⟩ := exc_bind hp
  obtain rfl : [k0, k1, k2, e, p0, p1, p2] = sends' := Except.ok.inj (hs.symm.trans hs')
  obtain ⟨per, hper, hp⟩ := exc_bind hp
  cases hp
  rw [show List.zip [a0, a1, a2, a3, a4, a5, a6] [k0, k1, k2, e, p0, p1, p2] =
    [(a0, k0), (a1, k1), (a2, k2), (a3, e), (a4, p0), (a5, p1), (a6, p2)] from rfl] at hper
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, u0, u1, u2, u3, u4, u5, u6, rfl⟩ := mapM7 hper
  have g0 : packChain c.sized.set a0.file a0.chain (a0.calls.flatMap Call.sendSamples) k0 =
    .ok q0 := u0
  have g1 : packChain c.sized.set a1.file a1.chain (a1.calls.flatMap Call.sendSamples) k1 =
    .ok q1 := u1
  have g2 : packChain c.sized.set a2.file a2.chain (a2.calls.flatMap Call.sendSamples) k2 =
    .ok q2 := u2
  have g3 : packChain c.sized.set a3.file a3.chain (a3.calls.flatMap Call.sendSamples) e =
    .ok q3 := u3
  have g4 : packChain c.sized.set a4.file a4.chain (a4.calls.flatMap Call.sendSamples) p0 =
    .ok q4 := u4
  have g5 : packChain c.sized.set a5.file a5.chain (a5.calls.flatMap Call.sendSamples) p1 =
    .ok q5 := u5
  have g6 : packChain c.sized.set a6.file a6.chain (a6.calls.flatMap Call.sendSamples) p2 =
    .ok q6 := u6
  rw [f4, c4, s4] at g4
  refine ⟨k0, k1, k2, e, p0, p1, p2, q4, hs, g4, ?_⟩
  have F2 : List.Forall₂ (fun (d : ChainSends) (q : List (Codes × List (OracleShape × Nat))) =>
      q.length = d.sends.length) [k0, k1, k2, e, p0, p1, p2] [q0, q1, q2, q3, q4, q5, q6] :=
    .cons (packChain_len g0) (.cons (packChain_len g1) (.cons (packChain_len g2)
      (.cons (packChain_len g3) (.cons (packChain_len g4) (.cons (packChain_len g5)
        (.cons (packChain_len g6) .nil))))))
  dsimp only at h
  split at h
  swap
  · obtain ⟨_, e', _⟩ := exc_bind h
    cases e'
  obtain ⟨_, _, h⟩ := exc_bind h
  have hR : R = ((([k0, k1, k2, e, p0, p1, p2].flatMap fun c => c.sends.map fun s => (c, s)).zip
      [q0, q1, q2, q3, q4, q5, q6].flatten).map fun x =>
      (⟨x.1.1.file, x.1.1.chain, x.1.2.entry, x.1.2.label, x.1.1.codes, x.2.2,
        (x.1.2.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow)) :=
    (Except.ok.inj h).symm
  rw [hR, zip_blocks _ _ F2]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, firstRows_append]
  rw [firstRows_no q0 (by rw [t0.1, t0.2]; rfl), firstRows_no q1 (by rw [t1.1, t1.2]; rfl),
    firstRows_no q2 (by rw [t2.1, t2.2]; rfl), firstRows_no q3 (by rw [t3.1, t3.2]; rfl),
    firstRows_yes q4 (by rw [t4.1, t4.2]; rfl), firstRows_no q5 (by rw [t5.1, t5.2]; rfl),
    firstRows_no q6 (by rw [t6.1, t6.2]; rfl)]
  simp only [List.nil_append, List.append_nil]

/-- A block reads of its share the second column alone. -/
theorem blockOf_snd (d : ChainSends) (q : List (Codes × List (OracleShape × Nat))) :
    blockOf d q = (d.sends.zip (q.map (·.2))).map fun x =>
      (⟨d.file, d.chain, x.1.entry, x.1.label, d.codes, x.2,
        (x.1.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow) := by
  unfold blockOf
  rw [List.zip_map_right, List.map_map]
  rfl

theorem blockOf_congr (d : ChainSends) {q q' : List (Codes × List (OracleShape × Nat))}
    (h : q.map (·.2) = q'.map (·.2)) : blockOf d q = blockOf d q' := by
  rw [blockOf_snd, blockOf_snd, h]

/-- The first proof chain's rows at the written values. -/
def rowsFirstW : List SendRow := blockOf proofSends0 (radsFull.map fun s => (({} : Codes), s))

/-- **In scope, under the pin, the first proof chain's rows are the written ones.** -/
theorem first_rows_written {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {R : List SendRow}
    (hr : sendRowsOf W.pol W.lay W.KL = .ok R) : P5T.firstRows R = rowsFirstW := by
  obtain ⟨p, hp⟩ := planned_of_rows hr
  rw [rows_of_made h hp] at hr
  obtain ⟨k0, k1, k2, e, p0, p1, p2, q, hs, hq, hR⟩ :=
    first_rows_block hr fun _ _ hc => calls_say hc
  obtain ⟨k0', k1', k2', e', hs'⟩ := sends_of_pub h
  have ep : p0 = Z.made.proof.1 := by
    have t := Except.ok.inj (hs.symm.trans hs')
    simp only [List.cons.injEq] at t
    exact t.2.2.2.2.1
  have hroad : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z := h
  have e1 : Z.made.p.chains.made.sized = writtenMade.sized :=
    congrArg Free.sized (made_in_scope hW hroad hy)
  have es : Z.made.proof.1 = proofSends0 := congrArg (·.1) (sends_in_scope hW hroad hy)
  rw [e1, ep, es] at hq
  have w := radii_written
  rw [show packChain recordSet "proof" 0 (samplesP0 proofSizedFull) proofSends0 = .ok q from hq]
    at w
  have hq2 : q.map (·.2) = radsFull := Option.some.inj w
  rw [hR, ep, es]
  unfold rowsFirstW
  refine blockOf_congr _ ?_
  rw [hq2, List.map_map]
  exact (List.map_id _).symm

/-- Of the rows a link's rows are the first proof chain's. -/
theorem linkRows_of_first (R : List SendRow) (l : ℕ) :
    linkRows (P5T.firstRows R) l = linkRows R l := by
  unfold linkRows P5T.firstRows
  rw [List.filter_filter]
  refine List.filter_congr fun r _ => ?_
  cases (r.file == "proof") <;> cases (r.chain == 0) <;> simp

/-- tableFrom reads of R the first proof chain's rows alone. -/
theorem tableFrom_first (z : ProofSized) (sub : Subproofs) (R : List SendRow) :
    tableFrom z sub (P5T.firstRows R) = tableFrom z sub R := by
  unfold tableFrom linkList
  simp only [linkRows_of_first]

/-- A stand-in for the sub-proofs: one open row a link. -/
def subOpenW : Subproofs :=
  { links := [], openRows := List.replicate proofSizedFull.request.link.length 1,
    plan := fun _ _ => pure (), pendingRows := 0, matrixRows := 0 }

set_option maxRecDepth 1000000 in
/-- **The one kernel line, at written values.** -/
theorem table_closed :
    swRowsB (tableFrom proofSizedFull subOpenW rowsFirstW) tableFullLit = true := by
  decide +kernel

/-! ## The comparison can say no -/

set_option maxRecDepth 1000000 in
/-- One radius turned. -/
theorem table_closed_rad : swRowsB (tableFrom proofSizedFull subOpenW
    (rowsFirstW.modifyHead fun r => { r with sampled := r.sampled.map fun x => (x.1, x.2 + 1) }))
    tableFullLit = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One label turned. -/
theorem table_closed_label : swRowsB (tableFrom proofSizedFull subOpenW
    (rowsFirstW.modifyHead fun r => { r with label := "elsewhere" })) tableFullLit = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Against the written table with its first row's kept places emptied. -/
theorem table_closed_kept : swRowsB (tableFrom proofSizedFull subOpenW rowsFirstW)
    (tableFullLit.modifyHead fun r => { r with kept := [] }) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Against the written table with its first row's radius one more. -/
theorem table_closed_radius : swRowsB (tableFrom proofSizedFull subOpenW rowsFirstW)
    (tableFullLit.modifyHead fun r => { r with rad := r.rad + 1 }) = false := by decide +kernel

/-! ## In scope -/

/-- **In scope, under the pin, the typed table is the written one, wherever it returns.** -/
theorem table_in_scope {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {t : List SwRow}
    (ht : tableOf W.pol W.lay W.KL = .ok t) : t = tableFullLit := by
  obtain ⟨p, R, hp, hR, rfl⟩ := tableOf_iff.1 ht
  rw [older_sized_written hW h hy hp, ← tableFrom_first, first_rows_written hW h hy hR]
  exact (tableFrom_sub _ rfl _).trans (swRowsB_eq table_closed)

/-- **So the row of the sentence on the carried claim is the written table's.** -/
theorem row_in_scope {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (m : ℕ) (r : SwRow)
    (hr : ProofFile.rowAtK2 Z.pol W.lay Z.KL m = some r) : tableFullLit[m]? = some r := by
  obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files h
  rw [e1, e2] at hr
  unfold ProofFile.rowAtK2 at hr
  cases ht : tableOf W.pol W.lay W.KL with
  | error e =>
    rw [ht] at hr
    cases hr
  | ok t =>
    rw [ht, table_in_scope hW h hy ht] at hr
    exact hr

/-- The same where the verifier's own value is laid. -/
theorem row_at_laid {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF) (m : ℕ) (r : SwRow)
    (hr : ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL m = some r) : tableFullLit[m]? = some r :=
  row_in_scope hZ L.pub (P5J.pins_of_laid hZ L).1 m r hr

/-- **The premise hr of K10's premise on the carried claim, from the scope and "the value is
laid" alone.** -/
theorem hr_at_laid {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF) (m : ℕ) :
    ∀ r, ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL m = some r → r.cs = codesFull2 ∧ r.lo = loAt m ∧
      r.g = gsAt m ∧ (∀ i : Fin (loAt m).length, kbW m i = true ↔ i.val ∈ r.kept) ∧
      r.rad ≤ radFull := by
  intro r hr
  have hw := row_at_laid hZ L m r hr
  have hm : m < 25 := by
    have := (List.getElem?_eq_some_iff.1 hw).1
    simpa [tableFullLit] using this
  have hB := List.all_eq_true.1 lit_pub m (List.mem_range.2 hm)
  rw [hw] at hB
  exact rowPub_of_B hB

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hr_at_laid
#print axioms VerifiableInference.Desc.LinkJoin.first_rows_block
#print axioms VerifiableInference.Desc.LinkJoin.blockOf_congr
#print axioms VerifiableInference.Desc.LinkJoin.first_rows_written
#print axioms VerifiableInference.Desc.LinkJoin.tableFrom_first
#print axioms VerifiableInference.Desc.LinkJoin.table_closed
#print axioms VerifiableInference.Desc.LinkJoin.table_closed_rad
#print axioms VerifiableInference.Desc.LinkJoin.table_closed_label
#print axioms VerifiableInference.Desc.LinkJoin.table_closed_kept
#print axioms VerifiableInference.Desc.LinkJoin.table_closed_radius
#print axioms VerifiableInference.Desc.LinkJoin.table_in_scope
#print axioms VerifiableInference.Desc.LinkJoin.row_in_scope
#print axioms VerifiableInference.Desc.LinkJoin.row_at_laid
