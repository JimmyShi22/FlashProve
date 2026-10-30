-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/RadiiInScope.lean: IN THE GOALS' SCOPE THE RADII OF THE FIRST PROOF CHAIN's
SAMPLED ORACLE MESSAGES, as the maker of the rows of the sendings computes them (`sendRowsOf`,
Johnson/G/LinkSig.lean), ARE THE WRITTEN ONES (`radsFull`, Johnson/HB/LLHARD/RadiiWritten.lean).
Statements with their proofs; nothing is evaluated here.

  `sends_of_pub`: a tool.
  `radii_in_scope`: **the statement**: (firstRows R).map (·.sampled) = radsFull.
  `rad_in_scope`: the same in the law's own reader `P5T.rad?` (Johnson/P5T/MembersByMake.lean).
  `radii_at_name`: the same from `LaidAt` (Johnson/P5J/LaidOpens.lean).

THE PREMISES, EACH WITH ITS PAYER: the scope · the public part is made at the second hash function
(`LaidAt.pub`) · hy: an accept of `madePinnedAt`: `LPFD.asks_pins`, where the thirteen-row prefix
of the verifier's entry tests is laid · hr: THE ROWS' MAKER RETURNS: asked by no test of the
verifier and given by no theorem: a named condition.

THE CHAIN. The maker reads the files a second time, through the program `verify-on-bytes`'s own
planner. (1) Where it returns, so has that planner (`planned_of_rows`), and its value is a second
text's at the public part's own planner's value: THE TWO PLANNERS' JOIN (`made_tie`, `rows_of_made`,
Johnson/Desc/First/Link/Law/RowsOfMade.lean). (2) The first proof chain's list of calls has the
samples off the sizes (`calls_say`, Johnson/HB/LLHARD/RadiiSays.lean). (3) The first
proof chain's rows are the fifth block, and their radii are the text on one chain's at these samples
(`first_block`, Johnson/HB/LLHARD/RadiiFirstBlock.lean). (4) The sizes and the setting are the
written ones (`made_in_scope`), the sendings too (`sends_in_scope`, with `sends_of_pub`). (5) At the
written values Lean's kernel has evaluated that text (`radii_written`).

Limits. The first proof chain alone. Nothing says that a verifier reads these radii. Nothing on
soundness.
-/
import Johnson.HB.LLHARD.RadiiSays
import Johnson.HB.LLHARD.RadiiFirstBlock
import Johnson.LPFE1R.RowsOneInScope
import Johnson.P5T.MembersByMake
import Johnson.P5J.LaidOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.G.MadeFree
open VerifiableInference.Number (sendsFrom)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (writtenMade made_in_scope sends_in_scope)

/-- The proof file's three lists of sendings in a public part are the last three of the seven that
are made of its own planner's value. -/
theorem sends_of_pub {pol lay KL : ByteArray} {Zp : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp) :
    ∃ k0 k1 k2 e, sendsFrom Zp.made.p.chains.made =
      .ok [k0, k1, k2, e, Zp.made.proof.1, Zp.made.proof.2.1, Zp.made.proof.2.2] := by
  obtain ⟨m, hm, hb⟩ := ProofFile.Law.pub_madeOfAtO
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL = .ok Zp from h)
  unfold VerifiableInference.PlanWritten.madeOfAtO at hm
  obtain ⟨p', _, hm⟩ := exc_bind hm
  obtain ⟨s', hs', hm⟩ := exc_bind hm
  unfold VerifiableInference.Number.packMade at hm
  split at hm
  · rename_i k0 k1 k2 e p0 p1 p2
    obtain rfl := Except.ok.inj hm
    rw [← hb]
    exact ⟨k0, k1, k2, e, hs'⟩
  · cases hm

/-- **IN THE GOALS' SCOPE THE FIRST PROOF CHAIN's ROWS' RADII ARE THE WRITTEN ONES**: sending by
sending, each sampled oracle message's shape and radius. hy: an accept of the verifier's test on the
sizes, the lists of rounds and the sendings. hr: the rows' maker returns. -/
theorem radii_in_scope {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {R : List SendRow}
    (hr : sendRowsOf W.pol W.lay W.KL = .ok R) :
    (P5T.firstRows R).map (·.sampled) = radsFull := by
  obtain ⟨p, hp⟩ := planned_of_rows hr
  rw [rows_of_made h hp] at hr
  obtain ⟨k0, k1, k2, e, p0, p1, p2, q, hs, hq, hR⟩ := first_block hr fun _ _ hc => calls_say hc
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
  rw [hR]
  exact Option.some.inj w

/-- The same in the law's own reader of a radius. -/
theorem rad_in_scope {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {R : List SendRow}
    (hr : sendRowsOf W.pol W.lay W.KL = .ok R) (k i : Nat) :
    P5T.rad? R k i = ((radsFull[k]?).bind (·[i]?)).map (·.2) := by
  have e := congrArg (·[k]?) (radii_in_scope hW h hy hr)
  simp only [List.getElem?_map] at e
  unfold P5T.rad?
  rw [← e]
  cases (P5T.firstRows R)[k]? <;> rfl

/-- **In the letters of the laws at the head.** -/
theorem radii_at_name {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) {R : List SendRow}
    (hr : sendRowsOf Z.pol Z.lay Z.KL = .ok R) :
    (P5T.firstRows R).map (·.sampled) = radsFull := radii_in_scope hZ L.pub hy hr

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sends_of_pub
#print axioms VerifiableInference.Desc.LinkJoin.radii_in_scope
#print axioms VerifiableInference.Desc.LinkJoin.rad_in_scope
#print axioms VerifiableInference.Desc.LinkJoin.radii_at_name
