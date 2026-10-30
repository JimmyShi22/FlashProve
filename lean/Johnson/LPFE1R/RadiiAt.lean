-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/RadiiAt.lean: THE HEAD's NAMED TEST "radii" (`P5T.radIsB` at P5J.At's letters:
At.Five's fifth, Johnson/P5J/TestsAtRun.lean; PlanOk's field radii) COMES DOWN TO ONE Bool THAT
READS NO SEAT AND NO ENTRY: "THE LAW-SIDE MAKER OF THE SENDINGS' ROWS RETURNS": (P5T.rowsAt? Zp.pol
Z.lay Zp.KL).isSome. Theorems on public data. A law file; no running text imports it.

  `pub_files`     the public part bears the files' own bytes.
  `sends_tie`     AT THE SECOND HASH FUNCTION: what Johnson.G.sendsOf returns at the three files is
                  what sendsFrom returns at what the proof file's own maker has made: the sendings
                  do not hang on the digest of the files (configure_at,
                  OnBytes/Tie/EntryPlanAtCfg.lean).
  `radii_of_rows`   ProofFile.pubPlain secondHashFunction pol lay KL = .ok Zp · Johnson.G.sendRowsOf pol lay KL = .ok
                  rows ⊢ radIsB rows Zp.made.proof.1.sends.length (radOf rows) (planSeats Zp dl) =
                  true.
  `At.radii_at`   in the letter of the join (HeadLeft's field radii): LaidAt secondHashFunction … Zp Np cF ·
                  (P5T.rowsAt? Zp.pol Z.lay Zp.KL).isSome = true ⊢ radIsB … = true.
  `At.radii_of_read`   the same against the one name P5J.rowsRead Z (
                  Johnson/Goal/Skeleton/RowsRead.lean): "RETURNS" IS ENOUGH FOR radIsB: nothing
beyond it is asked. Beneath: Johnson/Desc/First/Link/Law/RowsFirst.lean (rows_first · mine_le ·
radIsB_of_some · sendsFrom_tags).

Limits. IT STRIKES NOTHING: "the rows' maker returns" STAYS A NAMED CONDITION: sendRowsOf,
packListOf and Johnson.G.callsOf are texts on the laws' side: nothing that the verifier runs calls
them; packListOf refuses on its own at nine places, each of which holds the planner's plan against a
second text of the planner. Of LaidAt the field pub alone is spent. At secondHashFunction alone. Nothing on what
the radii are. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.RowsFirst
import Johnson.Desc.First.Link.Law.EndsOfMade
import Johnson.Goal.Skeleton.RowsRead
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import OnBytes.Model.Fit.PlannedParts
import OnBytes.Tie.EntryPlanAtCfg
import Johnson.P5J.TestsAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (ChainSends SendRow sendRowsOf sendsOf)
open VerifiableInference.Number (sendsFrom)
open P5T (planSeats radIsB radOf)

/-- The public part bears the files' own bytes. -/
theorem pub_files {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zp : ProofFile.Pub}
    (h : ProofFile.pubPlain o pol lay KL = .ok Zp) : Zp.pol = pol ∧ Zp.KL = KL := by
  have h' : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Zp := h
  unfold ProofFile.pubBy at h'
  obtain ⟨m, _, h'⟩ := ProofFile.Law.bind_ok h'
  simp only [bind, Except.bind, pure, Except.pure] at h'
  repeat' split at h'
  all_goals first | contradiction | (cases h'; exact ⟨rfl, rfl⟩)

/-- **The sendings do not hang on the digest.** -/
theorem sends_tie {pol lay KL : ByteArray} {Zp : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp) {sends : List ChainSends}
    (hs : sendsOf pol lay KL = .ok sends) : sendsFrom Zp.made.p.chains.made = .ok sends := by
  rw [VerifiableInference.Number.sendsOf_eq] at hs
  obtain ⟨p, hp, hs⟩ := exc_bind hs
  unfold OnBytes.Model.Verify.planned at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  dsimp only at hp
  obtain ⟨ch, hc, hp⟩ := exc_bind hp
  obtain ⟨b, _, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨m, hm, hb⟩ := ProofFile.Law.pub_madeOfAtO
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL = .ok Zp from h)
  unfold VerifiableInference.PlanWritten.madeOfAtO at hm
  obtain ⟨p', hp', hm⟩ := exc_bind hm
  obtain ⟨s', _, hm⟩ := exc_bind hm
  have ep := VerifiableInference.Number.packMade_p hm
  have e1 : Zp.made.p.chains = p'.chains := by
    rw [← hb, ← ep]
    rfl
  obtain ⟨hX', hc'⟩ := VerifiableInference.PlanWritten.plannedAtO_parts hp'
  rw [VerifiableInference.PlanWritten.publicOfO_older] at hX'
  obtain rfl : X = p'.X := Except.ok.inj (hX.symm.trans hX')
  obtain ⟨l1, x1, hs1, hf1, _, _⟩ := OnBytes.Model.Verify.chainsOf_parts hc
  obtain ⟨l2, x2, hs2, hf2, _, _⟩ := OnBytes.Model.Verify.chainsOf_parts hc'
  obtain ⟨-, rfl⟩ : l1 = l2 ∧ x1 = x2 := by
    have := Except.ok.inj (hs1.symm.trans hs2)
    exact Prod.mk.inj this
  obtain ⟨a1, a2, a3, b1, b2, b3, _, _, hat⟩ := OnBytes.Tie.configure_at hf1
  have e2 := Except.ok.inj ((hat VerifiableInference.Desc.fixedConfigurationDigest).symm.trans hf2)
  rw [e1, ← e2]
  exact hs

/-- **Where the rows' maker returns, the test accepts.** -/
theorem radii_of_rows {pol lay KL : ByteArray} {Zp : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp) {rows : List SendRow}
    (hr : sendRowsOf pol lay KL = .ok rows) (dl : List Fmt.DeclaredRound) :
    radIsB rows Zp.made.proof.1.sends.length (radOf rows) (planSeats Zp dl) = true := by
  obtain ⟨sends, hs⟩ : ∃ sends, sendsOf pol lay KL = .ok sends := by
    unfold sendRowsOf at hr
    obtain ⟨sends, hs, _⟩ := exc_bind hr
    exact ⟨sends, hs⟩
  obtain ⟨⟨k0, k1, k2, e, p1, p2, hm⟩, _⟩ :=
    made_parts (show ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL = .ok Zp from h)
  obtain rfl : sends = _ := Except.ok.inj ((sends_tie h hs).symm.trans hm)
  obtain ⟨t0, t1, t2, t3, t4, t5, t6⟩ := sendsFrom_tags hm
  have hf := rows_first hr hs t0 t1 t2 t3 t4 t5 t6
  refine radIsB_of_some _ _ _ fun k hk i hi => ?_
  have hle := mine_le Zp dl k
  rw [List.getElem?_eq_getElem hk] at hle
  refine rad_some hf (k := k) (c := cnt Zp.made.proof.1.sends[k]) ?_ (Nat.lt_of_lt_of_le hi hle)
  rw [List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

end VerifiableInference.Desc.LinkJoin

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- **"radii" comes down to "the rows' maker returns".** -/
theorem At.radii_at {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hrows : (P5T.rowsAt? Zp.pol Z.lay Zp.KL).isSome = true) :
    P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (At.rad Zp Z.lay) (At.pseats Zp) = true := by
  obtain ⟨e1, e2⟩ := VerifiableInference.Desc.LinkJoin.pub_files L.pub
  obtain ⟨rows, hr⟩ := Option.isSome_iff_exists.1 hrows
  have hR : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok rows := by
    rw [e1, e2] at hr
    unfold P5T.rowsAt? at hr
    cases hq : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL with
    | error w => rw [hq] at hr; cases hr
    | ok x =>
      rw [hq] at hr
      exact congrArg Except.ok (Option.some.inj hr)
  unfold At.rad
  rw [hr]
  exact VerifiableInference.Desc.LinkJoin.radii_of_rows L.pub hR Zp.D.1

/-- **The same against the one name** (P5J.rowsRead,
Johnson/Goal/Skeleton/RowsRead.lean). -/
theorem At.radii_of_read {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h : rowsRead Z) :
    P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (At.rad Zp Z.lay) (At.pseats Zp) = true := by
  obtain ⟨e1, e2⟩ := VerifiableInference.Desc.LinkJoin.pub_files L.pub
  exact At.radii_at L (by rw [e1, e2]; exact h.some)

end P5J

#print axioms P5J.At.radii_of_read
#print axioms VerifiableInference.Desc.LinkJoin.sends_tie
#print axioms VerifiableInference.Desc.LinkJoin.radii_of_rows
#print axioms P5J.At.radii_at
