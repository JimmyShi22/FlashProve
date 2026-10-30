-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Keys.lean: CONDITIONAL: what the four key forms of an attention segment
are worth: in a world in which every named scalar that the key forms read has, under its slot, its
rule value on some cells t, the key form of call c is worth the multilinear extension of the call's
vector of looked-up values on t at the call's key point. A joining of the library's lemmas; no
algebra is in this file. A definition, and statements with their proofs.

The verifier makes the key forms in its run "first" and hands them on in its run "keys"
(Johnson/Desc/First/Att/RunsP.lean). The library has: these forms are written sums of terms
(`keys_port`, Johnson/Desc/First/Att/Claims/PortJoin.lean); such a sum is worth the library's key
form `KF` at the values under the slots (`kfPort_value`, Johnson/Road/Rows/AttKeyPort.lean); `KF` at
the rule values is the extension (`kf_worth`, Johnson/Desc/First/Att/Claims/KeysWorth.lean).

Main names:
  `RuleAt W h u D C p t`   the premise: every named scalar that the key forms read has its rule
                    value on the cells t under its slot in the world W
  `kf_is_ext`       **the key forms are four, and each is worth the extension**
  `ruleAt_of`       `RuleAt` from its two halves: the scalars that one claim ties to a table, and
                    the four that are sums of products
  `prodAt_of_reads`   the second half, where the four slots hold elements that read as the sums of
                    the steps s6b, s6d, s8 and as the accumulator's rule value

THE PREMISES OF `kf_is_ext`, AND WHAT THE LIBRARY HAS FOR EACH:
  hg, hz, hN: the claims' reading is at the shape's numbers and the lookup's key points; the plan's
    number of calls is the shape's.
  h1, hk: the runs "first" and "keys" return.
  F4 (`CallsAre`): the place has four calls in the usual order, four plane claims and two units.
  KP (`KeyPub`, Johnson/Road/Rows/AttKeyAll.lean): public numbers in the terms read as the
    library's; Johnson/Desc/First/Att/Claims/KeyPubOf.lean has statements on it.
  hC, hdeep, hs: three conditions on the lookup's numbers, which follow from the public test
    `CallsFit` (Johnson/Road/Lane5CallsOf.lean).
  hv (`RuleAt`): the one premise on values. TWO ROADS LEAD TO IT. Straight: what lies under each
    slot is the prover's scalar, and that scalar, read, is the rule value. Or: for the scalars that
    one claim ties to a table, from "every gathered form is worth 0" in a world where every table is
    true (`keys_lin_top`, Johnson/Desc/First/Att/Claims/KeysTop.lean), and for the four others as in
    `prodAt_of_reads`. Neither road is walked in this file.
The table of scales scl is an instance letter, this library's own instance being struck in this
file: at a place the shape's is meant (`sclOf`, Johnson/Road/Lane5AttDef.lean), as `KeyPub` reads
the shift of the softmax-table call. The tables tb are a free letter.
Limits. That any premise is met at a state of an honest run is not shown here. `CallsAre` asks for
four calls: a plan with two shifts in a group (six calls) is not reached. hC holds among its clauses
the one on the table of exponentials: at the three small places of PremisesToy.lean that clause
fails and the statement is idle there; at that file's fourth place the whole test says yes.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.KeysWorth
import Johnson.Desc.First.Att.Claims.PortJoin
import Johnson.Desc.K5.Honest.Law.ProductsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att.End (ReadK)
open Inst.Model (Scl)
open Inst.Model.AttSeg (Dim Calls Pub Raw rv KSc Fam keyVec Step)
open K5Law (Six unitsSix CallsAre padOf oldOf)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **Every named scalar that the key forms read has its rule value on the cells t under its
slot.** -/
def RuleAt (W : World K) (h : Attention.Heard) (u : Units) (D : Dim) (C : Calls) (p : Pub K)
    (t : Raw → K) : Prop :=
  ∀ k, ReadK D k → slotVal W h u k = rv D C p t k

/-- **The key forms are four, and each is worth the extension of its call's vector of looked-up
values at the call's key point.** Conditional; the premises are listed in the file's head. -/
theorem kf_is_ext [scl : Scl] (A : Plan) {S : Attention.Shape} {gL : Forest.Heard}
    {i : P.Runs.In} {n : ℕ} {l₁ : List Aff} {j : JoinsP} {k3 : PadIn} {kf : Array Aff} {s : Six}
    {c0 c1 c2 c3 : ACall} (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i n = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (F4 : CallsAre (oldOf S gL i) s c0 c1 c2 c3) {C : Calls} {p : Pub K}
    (KP : KeyPub ρ (oldOf S gL i) (unitsSix (oldOf S gL i) s) C p (S.shd c1.sh)
      (padOf (oldOf S gL i) c1))
    (tb : Inst.Model.Tables) {t : Raw → K}
    (hv : RuleAt W (oldOf S gL i) (unitsSix (oldOf S gL i) s) (L5.dimOf S) C p t)
    (hC : C.OK (L5.dimOf S)) (hdeep : ∀ f : Fam, f.l (L5.dimOf S) ≤ C.Dk) (hs : C.a 0 = C.a 1) :
    kf.size = 4 ∧ ∀ c : Fin 4, (kf.getD c.val (Aff.ofConst zeroE)).value ρ W =
      Blocks.ext (C.a c) (keyVec (L5.dimOf S) tb t c) (C.zC c p.z) := by
  have ej := (K5Law.first_any A S gL i n l₁ j hg hz hN h1).2
  have ek : kf = (K5Law.joinsT (oldOf S gL i)).kf := by
    rw [K5Law.keys_is _ _ _ _ hk, ej, ← K5Law.joinsT_att A _ hN]
    rfl
  obtain ⟨z4, zc⟩ := K5Law.keys_port F4 ((oldOf S gL i).t.score.getD 0 default)
    ((oldOf S gL i).t.score.getD 1 default)
  refine ⟨by rw [ek]; exact z4, fun c => ?_⟩
  rw [ek, zc c]
  exact (kfPort_value W KP c).trans (K5Law.kf_worth (L5.dimOf S) C tb p t hv hC hdeep hs c)

/-- `RuleAt` from its two halves. -/
theorem ruleAt_of {h : Attention.Heard} {u : Units} {D : Dim} {C : Calls} {p : Pub K}
    {t : Raw → K} (hl : ∀ k, ReadK D k → Linear k → slotVal W h u k = rv D C p t k)
    (hp : ∀ k, ¬ Linear k → slotVal W h u k = rv D C p t k) : RuleAt W h u D C p t := fun k hr => by
  by_cases hk : Linear k
  · exact hl k hr hk
  · exact hp k hk

/-- **The four scalars that no claim ties to a table have their rule values**, where their slots
hold the sums of three summands that read as the library's steps s6b, s6d and s8, and an element
that reads as the accumulator's rule value. -/
theorem prodAt_of_reads {h : Attention.Heard} {u : Units} {D : Dim} {C : Calls} {p : Pub K}
    {t : Raw → K} {SM SD SE : Summand} (RM : StepReads ρ SM D C p t .s6b)
    (RD : StepReads ρ SD D C p t .s6d) (RE : StepReads ρ SE D C p t .s8) {acc : E}
    (ha : ρ.val acc = rv D C p t .acc)
    (sM : slotVal W h u (.ss .M) = ρ.val SM.total) (sD : slotVal W h u (.ss .D) = ρ.val SD.total)
    (sE : slotVal W h u .zo = ρ.val SE.total) (sA : slotVal W h u .acc = ρ.val acc) :
    ∀ k, ¬ Linear k → slotVal W h u k = rv D C p t k := by
  intro k hk
  match k, hk with
  | .ss .M, _ => rw [sM, RM.total]; rfl
  | .ss .D, _ => rw [sD, RD.total]; rfl
  | .zo, _ => rw [sE, RE.total]; rfl
  | .acc, _ => rw [sA, ha]
  | .cell _ _, hk => exact absurd trivial hk
  | .ms _, hk => exact absurd trivial hk
  | .zc, hk => exact absurd trivial hk
  | .rh, hk => exact absurd trivial hk
  | .rh', hk => exact absurd trivial hk
  | .ib _, hk => exact absurd trivial hk
  | .rg, hk => exact absurd trivial hk
  | .rg', hk => exact absurd trivial hk

end H2K5.Honest

#print axioms H2K5.Honest.kf_is_ext
#print axioms H2K5.Honest.ruleAt_of
#print axioms H2K5.Honest.prodAt_of_reads
