-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KeysSlots.lean: CONDITIONAL: the one premise on values of the statements
on the key forms of an attention segment (`RuleAt`, Johnson/Desc/K5/Honest/Law/Keys.lean), carried
back to "under each named scalar's slot the world holds the prover's scalar, read". A joining of
lemmas; no algebra is in this file. Definitions, and statements with their proofs.

The statements on the key forms stand at the units that the library's lemmas on the place conclude
at (`sixTop`, Johnson/Desc/First/Att/Claims/PortTop.lean). The prover's scalars, read, under the
library's names (`scalarOf`, Johnson/Desc/K5/Honest/Law/RuleAll.lean) are written over the values
that the verifier's function of the points returns. Here the two spellings are joined.

Main names:
  `slotP a1 a2 k1 k2 d`   the slot of each named scalar, in the verifier's own letters: a1, a2:
                    where the two remainder units' values begin; k1, k2: the two softmax-table
                    units; d: the division's points
  `slotOf_sixTop`   the library's `slotOf` at these units is `slotP`
  `ScalarsAt`       the premise: under each slot the world holds the value v of that name; v is a
                    letter: the prover's scalar, read, is the caller's choice of it
  `ruleAt_of_scalars`   **`RuleAt` at these units, from `ScalarsAt` and that each scalar, read, is
                    its rule value**
  `lookups_of`      where the verifier's function of the points returns at a place with the four
                    usual calls, two remainder units were heard and two softmax-table units are
                    returned
  `kf_at_law'`      `kf_at_law` (Johnson/Desc/K5/Honest/Law/KeysAtPlan.lean) without its four
                    look-ups: `RuleAt` is asked at whatever these return

Who is meant to show `ScalarsAt`: whoever ties the world's slots to what the prover sent. That each
scalar, read, is its rule value: `scalar_rule_all` (RuleAll.lean), under its own premises.
Limits. That any premise is met at a state of an honest run is not shown here.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.KeysAtPlan
import Johnson.Desc.K5.Honest.Law.RuleAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf RemP ScoreP DivP)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att.End (ReadK)
open K5Law (unitsSix oldOf sixTop PlanLaw LookAll KeyIs PlaceIs)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **The slot of each named scalar of the key forms**, in the verifier's own letters. A name that
the library's list does not hold gets the slot 0, as in the library's `slotOf`. -/
def slotP (a1 a2 : ℕ) (k1 k2 : ScoreP) (d : DivP) : Inst.Model.AttSeg.KSc → ℕ
  | .cell .m1 jj => a1 + jj
  | .cell .d1 jj => a2 + jj
  | .cell .m2 jj => k1.s0 + jj
  | .cell .d2 jj => k2.s0 + jj
  | .cell _ _ => 0
  | .ms .M => k1.s0 + 5
  | .ms .D => k2.s0 + 5
  | .ss .M => k1.s0 + 6
  | .ss .D => k2.s0 + 6
  | .acc => (K5Law.divBack d).sACC
  | .zo => (K5Law.divBack d).sZO
  | .zc => (K5Law.divBack d).sZC
  | .rh => (K5Law.divBack d).sRH
  | .rh' => (K5Law.divBack d).sRHP
  | .ib k => d.sIB + k
  | .rg => d.s5h
  | .rg' => d.s5h + 1

/-- The library's `slotOf` at the units of the statements on the key forms. -/
theorem slotOf_sixTop (S : Attention.Shape) (gL : Forest.Heard) (i : P.Runs.In)
    (zk : Array (Array E)) (a1 a2 : ℕ) (k1 k2 : ScoreP) (k : Inst.Model.AttSeg.KSc) :
    slotOf (oldOf S gL i) (unitsSix (oldOf S gL i) (sixTop S i zk a1 a2 k1 k2)) k =
      slotP a1 a2 k1 k2 i.p.d k := by
  match k with
  | .cell .m1 _ => rfl
  | .cell .d1 _ => rfl
  | .cell .m2 _ => rfl
  | .cell .d2 _ => rfl
  | .cell .w3 _ => rfl
  | .cell .x3 _ => rfl
  | .cell .f4 _ => rfl
  | .ms .M => rfl
  | .ms .D => rfl
  | .ss .M => rfl
  | .ss .D => rfl
  | .acc => rfl
  | .zo => rfl
  | .zc => rfl
  | .rh => rfl
  | .rh' => rfl
  | .ib _ => rfl
  | .rg => rfl
  | .rg' => rfl

/-- **Under each named scalar's slot the world holds the value v of that name**, for the names that
the key forms read. -/
def ScalarsAt (W : World K) (D : Inst.Model.AttSeg.Dim) (a1 a2 : ℕ) (k1 k2 : ScoreP) (d : DivP)
    (v : Inst.Model.AttSeg.KSc → K) : Prop :=
  ∀ k, ReadK D k → W.slot (slotP a1 a2 k1 k2 d k) = v k

/-- **`RuleAt` at the units of the statements on the key forms**, from what lies under the slots and
that each such value is the rule value. -/
theorem ruleAt_of_scalars {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}
    {zk : Array (Array E)} {a1 a2 : ℕ} {k1 k2 : ScoreP} {C : Inst.Model.AttSeg.Calls}
    {p : Inst.Model.AttSeg.Pub K} {t : Inst.Model.AttSeg.Raw → K}
    {v : Inst.Model.AttSeg.KSc → K} (hs : ScalarsAt W (L5.dimOf S) a1 a2 k1 k2 i.p.d v)
    (hv : ∀ k, ReadK (L5.dimOf S) k → v k = Inst.Model.AttSeg.rv (L5.dimOf S) C p t k) :
    RuleAt W (oldOf S gL i) (unitsSix (oldOf S gL i) (sixTop S i zk a1 a2 k1 k2)) (L5.dimOf S) C p
      t := fun k hr => by
  unfold slotVal
  rw [slotOf_sixTop, hs k hr, hv k hr]

section
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {gL : Forest.Heard} {i : P.Runs.In}
  {hh : P.Heard} {L' : P.Left} {zk : Array (Array E)}

/-- **Two remainder units were heard and two softmax-table units are returned**, where the
verifier's function of the points returns at a place with the four usual calls. -/
theorem lookups_of {c0 c1 c2 c3 : ACall} (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S)
    (hP : P.pointsOf i.g zk hh L' = some i.p) :
    ∃ a1 a2 k1 k2, hh.remainders[0]? = some a1 ∧ hh.remainders[1]? = some a2 ∧
      i.p.scores[0]? = some k1 ∧ i.p.scores[1]? = some k2 := by
  have PA := K5Law.points_are hP
  have Pn := K5Law.planes_are hP
  obtain ⟨_, _, nS⟩ := K5Law.points_counts hP
  have nR : hh.remainders.size = 2 := by
    rw [← Pn.nR, hg, K5Law.place_kr Pl]
    rfl
  have nH : hh.scores.size = 2 := by
    rw [← PA.nH, hg, K5Law.place_scores Pl]
    rfl
  have nS' : i.p.scores.size = 2 := nS.trans nH
  exact ⟨hh.remainders[0], hh.remainders[1], i.p.scores[0], i.p.scores[1],
    Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega),
    Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)⟩

end

section
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {gL : Forest.Heard} {i : P.Runs.In}
  {n : ℕ} {l₁ : List Aff} {j : JoinsP} {k3 : PadIn} {kf : Array Aff} {zx zy : Array E}
  {hh : P.Heard} {L' : P.Left} {p : Inst.Model.AttSeg.Pub K} {t : Inst.Model.AttSeg.Raw → K}

/-- **The key forms are four, and each is worth the extension of its call's vector of looked-up
values at the call's key point**: `kf_at_law` without its four look-ups. Conditional as that
statement; `RuleAt` is asked at whatever the four look-ups return. -/
theorem kf_at_law' (A : Plan) {lid : ℕ} {cf : Attention.Cfg}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs) (N : Numerals ρ)
    (Lk : LookAll ρ fs zx zy p) (hK : ∀ q : Fin 4, KeyIs fs zx zy (gL.zk.getD q.val #[]) q)
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hP : P.pointsOf i.g gL.zk hh L' = some i.p)
    (h1 : P.Runs.firstRun i n = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (tb : Inst.Model.Tables)
    (hv : ∀ a1 a2 k1 k2, hh.remainders[0]? = some a1 → hh.remainders[1]? = some a2 →
      i.p.scores[0]? = some k1 → i.p.scores[1]? = some k2 →
      RuleAt W (oldOf S gL i) (unitsSix (oldOf S gL i) (sixTop S i gL.zk a1 a2 k1 k2))
        (L5.dimOf S) (L5.callsOf fs) p t) :
    kf.size = 4 ∧ ∀ c : Fin 4, (kf.getD c.val (Aff.ofConst zeroE)).value ρ W =
      Blocks.ext ((L5.callsOf fs).a c)
        (Inst.Model.AttSeg.keyVec (scl := L5.sclOf S) (L5.dimOf S) tb t c)
        ((L5.callsOf fs).zC c p.z) := by
  obtain ⟨a1, a2, k1, k2, ha1, ha2, hk1, hk2⟩ := lookups_of PL.place hg hP
  exact kf_at_law A hid PL N Lk hK hg hz hP ha1 ha2 hk1 hk2 h1 hk tb
    (hv a1 a2 k1 k2 ha1 ha2 hk1 hk2)

end

end H2K5.Honest

#print axioms H2K5.Honest.slotOf_sixTop
#print axioms H2K5.Honest.ruleAt_of_scalars
#print axioms H2K5.Honest.lookups_of
#print axioms H2K5.Honest.kf_at_law'
