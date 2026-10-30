-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadersHold.lean: kind K5: THE READER's THREE LISTS HOLD THE LAW's: at the record behind the kind's lay, under the law's record of returns (Returns, Att/K05GatheredZero.lean, WITH ITS FIELD u3), the
generic reader ("the reader is the run itself": Johnson/Desc/First/Batch/ReaderOf.lean) gives at (2, "first") just l₁, at (2, "second") just l₂, at (2, "join") just [xj.1], each with no late slot: the premise hRd of the
carriage from the table's items to the forms' worth (Att/K05WorthAtTable.lean's billsWorthJ_of_formsT, in its form that hands the relation behind and the hearing's law's facts).

The reader is in Johnson/Desc/First/Batch/ReaderOf.lean. NOTHING COUNTED.

Main names:
  BehindOk A Kc gL s: WHAT IS ASKED OF THE RECORD BEHIND THE LAY, and of nothing else.
  unpaid_of_left: what the lookup's kind leaves (Fo.PadLeft) has the join's debt unpaid. unpaid_below: the kind's hearing leaves the debts.
  keysOfO_is: the seat's key forms are the law's kf.
  readers_hold: at one record: the three equations. hRd_of_readers: **hRd.**
THE LETTERS: Rd := Readers.ofStates states, states 2 = runsN A · S := A.S · tl := A.seam.tl · nW := A.nW · lk0 a := lookOfO (parCOf A).geo.lmb (gOf a) · tj := [] (the seated run calls joinF g KF F []) · A0 a letter with
  A0.iU3 = A.iU3 · k3 a letter with k3 = padOfO (gOf a).shape at every a with "on".
hB IS ASKED ONLY WHERE b.1 IS WHAT THE LAY MAKES OF a.1: without that tie it would ask of every b behind the record of every a in front.
IS IT EMPTY HERE? An implication; BehindOk is shown of no record here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05GatheredZero
import Johnson.Desc.First.Att.K05JoinThereAt
import Johnson.Desc.First.Att.K05HearBelow
import Johnson.Desc.First.Att.Claims.K5ReaderAt
import Johnson.Desc.First.Att.Claims.HeardPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9 (Read Readers lateOf ownRow readerOf RunOf runOfForms)
open K5Law (inAt inAt_is inOf_isAt firstAt secondAt firstAt_is secondAt_is first_named second_named heardPlain_of_said
  readers_at runsN_is matsOf)

/-- **What is asked of the record behind the lay.** -/
structure BehindOk (A : Attention.Plan) (Kc : ℕ) (gL : Forest.Heard) (s : First.S) : Prop where
  at_ : ∃ a₀ T, s.here = .att a₀ ∧ a₀.g = some gL ∧ a₀.lookHeard = some gL ∧ a₀.F.trees[A.iU3]? = some T ∧ T.K = Kc ∧
    T.R = 1 ∧ A.nW ≤ T.K ∧ K3.unpaid a₀.F gL.owedJoin = true ∧
    ∀ kf xj, keysOfO A s = some kf → Look.joinF gL kf a₀.F [] = some xj → xj.1.ents.all (ownRow a₀.F) = true

/-- What the lookup's kind leaves has the join's debt unpaid. -/
theorem unpaid_of_left {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard} (L : Fo.PadLeft h F F' g) :
    K3.unpaid F' g.owedJoin = true := by
  unfold K3.unpaid
  rw [L.owed, L.owedAt.2.2]
  simp [Array.getElem_push]

/-- The kind's hearing leaves the debts. -/
theorem unpaid_below {F G : Fork} (b : Below F G) (n : ℕ) : K3.unpaid G n = K3.unpaid F n := by
  unfold K3.unpaid
  rw [show G.owed = F.owed from congrArg (·.owed) b.2.1]

section One
variable (A : Attention.Plan) {gL : Forest.Heard} {h : Heard} {G : Fork} {l : Left} {i : Runs.In} {Kc : ℕ} {T : HTree}
  {s : First.S} {a₀ : First.AttOwn}

/-- The seat's key forms are the law's. -/
theorem keysOfO_is (hs : s.here = .att a₀) (hg : a₀.g = some gL) (h5 : a₀.heard5 = some h) (hF : a₀.F = G)
    (hin : inAt (parCOf A) gL h G = some (i, Kc)) {l₁ : List Aff} {jn : Runs.JoinsP} {kf : Array Aff}
    (first : Runs.firstRun i Kc = some (l₁, jn)) (keys : Runs.keysRun i (padOfO gL.shape) jn = some kf) :
    keysOfO A s = some kf := by
  unfold keysOfO keysOfK
  rw [inOf_isAt hs, hg, h5, hF]
  have hp : (seatCO (parCOf A)).pad s = some (padOfO gL.shape) := by
    show (match s.here with | .att a => a.g.map fun g : Forest.Heard => padOfO g.shape | _ => none) = _
    rw [hs]
    show a₀.g.map (fun g : Forest.Heard => padOfO g.shape) = _
    rw [hg]
    rfl
  simp only [Option.bind_eq_bind, Option.bind_some, hin, hp, first]
  exact keys

end One

/-- **At one record: the reader's three lists are the law's.** -/
theorem readers_hold (A A0 : Attention.Plan) (eu : A0.iU3 = A.iU3) {states : ℕ → List (RunOf First.S)}
    (hst : states 2 = runsN A) {Kc : ℕ} {gL : Forest.Heard} {s₀ : First.S} {att : First.AttOwn} {h : Heard} {G : Fork}
    {xr : Params.AttentionRounds} {Ls : Lists} (hs : Said xr h G Ls) (B : BehindOk A Kc gL (behind s₀ att h G)) {l : Left}
    {i : Runs.In} {l₁ l₂ : List Aff} {jn : Runs.JoinsP} {kf : Array Aff} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (Rt : Returns A.S gL.zx gL.zk G h l A0 gL i Kc l₁ l₂ jn (padOfO gL.shape) kf G [] xj A.seam.tl A.nW
      (lookOfO (parCOf A).geo.lmb gL)) :
    readerOf states 2 "first" (behind s₀ att h G) = some { forms := l₁, late := [] } ∧
      readerOf states 2 "second" (behind s₀ att h G) = some { forms := l₂, late := [] } ∧
      readerOf states 2 "join" (behind s₀ att h G) = some { forms := [xj.1], late := [] } := by
  obtain ⟨a₀, T, he, hg, hlk, hT, hK, hR1, hW, hun, hjo⟩ := B.at_
  obtain rfl : a₀ = { att with F := G, heard5 := some h } := by
    have : (First.Here.att { att with F := G, heard5 := some h }) = .att a₀ := he
    cases this
    rfl
  have hT' : G.trees[A.iU3]? = some T := hT
  have u3 : i.iU3 = A.iU3 := Rt.u3.trans eu
  have hc := heardPlain_of_said hs
  have e1 := firstAt_is A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT' hK Rt.first
  have e2 := secondAt_is A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT' hK Rt.second
  have own : ∀ (L : List Aff), (∀ f ∈ L, ∀ x ∈ f.ents.toList, x.tree = (parCOf A).iU3 ∧ x.row = 0 ∧ x.idx < (parCOf A).nW) →
      ∀ f ∈ L, f.ents.all (ownRow G) = true := fun L hL f hf =>
    all_ownRow fun e he' => ⟨(hL f hf e he').2.1, T, by rw [(hL f hf e he').1]; exact hT', hR1⟩
  have hst' : states 2 = (runsO A).map runOfForms := hst.trans (runsN_is A)
  obtain ⟨r1, r2⟩ := readers_at A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT' hK hst' (s := behind s₀ att h G) rfl hg rfl
    rfl Rt.first Rt.second (own l₁ (first_named e1 hc hT' hW)) (own l₂ (second_named e2 hc hT' hW))
  refine ⟨r1, r2, ?_⟩
  have hin := inAt_is A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT' hK
  have hk : keysOfO A (behind s₀ att h G) = some kf :=
    keysOfO_is A (s := behind s₀ att h G) rfl hg rfl rfl hin Rt.first Rt.keys
  have hG2 : ((behind s₀ att h G).putFork xj.2.1).fork? = some (G.paid gL.owedJoin) := by
    rw [joinF_ledger Rt.join]
    rfl
  exact readerOf_runN' (by rw [hst]; exact find_join A) (joinRun_behind A hlk hun hk Rt.join) rfl hG2 (lateOf_paid G _)
    fun f hf => by
      obtain rfl := List.mem_singleton.1 hf
      exact hjo kf xj hk Rt.join

/-- **hRd**, in the form that hands the relation behind and the hearing's law's facts. -/
theorem hRd_of_readers {W Y : Type} (A A0 : Attention.Plan) (eu : A0.iU3 = A.iU3) (Kc : ℕ) (k3 : Runs.PadIn)
    (gOf : First.S × Y → Forest.Heard) (xr : Params.AttentionRounds) (on : First.S × Y → Prop)
    (R' : First.S × Y → W → Prop) {states : ℕ → List (RunOf First.S)} (hst : states 2 = runsN A)
    (hk3 : ∀ a, on a → k3 = padOfO (gOf a).shape)
    (hB : ∀ a b w, on a → R' b w → ∀ (F G : Fork) (h : Heard), seatSO.ledger a.1 = some F →
      seatSO.lay a.1 h G = some b.1 → BehindOk A Kc (gOf a) b.1) :
    ∀ (a b : First.S × Y) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G → G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i Kc l₁ l₂ jn k3 kf G [] xj A.seam.tl A.nW
          (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : Read,
          (Readers.ofStates states).forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          (Readers.ofStates states).forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          (Readers.ofStates states).forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms := by
  intro a b w ha hR F G h Ls h1 h2 hs _ _ l i l₁ l₂ jn kf xj Rt
  obtain ⟨att, _, _, eb⟩ := lay_is h1 h2
  have B := hB a b w ha hR F G h h1 h2
  rw [eb] at B
  rw [hk3 a ha] at Rt
  obtain ⟨r1, r2, r3⟩ := readers_hold A A0 eu hst hs B Rt
  rw [eb]
  exact ⟨_, _, _, r1, rfl, fun f hf => hf, r2, rfl, fun f hf => hf, r3, rfl, List.mem_singleton.2 rfl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.unpaid_of_left
#print axioms VerifiableInference.Desc.First.Att.P.unpaid_below
#print axioms VerifiableInference.Desc.First.Att.P.readers_hold
#print axioms VerifiableInference.Desc.First.Att.P.hRd_of_readers
