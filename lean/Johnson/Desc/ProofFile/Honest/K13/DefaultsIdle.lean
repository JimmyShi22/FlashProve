-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/DefaultsIdle.lean: kind K13, the members' batching: FIVE OF THE
WRITTEN VALUES AND SILENT DEFAULTS IN WHAT THE KIND's HONEST SIDE READS: EACH IS IDLE, OR IS NOT
TAKEN UNDER A NAMED CONDITION. Statements with their proofs; no definition. IT IS NOT THE WHOLE
LIST: what it leaves is named at the end of this head.

The five places, and what is shown of each.
  1 `q0Idle` (PileOfAnySize.lean of this folder): a written value handed as the public data of the
    layers' honest parts: the layers' public data, the blank plan, and 0 in every number. IDLE, AT
    EVERY SIZE: of these data the claims' text overwrites four fields (`k4PubOfSeg`,
    SitesOfDefs.lean) and reads no other (`layersClaims_four`): so the filler is the same function
    at every value in that place (`pileOfAnySize_any_q0`, `pileAnyK3_any_q0`), the layers' parts'
    own data among them.
  2 The empty pile where `onlineFirstChainAt` rejects (`pileBoxOfAnySize`, the same file). NOT TAKEN where
    that function returns (`pileOfAnySize_of_chain`). That it returns under the library's one
    hypothesis at the full size: `pileAnyK3_at_head` (FiveAt355.lean of this folder).
  3 x := 0 where no challenge stands in front of the sumcheck's part, or the last one holds no
    element (`k13Job`, Part.lean; `k13X`, Plays.lean). NOT TAKEN at challenges that fit the kind's
    rounds: the first of them holds just one element, and that is x (`k13X_of_fit`).
  4 x, eps := 0 where the data of the message W find fewer challenges than they read (`wG`,
    WData.lean). NOT TAKEN WHERE THESE DATA's OWN TEST `ready` ACCEPTS (`wData_ready_own`).
  5 The count of challenges := 0 where the public data have no such round (`wHeard`, WData.lean).
    NOT TAKEN WHERE `ready` ACCEPTS (`wDataAt_ready_heard`). A stronger law: under the library's one
    hypothesis at the full size the count is a written number (`k13_wHeard_at_head`,
    AtFullSide/K13/WFillAtHead.lean).
4 AND 5 ARE CONDITIONAL: that `ready` accepts at a run's challenges is shown neither here nor in any
file that this one imports.

WHAT IS NOT TREATED HERE, BY NAME.
  The filler's other arm without a row: where one site's row cannot be made it yields none
    (`pileBySites`, Johnson/Desc/K13/Honest/PileDefs.lean), with the defaults beneath it that
    PileOfAnySize.lean's head lists. At a stand of the first chain's thread in front of the kind's
    member, at a base's ground and where the thread's clause on the reply has begun, that arm is not
    taken: `k13_pile_made_at_355` (FiveAt355.lean). That is the reading by the kind's own parts. The
    data of the message W read the same filler one member later: of that reading nothing is shown.
  The mask form and the target of the filler's rows: not treated here.
  `k13Wit`'s mask entries, 0 (Part.lean): the tables read the matrix alone: `tabsOf_mat` (Tie.lean).
  `smallInOf`'s cells and weights' digits, 0 (SitesOfDefs.lean): no claim reads them:
    `layersClaims_reads` (ClaimsText.lean).
  In `sumPart` (Honest/Sum.lean), which every kind with a masked sumcheck calls: eps := 0 where the
    part has heard no challenge of its own; the default variable; zeros where a list of values or of
    coins is too short (`padTo`). Not treated for this kind by itself. `withPoints`' placeholder for
    a variable without a point does not arise: the kind's variables are all summed plainly
    (`k13_all`, Plays.lean).
  In WData.lean: the default code where the shape's number names none (`wEll`); `wVec`'s 0 from
    2^kCol on, which is the true value.

What is not claimed. That the hypothesis at the full size holds at any public files. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySize
import Johnson.Desc.ProofFile.Honest.K13.WData
import Johnson.Desc.ProofFile.Honest.K13.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where battRounds fromOf?)
open ProofFile.Honest.SumLaw (elemOf)

/-! ## 1 The written public data of the layers' parts are idle -/

/-- **Of the public data of the layers' honest parts the claims read four fields alone**: the
layers' public data, the plan, the group's number and the count of rounds in front. -/
theorem layersClaims_four {Xi : Type} {Q Q' : K4Pub} (hP : Q.P = Q'.P) (hhp : Q.hp = Q'.hp)
    (hg : Q.g = Q'.g) (hr : Q.r0 = Q'.r0) (wOf : Xi → K4In) (x : Xi) (hd : List Fmt.Drawn) :
    layersClaims Q wOf x hd = layersClaims Q' wOf x hd := by
  obtain ⟨P, hp, g, link, piece, r0, seg⟩ := Q
  obtain ⟨P', hp', g', link', piece', r0', seg'⟩ := Q'
  obtain rfl : P = P' := hP
  obtain rfl : hp = hp' := hhp
  obtain rfl : g = g' := hg
  obtain rfl : r0 = r0' := hr
  rfl

/-- The claims' text, at any size, is the same at every value of that parameter. -/
theorem claimsTextOf_any_q0 (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub)
    (lookAt : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ Q₁ : Nat → K4Pub) :
    claimsTextOf c Z lookAt headArm Q₀ = claimsTextOf c Z lookAt headArm Q₁ := by
  funext l x hd
  unfold claimsTextOf
  by_cases e : l = headSegOf Z
  · rw [if_pos e, if_pos e]
  · rw [if_neg e, if_neg e]
    exact layersClaims_four rfl rfl rfl rfl _ x hd

/-- So is the filler over a chain. -/
theorem pileAtChain_any_q0 (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ Q₁ : Nat → K4Pub) :
    pileAtChain c Z headArm Q₀ = pileAtChain c Z headArm Q₁ := by
  unfold pileAtChain
  rw [claimsTextOf_any_q0 c Z _ headArm Q₀ Q₁]

/-- **THE PILE's FILLER IS THE SAME FUNCTION AT EVERY VALUE OF THAT PARAMETER**, at every size. -/
theorem pileOfAnySize_any_q0
    (armOf : Chain S ProofFile.Cl → ProofFile.Pub → ProofFile.Ground →
      ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim))
    (Q₀ Q₁ : ProofFile.Pub → Nat → K4Pub) : pileOfAnySize armOf Q₀ = pileOfAnySize armOf Q₁ := by
  funext Z G
  unfold pileOfAnySize pileBoxOfAnySize
  cases ProofFile.onlineFirstChainAt Z with
  | error _ => rfl
  | ok c =>
    show pileAtChain c Z (armOf c Z G) (Q₀ Z) = pileAtChain c Z (armOf c Z G) (Q₁ Z)
    exact pileAtChain_any_q0 c Z _ _ _

/-- **The closed term is the filler at every value in the place of its written zeros.** -/
theorem pileAnyK3_any_q0 (Q₀ : ProofFile.Pub → Nat → K4Pub) :
    pileAnyK3 = pileOfAnySize headArmOfSeg Q₀ :=
  pileOfAnySize_any_q0 headArmOfSeg q0Idle Q₀

/-! ## 2 The empty pile on an error -/

/-- Where the chain is made, the filler is the filler over that chain. -/
theorem pileOfAnySize_of_chain
    (armOf : Chain S ProofFile.Cl → ProofFile.Pub → ProofFile.Ground →
      ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim))
    (Q₀ : ProofFile.Pub → Nat → K4Pub) {Z : ProofFile.Pub} {c : Chain S ProofFile.Cl}
    (hc : ProofFile.onlineFirstChainAt Z = .ok c) (G : ProofFile.Ground) :
    pileOfAnySize armOf Q₀ Z G = pileAtChain c Z (armOf c Z G) (Q₀ Z) := by
  unfold pileOfAnySize pileBoxOfAnySize
  rw [hc]

/-! ## 3 x, in the sumcheck's part -/

/-- **At challenges that fit the kind's rounds, x is the one element of the first of them**: neither
the default for an empty list nor that for a challenge without an element is taken. front: any list:
meant: what has been heard in front of the kind's rounds. -/
theorem k13X_of_fit (p : Where) (front ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds p) ds = true) :
    ∃ (d₀ : Fmt.Drawn) (rest : List Fmt.Drawn) (x : E),
      ds = d₀ :: rest ∧ d₀.elems = [x.triple] ∧ k13X (front ++ [d₀]) = x := by
  obtain ⟨x, eps, gs, hb, -⟩ := fits_batt p ds hd
  cases ds with
  | nil => cases hb
  | cons d₀ rest =>
    have h0 : bare d₀ = k13Dr x := (List.cons.inj hb).1
    have he : d₀.elems = [x.triple] := congrArg Fmt.Drawn.elems h0
    refine ⟨d₀, rest, x, rfl, he, ?_⟩
    rw [k13X_snoc]
    unfold elemOf
    rw [he]
    rfl

/-! ## 4, 5 The data of the message W -/

variable {Xi : Type}

/-- **Where the data's own test accepts, the batching's own challenges are x, eps and a point of
kCol coordinates, and each of the challenges read holds just one element**: no default is taken. -/
theorem wData_ready_own (codes : Codes) (Sh : LinShape) (n u : Nat) (pile : PileOf Xi) (x : Xi)
    (hd : List Fmt.Drawn) (a : MsgAddr) (h : (wData codes Sh n u pile x).ready hd a = true) :
    (∃ (y eps : E) (pt : List E), wOwn Sh n hd = y :: eps :: pt ∧ pt.length = Sh.kCol) ∧
      ∀ d ∈ hd.drop (n - (2 + Sh.kCol)), d.elems.length = 1 := by
  have h' : (wPublic codes Sh n u && hd.length == n &&
      ((hd.drop (n - (2 + Sh.kCol))).all fun d => d.elems.length == 1) &&
      (pile x (wFront Sh n hd)).length == u && Batt.fits Sh.kCol (pile x (wFront Sh n hd)) &&
      (pile x (wFront Sh n hd)).all fun r => r.g.all fun t => t.vars == Sh.kRow) = true := h
  simp only [Bool.and_eq_true, wPublic, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hn⟩, -⟩, hl⟩, he⟩, -⟩, -⟩, -⟩ := h'
  refine ⟨?_, he⟩
  have hlen : (wOwn Sh n hd).length = 2 + Sh.kCol := by
    unfold wOwn drawnE
    rw [List.length_map, List.length_drop, hl]
    omega
  match hw : wOwn Sh n hd, hlen with
  | y :: eps :: pt, hlen =>
    exact ⟨y, eps, pt, rfl, by simp only [List.length_cons] at hlen; omega⟩
  | [_], hlen => simp only [List.length_cons, List.length_nil] at hlen; omega
  | [], hlen => simp only [List.length_nil] at hlen; omega

/-- **Where the data's own test accepts at a proof file's public data, these have the batching's
first round**: the count 0 is not taken. -/
theorem wDataAt_ready_heard (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    (hd : List Fmt.Drawn) (a : MsgAddr) (h : (wDataAt pile Z G x).ready hd a = true) :
    (fromOf? Z).isSome = true := by
  cases e : fromOf? Z with
  | some _ => rfl
  | none =>
    have q := (wDataAt_none pile Z G e x a).2 hd
    rw [h] at q
    cases q

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.layersClaims_four
#print axioms ProofFile.Honest.K13.claimsTextOf_any_q0
#print axioms ProofFile.Honest.K13.pileAtChain_any_q0
#print axioms ProofFile.Honest.K13.pileOfAnySize_any_q0
#print axioms ProofFile.Honest.K13.pileAnyK3_any_q0
#print axioms ProofFile.Honest.K13.pileOfAnySize_of_chain
#print axioms ProofFile.Honest.K13.k13X_of_fit
#print axioms ProofFile.Honest.K13.wData_ready_own
#print axioms ProofFile.Honest.K13.wDataAt_ready_heard
