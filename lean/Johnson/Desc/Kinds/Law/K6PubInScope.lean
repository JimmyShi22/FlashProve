-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TWELVE TESTS
ON PUBLIC PARAMETERS OF Law/K6PubNumbers.lean ACCEPT: k6PubC X = true IS A THEOREM THERE. Statements
and proofs.

By Law/HeadFsWritten.lean (the shape of the lookup on the head's calls), Law/HeadPlanWritten.lean
(the plan's sizes) and Johnson/Desc/First/Look/K3PlaceLetters.lean's place_head (the place of the
lookup on the calls). New here: the place of the lookup on the digits of the head's smallness test.

  shape_cut, planH2_cut   the record of the smallness test's lookup in the head's plan is what
                   Forest.shape makes of its two calls, with padding numbers that pass
                   Forest.pubAsk.
  lk_full          the committed matrix of weights has 2^18 columns (by the kernel, on a closed
                   term).
  calls_place      placeAt X 24 false: there; its shape, first slot and number of slots.
  digits_place     placeAt X 24 true: there; its shape is the plan's; its first slot is 2,168.
  k6Pub_in_scope   MAIN.

WHAT IT IS NOT. Facts on public parameters alone. Nothing on soundness. UNDER THE LIBRARY's publicOf
ALONE. The test on the layout's array of the reads (Law/ReadsEntInT.lean: readsRoomC) is not here.
LETTERS. Under "there is": p (twice): pinned by placeAt's equation; f9, pub: by equations.

-/
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Desc.Kinds.Law.K6PubNumbers
import Johnson.Desc.First.Look.K3PlaceLetters
import Johnson.Desc.First.Look.ShapeOwnAgrees2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model (TMat HTailF2 T2Foreign Settings Forest.Shape)
open OnBytes.Model.Head (Shape HL Border Owner HPlanH2 planH2)
open OnBytes.Road (ok_of_bind ok_of_jp)
open VerifiableInference.Desc.First.Look (placeAt lookAt P k3SortAt)

/-- What HTailF2.shape returns: the record of its lookup is made of its two calls. -/
theorem shape_cut {tl t' : HTailF2} {m : Array TMat} {txOf : Array (Option ℕ)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : ℕ}
    (h : tl.shape m txOf f hasU tau = .ok t') :
    ∃ (f9 : Forest.Shape) (pub : Array Nat),
      OnBytes.Model.Forest.shape #[t'.z1.call, t'.z2.call] t'.lidb = .ok f9 ∧
      OnBytes.Model.Forest.pubAsk f9 pub = .ok () ∧ t'.f9 = { f9 with pub := pub } := by
  unfold HTailF2.shape HTailF2.shapeF at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r1, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r2, -, h⟩ := ok_of_bind h
  obtain ⟨r3, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  exact Fo.ZPlan.piecesF_cut h

/-- **The same of the head's plan.** -/
theorem planH2_cut {g : Settings} {h : Shape} {L : HL} {b : Border} {O : Owner} {NGr lkW : ℕ}
    {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∃ (f9 : Forest.Shape) (pub : Array Nat),
      OnBytes.Model.Forest.shape #[hp.tl.z1.call, hp.tl.z2.call] hp.tl.lidb = .ok f9 ∧
      OnBytes.Model.Forest.pubAsk f9 pub = .ok () ∧ hp.tl.f9 = { f9 with pub := pub } := by
  obtain ⟨stream, t1, r, Tp2, h1, hr, h3, _, _⟩ := planH2_parts hpl
  obtain ⟨t2, Fp, Tp⟩ := r
  obtain ⟨f9, pub, c1, c2, c3⟩ := shape_cut h1
  obtain ⟨k1, k2, k3, k4⟩ := Fo.addTreesF_zkeep (tl := t1) hr
  obtain ⟨q1, q2, q3, q4⟩ := Fo.ownerHeld_zkeep h3
  refine ⟨f9, pub, ?_, c2, ?_⟩
  · rw [q1, q2, q3]
    show OnBytes.Model.Forest.shape #[t2.z1.call, t2.z2.call] t2.lidb = .ok f9
    rw [k1, k2, k3]
    exact c1
  · rw [q4]
    show t2.f9 = _
    rw [k4]
    exact c3

/-- The column bits of the layout of the committed matrix at the full size, as a test. -/
def lkChk : Bool :=
  match OnBytes.Model.wsLayOf Lk6.AtPlan.wsFull true OnBytes.Params.recordLines.blockLog with
  | .ok Y => Y.lk == 18
  | .error _ => false

set_option maxRecDepth 100000 in
theorem lkChk_true : lkChk = true := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

theorem lk_full (hZ : VerifierAndGoals.InScope Z = true)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : X.layers.wsLay.lk = 18 := by
  have W := (H2K.Sizes.pubFull_of_steps hZ (VerifiableInference.PlanWritten.publicSteps_of h)).wsLay
  have T := lkChk_true
  unfold lkChk at T
  rw [W] at T
  exact beq_iff_eq.1 T

/-- The head's segment is number 24. -/
theorem head_24 (hZ : VerifierAndGoals.InScope Z = true)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.p4 = true ∧ X.NGr = 12 :=
  have B := H2K.Sizes.pubFull_of_steps hZ (VerifiableInference.PlanWritten.publicSteps_of h)
  ⟨B.p4, B.groups⟩

/-- **The place of the lookup on the head's calls.** -/
theorem calls_place (hZ : VerifierAndGoals.InScope Z = true)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    ∃ p, placeAt X 24 false = some p ∧ p.shape = some X.HLy.fs ∧ p.first = 0 ∧ p.ns = X.H.ns := by
  obtain ⟨h4, hN⟩ := head_24 hZ h
  have e24 : (if X.p4 then 2 else 1) * X.NGr = 24 := by rw [h4, hN]; rfl
  have hs : (placeAt X 24 false).isSome = true := by
    unfold placeAt lookAt
    rw [h4, hN]
    rfl
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨s1, _, s3, s4⟩ := VerifiableInference.Desc.First.Look.place_head h (p := p)
    (by rw [e24]; exact hp)
  exact ⟨p, hp, s1, s3, s4⟩

/-- **The place of the lookup on the digits of the head's smallness test.** -/
theorem digits_place (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    ∃ p, placeAt X 24 true = some p ∧ p.shape = some X.H.tl.f9 ∧ p.first = 2168 := by
  obtain ⟨h4, hN⟩ := head_24 hZ h
  have Pw := plan_in_scope hZ hR h
  have hlk := lk_full hZ h
  have St := VerifiableInference.PlanWritten.publicSteps_of h
  obtain ⟨A0, seen, _, _, _, H0, hpl, eH, _⟩ := St.attention
  obtain ⟨f9, pub, c1, c2, c3⟩ := planH2_cut hpl
  have c1' : OnBytes.Model.Forest.shape #[X.H.tl.z1.call, X.H.tl.z2.call] X.H.tl.lidb = .ok f9 := by
    rw [eH]
    exact c1
  have c3' : X.H.tl.f9 = { f9 with pub := pub } := by
    rw [eH]
    exact c3
  have hn : VerifiableInference.Desc.First.Look.digitsNext X.H.ns
      (OnBytes.Model.wsForkSlots X.layers.wsLay.lk) (OnBytes.Model.Forest.elems X.H.tl.f9) =
      some 2168 := by
    rw [Pw.ns, hlk, Pw.elems]
    decide
  have e : lookAt X 24 true = (VerifiableInference.Desc.First.Look.digitsNext X.H.ns
      (OnBytes.Model.wsForkSlots X.layers.wsLay.lk) (OnBytes.Model.Forest.elems X.H.tl.f9)).map
      fun nx => { name := s!"LINK {24} ({"head"}) digits", link := 24,
                  calls := #[X.H.tl.z1.call, X.H.tl.z2.call], pub := X.H.tl.f9.pub,
                  lid := X.H.tl.lidb,
                  base := (({ trees := X.H.Fp.trees } : OnBytes.Model.Fork).fillL),
                  F := { (({ trees := X.H.Fp.trees } : OnBytes.Model.Fork).fillL).slots X.H.ns
                    with next := nx },
                  fs := X.H.tl.f9, ns := X.H.ns, lm := 5 } := by
    unfold lookAt
    rw [h4, hN]
    rfl
  rw [hn] at e
  refine ⟨_, by unfold placeAt; rw [e]; rfl, ?_, rfl⟩
  unfold P.shape
  show (VerifiableInference.Desc.First.Look.shapeOwn #[X.H.tl.z1.call, X.H.tl.z2.call]
    X.H.tl.lidb).bind (fun h0 => if VerifiableInference.Desc.First.Look.pubOk h0 X.H.tl.f9.pub
      then some { h0 with pub := X.H.tl.f9.pub } else none) = some X.H.tl.f9
  rw [VerifiableInference.Desc.First.Look.shapeOwn_eq, c1']
  have hp : X.H.tl.f9.pub = pub := by rw [c3']
  show (if VerifiableInference.Desc.First.Look.pubOk f9 X.H.tl.f9.pub
      then some { f9 with pub := X.H.tl.f9.pub } else none) = some X.H.tl.f9
  rw [hp, VerifiableInference.Desc.First.Look.pubOk_eq, c2, ← c3']
  rfl

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE TWELVE TESTS ACCEPT.** -/
theorem k6Pub_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : k6PubC X = true := by
  obtain ⟨h4, hN⟩ := head_24 hZ h
  have Pw := plan_in_scope hZ hR h
  have F := fs_in_scope hZ hR h
  obtain ⟨p3, e3, s3, a3, n3⟩ := calls_place hZ h
  obtain ⟨p8, e8, s8, a8⟩ := digits_place hZ hR h
  have e : X.hS = OnBytes.Model.Verify.headShape
      (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef (VerifierAndGoals.freeLinesOf pp)) X.y :=
    Meaning.HeadS.hS_in_scope hZ hR h
  have N := numbers_in_scope hZ hR h
  have tk : takesOf (parOf X.hS (workOf X)) = 173 := by
    unfold takesOf Norm.lPd
    show 41 + 8 * X.hS.lt + 4 * OnBytes.Model.clog2 X.hS.d = 173
    rw [N.lt, N.d]
    decide
  have lt' : (parOf X.hS (workOf X)).sizes.lt = 10 := by
    rw [e]
    rfl
  have lm : X.hS.lmbH = 15 := by rw [e]; rfl
  have ls : X.hS.ls = 6 := by rw [e]; rfl
  have c0 := layout_cols hZ hR h 0 (by decide)
  unfold k6PubC k6PubTests
  rw [e3, e8]
  simp only [s3, s8, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, F.NC, F.calls, ?_, ?_, ?_⟩
  · unfold k3SortAt VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
    rw [h4, hN]
    rfl
  · unfold k3SortAt VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
    rw [h4, hN]
    rfl
  · rw [a3, F.elems, tk, a8]
  · rw [a8, Pw.elems, n3, Pw.ns]
    decide
  · rw [lt', F.dT]
    decide
  · rw [Pw.nU]
    decide
  · rw [lm]
    decide
  · rw [lm, F.kT]
    decide
  · rw [ls, c0]
    decide
  · rw [ls, F.n0]
    decide

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.planH2_cut
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.lk_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_place
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.digits_place
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.k6Pub_in_scope
