-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/PlanListsSub.lean: the rounds of the model's three kinds of sub-proof, as lists.

OnBytes/Params/SubRounds.lean plans the rounds of a group of layers, of its attention and of the
output head, moment by moment. This file gives for each routine there a list of descriptions
(`RoundSpec`, OnBytes/Params/PlanningLaws.lean) and proves that the routine adds the rounds of that
list, from nothing open to nothing open. In these routines the prover often sends elements before a
block begins, so the block's first round takes them in: the sumcheck and the batching by powers are
therefore described once more with the bytes that are open before them (`pscListFrom`,
`batSigmaFrom`); OnBytes/Params/PlanListsSum.lean has them from nothing open. For every record of
numbers: nothing is evaluated.

Main definitions: `pscEpsilonFrom`, `pscListFrom`, `batSigmaFrom`, `rngRound`, `forestList`,
`smallList`, `productLayerList`, `zeroRound`, `joinRound`, `headOwnList`, `headEndList`, `headList`,
`layerOwnList`, `layerList`, `scoreListFrom`, `scoreOpen`, `planeBytes`, `attentionOwnList`,
`attentionList`.
Main theorems: `runs_when2`, `runs_scalarsIf`, `runs_psc_from`, `pscListFrom_zero`,
`runs_batSigma_from`, `runs_rng`, `runs_forest`, `runs_small`, `runs_productLayer`,
`runs_tokenSumcheck`, `runs_tokenSum`, `runs_headOwn`, `runs_headEnd`, `runs_headRounds`,
`runs_layerOwn`, `runs_layerRounds`, `runs_scoreFrom`, `runs_attentionOwn`, `runs_attentionRounds`.
What is not claimed: that a routine ends well. A moment above 2 is refused by the routines; its list
is written as the lookup on the digits alone, and is no plan's. Of the routines' own tests nothing
is kept: not that the number of combinations is the sub-proof's (`plan-tau`), nor that the number of
drawn entries fits 64 bits. Four tests of the sub-proofs have no round of their own, and neither
have the equations of the smallness test (the head of OnBytes/Params/SubRounds.lean): so no
description here stands for them. That an error that a description states bounds anything. Nothing
on the C++ planner, of which OnBytes/Params/ is a rendering. For proofs only; the program, that is
the Lean port built from OnBytes/, does not import this file.
-/
import OnBytes.Params.PlanListsSum
import OnBytes.Params.SubRounds

set_option autoImplicit false

namespace OnBytes.Params

/-- The first round of a sumcheck, where b bytes are open before it. -/
def pscEpsilonFrom (s : Setting) (b : Nat) : RoundSpec :=
  .said "PSC epsilon" .field (fieldError s 1) { drawE := 1, priced := .settingAlone }
    (b + 24 * 1) 0 0

/-- The rounds of a sumcheck, where b bytes are open before it: they go into its first round. -/
def pscListFrom (s : Setting) (x : PscSize) (b : Nat) : List RoundSpec :=
  pscEpsilonFrom s b :: (x.degree.map (pscVariable s) ++
    (if x.withY = true then [pscY s x.degreeY, .silent "PSC values" (24 * x.values) 0] else []))

/-- The round that batches rows by powers, where b bytes are open before it. -/
def batSigmaFrom (s : Setting) (rows b : Nat) : RoundSpec :=
  .said "BAT-sigma" .field (powersError s rows) { drawE := 1, rows := rows, priced := .asSaid }
    b 0 0

/-- The draw of the matrix of the smallness test. -/
def rngRound (s : Setting) (c : Scope) (columns : Nat) : RoundSpec :=
  .said "RNG" .small (Bound.exact (Binary.twoTo (-(rngCombinations s c : Int))))
    { trits := columns * rngCombinations s c, combinations := rngCombinations s c,
      priced := .asSaid } 0 0 0

/-- The rounds of a lookup of a group of calls. -/
def forestList (s : Setting) (x : ForestSize) : List RoundSpec :=
  lookupList s { v := x.v, d := x.d, mu := 5, shifted := x.shifted }

/-- The rounds of the smallness test after a moment: the matrix, or the lookup on the digits. -/
def smallList (s : Setting) (c : Scope) (x : SmallSize) (which : Nat) : List RoundSpec :=
  if which == 0 then [rngRound s c x.columns] else forestList s x.digits

/-- A sumcheck and the point of a line. -/
def productLayerList (s : Setting) (vars : Nat) : List RoundSpec :=
  pscList s { degree := List.replicate vars 3, degreeY := 2, values := 2 } ++ [lineRound s]

section
variable {s : Setting} {c : Scope}

/-- Two routines that are run or left out together, and what follows in both cases. -/
theorem runs_when2 {β : Type} {P : Prop} [Decidable P] {x1 x2 : Planning PUnit}
    {k : PUnit → Planning β} {w : β} {l1 l2 l3 : List RoundSpec} {b' r' a' : Nat}
    (h1 : Runs s c 0 0 0 x1 () l1 0 0 0) (h2 : Runs s c 0 0 0 x2 () l2 0 0 0)
    (h3 : Runs s c 0 0 0 (k ()) w l3 b' r' a') :
    Runs s c 0 0 0 (if P then x1 >>= fun _ => x2 >>= k else pure PUnit.unit >>= k) w
      ((if P then l1 ++ l2 else []) ++ l3) b' r' a' := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp]
    exact Runs.cast (runs_bind h1 (runs_bind h2 h3)) (by simp)
  · rw [if_neg hp, if_neg hp]
    exact runs_bind (runs_pure () 0 0 0) h3

/-- A sumcheck, from b bytes open. -/
theorem runs_psc_from (x : PscSize) (b : Nat) :
    Runs s c b 0 0 (planPsc x) () (pscListFrom s x b) 0 0 0 := by
  unfold planPsc
  exact Runs.cast (runs_bind (runs_setting b 0 0) (runs_bind (runs_scalars 1 b 0 0)
    (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_pscRounds x.degree)
      (runs_ite
        (fun _ => runs_bind (runs_scalars0 x.degreeY 0 0) (runs_bind (runs_close _ _ _ _ _ _ _)
          (runs_bind (runs_scalars0 x.values 0 0) (runs_closeNone _ _ _ _))))
        (fun _ => runs_pure () 0 0 0))))))
    (by simp [pscListFrom, pscEpsilonFrom, pscY])

/-- From nothing open the two descriptions of a sumcheck are one. -/
theorem pscListFrom_zero (x : PscSize) : pscListFrom s x 0 = pscList s x := by
  simp [pscListFrom, pscEpsilonFrom, pscList, pscEpsilon]

/-- BAT-sigma, from b bytes open. -/
theorem runs_batSigma_from (rows b : Nat) :
    Runs s c b 0 0 (planBatSigma rows) () [batSigmaFrom s rows b] 0 0 0 := by
  unfold planBatSigma
  exact Runs.cast (runs_bind (runs_setting b 0 0) (runs_close _ _ _ _ _ _ _))
    (by simp [batSigmaFrom])

/-- The draw of the matrix of the smallness test. -/
theorem runs_rng (columns : Nat) :
    Runs s c 0 0 0 (planRng columns) () [rngRound s c columns] 0 0 0 := by
  unfold planRng
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_scope 0 0 0)
    (runs_bind (runs_needs _ _ 0 0 0) (runs_close _ _ _ _ _ _ _)))) (by simp [rngRound])

/-- A lookup of a group of calls. -/
theorem runs_forest (x : ForestSize) : Runs s c 0 0 0 (planForest x) () (forestList s x) 0 0 0 :=
  runs_lookup _

/-- The smallness test after a moment. -/
theorem runs_small (x : SmallSize) (which : Nat) :
    Runs s c 0 0 0 (planSmall x which) () (smallList s c x which) 0 0 0 := by
  unfold planSmall smallList
  by_cases h : (which == 0) = true
  · rw [if_pos h, if_pos h]
    exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_scope 0 0 0)
      (runs_bind (runs_needs _ _ 0 0 0) (runs_rng _)))) (by simp)
  · rw [if_neg h, if_neg h]
    exact Runs.cast (runs_bind (runs_needs _ _ 0 0 0) (runs_forest _)) (by simp)

/-- A product of two halves under equality weights. -/
theorem runs_productLayer (vars : Nat) :
    Runs s c 0 0 0 (planProductLayer vars) () (productLayerList s vars) 0 0 0 := by
  unfold planProductLayer
  exact runs_bind (runs_psc _) runs_line

/-- A claimed sum and the sumcheck over the token bits that starts from it. -/
theorem runs_tokenSumcheck (lt degreeY shown : Nat) :
    Runs s c 0 0 0 (planTokenSumcheck lt degreeY shown) ()
      (pscListFrom s { degree := List.replicate lt 3, degreeY := degreeY, values := shown }
        (24 * 1)) 0 0 0 := by
  unfold planTokenSumcheck
  exact Runs.cast (runs_bind (runs_scalars0 1 0 0) (runs_psc_from _ _)) (by simp)

/-- A claimed sum and the sumcheck that starts from it. -/
theorem runs_tokenSum (lt shown degreeInY more : Nat) :
    Runs s c 0 0 0 (planTokenSum lt shown degreeInY more) ()
      (pscListFrom s
        { degree := List.replicate (lt + more) 3, degreeY := degreeInY, values := shown,
          withY := decide (0 < shown) } (24 * 1)) 0 0 0 := by
  unfold planTokenSum
  exact Runs.cast (runs_bind (runs_scalars0 1 0 0) (runs_psc_from _ _)) (by simp)

end

/-! ## The output head -/

/-- The round ZERO. -/
def zeroRound (s : Setting) (vars : Nat) : RoundSpec :=
  .said "ZERO" .field (fieldError s vars) { drawE := vars, priced := .roundItself } 0 0 0

/-- The head sub-proof's own rounds after its lookup. -/
def headOwnList (s : Setting) (x : HeadRounds) : List RoundSpec :=
  zeroRound s x.lt :: batSigmaFrom s x.sums (24 * x.sums) ::
    (pscList s { degree := List.replicate (x.lPd + x.lt) 3, degreeY := 2, values := 2 } ++
      (lineRound s :: batSigmaFrom s x.products (24 * x.products) ::
        (pscListFrom s
            { degree := List.replicate (x.lt + 0) 3, degreeY := 2, values := x.rowValues,
              withY := decide (0 < x.rowValues) } (24 * 1) ++
          (pscListFrom s
              { degree := List.replicate (x.lt + 0) 3, degreeY := 2, values := 2,
                withY := decide (0 < 2) } (24 * 1) ++
            pscListFrom s
              { degree := List.replicate (x.lt + x.lPd) 3, degreeY := 2, values := 2,
                withY := decide (0 < 2) } (24 * 1)))))

/-- The head sub-proof's rounds after the smallness test. -/
def headEndList (s : Setting) (x : HeadRounds) : List RoundSpec :=
  batSigmaFrom s 1 0 ::
    (pscList s { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 } ++
      [batSigmaFrom s x.rows 0])

/-- The rounds of the head sub-proof after a moment. -/
def headList (s : Setting) (c : Scope) (look : ForestSize) (x : HeadRounds) (small : SmallSize)
    (moment : Nat) : List RoundSpec :=
  (if moment == 0 then forestList s look ++ headOwnList s x else []) ++
    ((if 1 ≤ moment then smallList s c small (moment - 1) else []) ++
      (if moment == 2 then headEndList s x else []))

section
variable {s : Setting} {c : Scope}

/-- The head sub-proof's own rounds. -/
theorem runs_headOwn (x : HeadRounds) :
    Runs s c 0 0 0 (planHeadOwn x) () (headOwnList s x) 0 0 0 := by
  unfold planHeadOwn
  exact Runs.cast (runs_bind (runs_zero _) (runs_bind (runs_scalars0 _ 0 0)
    (runs_bind (runs_batSigma_from _ _) (runs_bind (runs_psc _) (runs_bind runs_line
      (runs_bind (runs_scalars0 _ 0 0) (runs_bind (runs_batSigma_from _ _)
        (runs_bind (runs_tokenSum _ _ _ _) (runs_bind (runs_tokenSum _ _ _ _)
          (runs_tokenSum _ _ _ _)))))))))) (by simp [headOwnList, zeroRound])

/-- The head sub-proof's end. -/
theorem runs_headEnd (x : HeadRounds) :
    Runs s c 0 0 0 (planHeadEnd x) () (headEndList s x) 0 0 0 := by
  unfold planHeadEnd
  exact Runs.cast (runs_bind (runs_batSigma_from _ 0) (runs_bind (runs_psc _)
    (runs_batSigma_from _ 0))) (by simp [headEndList])

/-- The head sub-proof after a moment. -/
theorem runs_headRounds (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) :
    Runs s c 0 0 0 (headRounds look x small moment) () (headList s c look x small moment)
      0 0 0 := by
  unfold headRounds headList
  refine runs_when2 (runs_forest _) (runs_headOwn _) ?_
  refine runs_when (runs_small _ _) ?_
  exact runs_ite (v := ()) (w := ()) (fun _ => runs_headEnd _) (fun _ => runs_pure () 0 0 0)

end

/-! ## A group of layers -/

/-- The round JOIN. -/
def joinRound (s : Setting) (vars : Nat) : RoundSpec :=
  .said "JOIN" .field (fieldError s vars) { drawE := vars, priced := .roundItself } 0 0 0

/-- A layer sub-proof's own rounds, in the order of `planLayerOwn`. -/
def layerOwnList (s : Setting) (x : LayerRounds) : List RoundSpec :=
  zeroRound s x.lt ::
  ((if x.firstGroup = true then [zeroRound s (x.ls + x.lt), zeroRound s (x.lPd - x.ls)] else []) ++
  (batSigmaFrom s x.NS (24 * (x.NS * x.NI)) ::
  ((if (x.lNI != 0) = true then [joinRound s x.lNI] else []) ++
  (productLayerList s (x.lNI + x.lPd + x.lt) ++
  (batSigmaFrom s (x.NP * x.NI) (24 * (x.NP * x.NI)) ::
  (pscListFrom s { degree := List.replicate x.lt 3, degreeY := 2, values := x.NO * x.NI }
      (24 * 1) ++
  ((if x.withTerms = true then
      pscListFrom s { degree := List.replicate x.lt 3, degreeY := 1, values := x.shownByTheTerms }
        (24 * 1) ++ [batSigmaFrom s 2 0]
    else []) ++
  (pscList s { degree := List.replicate x.lamS 3, degreeY := 2,
               values := 2 + x.neverSent + x.weightClaims } ++
  (productLayerList s (x.ll + x.lPf + x.lt) ++
  ((if x.routed = true then
      (if 1 < x.ll then [joinRound s (x.ll - 1)] else []) ++
        productLayerList s (x.ll - 1 + x.lfe + x.lt)
    else []) ++
  (batSigmaFrom s (x.weightClaims + (if x.firstGroup then 1 else 0))
      (if x.firstGroup = true then 24 * 1 else 0) ::
  pscList s { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 })))))))))))

/-- The rounds of a layer sub-proof after a moment. `claims`: all its linear claims and the
equations of its smallness test, which the last round batches. -/
def layerList (s : Setting) (c : Scope) (look : ForestSize) (x : LayerRounds) (small : SmallSize)
    (claims moment : Nat) : List RoundSpec :=
  if moment == 0 then forestList s look ++ layerOwnList s x
  else smallList s c small (moment - 1) ++
    (if moment == 2 then [batSigmaFrom s claims 0] else [])

section
variable {s : Setting} {c : Scope}

/-- The prover sends n elements or nothing, and what follows from the bytes that are then open. -/
theorem runs_scalarsIf {β : Type} {P : Prop} [Decidable P] (n : Nat) {k : PUnit → Planning β}
    {w : β} {l : List RoundSpec} {b' r' a' : Nat}
    (h : Runs s c (if P then 24 * n else 0) 0 0 (k ()) w l b' r' a') :
    Runs s c 0 0 0 (if P then planScalars n >>= k else pure PUnit.unit >>= k) w l b' r' a' := by
  by_cases hp : P
  · rw [if_pos hp] at h ⊢
    exact Runs.cast (runs_bind (runs_scalars0 n 0 0) h) (by simp)
  · rw [if_neg hp] at h ⊢
    exact Runs.cast (runs_bind (runs_pure () 0 0 0) h) (by simp)

/-- A layer sub-proof's own rounds. -/
theorem runs_layerOwn (x : LayerRounds) :
    Runs s c 0 0 0 (planLayerOwn x) () (layerOwnList s x) 0 0 0 := by
  have T4 := runs_scalarsIf (s := s) (c := c) (P := x.firstGroup = true) 1
    (k := fun _ => planBatSigma (x.weightClaims + (if x.firstGroup then 1 else 0)) >>= fun _ =>
      planPsc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 })
    (runs_bind (runs_batSigma_from (x.weightClaims + (if x.firstGroup then 1 else 0)) _)
      (runs_psc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 }))
  unfold planLayerOwn layerOwnList
  refine Runs.cast (runs_bind (runs_zero _) (runs_when2 (runs_zero _) (runs_zero _)
    (runs_bind (runs_scalars0 _ 0 0) (runs_bind (runs_batSigma_from _ _)
      (runs_when (runs_join _) (runs_bind (runs_productLayer _) (runs_bind (runs_scalars0 _ 0 0)
        (runs_bind (runs_batSigma_from _ _) (runs_bind (runs_tokenSumcheck _ _ _)
          (runs_when2 (runs_tokenSumcheck _ _ _) (runs_batSigma_from _ 0)
            (runs_bind (runs_psc _) (runs_bind (runs_productLayer _)
              (runs_ite (v := ()) (w := ())
                (fun _ => runs_when (runs_join _) (runs_bind (runs_productLayer _) T4))
                (fun _ => runs_bind (runs_pure () 0 0 0) T4)))))))))))))) ?_
  cases x.routed <;> simp [zeroRound, joinRound]

/-- The rounds of a layer sub-proof after a moment. -/
theorem runs_layerRounds (look : ForestSize) (x : LayerRounds) (small : SmallSize)
    (claims moment : Nat) :
    Runs s c 0 0 0 (layerRounds look x small claims moment) ()
      (layerList s c look x small claims moment) 0 0 0 := by
  unfold layerRounds layerList
  exact runs_ite (v := ()) (w := ()) (fun _ => runs_bind (runs_forest _) (runs_layerOwn _))
    (fun _ => runs_bind (runs_small _ _)
      (runs_ite (v := ()) (w := ()) (fun _ => runs_batSigma_from _ 0)
        (fun _ => runs_pure () 0 0 0)))

end

/-! ## Attention -/

/-- The rounds of the score segments' sumchecks, where b bytes are open before them: seven elements
and a sumcheck for each segment. What is open goes into the first segment's first round. -/
def scoreListFrom (s : Setting) (b : Nat) : List (Nat × Nat) → List RoundSpec
  | [] => []
  | p :: t => pscListFrom s (attentionSc3 p.1 p.2) (b + 24 * 7) ++
      (t.map fun q => pscListFrom s (attentionSc3 q.1 q.2) (24 * 7)).flatten

/-- The bytes that are open after the score segments: those from before, if there is no segment. -/
def scoreOpen (b : Nat) : List (Nat × Nat) → Nat
  | [] => b
  | _ :: _ => 0

/-- The bytes of the plane values, which are open before the score segments. -/
def planeBytes (x : AttentionRounds) : Nat :=
  if (x.planeMessages != 0) = true then 24 * (3 * x.planeMessages) else 0

/-- An attention sub-proof's own rounds, in the order of `planAttentionOwn`. -/
def attentionOwnList (s : Setting) (x : AttentionRounds) : List RoundSpec :=
  scoreListFrom s (planeBytes x) x.score ++
  (pscListFrom s (attentionSc3 x.e x.pairs)
      (scoreOpen (planeBytes x) x.score + 24 * (5 + x.lt + 2)) ++
  (batSigmaFrom s 2 0 ::
  (pscListFrom s (attentionSc3 x.valueM x.pairs) (24 * 2) ++
  (pscList s (attentionSc3 x.valueD x.pairs) ++
  (zeroRound s (2 * x.lgk + 2 * x.lt + 4) ::
  batSigmaFrom s x.pairs (24 * x.pairs) ::
  (pscList s (attentionSc3 x.attained x.pairs) ++
  (batSigmaFrom s x.pairs 0 ::
  (pscList s (attentionScd x.lt x.lgk x.pairs x.Lam) ++
  (batSigmaFrom s x.pairs 0 ::
  pscList s (attentionSc3 x.bits x.pairs))))))))))

/-- The rounds of an attention sub-proof after a moment. -/
def attentionList (s : Setting) (c : Scope) (look : ForestSize) (x : AttentionRounds)
    (small : SmallSize) (moment : Nat) : List RoundSpec :=
  (if moment == 0 then forestList s look ++ attentionOwnList s x else []) ++
    ((if 1 ≤ moment then smallList s c small (moment - 1) else []) ++
      (if moment == 2 then [batSigmaFrom s x.rows 0] else []))

section
variable {s : Setting} {c : Scope}

/-- The score segments' sumchecks, from b bytes open. -/
theorem runs_scoreFrom (b : Nat) : ∀ l : List (Nat × Nat),
    Runs s c b 0 0
      (forEach l fun p => do
        planScalars 7
        planPsc (attentionSc3 p.1 p.2)) () (scoreListFrom s b l) (scoreOpen b l) 0 0
  | [] => runs_pure () b 0 0
  | p :: t => by
      have h1 : Runs s c b 0 0 (planScalars 7 >>= fun _ => planPsc (attentionSc3 p.1 p.2)) ()
          (pscListFrom s (attentionSc3 p.1 p.2) (b + 24 * 7)) 0 0 0 :=
        Runs.cast (runs_bind (runs_scalars 7 b 0 0) (runs_psc_from _ _)) (by simp)
      have h2 := runs_forEach (s := s) (c := c)
        (f := fun q : Nat × Nat => planScalars 7 >>= fun _ => planPsc (attentionSc3 q.1 q.2))
        (L := fun q => pscListFrom s (attentionSc3 q.1 q.2) (24 * 7))
        (fun q => Runs.cast (runs_bind (runs_scalars0 7 0 0) (runs_psc_from _ _)) (by simp)) t
      exact runs_bind h1 h2

/-- An attention sub-proof's own rounds. -/
theorem runs_attentionOwn (x : AttentionRounds) :
    Runs s c 0 0 0 (planAttentionOwn x) () (attentionOwnList s x) 0 0 0 := by
  unfold planAttentionOwn attentionOwnList
  refine runs_scalarsIf (3 * x.planeMessages) ?_
  exact Runs.cast (runs_bind (runs_scoreFrom (planeBytes x) x.score)
    (runs_bind (runs_scalars _ _ 0 0) (runs_bind (runs_psc_from _ _)
      (runs_bind (runs_batSigma_from _ 0) (runs_bind (runs_scalars0 _ 0 0)
        (runs_bind (runs_psc_from _ _) (runs_bind (runs_psc _) (runs_bind (runs_zero _)
          (runs_bind (runs_scalars0 _ 0 0) (runs_bind (runs_batSigma_from _ _)
            (runs_bind (runs_psc _) (runs_bind (runs_batSigma_from _ 0) (runs_bind (runs_psc _)
              (runs_bind (runs_batSigma_from _ 0) (runs_psc _)))))))))))))))
    (by simp [zeroRound])

/-- The rounds of an attention sub-proof after a moment. -/
theorem runs_attentionRounds (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
    (moment : Nat) :
    Runs s c 0 0 0 (attentionRounds look x small moment) ()
      (attentionList s c look x small moment) 0 0 0 := by
  unfold attentionRounds attentionList
  refine runs_when2 (runs_forest _) (runs_attentionOwn _) ?_
  refine runs_when (runs_small _ _) ?_
  exact runs_ite (v := ()) (w := ()) (fun _ => runs_batSigma_from _ 0)
    (fun _ => runs_pure () 0 0 0)

end

end OnBytes.Params
