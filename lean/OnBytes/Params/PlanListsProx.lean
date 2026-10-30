-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/PlanListsProx.lean: the rounds that the planner's routines for sending, batching,
folding, positions and the proximity test add, as lists.

The like of OnBytes/Params/PlanListsSum.lean for the routines of OnBytes/Params/Planner.lean that
read an analysis of codes. The values that these routines take from the state or return (an
analysis, a list size, a sum of sample errors, a number of positions) are given as functions of the
setting and the scope, without the state.

Main definitions: `largestList`, `sampleSum`, `sendSeed`, `foldFromList`, `foldList`, `csCount`,
`csList`, `baseCount`, `baseList`, `stagesList`, `ioppList`.
Main theorems: `runs_analysis`, `runs_listOfGroups`, `runs_sampleErrors`, `runs_send`,
`runs_send_open`, `runs_bat`, `runs_foldFrom`, `runs_fold`, `runs_loc`, `runs_cs`, `runs_base`,
`runs_stages`, `runs_iopp`.
What is not claimed: that a routine ends well, or what its own tests found. Nothing on the C++
planner, of which OnBytes/Params/ is a rendering. For proofs only; the program, that is the Lean
port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.PlanListsSum

set_option autoImplicit false

namespace OnBytes.Params

/-- The largest list size among groups; no group: 1. -/
def largestList (s : Setting) : List GroupSize → Nat
  | [] => 1
  | g :: gs => max (analysis s g).list (largestList s gs)

/-- The sum of the sample errors of oracle messages, from e on. -/
def sampleSum (s : Setting) : List SampleSize → Bound → Bound
  | [], e => e
  | x :: xs, e => sampleSum s xs (e + sampleError s (largestList s x.groups) x.cubeBits s.samples)

/-- The round of the seeds of the samples of the oracle messages o, sent with so many roots. -/
def sendSeed (s : Setting) (o : List SampleSize) (roots : Nat) : RoundSpec :=
  .said "SEND seed" .sample (sampleSum s o (Bound.ofWord 0))
    { drawE := s.samples * (o.foldl (fun c x => max c x.cubeBits) 0 + 1), drawNZ := s.samples,
      priced := .callersWord } (32 * roots) roots 0

/-- Round j of a fold. -/
def foldRound (s : Setting) (g : GroupSize) (a : Analysis) (j : Nat) : RoundSpec :=
  .said "FOLD round" .closeness (foldRoundError s g a j)
    { drawE := 1, group := pricedOf g, priced := .asSaid,
      rests := if g.hasMask && j ≤ g.h then weakestSource a else a.mainAt.source } (24 * 2) 0 0

/-- The rounds of a fold from round j on, as many as the fuel. -/
def foldFromList (s : Setting) (g : GroupSize) (a : Analysis) : Nat → Nat → List RoundSpec
  | 0, _ => []
  | fuel + 1, j => foldRound s g a j :: foldFromList s g a fuel (j + 1)

/-- The first round of a fold. -/
def foldFirst (s : Setting) (g : GroupSize) (roots : Nat) : RoundSpec :=
  .said "FOLD epsilon" .field (Bound.ofNat (analysis s g).list * fieldError s 1)
    { drawE := 1, group := pricedOf g, priced := .asSaid } (32 * roots + 24 * 1) roots 0

/-- The rounds of a fold. -/
def foldList (s : Setting) (g : GroupSize) (roots : Nat) : List RoundSpec :=
  foldFirst s g roots :: foldFromList s g (analysis s g) g.k 1

/-- The number of positions of a code switch. -/
def csCount (s : Setting) (c : Scope) (source target : GroupSize) (oldRows symbols : Nat) : Nat :=
  csPositions s c (analysis s source).mainAt.agree (analysis s target).list oldRows symbols 64 0

/-- The two rounds of a code switch. -/
def csList (s : Setting) (c : Scope) (source target : GroupSize)
    (cubeBits oldRows symbols roots : Nat) : List RoundSpec :=
  [sendSeed s [⟨cubeBits, [target]⟩] roots,
   .said "CS" .query
    (Bound.pow (analysis s source).mainAt.agree (csCount s c source target oldRows symbols) +
      Bound.ofNat (analysis s target).list *
        powersError s (oldRows + s.samples + symbols * csCount s c source target oldRows symbols))
    { poss := csCount s c source target oldRows symbols, logN := source.main.logN, drawE := 1,
      rows := oldRows + s.samples + symbols * csCount s c source target oldRows symbols,
      group := pricedOf source, priced := .callersWord }
    (24 * (s.samples * 1)) 0 (s.samples * 1)]

/-- The number of positions of a group at its main code's agreement. -/
def baseCount (s : Setting) (c : Scope) (g : GroupSize) : Nat :=
  scopePositions s c (analysis s g).mainAt.agree (Bound.ofWord 0)

/-- The two rounds of the last step. -/
def baseList (s : Setting) (c : Scope) (g : GroupSize) (roots : Nat) : List RoundSpec :=
  [.said "BASE lambda" .closeness (baseError s g (analysis s g))
    { drawE := 1, group := pricedOf g, rests := weakestSource (analysis s g), priced := .asSaid }
    (32 * roots + 24 * 1) roots 0,
   .said "BASE" .query (Bound.pow (analysis s g).mainAt.agree (baseCount s c g))
    { poss := baseCount s c g, logN := g.main.logN, group := pricedOf g, priced := .asSaid }
    (24 * (g.main.dim * g.slots + (if g.hasMask then g.mask.dim else 0))) 0 0]

/-- The rounds of the stages of a proximity test: a fold and a code switch for every stage but the
last, then the last step. Written as empty for no stage; the routine then refuses. -/
def stagesList (s : Setting) (c : Scope) (firstMaskRoots : Nat) (masksRide : Bool) :
    Bool → List StageSize → List RoundSpec
  | first, x :: y :: rest =>
    foldList s x.g (if first then firstMaskRoots else if masksRide then 0 else 1) ++
      (csList s c x.g y.g (stageCubeBits y.g) 1 (x.g.slots + (if x.g.hasMask then 2 else 0)) 1 ++
        stagesList s c firstMaskRoots masksRide false (y :: rest))
  | _, [x] => baseList s c x.g (if masksRide then 0 else 1)
  | _, [] => []

/-- The round that batches rows. -/
def batRound (s : Setting) (groups : List GroupSize) (rows : Nat) : RoundSpec :=
  .said "BAT" .field (Bound.ofNat (largestList s groups) * powersError s rows)
    { drawE := 1, rows := rows, priced := .callersWord } 0 0 0

/-- The rounds of a proximity test. For fewer than two stages the routine refuses, and the list is
no plan's. -/
def ioppList (s : Setting) (c : Scope) (st : List StageSize) (rows firstMaskRoots : Nat)
    (masksRide : Bool) : List RoundSpec :=
  batRound s (st.take 1 |>.map (·.g)) rows :: stagesList s c firstMaskRoots masksRide true st

section
variable {s : Setting} {c : Scope}

/-- The prover sends n roots where no bytes and no roots are open. -/
theorem runs_roots0 (n a : Nat) : Runs s c 0 0 a (planRoots n) () [] (32 * n) n a := by
  have h := runs_roots (s := s) (c := c) n 0 0 a
  rw [Nat.zero_add, Nat.zero_add] at h
  exact h

/-- The prover sends n answers where no bytes and no answers are open. -/
theorem runs_answers0 (n r : Nat) : Runs s c 0 r 0 (planAnswers n) () [] (24 * n) r n := by
  have h := runs_answers (s := s) (c := c) n 0 r 0
  rw [Nat.zero_add, Nat.zero_add] at h
  exact h

/-- The analysis of a group. -/
theorem runs_analysis (g : GroupSize) (b r a : Nat) :
    Runs s c b r a (planAnalysis g) (analysis s g) [] b r a := by
  unfold planAnalysis
  exact Runs.cast (runs_bind (runs_setting b r a) (runs_bind (runs_needs _ _ b r a)
    (runs_pure _ b r a))) (by simp)

/-- A number of positions. -/
theorem runs_positions (agree extra : Bound) (b r a : Nat) :
    Runs s c b r a (planPositions agree extra) (scopePositions s c agree extra) [] b r a := by
  unfold planPositions
  exact Runs.cast (runs_bind (runs_setting b r a) (runs_bind (runs_scope b r a)
    (runs_pure _ b r a))) (by simp)

/-- The test on listed positions adds nothing. -/
theorem runs_listed (logN t b r a : Nat) : Runs s c b r a (planListed logN t) () [] b r a := by
  unfold planListed
  exact Runs.cast (runs_bind (runs_setting b r a) (runs_needs _ _ b r a)) (by simp)

/-- The largest list size among groups. -/
theorem runs_listOfGroups (b r a : Nat) :
    ∀ gs : List GroupSize, Runs s c b r a (listOfGroups gs) (largestList s gs) [] b r a
  | [] => runs_pure 1 b r a
  | g :: gs => by
      unfold listOfGroups
      exact Runs.cast (runs_bind (runs_analysis g b r a) (runs_bind (runs_listOfGroups b r a gs)
        (runs_pure _ b r a))) (by simp)

/-- The sum of sample errors. -/
theorem runs_sampleErrors (b r a : Nat) :
    ∀ (o : List SampleSize) (e : Bound),
      Runs s c b r a (sampleErrors s o e) (sampleSum s o e) [] b r a
  | [], e => runs_pure e b r a
  | x :: xs, e => by
      unfold sampleErrors
      exact Runs.cast (runs_bind (runs_listOfGroups b r a x.groups) (runs_sampleErrors b r a xs _))
        (by simp)

/-- SEND with the round of the answers. -/
theorem runs_send (o : List SampleSize) (roots : Nat) :
    Runs s c 0 0 0 (planSend o roots) ()
      [sendSeed s o roots,
        .silent "SEND answer" (24 * (s.samples * o.length)) (s.samples * o.length)] 0 0 0 := by
  unfold planSend
  rw [if_pos rfl]
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_roots0 roots 0)
    (runs_bind (runs_sampleErrors _ _ _ o _) (runs_bind (runs_close _ _ _ _ _ _ _)
      (runs_bind (runs_answers0 _ 0) (runs_closeNone _ _ _ _)))))) (by simp [sendSeed])

/-- SEND without the round of the answers: they stay open. -/
theorem runs_send_open (o : List SampleSize) (roots : Nat) :
    Runs s c 0 0 0 (planSend o roots false) () [sendSeed s o roots]
      (24 * (s.samples * o.length)) 0 (s.samples * o.length) := by
  unfold planSend
  rw [if_neg (by decide)]
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_roots0 roots 0)
    (runs_bind (runs_sampleErrors _ _ _ o _) (runs_bind (runs_close _ _ _ _ _ _ _)
      (runs_bind (runs_answers0 _ 0) (runs_pure _ _ _ _)))))) (by simp [sendSeed])

/-- BAT. -/
theorem runs_bat (groups : List GroupSize) (rows : Nat) :
    Runs s c 0 0 0 (planBat groups rows) () [batRound s groups rows] 0 0 0 := by
  unfold planBat
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_listOfGroups 0 0 0 groups)
    (runs_close _ _ _ _ _ _ _))) (by simp [batRound])

/-- The rounds of a fold from round j on. -/
theorem runs_foldFrom (g : GroupSize) (a : Analysis) :
    ∀ fuel j : Nat, Runs s c 0 0 0 (planFoldFrom s g a fuel j) () (foldFromList s g a fuel j) 0 0 0
  | 0, _ => runs_pure () 0 0 0
  | fuel + 1, j => by
      unfold planFoldFrom
      exact Runs.cast (runs_bind (runs_scalars0 2 0 0) (runs_bind (runs_close _ _ _ _ _ _ _)
        (runs_foldFrom g a fuel (j + 1)))) (by simp [foldFromList, foldRound])

/-- A fold. -/
theorem runs_fold (g : GroupSize) (roots : Nat) :
    Runs s c 0 0 0 (planFold g roots) () (foldList s g roots) 0 0 0 := by
  unfold planFold planFoldRounds
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_analysis g 0 0 0)
    (runs_bind (runs_roots0 roots 0) (runs_bind (runs_scalars 1 _ _ _)
      (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_analysis g 0 0 0)
        (runs_bind (runs_setting 0 0 0) (runs_foldFrom g _ g.k 1))))))))
    (by simp [foldList, foldFirst])

/-- LOC, from whatever is open. -/
theorem runs_loc (g : GroupSize) (b r a : Nat) :
    Runs s c b r a (planLoc g) (baseCount s c g)
      [.said "LOC" .query (Bound.pow (analysis s g).mainAt.agree (baseCount s c g))
        { poss := baseCount s c g, logN := g.main.logN, group := pricedOf g, priced := .asSaid }
        b r a] 0 0 0 := by
  unfold planLoc
  exact Runs.cast (runs_bind (runs_analysis g b r a) (runs_bind (runs_positions _ _ b r a)
    (runs_bind (runs_needs _ _ b r a) (runs_bind (runs_close _ _ _ _ _ _ _)
      (runs_bind (runs_listed _ _ 0 0 0) (runs_pure _ 0 0 0)))))) (by simp [baseCount])

/-- A code switch. -/
theorem runs_cs (source target : GroupSize) (cubeBits oldRows symbols roots : Nat) :
    Runs s c 0 0 0 (planCs source target cubeBits oldRows symbols roots)
      (csCount s c source target oldRows symbols)
      (csList s c source target cubeBits oldRows symbols roots) 0 0 0 := by
  unfold planCs
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_analysis source 0 0 0)
    (runs_bind (runs_analysis target 0 0 0) (runs_bind (runs_send_open _ roots)
      (runs_bind (runs_scope _ _ _) (runs_bind (runs_needs _ _ _ _ _)
        (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_listed _ _ 0 0 0)
          (runs_pure _ 0 0 0))))))))) (by simp [csList, csCount])

/-- The last step. -/
theorem runs_base (g : GroupSize) (roots : Nat) :
    Runs s c 0 0 0 (planBase g roots) (baseCount s c g) (baseList s c g roots) 0 0 0 := by
  unfold planBase
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_analysis g 0 0 0)
    (runs_bind (runs_roots0 roots 0) (runs_bind (runs_scalars 1 _ _ _)
      (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_scalars0 _ 0 0)
        (runs_bind (runs_positions _ _ _ _ _) (runs_bind (runs_needs _ _ _ _ _)
          (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_listed _ _ 0 0 0)
            (runs_pure _ 0 0 0))))))))))) (by simp [baseList, baseCount])

/-- The stages of a proximity test. -/
theorem runs_stages (firstMaskRoots : Nat) (masksRide : Bool) :
    ∀ (first : Bool) (st : List StageSize),
      Runs s c 0 0 0 (planStages firstMaskRoots masksRide first st) ()
        (stagesList s c firstMaskRoots masksRide first st) 0 0 0
  | first, x :: y :: rest => by
      unfold planStages
      exact Runs.cast (runs_bind (runs_fold _ _) (runs_bind (runs_cs _ _ _ _ _ _)
        (runs_bind (runs_needs _ _ 0 0 0)
          (runs_stages firstMaskRoots masksRide false (y :: rest)))))
        (by simp [stagesList])
  | _, [x] => by
      unfold planStages
      exact Runs.cast (runs_bind (runs_base _ _) (runs_needs _ _ 0 0 0)) (by simp [stagesList])
  | _, [] => by
      unfold planStages
      exact runs_refuse _ _ _ _ _ _ _ _ _

/-- A proximity test. -/
theorem runs_iopp (st : List StageSize) (rows firstMaskRoots : Nat) (masksRide : Bool) :
    Runs s c 0 0 0 (planIopp st rows firstMaskRoots masksRide) ()
      (ioppList s c st rows firstMaskRoots masksRide) 0 0 0 := by
  unfold planIopp
  exact Runs.cast (runs_bind (runs_needs _ _ 0 0 0) (runs_bind (runs_bat _ _)
    (runs_stages firstMaskRoots masksRide true st))) (by simp [ioppList])

end

end OnBytes.Params

#print axioms OnBytes.Params.runs_send
#print axioms OnBytes.Params.runs_fold
#print axioms OnBytes.Params.runs_cs
#print axioms OnBytes.Params.runs_base
#print axioms OnBytes.Params.runs_stages
#print axioms OnBytes.Params.runs_iopp
