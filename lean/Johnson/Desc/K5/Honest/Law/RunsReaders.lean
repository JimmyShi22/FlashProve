-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsReaders.lean: THE READERS OF AN ATTENTION SEGMENT's CLAIMS
(Johnson/Desc/First/Att/RunsP.lean) AT TWO INPUTS THAT AGREE IN WHAT IS PUBLIC AND IN THE SLOTS'
NUMBERS: THEY REFUSE TOGETHER, OR RETURN FORMS OF ONE SHAPE. After the library's
Johnson/Desc/First/Att/Claims/Same.lean, lemma for lemma, in the kit of
Johnson/Desc/K5/Honest/Law/RunsKit.lean. Definitions, and statements with their proofs.

Main names:
  `sameF_const`, `sameF_addMul`, `sameF_add`, `sameF_sub`, `sameF_scale`   a form's shape hangs on
    no coefficient
  `ShSum`, `ShRem`, `ShScore`, `ShIn`   **two inputs of the runs agree in what is public (the
    library's `Same`), in the number of the tables' array, in every slot's number, and in the shapes
    of the rows that the sumchecks leave**
  `sh_uEnt`, `sh_u3at`, `sh_weighted`, `sh_plane`, `sh_shV`, `sh_overG`, `sh_readDenominator`,
    `sh_readMaximum`, `sh_readIndexBit`, `sh_xl`, `sh_readHead`, `sh_readGroup`, `sh_lessPieces`
    the readers

Every statement on a reader is conditional on `ShIn` (or on the lengths that it names).
Limits. No field element is compared. Nothing says that a reader returns anywhere, nor that two
inputs meet `ShIn`.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsKit
import Johnson.Desc.First.Att.Claims.SameClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP MaxP Pts SumP TablesP Geo Ten CallG)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_addMul affSh_add affSh_sub)
open K5Law (Any OptRel Same SameW SameRem SameScore eqTab_size cutLast_rel)

variable {K : ℕ}

/-! ## 1 A form's shape hangs on no coefficient -/

theorem sameF_const (v v' : E) : SameF (Aff.ofConst v) (Aff.ofConst v') := rfl

theorem sameF_addMul {a a' b b' : Aff} (ha : SameF a a') (hb : SameF b b') (k k' : E) :
    SameF (Aff.addMul a b k) (Aff.addMul a' b' k') := by
  unfold SameF at *
  rw [affSh_addMul, affSh_addMul, ha, hb]

theorem sameF_add {a a' b b' : Aff} (ha : SameF a a') (hb : SameF b b') :
    SameF (a + b) (a' + b') := sameF_addMul ha hb _ _

theorem sameF_sub {a a' b b' : Aff} (ha : SameF a a') (hb : SameF b b') :
    SameF (a - b) (a' - b') := sameF_addMul ha hb _ _

theorem sameF_scale {a a' : Aff} (ha : SameF a a') (k k' : E) :
    SameF (Aff.scale a k) (Aff.scale a' k') := sameF_addMul rfl ha _ _

/-! ## 2 What two inputs share -/

/-- Two sumchecks, as the claims read them: one first end slot; rows of one shape. -/
structure ShSum (s s' : SumP) : Prop where
  ends : s.ends = s'.ends
  row : SameF s.row s'.row

/-- Two units of which plane values are claimed. -/
structure ShRem (c c' : RemP) : Prop where
  same : SameRem c c'
  s0 : c.s0 = c'.s0

/-- Two units of a softmax-table call. -/
structure ShScore (k k' : ScoreP) : Prop where
  same : SameScore k k'
  s0 : k.s0 = k'.s0
  sc : ShSum k.sc k'.sc

/-- **Two inputs of the runs agree in what is public, in the number of the tables' array, in every
slot's number and in the shapes of the rows that the sumchecks leave.** It is a definition: a
premise's form. -/
structure ShIn (i i' : In) : Prop where
  same : Same i i'
  iU3 : i.iU3 = i'.iU3
  planes : List.Forall₂ ShRem i.p.planes.toList i'.p.planes.toList
  scores : List.Forall₂ ShScore i.p.scores.toList i'.p.scores.toList
  s5 : i.p.d.s5 = i'.p.d.s5
  sIB : i.p.d.sIB = i'.p.d.sIB
  s5h : i.p.d.s5h = i'.p.d.s5h
  sCl : i.p.d.sCl = i'.p.d.sCl
  scE : ShSum i.p.d.scE i'.p.d.scE
  vpm : ShSum i.p.d.vpm i'.p.d.vpm
  vpd : ShSum i.p.d.vpd i'.p.d.vpd
  sM6 : i.p.x.sM6 = i'.p.x.sM6
  scF : ShSum i.p.x.scF i'.p.x.scF
  scd : ShSum i.p.x.scd i'.p.x.scd
  scH : ShSum i.p.x.scH i'.p.x.scH

/-! ## 3 The readers -/

theorem sh_uEnt (t x : ℕ) : RSh K SameF (P.Runs.uEnt t x) (P.Runs.uEnt t x) := by
  unfold P.Runs.uEnt
  refine RSh.bind RSh.read fun a a' e => ?_
  subst e
  exact RSh.bind (RSh.mustAs _ _ rfl) fun _ _ _ => RSh.pure rfl

variable {i i' : In}

theorem sh_u3at (H : ShIn i i') (t n : ℕ) :
    RSh K SameF (P.Runs.u3at i t n) (P.Runs.u3at i' t n) := by
  unfold P.Runs.u3at
  rw [H.same.t.tabLen, H.iU3]
  exact RSh.bind (RSh.mustAs _ _ rfl) fun _ _ _ => sh_uEnt _ _

theorem sh_weighted (n : ℕ) (w w' : Array E) (f f' : ℕ → W Aff)
    (hf : ∀ k, RSh K SameF (f k) (f' k)) :
    RSh K SameF (P.Runs.weighted n w f) (P.Runs.weighted n w' f') := by
  unfold P.Runs.weighted
  exact RSh.foldlM1 (R := SameF)
    (fun _ _ k hs => RSh.bind (hf k) fun _ _ hx => RSh.pure (sameF_addMul hs hx _ _)) _
    (sameF_const _ _)

theorem sh_plane (H : ShIn i i') (t x lam a : ℕ) (z z' : Array E) (hz : z.size = z'.size)
    (isD : Bool) :
    RSh K SameF (P.Runs.plane i t x lam a z isD) (P.Runs.plane i' t x lam a z' isD) := by
  unfold P.Runs.plane
  dsimp only
  rw [H.same.g, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract, hz]
  exact sh_weighted _ _ _ _ _ fun _ => sh_u3at H _ _

theorem sh_shV (H : ShIn i i') (t off nl J lam j : ℕ) :
    RSh K SameF (P.Runs.shV i t off nl J lam j) (P.Runs.shV i' t off nl J lam j) := by
  unfold P.Runs.shV
  rw [H.same.g]
  exact sh_weighted _ _ _ _ _ fun _ => sh_u3at H _ _

theorem sh_overG (H : ShIn i i') (zg zg' : Array E) (f f' : ℕ → W Aff)
    (hf : ∀ k, RSh K SameF (f k) (f' k)) :
    RSh K SameF (P.Runs.overG i zg f) (P.Runs.overG i' zg' f') := by
  unfold P.Runs.overG
  rw [H.same.g]
  exact sh_weighted _ _ _ _ _ hf

theorem sh_readDenominator (H : ShIn i i') (t : ℕ) (zg zg' : Array E) (lam a : ℕ) :
    RSh K SameF (P.Runs.readDenominator i t zg lam a) (P.Runs.readDenominator i' t zg' lam a) := by
  unfold P.Runs.readDenominator
  refine sh_overG H _ _ _ _ fun g => ?_
  rw [H.same.g]
  exact sh_shV H _ _ _ _ _ _

theorem sh_readMaximum (H : ShIn i i') (t : ℕ) (zg zg' : Array E) (lam a : ℕ) :
    RSh K SameF (P.Runs.readMaximum i t zg lam a) (P.Runs.readMaximum i' t zg' lam a) := by
  unfold P.Runs.readMaximum
  refine sh_overG H _ _ _ _ fun g => ?_
  rw [H.same.g]
  exact sh_shV H _ _ _ _ _ _

theorem sh_readIndexBit (H : ShIn i i') (t : ℕ) (zg zg' : Array E) (lam a k : ℕ) :
    RSh K SameF (P.Runs.readIndexBit i t zg lam a k) (P.Runs.readIndexBit i' t zg' lam a k) := by
  unfold P.Runs.readIndexBit
  refine sh_overG H _ _ _ _ fun g => ?_
  rw [H.same.g]
  exact sh_shV H _ _ _ _ _ _

theorem sh_xl (H : ShIn i i') (t : ℕ) (X : Ten) (lam hd : ℕ) (zc zc' : Array E)
    (hz : zc.size = zc'.size) :
    RSh K SameF (P.Runs.xl i t X lam hd zc) (P.Runs.xl i' t X lam hd zc') := by
  unfold P.Runs.xl
  dsimp only
  rw [H.same.g]
  have hc := cutLast_rel (zc.extract 0 i'.g.ldh) (zc'.extract 0 i'.g.ldh)
    (by rw [Array.size_extract, Array.size_extract, hz]) i'.g.ls
  cases h1 : P.cutLast (zc.extract 0 i'.g.ldh) i'.g.ls <;>
    cases h2 : P.cutLast (zc'.extract 0 i'.g.ldh) i'.g.ls <;> rw [h1, h2] at hc
  · exact RSh.refuse _ _
  · exact hc.elim
  · exact hc.elim
  · dsimp only
    cases P.headFeat X hd i'.g.dh with
    | none => exact RSh.refuse _ _
    | some j0 =>
      dsimp only
      rw [eqTab_size, eqTab_size, hc]
      exact sh_weighted _ _ _ _ _ fun _ => sh_weighted _ _ _ _ _ fun _ => sh_u3at H _ _

theorem sh_readHead (H : ShIn i i') (t : ℕ) (X : Ten) (zg zg' zc zc' : Array E)
    (hz : zc.size = zc'.size) (lam a : ℕ) :
    RSh K SameF (P.Runs.readHead i t X zg zc lam a) (P.Runs.readHead i' t X zg' zc' lam a) := by
  unfold P.Runs.readHead
  refine sh_overG H _ _ _ _ fun g => ?_
  rw [H.same.g]
  exact sh_xl H _ _ _ _ _ _ hz

theorem sh_readGroup (H : ShIn i i') (t : ℕ) (X : Ten) (zg zg' zc zc' : Array E)
    (hz : zc.size = zc'.size) (lam : ℕ) :
    RSh K SameF (P.Runs.readGroup i t X zg zc lam) (P.Runs.readGroup i' t X zg' zc' lam) := by
  unfold P.Runs.readGroup
  exact sh_overG H _ _ _ _ fun g => sh_xl H _ _ _ _ _ _ hz

theorem sh_lessPieces {s s' : Aff} (hs : SameF s s') {pw pw' : Array W1} (hp : SameW pw pw')
    (f f' : W1 → W Aff)
    (hf : ∀ w w' : W1, w.lam = w'.lam → w.a = w'.a → RSh K SameF (f w) (f' w')) :
    RSh K SameF (P.Runs.lessPieces s pw f) (P.Runs.lessPieces s' pw' f') := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact RSh.foldlM₂ (R := SameF)
    (fun _ _ w w' h0 h => RSh.bind (hf w w' h.1 h.2) fun _ _ hx =>
      RSh.pure (sameF_addMul h0 hx _ _)) hp hs

end H2K5.Honest

#print axioms H2K5.Honest.sameF_const
#print axioms H2K5.Honest.sameF_addMul
#print axioms H2K5.Honest.sameF_add
#print axioms H2K5.Honest.sameF_sub
#print axioms H2K5.Honest.sameF_scale
#print axioms H2K5.Honest.sh_uEnt
#print axioms H2K5.Honest.sh_u3at
#print axioms H2K5.Honest.sh_weighted
#print axioms H2K5.Honest.sh_plane
#print axioms H2K5.Honest.sh_shV
#print axioms H2K5.Honest.sh_overG
#print axioms H2K5.Honest.sh_readDenominator
#print axioms H2K5.Honest.sh_readMaximum
#print axioms H2K5.Honest.sh_readIndexBit
#print axioms H2K5.Honest.sh_xl
#print axioms H2K5.Honest.sh_readHead
#print axioms H2K5.Honest.sh_readGroup
#print axioms H2K5.Honest.sh_lessPieces
