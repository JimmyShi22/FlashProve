-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/StageView.lean: THE IMAGE OF A MASKED SUMCHECK'S WRITTEN ROUNDS UNDER THE
CHAIN'S MAPS (`ChM.rideMaps`, ChMaps.lean) IS THE TYPED TRANSCRIPT THAT THE LIBRARY MAKES OF THE
WORDS HEARD (`sumTr`, OnBytes/Tie/Pv/Lay/SumTie.lean), at the reading `gl`. Definitions, statements
and proofs.

Why. The library's ties from a sumcheck's record to the typed output (`sum_said`, `SumSaid.row`,
`sum_end_world`; `StgH.tr`, `own_last`, OnBytes/Tie/Pv/Lay/OwnTieL.lean) speak of `sumTr` on lists
of words. The carriage of the typed chain's count speaks of `Maps.view`. Here the two are one.

  `midRs`, `midY`, `midV`: of the written rounds behind a sumcheck's first round: what each
    variable's round sent, with the first word that it drew; the same of the further variable's
    round; what the round of the end values sent. Words (`sentE`, `drawnE`, RoundRead.lean).
  `mid_eq`: the two ways of writing these rounds' typed list are one list.
  `mid_view`, `mid_view'`: the image of these rounds under `midMaps` (RoundMaps.lean), along that
    equation, is `cubeTr` of `lastTr` (OnBytes/Tie/Pv/Att/Tr.lean) on these words.
  `stage_view`: for parameters `SumL` L with as many variables as there are written rounds for them,
    all of degree 2, and DY scalars in the further variable's round: the image of (mE, cE, σ) under
    `rideMaps L.T.par n …` is: the first n words that the first round sent, read, and the word
    number n, read; the first word that it drew, read; `sumTr gl L` on `midRs`, `midY` and the end
    values: the word number num a of `midV`, read.

NO NEW ARGUMENT: `sent_at`, `drawn_head`, `drawn_seed` (RoundRead.lean), round by round.

NEAREST KIN: Johnson/Top/H0/MergeLaw/View.lean (`mid_view`, `whole_view`): the
same for the merge's sumcheck: one scalar in the further variable's round, one end value, its own
maps. Typed apart; seen after this file.

Limits. PREMISES: `AllE` at every round of the stage; hβ: THE READING OF THE FIRST WORD THAT THE
FURTHER VARIABLE'S ROUND DREW IS NOT 0 (`sumTr` asks it; where it is 0 the map's value is 1 and the
two differ); hk, hn, hD: the parameters' numbers. At every written transcript, also where a test of
work fails. That these words are what a text's functions read off its tape is not said here. Nothing
on soundness.
-/
import OnBytes.Desc.First.P1.ChView
import OnBytes.Desc.First.P1.RoundRead
import OnBytes.Tie.Pv.Lay.SumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Tie.Pv.Att (cubeTr lastTr)
open OnBytes.Tie.Pv.Lay.Eng (sumTr)
open _root_.Run (ckP)


theorem trCast_cons {r : Round} {s s' : Shape} (h : s = s') (h2 : r :: s = r :: s') (m : r.Msg)
    (c : r.Chal) (τ : Tr s) :
    trCast h2 ((m, c, τ) : Tr (r :: s)) = ((m, c, trCast h τ) : Tr (r :: s')) := by
  subst h
  rfl

/-! ### The words of the rounds behind a sumcheck's first round -/

section Mid
variable (dY dV : RDT)

/-- What each variable's round sent, with the first word that it drew. -/
def midRs : (vs : List RDT) → Tr (uLT (ckP .two) (vs ++ [dY, dV])) →
    List (List OnBytes.E × OnBytes.E)
  | [], _ => []
  | d :: vs, (m, c, σ) => (sentE d m, (drawnE d c).headD OnBytes.zeroE) :: midRs vs σ

/-- What the further variable's round sent, with the first word that it drew. -/
def midY : (vs : List RDT) → Tr (uLT (ckP .two) (vs ++ [dY, dV])) → List OnBytes.E × OnBytes.E
  | [], (m, c, _) => (sentE dY m, (drawnE dY c).headD OnBytes.zeroE)
  | _ :: vs, (_, _, σ) => midY vs σ

/-- What the round of the end values sent. -/
def midV : (vs : List RDT) → Tr (uLT (ckP .two) (vs ++ [dY, dV])) → List OnBytes.E
  | [], (_, _, m, _, _) => sentE dV m
  | _ :: vs, (_, _, σ) => midV vs σ

end Mid

/-- The two ways of writing these rounds' typed list. -/
theorem mid_eq (DY : ℕ) (A : Type) : ∀ k : ℕ,
    List.replicate k (sRound (pfCube GE 2)) ++ [sRound (pDummy GE DY), pRoundV GE A] =
      sRounds (ldPartFmt GE k (fun _ => 2) ++ [pDummy GE DY]) ++ [pRoundV GE A]
  | 0 => rfl
  | k + 1 => congrArg (sRound (pfCube GE 2) :: ·) (mid_eq DY A k)

/-- **The image of the rounds behind a sumcheck's first round.** -/
theorem mid_view {A : Type} (DY : ℕ) (num : A → ℕ) {dY dV : RDT} (hY : AllE dY) (hV : AllE dV) :
    ∀ (vs : List RDT), (∀ d ∈ vs, AllE d) → ∀ (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV])))
      (hβ : gl.val (midY dY dV vs σ).2 ≠ 0)
      (e : List.replicate vs.length (sRound (pfCube GE 2)) ++
          [sRound (pDummy GE DY), pRoundV GE A] =
        sRounds (ldPartFmt GE vs.length (fun _ => 2) ++ [pDummy GE DY]) ++ [pRoundV GE A]),
      trCast e ((midMaps DY num dY dV vs).view σ) =
        cubeTr gl (pDummy GE DY) [pRoundV GE A] vs.length (fun _ => 2) (midRs dY dV vs σ)
          (lastTr gl DY A (midY dY dV vs σ).1 (midY dY dV vs σ).2 hβ
            fun a => gl.val ((midV dY dV vs σ).getD (num a) OnBytes.zeroE))
  | [], _, (mY, cY, mV, cV, u), hβ, e => by
    have h1 : (fun t : Fin DY => sentT dY mY t.val) = rd gl DY (sentE dY mY) :=
      funext fun t => (sent_at dY mY hY t.val).symm
    have h3 : (fun a => sentT dV mV (num a)) =
        fun a => gl.val ((sentE dV mV).getD (num a) OnBytes.zeroE) :=
      funext fun a => (sent_at dV mV hV (num a)).symm
    have hs : (⟨(gSeed 0 _ (valsOf (toRD dY) cY)).2.val,
          (gSeed 0 _ (valsOf (toRD dY) cY)).2.ne_zero⟩ : {x : GE // x ≠ 0}) =
        ⟨gl.val ((drawnE dY cY).headD OnBytes.zeroE), hβ⟩ :=
      Subtype.ext (drawn_seed dY mY cY hβ)
    show ((((), fun t : Fin DY => sentT dY mY t.val),
        (⟨(gSeed 0 _ (valsOf (toRD dY) cY)).2.val,
          (gSeed 0 _ (valsOf (toRD dY) cY)).2.ne_zero⟩ : {x : GE // x ≠ 0}),
        (((), fun a => sentT dV mV (num a)), (), ())) :
          Tr (sRound (pDummy GE DY) :: [pRoundV GE A])) =
      (((), rd gl DY (sentE dY mY)), ⟨gl.val ((drawnE dY cY).headD OnBytes.zeroE), hβ⟩,
        (((), fun a => gl.val ((sentE dV mV).getD (num a) OnBytes.zeroE)), (), ()))
    rw [h1, h3, hs]
    rfl
  | d :: vs, h, (m, c, σ), hβ, e => by
    have ih := mid_view DY num hY hV vs (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) σ hβ
      (mid_eq DY A vs.length)
    have h1 : (fun t : Fin 2 => sentT d m t.val) = rd gl 2 (sentE d m) :=
      funext fun t => (sent_at d m (h d List.mem_cons_self) t.val).symm
    have h2 : gOne _ (valsOf (toRD d) c) = gl.val ((drawnE d c).headD OnBytes.zeroE) :=
      (drawn_head d m c).symm
    have step : ((((), fun t : Fin 2 => sentT d m t.val), gOne _ (valsOf (toRD d) c),
        trCast (mid_eq DY A vs.length) ((midMaps DY num dY dV vs).view σ)) :
          Tr (sRound (pfCube GE 2) :: (sRounds (ldPartFmt GE vs.length (fun _ => 2) ++
            [pDummy GE DY]) ++ [pRoundV GE A]))) =
      (((), rd gl 2 (sentE d m)), gl.val ((drawnE d c).headD OnBytes.zeroE),
        cubeTr gl (pDummy GE DY) [pRoundV GE A] vs.length (fun _ => 2) (midRs dY dV vs σ)
          (lastTr gl DY A (midY dY dV vs σ).1 (midY dY dV vs σ).2 hβ
            fun a => gl.val ((midV dY dV vs σ).getD (num a) OnBytes.zeroE))) := by
      rw [h1, h2, ih]
    exact (trCast_cons (mid_eq DY A vs.length) e _ _ _).trans step

/-- The same at numbers that are given by equations. -/
theorem mid_view' {A : Type} (DY : ℕ) (num : A → ℕ) {dY dV : RDT} (hY : AllE dY) (hV : AllE dV)
    (vs : List RDT) (hvs : ∀ d ∈ vs, AllE d) (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV])))
    (hβ : gl.val (midY dY dV vs σ).2 ≠ 0) (k : ℕ) (n : Fin k → ℕ) (DY' : ℕ)
    (hk : vs.length = k) (hn : ∀ i, n i = 2) (hD : DY = DY')
    (e : List.replicate vs.length (sRound (pfCube GE 2)) ++
        [sRound (pDummy GE DY), pRoundV GE A] =
      sRounds (ldPartFmt GE k n ++ [pDummy GE DY']) ++ [pRoundV GE A]) :
    trCast e ((midMaps DY num dY dV vs).view σ) =
      cubeTr gl (pDummy GE DY') [pRoundV GE A] k n (midRs dY dV vs σ)
        (lastTr gl DY' A (midY dY dV vs σ).1 (midY dY dV vs σ).2 hβ
          fun a => gl.val ((midV dY dV vs σ).getD (num a) OnBytes.zeroE)) := by
  subst hk
  subst hD
  obtain rfl : n = fun _ => 2 := funext hn
  exact mid_view DY num hY hV vs hvs σ hβ e

/-- **The image of a masked sumcheck's written rounds is the library's transcript of the words
heard.** -/
theorem stage_view (L : SumL GE) (n : ℕ) {dE : RDT} {vs : List RDT} {dY dV : RDT} (DY : ℕ)
    (num : L.T.par.A → ℕ)
    (hf : L.T.par.fmt = List.replicate vs.length (pfCube GE 2) ++ [pDummy GE DY])
    (hE : AllE dE) (hvs : ∀ d ∈ vs, AllE d) (hY : AllE dY) (hV : AllE dV)
    (hk : vs.length = L.S.k) (hn : ∀ i, L.M.n i = 2) (hD : DY = L.M.DY)
    (mE : (wT dE).Msg) (cE : (wT dE).Chal) (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV])))
    (hβ : gl.val (midY dY dV vs σ).2 ≠ 0) :
    (ChM.rideMaps L.T.par n dE vs dY dV DY num hf).view (mE, cE, σ) =
      (((), (rd gl n (sentE dE mE), gl.val ((sentE dE mE).getD n OnBytes.zeroE))),
        gl.val ((drawnE dE cE).headD OnBytes.zeroE),
        sumTr gl L (midRs dY dV vs σ) (midY dY dV vs σ).1 (midY dY dV vs σ).2 hβ
          fun a => gl.val ((midV dY dV vs σ).getD (num a) OnBytes.zeroE)) := by
  have h1 : (fun i : Fin n => sentT dE mE i.val) = rd gl n (sentE dE mE) :=
    funext fun i => (sent_at dE mE hE i.val).symm
  have h2 : sentT dE mE n = gl.val ((sentE dE mE).getD n OnBytes.zeroE) :=
    (sent_at dE mE hE n).symm
  have h3 : gOne _ (valsOf (toRD dE) cE) = gl.val ((drawnE dE cE).headD OnBytes.zeroE) :=
    (drawn_head dE mE cE).symm
  show (((), ((fun i : Fin n => sentT dE mE i.val), sentT dE mE n)),
      gOne _ (valsOf (toRD dE) cE),
      (Maps.castT ((mid_shape vs.length DY L.T.par.A).trans (by rw [hf]))
        (midMaps DY num dY dV vs)).view σ) = _
  rw [view_cast, h1, h2, h3]
  exact congrArg (fun z => (((), (rd gl n (sentE dE mE),
      gl.val ((sentE dE mE).getD n OnBytes.zeroE))),
      gl.val ((drawnE dE cE).headD OnBytes.zeroE), z))
    (mid_view' DY num hY hV vs hvs σ hβ L.S.k L.M.n L.M.DY hk hn hD _)

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.mid_view
#print axioms OnBytes.Desc.First.P1.stage_view
