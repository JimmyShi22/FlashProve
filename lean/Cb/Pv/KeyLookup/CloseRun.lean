-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/CloseRun.lean: at the short sumcheck, what the verifiers of the join point, the
closing, the zero point and the test of the bits put out, as plain functions of the flat transcript.

It imports CloseLaid.lean, CloseCf.lean, Cb/Pv/KeyLookup/Flat.lean (`Runs`, the readers of rounds)
and Cb/Pv/KeyLookup/LevRunA.lean (the short sumcheck on k variables of degree 2 and a further
variable, written out); no file of the port.

A flat transcript is a list of rounds, each a pair (scalars sent, elements drawn).
`Flat.Runs b fm run` says: for all x, y, τ the verifier of b puts out `some (run x (view τ))`, and
the rounds have the formats fm.
Main names:
  `Clo.hidM`, `Clo.finM`   for a sumcheck with a degree for each variable and no further variable:
                  the form on the coefficients of the hiding polynomial, and the running claim
                  behind all rounds. Under the equality weight at z a round's constant is σ − z · Σ
                  q_t.
  `Clo.fill_eqN`  a round's polynomial completed at its constant, at the draw, for every degree.
  `A.joinRun`, `A.closeRun P`, `A.zeroRun`, `A.bitsRun P`   the four plain functions.
  `joinK_runs`, `closeK_runs`, `zeroK_runs`, `bitsK_runs`   `Flat.Runs` of the four blocks at `SK₀`.
Limits: [DecidableEq E] is asked beside the library's [Field E] [Fintype E]. Nothing on an honest
side. That these functions are what the port computes is not shown here.

-/
import Cb.Pv.KeyLookup.CloseLaid
import Cb.Pv.KeyLookup.CloseCf
import Cb.Pv.KeyLookup.Flat
import Cb.Pv.KeyLookup.LevRunA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Johnson.L5.Layers Flat Finset

namespace Clo

/-! ### a sumcheck with a degree for each variable, flat -/
section
variable {E : Type} [Field E] [Fintype E]

/-- The form on the coefficients of the hiding polynomial: c_l^(t + 1) at the place of (round l,
degree t + 1), and 1 at the constant's place. -/
def hidM {J : Type} [DecidableEq J] : (k : ℕ) → (dg : Fin k → ℕ) → (PIdx (pfMix E k dg) → J) →
    (ℕ → E) → J → E
  | 0, _, w, _, j => Lev.one (w ()) 1 j
  | k + 1, dg, w, c, j =>
    (∑ t : Fin (dg 0), Lev.one (w (.inl t)) (c 0 ^ ((t : ℕ) + 1)) j) +
      hidM k (fun i => dg i.succ) (fun i => w (.inr i)) (fun i => c (i + 1)) j

theorem nSum_hidM {J : Type} [DecidableEq J] : ∀ (k : ℕ) (dg : Fin k → ℕ)
    (w : PIdx (pfMix E k dg) → J) (γ : PPt (pfMix E k dg)) (j : J),
    Cf.nSum (pfMix E k dg) (fun i => if w i = j then Cf.nH (pfMix E k dg) γ i else 0) =
      hidM k dg w (ppGet (pfMix E k dg) γ) j
  | 0, _, w, _, j => Lev.ite_one (w ()) j 1 _
  | k + 1, dg, w, γ, j => by
    show (∑ t : Fin (dg 0), if w (.inl t) = j then γ.1 ^ ((t : ℕ) + 1) else 0) +
      Cf.nSum (pfMix E k fun i => dg i.succ)
        (fun i => if w (.inr i) = j then Cf.nH (pfMix E k fun i => dg i.succ) γ.2 i else 0) = _
    rw [nSum_hidM k (fun i => dg i.succ) (fun i => w (.inr i)) γ.2 j]
    exact congrArg (· + _) (Finset.sum_congr rfl fun t _ => Lev.ite_one _ _ _ _)

/-- A round's polynomial completed at its constant, at the draw, under an equality weight. -/
theorem fill_eqN (n : ℕ) (z σ γ : E) (q : Fin n → E) :
    hev (hFill ((pfCube E n).var (pdEq E n z)) ((0 : Fin (n + 1)), (1 : E)) σ q) γ =
      σ - z * ∑ t, q t + ∑ t : Fin n, q t * γ ^ ((t : ℕ) + 1) := by
  have h0 : ((pfCube E n).var (pdEq E n z)).phi
      ((0 : Fin (n + 1)).insertNth (α := fun _ => E) 0 q) = z * ∑ t, q t := by
    show ∑ b : Bool, (if b then z else 1 - z) • ∑ t : Fin (n + 1),
      (if b then (1 : E) else 0) ^ (t : ℕ) •
        ((0 : Fin (n + 1)).insertNth (α := fun _ => E) 0 q) t = _
    rw [Fintype.sum_bool]
    simp [Fin.sum_univ_succ]
  show hev ((0 : Fin (n + 1)).insertNth (α := fun _ => E) ((1 : E) • (σ -
    ((pfCube E n).var (pdEq E n z)).phi
      ((0 : Fin (n + 1)).insertNth (α := fun _ => E) 0 q))) q) γ = _
  rw [h0]
  show ∑ t : Fin (n + 1), γ ^ (t : ℕ) •
    ((0 : Fin (n + 1)).insertNth (α := fun _ => E) ((1 : E) • (σ - z * ∑ t, q t)) q) t = _
  rw [Fin.sum_univ_succ]
  simp [mul_comm]

end

section
variable {E : Type} [Field E]

/-- The running claim behind k rounds under equality weights at z. -/
def finM : (k : ℕ) → (Fin k → ℕ) → (Fin k → E) → E → List (RV E) → E
  | 0, _, _, σ, _ => σ
  | k + 1, dg, z, σ, f =>
    finM k (fun i => dg i.succ) (fun i => z i.succ)
      (σ - z 0 * (∑ t : Fin (dg 0), Lev.snt f 0 t) +
        ∑ t : Fin (dg 0), Lev.snt f 0 t * Lev.chC f 0 ^ ((t : ℕ) + 1)) f.tail

/-- The formats of the k rounds. -/
def fmM : (k : ℕ) → (Fin k → ℕ) → List Fm
  | 0, _ => []
  | k + 1, dg => ⟨dg 0, 1, false⟩ :: fmM k fun i => dg i.succ

end

section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]

/-- How the draws of the k rounds are written. -/
def fuM : (k : ℕ) → (dg : Fin k → ℕ) → FUs (pfMix E k dg)
  | 0, _ => ()
  | k + 1, dg => (fuCube (dg 0), fuM k fun i => dg i.succ)

theorem fuM_fms : ∀ (k : ℕ) (dg : Fin k → ℕ),
    (rdVars (pfMix E k dg) (fuM k dg)).fms = fmM k dg
  | 0, _ => rfl
  | k + 1, dg => by
    show (⟨dg 0, 1, false⟩ : Fm) :: (rdVars (pfMix E k fun i => dg i.succ)
      (fuM k fun i => dg i.succ)).fms = _
    rw [fuM_fms k fun i => dg i.succ]
    rfl

theorem fin_viewM : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E) (σ : E)
    (τ : Tr (sRounds (pfMix E k dg))),
    (TWhole.vFin (pfMix E k dg) (pdMix E k dg z)
        (TWhole.fix0 (pVars (pfMix E k dg) (pdMix E k dg z))) σ τ).1 =
      finM k dg z σ ((rdVars (pfMix E k dg) (fuM k dg)).view τ)
  | 0, _, _, _, _ => rfl
  | k + 1, dg, z, σ, (m, c, τ) => by
    have ih := fin_viewM k (fun i => dg i.succ) (fun i => z i.succ)
      (hev (hFill ((pfCube E (dg 0)).var (pdEq E (dg 0) (z 0))) ((0 : Fin (dg 0 + 1)), (1 : E)) σ
        m.2) c) τ
    refine ih.trans ?_
    rw [fill_eqN]
    have e : ∀ t : Fin (dg 0), (List.ofFn m.2).getD t.val 0 = m.2 t := fun t => getD_ofFn m.2 t
    show _ = finM k (fun i => dg i.succ) (fun i => z i.succ)
      (σ - z 0 * (∑ t : Fin (dg 0), (List.ofFn m.2).getD t.val 0) +
        ∑ t : Fin (dg 0), (List.ofFn m.2).getD t.val 0 * c ^ ((t : ℕ) + 1))
      ((rdVars (pfMix E k fun i => dg i.succ) (fuM k fun i => dg i.succ)).view τ)
    simp only [e]

variable (E) in
/-- The reader of the round of one shown value. -/
def rdV1 : RdS E [pRoundV E Unit] := (rdV finOneEquiv.symm, ())

theorem ch_viewM : ∀ (l : List (PFmt E)) (U : FUs l) (τ : Tr (sRounds l)) (j : ℕ),
    chC l τ j = Lev.chC ((rdVars l U).view τ) j
  | [], _, _, _ => by simp [chC, Lev.chC, RdS.view, rdVars]
  | _ :: _, (_, _), (_, _, _), 0 => rfl
  | _ :: l, (_, U), (_, _, τ), j + 1 => ch_viewM l U τ j

/-- The form on the coefficients of the hiding polynomial of k variables of degree 2 and a further
variable of degree 2, as Cb/Pv/KeyLookup/LevRunA.lean writes it. -/
theorem nSum_rowF {J : Type} [DecidableEq J] : ∀ (k : ℕ) (w : PIdx (Lev.lk E k) → J)
    (γ : PPt (Lev.lk E k)) (j : J),
    Cf.nSum (Lev.lk E k) (fun i => if w i = j then Cf.nH (Lev.lk E k) γ i else 0) =
      Lev.rowF k (fun r t => w (Lev.nmV E k r t)) (w (Lev.nmC E k)) (ppGet (Lev.lk E k) γ) j
  | 0, w, γ, j => by
    show (∑ t : Fin 2, if w (.inl t) = j then γ.1 ^ ((t : ℕ) + 1) else 0) +
      (if w (.inr ()) = j then (1 : E) else 0) = _
    rw [Fin.sum_univ_two, Lev.ite_one, Lev.ite_one, Lev.ite_one]
    show Lev.one _ (γ.1 ^ (0 + 1)) j + Lev.one _ (γ.1 ^ (1 + 1)) j + Lev.one _ 1 j =
      Lev.one _ γ.1 j + Lev.one _ (γ.1 ^ 2) j + Lev.one _ 1 j
    rw [zero_add, pow_one]
    rfl
  | k + 1, w, γ, j => by
    show (∑ t : Fin 2, if w (.inl t) = j then γ.1 ^ ((t : ℕ) + 1) else 0) +
      Cf.nSum (Lev.lk E k)
        (fun i => if w (.inr i) = j then Cf.nH (Lev.lk E k) γ.2 i else 0) = _
    rw [nSum_rowF k (fun i => w (.inr i)) γ.2 j, Fin.sum_univ_two, Lev.ite_one, Lev.ite_one]
    show Lev.one _ (γ.1 ^ (0 + 1)) j + Lev.one _ (γ.1 ^ (1 + 1)) j + _ =
      Lev.one _ γ.1 j + Lev.one _ (γ.1 ^ 2) j + _
    rw [zero_add, pow_one]
    rfl

omit [Fintype E] [DecidableEq E] in
/-- That form reads the challenges of the k + 1 rounds alone. -/
theorem rowF_congr {J : Type} [DecidableEq J] : ∀ (k : ℕ) (wv : ℕ → Fin 2 → J) (wc : J)
    (c c' : ℕ → E), (∀ i, i ≤ k → c i = c' i) → Lev.rowF k wv wc c = Lev.rowF k wv wc c'
  | 0, wv, wc, c, c', h => by
    funext j
    show Lev.one _ (c 0) j + Lev.one _ (c 0 ^ 2) j + _ =
      Lev.one _ (c' 0) j + Lev.one _ (c' 0 ^ 2) j + _
    rw [h 0 (Nat.le_refl 0)]
  | k + 1, wv, wc, c, c', h => by
    funext j
    show Lev.one _ (c 0) j + Lev.one _ (c 0 ^ 2) j +
        Lev.rowF k (fun i => wv (i + 1)) wc (fun i => c (i + 1)) j =
      Lev.one _ (c' 0) j + Lev.one _ (c' 0 ^ 2) j +
        Lev.rowF k (fun i => wv (i + 1)) wc (fun i => c' (i + 1)) j
    rw [h 0 (Nat.zero_le _), rowF_congr k (fun i => wv (i + 1)) wc (fun i => c (i + 1))
      (fun i => c' (i + 1)) fun i hi => h (i + 1) (Nat.succ_le_succ hi)]

end
end Clo

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A)

/-! ### the four plain functions -/

/-- The join point, flat: the one round draws mu elements. -/
def joinRun (x : A.XS) (f : List (RV E)) : A.XS :=
  A.joinNx x fun t => (f.headD ([], [])).2.getD t.val 0

/-- The zero point, flat: the one round draws mu + d elements. -/
def zeroRun (x : A.XS) (f : List (RV E)) : A.XS :=
  A.zeroNx x fun t => (f.headD ([], [])).2.getD t.val 0

/-- The closing, flat. Round 0: one scalar, ε. Then a round for each variable. -/
def closeRun (x : A.XS) (f : List (RV E)) : A.XS :=
  { x with
    rows := x.rows ++
      [⟨fun j =>
          Clo.hidM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d))) P.wE
              (fun i => Lev.chC f (i + 1)) j +
            Lev.chC f 0 * x.top.mf j +
            Lev.chC f 0 *
              (Alg.mle (fun r : Fin A.d → Bool => x.al - 1 - A.tab x.st (numLE r))
                  (fun r => Lev.chC f ((Fin.natAdd A.mu r).rev.val + 1)) *
                A.cellW (fun t => Lev.chC f (t.rev.val + 1)) j),
        Clo.finM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))
            (fun i => x.pt (ordC (A.mu + A.d) i)) (Lev.snt f 0 0 + Lev.chC f 0 * x.top.tg) f.tail -
          Lev.chC f 0⟩] }

/-- The test of the bits, flat. Round 0: one scalar, ε. Then a round for each variable, the further
variable's round, and the round of the one shown value. -/
def bitsRun (x : A.XS) (f : List (RV E)) : A.XS :=
  { x with
    rows := x.rows ++
      [⟨Lev.rowF (A.mu + A.d) (fun r t => P.wB (Lev.nmV E (A.mu + A.d) r t))
          (P.wB (Lev.nmC E (A.mu + A.d))) (fun i => Lev.chC f (i + 1)),
        Lev.finC (A.mu + A.d) (fun i => x.zt (ordC (A.mu + A.d) i))
            (Lev.snt f 0 0 + Lev.chC f 0 * 0) f.tail -
          Lev.chC f 0 * (Lev.snt f (A.mu + A.d + 2) 0 * (Lev.snt f (A.mu + A.d + 2) 0 - 1))⟩,
       ⟨fun j => A.cellW (fun t => Lev.chC f (t.rev.val + 1)) j +
          Lev.one P.cB (Lev.chC f (A.mu + A.d + 1)) j,
        Lev.snt f (A.mu + A.d + 2) 0⟩] }

/-! ### the typed values against the flat ones -/
section
variable [DecidableEq E]

/-- The readers of the closing's rounds, and of the rounds of the test of the bits. -/
noncomputable def rdC : RdS E (TWhole.shapeSC (A.En P).par) :=
  rdCore (A.En P).par (Clo.fuM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d))))
noncomputable def rdB : RdS E (shapeS (A.BT P).par) :=
  rdFull (A.BT P).par (Lev.fuK (A.mu + A.d)) finOneEquiv.symm

/-- The formats of the closing's rounds. -/
def fmClo : List Fm :=
  ⟨1, 1, false⟩ :: Clo.fmM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))

theorem rdC_fms : (A.rdC P).fms = A.fmClo :=
  congrArg (List.cons (⟨1, 1, false⟩ : Fm)) (Clo.fuM_fms _ _)

theorem close_view (x : A.XS) (τ : Tr (TWhole.shapeSC (A.En P).par)) :
    A.closeOut P (A.zzOf P x τ) = A.closeRun P x ((A.rdC P).view τ) := by
  obtain ⟨m, ε, τ'⟩ := τ
  have hγ : ∀ i : ℕ, ppGet (A.En P).par.fmt (A.zzOf P x (m, ε, τ')).pt i =
      Lev.chC ((A.rdC P).view (m, ε, τ')) (i + 1) := fun i =>
    (Clo.ppGet_vFin _ _ _ _ _ i).trans (Clo.ch_viewM _ _ τ' i)
  have hfin : (A.zzOf P x (m, ε, τ')).fin =
      Clo.finM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))
        (fun i => x.pt (ordC (A.mu + A.d) i)) (m.2 + ε * x.top.tg)
        ((A.rdC P).view (m, ε, τ')).tail :=
    Clo.fin_viewM _ _ _ _ τ'
  have hrow : A.rowE P (A.zzOf P x (m, ε, τ')) =
      ⟨fun j =>
          Clo.hidM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d))) P.wE
              (fun i => Lev.chC ((A.rdC P).view (m, ε, τ')) (i + 1)) j +
            ε * x.top.mf j +
            ε *
              (Alg.mle (fun r : Fin A.d → Bool => x.al - 1 - A.tab x.st (numLE r))
                  (fun r => Lev.chC ((A.rdC P).view (m, ε, τ'))
                    ((Fin.natAdd A.mu r).rev.val + 1)) *
                A.cellW (fun t => Lev.chC ((A.rdC P).view (m, ε, τ')) (t.rev.val + 1)) j),
        Clo.finM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))
            (fun i => x.pt (ordC (A.mu + A.d) i)) (m.2 + ε * x.top.tg)
            ((A.rdC P).view (m, ε, τ')).tail - ε⟩ := by
    refine congrArg₂ Row.mk (funext fun j => ?_) ?_
    · refine (A.rowE_cf P _ j).trans ?_
      have h1 : ppGet (A.En P).par.fmt (A.zzOf P x (m, ε, τ')).pt =
          fun i => Lev.chC ((A.rdC P).view (m, ε, τ')) (i + 1) := funext hγ
      have h2 : A.ptE P (A.zzOf P x (m, ε, τ')) =
          fun t => Lev.chC ((A.rdC P).view (m, ε, τ')) (t.rev.val + 1) :=
        funext fun t => hγ t.rev.val
      have h3 : A.facE P (A.zzOf P x (m, ε, τ')) =
          Alg.mle (fun r : Fin A.d → Bool => x.al - 1 - A.tab x.st (numLE r))
            (fun r => Lev.chC ((A.rdC P).view (m, ε, τ')) ((Fin.natAdd A.mu r).rev.val + 1)) := by
        unfold facE
        rw [h2]
        rfl
      have h0 : Cf.nSum (A.En P).par.fmt (fun i => if P.wE i = j then
            Cf.nH (A.En P).par.fmt (A.zzOf P x (m, ε, τ')).pt i else 0) =
          Clo.hidM (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d))) P.wE
            (fun i => Lev.chC ((A.rdC P).view (m, ε, τ')) (i + 1)) j :=
        (Clo.nSum_hidM _ _ P.wE _ j).trans (congrArg (fun c => Clo.hidM _ _ P.wE c j) h1)
      rw [h0, h2, h3]
      rfl
    · exact (A.rowE_tg P _).trans (congrArg (· - ε) hfin)
  show ({ x with rows := x.rows ++ [A.rowE P (A.zzOf P x (m, ε, τ'))] } : A.XS) = _
  rw [hrow]
  rfl

/-- The formats of the rounds of the test of the bits. -/
def fmBits : List Fm :=
  ⟨1, 1, false⟩ ::
    ((List.replicate (A.mu + A.d) (⟨2, 1, false⟩ : Fm) ++ [⟨2, 1, true⟩]) ++ [⟨1, 0, false⟩])

theorem fuK_fms : ∀ k : ℕ, (rdVars (Lev.lk E k) (Lev.fuK k)).fms =
    List.replicate k (⟨2, 1, false⟩ : Fm) ++ [⟨2, 1, true⟩]
  | 0 => rfl
  | k + 1 => by
    show (⟨2, 1, false⟩ : Fm) :: (rdVars (Lev.lk E k) (Lev.fuK k)).fms = _
    rw [fuK_fms k]
    rfl

theorem rdB_fms : (A.rdB P).fms = A.fmBits := by
  show (⟨1, 1, false⟩ : Fm) :: ((rdVars (Lev.lk E (A.mu + A.d)) (Lev.fuK (A.mu + A.d))).app
    (Clo.rdV1 E)).fms = _
  rw [RdS.fms_app, fuK_fms]
  rfl

theorem bits_view (x : A.XS) (τ : Tr (shapeS (A.BT P).par)) :
    A.bitsOut P (A.oOf P x τ) = A.bitsRun P x ((A.rdB P).view τ) := by
  obtain ⟨m, ε, τ'⟩ := τ
  have hγ : ∀ i : ℕ, i ≤ A.mu + A.d → ppGet (A.BT P).par.fmt (A.oOf P x (m, ε, τ')).pt i =
      Lev.chC ((A.rdB P).view (m, ε, τ')) (i + 1) := fun i hi =>
    (ppGet_vFinT _ _ _ _ _ _ i).trans
      (Lev.ch_view (t := [pRoundV E Unit]) (Clo.rdV1 E) (A.mu + A.d) τ' i hi)
  have hfin : (A.oOf P x (m, ε, τ')).fin =
      Lev.finC (A.mu + A.d) (fun i => x.zt (ordC (A.mu + A.d) i)) (m.2 + ε * 0)
        ((A.rdB P).view (m, ε, τ')).tail :=
    Lev.fin_view (t := [pRoundV E Unit]) (Clo.rdV1 E) (A.mu + A.d) _ _ τ'
  have hv : (A.oOf P x (m, ε, τ')).vals () =
      Lev.snt ((A.rdB P).view (m, ε, τ')) (A.mu + A.d + 2) 0 := by
    have h := Lev.tail_view (t := [pRoundV E Unit]) (Clo.rdV1 E) (A.mu + A.d)
      (fun i => x.zt (ordC (A.mu + A.d) i)) (m.2 + ε * 0) τ' 0
    show _ = ((((rdVars (Lev.lk E (A.mu + A.d)) (Lev.fuK (A.mu + A.d))).app
      (Clo.rdV1 E)).view τ').getD
        (A.mu + A.d + 1 + 0) ([], [])).1.getD 0 0
    rw [h]
    rfl
  have hU : A.rowU P (A.oOf P x (m, ε, τ')) =
      ⟨Lev.rowF (A.mu + A.d) (fun r t => P.wB (Lev.nmV E (A.mu + A.d) r t))
          (P.wB (Lev.nmC E (A.mu + A.d)))
          (fun i => Lev.chC ((A.rdB P).view (m, ε, τ')) (i + 1)),
        Lev.finC (A.mu + A.d) (fun i => x.zt (ordC (A.mu + A.d) i)) (m.2 + ε * 0)
            ((A.rdB P).view (m, ε, τ')).tail -
          ε * (Lev.snt ((A.rdB P).view (m, ε, τ')) (A.mu + A.d + 2) 0 *
            (Lev.snt ((A.rdB P).view (m, ε, τ')) (A.mu + A.d + 2) 0 - 1))⟩ := by
    refine congrArg₂ Row.mk (funext fun j => ?_) ?_
    · exact (A.rowU_cf P _ j).trans ((Clo.nSum_rowF (A.mu + A.d) P.wB _ j).trans
        (congrFun (Clo.rowF_congr (A.mu + A.d) _ _ _ _ hγ) j))
    · refine (A.rowU_tg P _).trans ?_
      rw [hfin, hv]
      rfl
  have hV : A.rowV P (A.oOf P x (m, ε, τ')) =
      ⟨fun j => A.cellW (fun t => Lev.chC ((A.rdB P).view (m, ε, τ')) (t.rev.val + 1)) j +
          Lev.one P.cB (Lev.chC ((A.rdB P).view (m, ε, τ')) (A.mu + A.d + 1)) j,
        Lev.snt ((A.rdB P).view (m, ε, τ')) (A.mu + A.d + 2) 0⟩ := by
    refine congrArg₂ Row.mk (funext fun j => ?_) hv
    refine (A.rowV_cf P _ j).trans ?_
    have h2 : A.ptB P (A.oOf P x (m, ε, τ')) =
        fun t => Lev.chC ((A.rdB P).view (m, ε, τ')) (t.rev.val + 1) :=
      funext fun t => hγ t.rev.val (Nat.le_of_lt t.rev.isLt)
    have h3 : A.betaB P (A.oOf P x (m, ε, τ')) =
        Lev.chC ((A.rdB P).view (m, ε, τ')) (A.mu + A.d + 1) :=
      (A.betaB_get P _).trans (hγ _ (Nat.le_refl _))
    rw [h2, h3]
    rfl
  show ({ x with rows := x.rows ++ [A.rowU P (A.oOf P x (m, ε, τ')),
    A.rowV P (A.oOf P x (m, ε, τ'))] } : A.XS) = _
  rw [hU, hV]
  rfl

variable (Ex : ExtSpec)

/-- For all transcripts: the four verifiers' outputs are the plain functions of the view. -/
noncomputable def joinK_runs : Runs (A.joinK Ex) [⟨0, A.mu, false⟩] A.joinRun :=
  Runs.draw A.joinNx _ (rdPt A.mu) (fun l t => l.getD t.val 0) fun c =>
    funext fun t => getD_ofFn c t

noncomputable def zeroK_runs : Runs (A.zeroK Ex) [⟨0, A.mu + A.d, false⟩] A.zeroRun :=
  Runs.draw A.zeroNx _ (rdPt (A.mu + A.d)) (fun l t => l.getD t.val 0) fun c =>
    funext fun t => getD_ofFn c t

noncomputable def closeK_runs : Runs (A.closeK P (SK₀ E Ex)) A.fmClo (A.closeRun P) :=
  ((Runs.ofOut (b := A.closeK P (SK₀ E Ex)) (A.rdC P) (fun x τ => A.closeOut P (A.zzOf P x τ))
    (A.close_out P Ex)).fmEq (A.rdC_fms P)).congr fun x f hf => by
      show A.closeOut P (A.zzOf P x ((A.rdC P).mk f)) = _
      rw [A.close_view P x, (A.rdC P).view_mk f (by rw [A.rdC_fms P]; exact hf)]

noncomputable def bitsK_runs : Runs (A.bitsK P (SK₀ E Ex)) A.fmBits (A.bitsRun P) :=
  ((Runs.ofOut (b := A.bitsK P (SK₀ E Ex)) (A.rdB P) (fun x τ => A.bitsOut P (A.oOf P x τ))
    (A.bits_out P Ex)).fmEq (A.rdB_fms P)).congr fun x f hf => by
      show A.bitsOut P (A.oOf P x ((A.rdB P).mk f)) = _
      rw [A.bits_view P x, (A.rdB P).view_mk f (by rw [A.rdB_fms P]; exact hf)]

end

end Dat
end Lk6

#print axioms Lk6.Dat.bits_view
#print axioms Lk6.Dat.bitsK_runs
#print axioms Lk6.Dat.close_view
#print axioms Lk6.Dat.joinK_runs
#print axioms Lk6.Dat.zeroK_runs
#print axioms Lk6.Dat.closeK_runs
