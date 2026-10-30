-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwState.lean.
The state that the lookup's chain leaves, read as a trace, is the flat trace of the transcript read
as plain data.

Definitions, and theorems with their proofs, general in the assembly A.
Main names:
  `tie_base`, `tree_root`, `forest_root`: at the state that a block puts out, the library's readers
    (base, root) give back the state with which the block was entered.
  `keyTr`, `flTab`, `flForest_eq`, `x4Of`, `forest_tab`: the forest, cut in its two trees.
  `RootTg A st kAt`: two equations on the targets at the trees' roots, a premise here (proved in
    Cb/Pv/Lookup/Out/TwRoot.lean; see Cb/Pv/Lookup/Out/TwStateR.lean).
  `bit_tg0`: the bit test's sumcheck starts from the target 0. `traceOf_of`: `traceOf` at a last
    state whose readers give named states.
  `state_eq_of`: under `RootTg A st kAt`, for every state st of the caller and every typed
    transcript τ:
    `traceOf A (chnV (SV₀ E Ex) A st τ) = traceOfFlat (numsOf A st kAt) (flChn Ex A τ)`.
    `state_eq7`: the same, with the transcript given in its seven parts.
Limits: kAt, and st on the right side, enter through the record `numsOf` alone, of which
`traceOfFlat` reads only n, v', d, w and the four orders. At the filling `SK₀`, `SV₀`
(Cb/Pv/Lookup/Out/TwFill.lean). What "read as plain data" means is the text of `flChn`
(Cb/Pv/Lookup/Out/TwFlat.lean); what "read as a trace" means is the text of `traceOf`
(Cb/Pv/Lookup/Out/TwTraceOf.lean). Both sides are functions in Lean: neither is compared here with
a program or with bytes. The verifier's side alone. The chain refuses no transcript (`chnK₀_out`,
Cb/Pv/Lookup/Out/TwFill.lean), so the equation says nothing on what is accepted.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwLev
import Cb.Pv.Lookup.Out.TwTraceL
import Cb.Pv.Lookup.Order.TwWt

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3

noncomputable section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec)

/-! ### the readers on a run -/

theorem tie_base (D : TieF E) : ∀ (n : ℕ) (x : E × (D.lv 0).T.St)
    (τ : Tr (D.tieK (SK₀ E Ex) n).R.shape), (D.lv (n + 1)).base (tieV (SV₀ E Ex) D n x τ).2 = x.2
  | 0, _, _ => rfl
  | n + 1, x, τ => tie_base D n x (Tr.fst τ)

theorem tree_root (D : TreeP E) : ∀ (n : ℕ) (x : E × (D.lv 0).T.St)
    (τ : Tr (D.treeK (SK₀ E Ex) n).R.shape), D.root (n + 1) (treeV (SV₀ E Ex) D n x τ).2 = x.2
  | 0, _, _ => rfl
  | n + 1, x, τ => tree_root D n x (Tr.fst τ)

/-! ### the forest, cut in its two trees -/
variable (A : LkAsmH E)

/-- the keys' side's part of a forest's transcript -/
def keyTr : (l : ℕ) → Tr (A.forestK (SK₀ E Ex) l).R.shape →
    Tr ((A.IK.setV (A.v' + 1)).DK.treeK (SK₀ E Ex) A.v').R.shape
  | 0, τ => τ
  | l + 1, τ => keyTr l (Tr.fst τ)

/-- the table's levels' part, as plain data -/
def flTab : (l : ℕ) → Tr (A.forestK (SK₀ E Ex) l).R.shape → Rounds E
  | 0, _ => []
  | l + 1, τ => flTab l (Tr.fst τ) ++ flLev Ex A.D l (Tr.snd (s := (A.forestK (SK₀ E Ex) l).R.shape)
      τ)

theorem flForest_eq : ∀ (l : ℕ) (τ : Tr (A.forestK (SK₀ E Ex) l).R.shape),
    flForest Ex A l τ = flTree Ex (A.IK.setV (A.v' + 1)).DK A.v' (keyTr Ex A l τ) ++ flTab Ex A l τ
  | 0, _ => (List.append_nil _).symm
  | l + 1, τ => by
    show flForest Ex A l (Tr.fst τ) ++ flLev Ex A.D l _ = _ ++ (flTab Ex A l (Tr.fst τ) ++ _)
    rw [flForest_eq l (Tr.fst τ), List.append_assoc]
    rfl

/-- the state behind the keys' side -/
def x4Of (xR : A.XR) (τK : Tr ((A.IK.setV (A.v' + 1)).DK.treeK (SK₀ E Ex) A.v').R.shape) : A.X4 :=
  segKV (SV₀ E Ex) A.IK A.v' (fun x => A.tK (A.oR x)) xR τK

theorem forest_root : ∀ (l : ℕ) (xR : A.XR) (τ : Tr (A.forestK (SK₀ E Ex) l).R.shape),
    A.D.root l (forestV (SV₀ E Ex) A l xR τ).2 = (A.enterT (x4Of Ex A xR (keyTr Ex A l τ))).2
  | 0, _, _ => rfl
  | l + 1, xR, τ => forest_root l xR (Tr.fst τ)

theorem forest_tab (o : ℕ → List ℕ)
    (ho : ∀ l, o l = List.ofFn fun j : Fin (A.D.g + l) => ((A.D.sg l j : Fin (A.D.g + l)) : ℕ)) :
    ∀ (l : ℕ) (xR : A.XR) (τ : Tr (A.forestK (SK₀ E Ex) l).R.shape) (rest : Rounds E),
    lvGo o l 0 (A.enterT (x4Of Ex A xR (keyTr Ex A l τ))).1
        (List.ofFn ((A.D.lv 0).pnt (A.enterT (x4Of Ex A xR (keyTr Ex A l τ))).2))
        (flTab Ex A l τ ++ rest) =
      ((lvN A.D l (forestV (SV₀ E Ex) A l xR τ).2).reverse, (forestV (SV₀ E Ex) A l xR τ).1,
        List.ofFn ((A.D.lv l).pnt (forestV (SV₀ E Ex) A l xR τ).2), rest)
  | 0, _, _, _ => rfl
  | l + 1, xR, τ, rest => by
    have hf : flTab Ex A (l + 1) τ ++ rest = flTab Ex A l (Tr.fst τ) ++
        (flLev Ex A.D l (Tr.snd (s := (A.forestK (SK₀ E Ex) l).R.shape) τ) ++ rest) :=
      List.append_assoc _ _ _
    rw [hf]
    exact lev_step Ex o A.D ho l _ _ _ (forestV (SV₀ E Ex) A l xR (Tr.fst τ))
      (Tr.snd (s := (A.forestK (SK₀ E Ex) l).R.shape) τ) rest (forest_tab o ho l xR (Tr.fst τ) _)

/-! ### the whole -/

/-- Two equations between a typed and a flat target, at every state x behind the tie and every trace
t whose tie is `tieN` of x, the oldest first. tK: the target with which the keys' tree is entered.
tgT0: the target that the planes' point ϱ hands to the table's level 0, where x.1 is the shown value
that the last step hands on and t.join is ϱ as a list. -/
structure RootTg (st : A.St) (kAt : ℕ → A.J ⊕ E) : Prop where
  tK : ∀ (x : A.X2) (t : Trace E), t.tie = (tieN A.H.tie (A.n + 1) x.2).reverse → A.tK x = TwV.tK t
  tgT0 : ∀ (x : A.X2), x.1 = x.2.vals (A.H.tie.lv A.n).nx → ∀ (ϱ : Fin (A.w + 0) → E) (t : Trace E),
    t.tie = (tieN A.H.tie (A.n + 1) x.2).reverse → t.join = List.ofFn ϱ →
    (A.R.toIn.nxX x ϱ).1 = TwV.tgT0 (numsOf A st kAt) t

/-- the bits' sumcheck starts from the target 0 -/
theorem bit_tg0 (z : A.XE) (ζ : A.Bt.zc.toIn.ev.D) : (A.Bt.zc.toIn.nxX z ζ).1 = 0 := by
  show ∑ i, A.Bt.zc.toIn.ev.ze ζ i * (0 : E) = 0
  simp

/-- what traceOf reads off a last state whose readers give the named states -/
theorem traceOf_of (st : A.St) (lam : E) (x2 : A.X2) (hb2 : A.b2 x2 = (st, lam)) (xR : A.XR)
    (hoR : A.oR xR = x2) (x4 : A.X4) (h4 : A.o4 x4 = xR) (yF : E × (A.D.lv A.d).T.St)
    (hroot : A.D.root A.d yF.2 = (x4, xR.2.2)) (zE : A.XE) (hz : zE.st = yF.2)
    (ζ : A.Bt.zc.toIn.ev.D) (oB : A.XB) (ho : oB.st = (zE, ζ)) :
    traceOf A oB = ⟨lam, (tieN A.H.tie (A.n + 1) x2.2).reverse, List.ofFn xR.2.2,
      (lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1) x4.2).reverse, x4.1, (lvN A.D A.d yF.2).reverse,
      scMid A.En.par zE, List.ofFn ζ.2, scOf A.Bt.zc.next.par [()] oB⟩ := by
  have e1 : A.outE oB = zE := congrArg Prod.fst ho
  have e2 : A.oldT oB = x4 := by
    unfold LkAsmH.oldT
    rw [e1, hz, hroot]
  unfold traceOf
  rw [e1, e2, h4, hoR, hb2, hz, hroot, ho]
  rfl

/-- `state_eq_of` with the transcript in seven parts: λ, the tie, the planes' point, the forest, the
closing, the bit test's point, the bit test's sumcheck. -/
theorem state_eq7 (st : A.St) (kAt : ℕ → A.J ⊕ E) (hR : RootTg A st kAt) (lam : E)
    (τT : Tr (A.H.tie.tieK (SK₀ E Ex) A.n).R.shape) (ϱ : Fin (A.w + 0) → E)
    (τF : Tr (A.forestK (SK₀ E Ex) A.d).R.shape) (τE : Tr (A.endK (SK₀ E Ex)).R.shape)
    (ζ : A.Bt.zc.toIn.ev.D) (τB : Tr ((SK₀ E Ex).full A.Bt.zc.next.par).R.shape) :
    traceOf A ((SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX
        ((SV₀ E Ex).core A.En.par (forestV (SV₀ E Ex) A A.d
          (A.R.toIn.nxX (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) ϱ) τF) τE) ζ) τB) =
      traceOfFlat (numsOf A st kAt) (([], [lam]) :: (flTie Ex A.H.tie A.n τT ++ (([], List.ofFn ϱ)
          ::
        (flForest Ex A A.d τF ++ (flEnd Ex A τE ++ (([], List.ofFn ζ.2) ::
          flFull Ex A.Bt.zc.next.par [()] τB)))))) := by
  -- the tie
  have h1 := tie_flat Ex A.H.tie A.n ((0 : E), (st, lam)) τT (([], List.ofFn ϱ) ::
    (flForest Ex A A.d τF ++ (flEnd Ex A τE ++ (([], List.ofFn ζ.2) ::
      flFull Ex A.Bt.zc.next.par [()] τB))))
  have hb2 : A.b2 (tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT) = (st, lam) :=
    tie_base Ex A.H.tie A.n ((0 : E), (st, lam)) τT
  have htg := tie_tg Ex A.H.tie A.n ((0 : E), (st, lam)) τT
  generalize tieV (SV₀ E Ex) A.H.tie A.n ((0 : E), (st, lam)) τT = x2 at h1 hb2 htg ⊢
  have hK := hR.tK x2 ⟨lam, (tieN A.H.tie (A.n + 1) x2.2).reverse, List.ofFn ϱ, [], 0, [], Sc.zero,
      [],
    Sc.zero⟩ rfl
  have hT := hR.tgT0 x2 htg ϱ ⟨lam, (tieN A.H.tie (A.n + 1) x2.2).reverse,
    List.ofFn ϱ, [], 0, [], Sc.zero, [], Sc.zero⟩ rfl rfl
  -- the point
  have hoR : A.oR (A.R.toIn.nxX x2 ϱ) = x2 := rfl
  have hϱ : (A.R.toIn.nxX x2 ϱ).2.2 = ϱ := rfl
  generalize A.R.toIn.nxX x2 ϱ = xR at hT hoR hϱ ⊢
  -- the keys' side
  have h2 := tree_flat Ex (numsOf A st kAt).oK (A.IK.setV (A.v' + 1)).DK (fun _ => rfl) A.v'
    (enterK (A.IK.setV (A.v' + 1)) (fun x => A.tK (A.oR x)) xR) (keyTr Ex A A.d τF)
    (flTab Ex A A.d τF ++ (flEnd Ex A τE ++ (([], List.ofFn ζ.2) ::
      flFull Ex A.Bt.zc.next.par [()] τB)))
  have h2' : lvGo (numsOf A st kAt).oK ((numsOf A st kAt).v' + 1) 0 (A.tK (A.oR xR)) []
      (flTree Ex (A.IK.setV (A.v' + 1)).DK A.v' (keyTr Ex A A.d τF) ++
        (flTab Ex A A.d τF ++ (flEnd Ex A τE ++ (([], List.ofFn ζ.2) ::
          flFull Ex A.Bt.zc.next.par [()] τB)))) =
      ((lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (x4Of Ex A xR (keyTr Ex A A.d τF)).2).reverse,
        (x4Of Ex A xR (keyTr Ex A A.d τF)).1,
        List.ofFn (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).pnt (x4Of Ex A xR (keyTr Ex A A.d
            τF)).2),
        flTab Ex A A.d τF ++ (flEnd Ex A τE ++ (([], List.ofFn ζ.2) ::
          flFull Ex A.Bt.zc.next.par [()] τB))) := h2
  have h4 : A.o4 (x4Of Ex A xR (keyTr Ex A A.d τF)) = xR :=
    congrArg Prod.fst (tree_root Ex (A.IK.setV (A.v' + 1)).DK A.v'
      (enterK (A.IK.setV (A.v' + 1)) (fun x => A.tK (A.oR x)) xR) (keyTr Ex A A.d τF))
  -- the table's levels
  have h3 := forest_tab Ex A (numsOf A st kAt).oT (fun _ => rfl) A.d xR τF
    (flEnd Ex A τE ++ (([], List.ofFn ζ.2) :: flFull Ex A.Bt.zc.next.par [()] τB))
  have hroot := forest_root Ex A A.d xR τF
  generalize x4Of Ex A xR (keyTr Ex A A.d τF) = x4 at h2' h4 h3 hroot
  have e1 : (A.enterT x4).1 = xR.1 := congrArg Prod.fst h4
  have e2 : (A.D.lv 0).pnt (A.enterT x4).2 = xR.2.2 := congrArg (fun x : A.XR => x.2.2) h4
  have e3 : (A.enterT x4).2 = (x4, xR.2.2) := congrArg (fun x : A.XR => (x4, x.2.2)) h4
  rw [e1, e2] at h3
  rw [e3] at hroot
  generalize forestV (SV₀ E Ex) A A.d xR τF = yF at h3 hroot ⊢
  -- the closing
  have h4' := takeSc_flatC A.En.par yF.1 yF.2 _ (end_wt A st kAt yF.2) τE
    (([], List.ofFn ζ.2) :: flFull Ex A.Bt.zc.next.par [()] τB)
  have hz : ((SV₀ E Ex).core A.En.par yF τE).st = yF.2 := rfl
  have h4'' : takeSc (flEnd Ex A τE ++ (([], List.ofFn ζ.2) :: flFull Ex A.Bt.zc.next.par [()] τB))
      yF.1
      (inRounds (numsOf A st kAt).oE (List.ofFn ((A.D.lv A.d).pnt yF.2))) false =
      (scMid A.En.par ((SV₀ E Ex).core A.En.par yF τE),
        ([], List.ofFn ζ.2) :: flFull Ex A.Bt.zc.next.par [()] τB) := h4'
  generalize (SV₀ E Ex).core A.En.par yF τE = zE at hz h4'' ⊢
  -- the bits
  have h5 := takeSc_flat A.Bt.zc.next.par [()] (A.Bt.zc.toIn.nxX zE ζ).1 (A.Bt.zc.toIn.nxX zE ζ).2 _
    (bit_wt A st kAt (A.Bt.zc.toIn.nxX zE ζ).2) τB []
  rw [bit_tg0, List.append_nil] at h5
  have h5' : takeSc (flFull Ex A.Bt.zc.next.par [()] τB) 0
      (inRounds (numsOf A st kAt).oB (List.ofFn ζ.2) ++ [0]) true =
      (scOf A.Bt.zc.next.par [()] ((SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX zE ζ) τB), [])
          := by
    have e : ((SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX zE ζ) τB) =
        shortV A.Bt.zc.next.par (F₀ A.Bt.zc.next.par) (0, (A.Bt.zc.toIn.nxX zE ζ).2) τB := by
      show shortV A.Bt.zc.next.par (F₀ A.Bt.zc.next.par) ((A.Bt.zc.toIn.nxX zE ζ).1,
        (A.Bt.zc.toIn.nxX zE ζ).2) τB = _
      rw [bit_tg0]
    rw [e]
    exact h5
  have ho : ((SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX zE ζ) τB).st = (zE, ζ) := rfl
  generalize (SV₀ E Ex).full A.Bt.zc.next.par (A.Bt.zc.toIn.nxX zE ζ) τB = oB at h5' ho ⊢
  -- together
  rw [flForest_eq, List.append_assoc] at h1 ⊢
  rw [hoR, hK] at h2'
  rw [hT, hϱ] at h3
  rw [traceOf_of A st lam x2 hb2 xR hoR x4 h4 yF hroot zE hz ζ oB ho, hϱ]
  exact (traceOfFlat_of (numsOf A st kAt) lam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2' h3 h4''
      h5').symm

/-- The state's equation, under `RootTg`. Without the premise: `state_eq`,
Cb/Pv/Lookup/Out/TwStateR.lean. -/
theorem state_eq_of (st : A.St) (kAt : ℕ → A.J ⊕ E) (hR : RootTg A st kAt)
    (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    traceOf A (chnV (SV₀ E Ex) A st τ) = traceOfFlat (numsOf A st kAt) (flChn Ex A τ) := by
  have h := state_eq7 Ex A st kAt hR (drawn (Tr.fst (Tr.fst (Tr.fst (Tr.fst (Tr.fst τ))))))
    (Tr.snd (s := [drawRound E]) (Tr.fst (Tr.fst (Tr.fst (Tr.fst τ)))))
    (drawn (Tr.snd (s := (A.H.headK (SK₀ E Ex)).R.shape) (Tr.fst (Tr.fst (Tr.fst τ)))))
    (Tr.snd (s := ((A.H.headK (SK₀ E Ex)).seq (A.rootK Ex)).R.shape) (Tr.fst (Tr.fst τ)))
    (Tr.snd (s := (((A.H.headK (SK₀ E Ex)).seq (A.rootK Ex)).seq (A.forestK (SK₀ E Ex)
        A.d)).R.shape)
      (Tr.fst τ))
    (drawn (Tr.fst (Tr.snd (s := ((((A.H.headK (SK₀ E Ex)).seq (A.rootK Ex)).seq
      (A.forestK (SK₀ E Ex) A.d)).seq (A.endK (SK₀ E Ex))).R.shape) τ)))
    (Tr.snd (s := [drawRound A.Bt.zc.toIn.ev.D]) (Tr.snd (s := ((((A.H.headK (SK₀ E Ex)).seq
      (A.rootK Ex)).seq (A.forestK (SK₀ E Ex) A.d)).seq (A.endK (SK₀ E Ex))).R.shape) τ))
  refine Eq.trans h (congrArg (traceOfFlat (numsOf A st kAt)) ?_)
  unfold flChn flHead flRoot flBit fseq fdraw
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rfl

end
end Tw
#print axioms Tw.state_eq7
#print axioms Tw.state_eq_of
