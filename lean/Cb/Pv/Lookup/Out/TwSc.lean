-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwSc.lean.
One short sumcheck: the flat step on plain data gives the fields of the typed verifier's
out-statement.

Definitions, and theorems with their proofs. The flat step `TwV.takeSc` is of Cb/G9/FlatStep.lean;
`shortV`, `shortVC`, `F₀`, `Eq0` are of Cb/G6/Value.lean, Cb/G6/Core.lean and Cb/G6/Pick.lean.
Main names:
  `flS`, `flS0`, `flSc Y sh`, `flScC Y`: a typed transcript of a short sumcheck as plain data: for
    each round the scalars sent (the coefficients of the powers 1 to n, rising) and the values of
    the challenges drawn; sh is the order in which the shown values are listed.
  `Wt l d zs`: what the flat step knows of a variable: the "sum" (`HVar.mon`,
    Cb/Ld/LdHideShort.lean) of each of its powers from 1 to n is one number z, the list's member.
    `wt_eqs`, `wt_mix`, `wt_snoc_dummy`: it holds for equality variables (z: the weight's point), of
    one degree or of a degree each, and with the further variable after them (z = 0).
  `fill_eval`: the completed round polynomial at a point. `runVars_flat`, `runVars_flat0`: all
    rounds of the variables.
  `takeSc_flat`, `takeSc_flatC`: under `Wt Y.fmt (Y.dat st) zs`, for every Y, target, state st,
    typed transcript and any rounds after it: `TwV.takeSc` on the plain data, at zs, gives the
    fields eps, pt (as a list) and fin of `shortV`, `shortVC` at the pick `F₀`, of `shortV` also
    vals in sh's order, and hands back the rounds after it. The field st is not compared.
Limits: `takeSc_flat` holds for every list sh, a wrong or doubled one too: which shown value is
which is not pinned here but by the lists that Cb/Pv/Lookup/Out/TwFlat.lean and
Cb/Pv/Lookup/Out/TwTraceOf.lean share. Likewise the order of a message's scalars is `flS`'s text.
The lemmas do not need `Eq0`: they equate with `shortV` at the pick whether or not it is lawful.
That the typed verifier puts out `shortV` is `short_out` (Cb/G6/Value.lean), under `HFixs.OK`.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwV
import Cb.Pv.Lookup.Order.TwPoint
import Cb.G6.Pick

set_option autoImplicit false

namespace Tw
open Iop Prob Cb Cb.Tw TWhole Johnson.L5.Layers TwV

section
variable {E : Type} [Field E]

/-! ### plain data off a typed short transcript -/

def flS : (l : List (PFmt E)) → (t : Shape) → Tr (sRounds l ++ t) → Rounds E
  | [], _, _ => []
  | f :: l, t, (m, c, τ) => (List.ofFn m.2, [f.val c]) :: flS l t τ

def flS0 : (l : List (PFmt E)) → Tr (sRounds l) → Rounds E
  | [], _ => []
  | f :: l, (m, c, τ) => (List.ofFn m.2, [f.val c]) :: flS0 l τ

theorem flS_length : ∀ (l : List (PFmt E)) (t : Shape) (τ : Tr (sRounds l ++ t)),
    (flS l t τ).length = l.length
  | [], _, _ => rfl
  | _ :: l, t, (_, _, τ) => congrArg (· + 1) (flS_length l t τ)

theorem flS0_length : ∀ (l : List (PFmt E)) (τ : Tr (sRounds l)), (flS0 l τ).length = l.length
  | [], _ => rfl
  | _ :: l, (_, _, τ) => congrArg (· + 1) (flS0_length l τ)

/-- What the flat step knows of each variable: one number z, the "sum" of each of its powers from 1
to n. The two lists have one length. -/
def Wt : (l : List (PFmt E)) → PDats l → List E → Prop
  | [], _, zs => zs = []
  | _ :: _, _, [] => False
  | f :: l, d, z :: zs => (∀ a : Fin f.n, (f.var d.1).mon a.succ = z) ∧ Wt l d.2 zs

theorem Wt.length : ∀ {l : List (PFmt E)} {d : PDats l} {zs : List E}, Wt l d zs →
    zs.length = l.length
  | [], _, _, h => by rw [show _ = [] from h]; rfl
  | _ :: _, _, [], h => h.elim
  | _ :: _, _, _ :: _, h => congrArg (· + 1) (Wt.length h.2)

/-! ### one round -/

theorem evalGo_ofFn (x : E) : ∀ (n k : ℕ) (q : Fin n → E),
    evalGo x k (List.ofFn q) = ∑ t : Fin n, q t * x ^ (k + (t : ℕ) + 1)
  | 0, _, _ => by simp [evalGo]
  | n + 1, k, q => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    show q 0 * x ^ (k + 1) + evalGo x (k + 1) (List.ofFn fun i => q i.succ) = _
    rw [evalGo_ofFn x n (k + 1)]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun t _ => ?_)
    rw [Fin.val_succ, show k + 1 + (t : ℕ) + 1 = k + ((t : ℕ) + 1) + 1 by omega]

theorem hev_cons0 {n : ℕ} (q : Fin n → E) (y : E) :
    hev ((0 : Fin (n + 1)).insertNth (α := fun _ => E) 0 q) y = ∑ t : Fin n, q t * y ^ ((t : ℕ) + 1)
        := by
  unfold hev
  rw [Fin.sum_univ_succ]
  simp only [Fin.insertNth_zero, Fin.cons_zero, Fin.cons_succ, smul_eq_mul, mul_zero, zero_add,
    Fin.val_succ]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem phi_cons0 (v : HVar E) (z : E) (h : ∀ a : Fin v.n, v.mon a.succ = z) (q : Fin v.n → E) :
    v.phi ((0 : Fin (v.n + 1)).insertNth (α := fun _ => E) 0 q) = z * ∑ t, q t := by
  unfold HVar.phi HVar.sum
  simp only [hev_cons0, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← h t]
  unfold HVar.mon
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fin.val_succ]
  ring

/-- One round: the completion at (power 0, inverse 1), evaluated. -/
theorem fill_eval (v : HVar E) (z : E) (h : ∀ a : Fin v.n, v.mon a.succ = z) (σ : E)
    (q : Fin v.n → E) (x : E) :
    hev (hFill v ((0 : Fin (v.n + 1)), (1 : E)) σ q) x =
      (σ - z * (List.ofFn q).sum) + evalGo x 0 (List.ofFn q) := by
  unfold hFill
  rw [hev_split, hev_cons0, phi_cons0 v z h, evalGo_ofFn, List.sum_ofFn]
  simp only [Fin.val_zero, pow_zero, smul_eq_mul, one_mul, zero_add]
  exact add_comm _ _

/-! ### the variables' rounds -/

theorem runVars_nil (σ : E) (rs : Rounds E) : runVars σ [] rs = (σ, []) := by
  unfold runVars
  rfl

theorem runVars_cons (σ z : E) (zs : List E) (r : List E × List E) (rs : Rounds E) :
    runVars σ (z :: zs) (r :: rs) =
      ((runVars ((σ - z * r.1.sum) + evalGo (r.2.headD 0) 0 r.1) zs rs).1,
        r.2.headD 0 :: (runVars ((σ - z * r.1.sum) + evalGo (r.2.headD 0) 0 r.1) zs rs).2) := by
  rw [runVars]

theorem runVars_flat : ∀ (l : List (PFmt E)) (d : PDats l) (zs : List E), Wt l d zs →
    ∀ (σ : E) (t : Shape) (τ : Tr (sRounds l ++ t)) (rest : Rounds E),
    runVars σ zs (flS l t τ ++ rest) =
      ((vFinT l d (fix0 (pVars l d)) σ t τ).1.1, ppList l (vFinT l d (fix0 (pVars l d)) σ t τ).1.2)
  | [], _, _, h, σ, _, _, _ => by
    rw [show _ = [] from h]
    exact runVars_nil σ _
  | _ :: _, _, [], h, _, _, _, _ => h.elim
  | f :: l, d, z :: zs, h, σ, t, (m, c, τ), rest => by
    show runVars σ (z :: zs) ((List.ofFn m.2, [f.val c]) :: (flS l t τ ++ rest)) = _
    rw [runVars_cons]
    show ((runVars ((σ - z * (List.ofFn m.2).sum) + evalGo (f.val c) 0 (List.ofFn m.2)) zs
        (flS l t τ ++ rest)).1, f.val c :: (runVars ((σ - z * (List.ofFn m.2).sum) +
          evalGo (f.val c) 0 (List.ofFn m.2)) zs (flS l t τ ++ rest)).2) = _
    rw [← fill_eval (f.var d.1) z h.1 σ m.2 (f.val c), runVars_flat l d.2 zs h.2]
    rfl

theorem runVars_flat0 : ∀ (l : List (PFmt E)) (d : PDats l) (zs : List E), Wt l d zs →
    ∀ (σ : E) (τ : Tr (sRounds l)) (rest : Rounds E),
    runVars σ zs (flS0 l τ ++ rest) =
      ((vFin l d (fix0 (pVars l d)) σ τ).1, ppList l (vFin l d (fix0 (pVars l d)) σ τ).2)
  | [], _, _, h, σ, _, _ => by
    rw [show _ = [] from h]
    exact runVars_nil σ _
  | _ :: _, _, [], h, _, _, _ => h.elim
  | f :: l, d, z :: zs, h, σ, (m, c, τ), rest => by
    show runVars σ (z :: zs) ((List.ofFn m.2, [f.val c]) :: (flS0 l τ ++ rest)) = _
    rw [runVars_cons]
    show ((runVars ((σ - z * (List.ofFn m.2).sum) + evalGo (f.val c) 0 (List.ofFn m.2)) zs
        (flS0 l τ ++ rest)).1, f.val c :: (runVars ((σ - z * (List.ofFn m.2).sum) +
          evalGo (f.val c) 0 (List.ofFn m.2)) zs (flS0 l τ ++ rest)).2) = _
    rw [← fill_eval (f.var d.1) z h.1 σ m.2 (f.val c), runVars_flat0 l d.2 zs h.2]
    rfl

/-- the tail that the loop `vFinT` hands back is the transcript's own -/
theorem vFinT_tail : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E) (t : Shape)
    (τ : Tr (sRounds l ++ t)), (vFinT l d F σ t τ).2 = Tr.snd (s := sRounds l) τ
  | [], _, _, _, _, _ => rfl
  | f :: l, d, F, σ, t, (m, c, τ) =>
    vFinT_tail l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ

end

/-! ### a whole sumcheck -/
section
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E)

/-- A short sumcheck's transcript as plain data; sh: the order in which the shown values are listed.
-/
def flSc (sh : List Y.A) (τ : Tr (shapeS Y)) : Rounds E :=
  ([τ.1.2], [τ.2.1]) :: (flS Y.fmt [pRoundV E Y.A] τ.2.2 ++
    [(sh.map (Tr.snd (s := sRounds Y.fmt) (t := [pRoundV E Y.A]) τ.2.2).1.2, [])])

def flScC (τ : Tr (shapeSC Y)) : Rounds E := ([τ.1.2], [τ.2.1]) :: flS0 Y.fmt τ.2.2

theorem flSc_length (sh : List Y.A) (τ : Tr (shapeS Y)) :
    (flSc Y sh τ).length = 1 + Y.fmt.length + 1 := by
  unfold flSc
  rw [List.length_cons, List.length_append, flS_length]
  simp only [List.length_cons, List.length_nil]
  omega

theorem flScC_length (τ : Tr (shapeSC Y)) : (flScC Y τ).length = 1 + Y.fmt.length := by
  unfold flScC
  rw [List.length_cons, flS0_length]
  omega

/-- The sumcheck with the values' round: under Wt, takeSc on the plain data gives eps, pt, fin and
(in sh's order) vals of shortV at the pick F₀, and hands back rest. -/
theorem takeSc_flat (sh : List Y.A) (tg : E) (st : Y.St) (zs : List E) (h : Wt Y.fmt (Y.dat st) zs)
    (τ : Tr (shapeS Y)) (rest : Rounds E) :
    takeSc (flSc Y sh τ ++ rest) tg zs true =
      (⟨(shortV Y (F₀ Y) (tg, st) τ).eps, ppList Y.fmt (shortV Y (F₀ Y) (tg, st) τ).pt,
          (shortV Y (F₀ Y) (tg, st) τ).fin, sh.map (shortV Y (F₀ Y) (tg, st) τ).vals⟩, rest) := by
  have hl := h.length
  have hr := runVars_flat Y.fmt (Y.dat st) zs h (τ.1.2 + τ.2.1 * tg) [pRoundV E Y.A] τ.2.2
    ((sh.map (Tr.snd (s := sRounds Y.fmt) (t := [pRoundV E Y.A]) τ.2.2).1.2, []) :: rest)
  have hv := vFinT_tail Y.fmt (Y.dat st) (fix0 (pVars Y.fmt (Y.dat st))) (τ.1.2 + τ.2.1 * tg)
    [pRoundV E Y.A] τ.2.2
  have hlen := flS_length Y.fmt [pRoundV E Y.A] τ.2.2
  unfold takeSc flSc
  simp only [List.cons_append, List.append_assoc, List.nil_append, List.headD_cons, List.tail_cons,
    if_true]
  rw [hr]
  refine Prod.ext (congrArg (fun b : List E => (⟨τ.2.1, _, _, b⟩ : Sc E)) ?_) ?_
  · show ((_ :: _ : Rounds E).getD (1 + zs.length) ([], [])).1 = _
    rw [Nat.add_comm 1, List.getD_cons_succ, hl, ← hlen, List.getD_append_right _ _ _ _ (le_refl _),
      Nat.sub_self]
    show sh.map _ = sh.map _
    rw [← hv]
    rfl
  · show List.drop (1 + zs.length + 1) (([τ.1.2], [τ.2.1]) :: (flS Y.fmt [pRoundV E Y.A] τ.2.2 ++
      (sh.map (Tr.snd (s := sRounds Y.fmt) (t := [pRoundV E Y.A]) τ.2.2).1.2, []) :: rest)) = rest
    rw [show 1 + zs.length + 1 = (zs.length + 1) + 1 by omega, List.drop_succ_cons, hl, ← hlen]
    simp

/-- The sumcheck without the values' round: the same of shortVC; the list of values is empty. -/
theorem takeSc_flatC (tg : E) (st : Y.St) (zs : List E) (h : Wt Y.fmt (Y.dat st) zs)
    (τ : Tr (shapeSC Y)) (rest : Rounds E) :
    takeSc (flScC Y τ ++ rest) tg zs false =
      (⟨(shortVC Y (F₀ Y) (tg, st) τ).eps, ppList Y.fmt (shortVC Y (F₀ Y) (tg, st) τ).pt,
          (shortVC Y (F₀ Y) (tg, st) τ).fin, []⟩, rest) := by
  have hl := h.length
  have hr := runVars_flat0 Y.fmt (Y.dat st) zs h (τ.1.2 + τ.2.1 * tg) τ.2.2 rest
  have hlen := flS0_length Y.fmt τ.2.2
  unfold takeSc flScC
  simp only [List.cons_append, List.headD_cons, List.tail_cons, Bool.false_eq_true, if_false]
  rw [hr]
  refine Prod.ext rfl ?_
  show (_ :: _ : Rounds E).drop (1 + zs.length + 0) = rest
  rw [show 1 + zs.length + 0 = zs.length + 1 by omega, List.drop_succ_cons, hl, ← hlen]
  simp

/-! ### Wt at a lookup's lists of variables -/

theorem monS_eq (n : ℕ) (z : E) (a : Fin n) : ((pfCube E n).var (pdEq E n z)).mon a.succ = z := by
  show ∑ b : Bool, (if b then z else 1 - z) * (if b then (1 : E) else 0) ^ ((a.succ : Fin (n + 1)) :
      ℕ) = z
  rw [Fintype.sum_bool, Fin.val_succ]
  simp

theorem monS_dummy (D : ℕ) (a : Fin D) : ((pDummy E D).var (pDummyD E D)).mon a.succ = 0 := by
  show ∑ _s : Unit, (1 : E) * (0 : E) ^ ((a.succ : Fin (D + 1)) : ℕ) = 0
  rw [Fin.val_succ]
  simp

theorem wt_eqs (n : ℕ) : ∀ (k : ℕ) (z : Fin k → E),
    Wt (List.replicate k (pfCube E n)) (pdEqs E n k z) (List.ofFn z)
  | 0, _ => by simp [Wt]
  | k + 1, z => by
    rw [List.ofFn_succ]
    exact ⟨monS_eq n (z 0), wt_eqs n k fun i => z i.succ⟩

theorem wt_mix : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    Wt (pfMix E k dg) (pdMix E k dg z) (List.ofFn z)
  | 0, _, _ => by simp [Wt, pfMix]
  | k + 1, dg, z => by
    rw [List.ofFn_succ]
    exact ⟨monS_eq (dg 0) (z 0), wt_mix k (fun i => dg i.succ) fun i => z i.succ⟩

theorem wt_snoc_dummy (D : ℕ) : ∀ (l : List (PFmt E)) (d : PDats l) (zs : List E), Wt l d zs →
    Wt (l ++ [pDummy E D]) (PDats.snoc l d (pDummy E D) (pDummyD E D)) (zs ++ [0])
  | [], _, _, h => by
    rw [show _ = [] from h]
    exact ⟨monS_dummy D, rfl⟩
  | _ :: _, _, [], h => h.elim
  | _ :: l, d, _ :: zs, h => ⟨h.1, wt_snoc_dummy D l d.2 zs h.2⟩

end
end Tw
#print axioms Tw.fill_eval
#print axioms Tw.runVars_flat
#print axioms Tw.runVars_flat0
#print axioms Tw.takeSc_flat
#print axioms Tw.takeSc_flatC
#print axioms Tw.wt_eqs
#print axioms Tw.wt_mix
#print axioms Tw.wt_snoc_dummy
