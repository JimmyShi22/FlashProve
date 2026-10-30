-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVProofs.lean: the proofs of the statements of Cb/Ld/LdBattV.lean.
The proofs for a batching step of an interactive oracle proof: a random linear combination of linear
claims on one matrix, then a sumcheck over the columns with one more variable.

The proofs combine: the draw from Cb/Ld/LdBattKit.lean, the sumcheck with the dummy variable from
Cb/Ld/LdLineAt.lean (for each fixed tuple) and Cb/Ld/LdPscZkOur.lean (masked messages), the draw
before a masked block from Ior/MaskedDraw.lean.
The main theorems are `battV_goodAt`, `battV_mm` and `battV_goodM_sig`. What they state, under which
hypotheses, and the limits: the head of Cb/Ld/LdBattV.lean.
  `battV_goodAt`: the block at the base, for each fixed tuple of messages (`GoodAt`,
    Cb/Ld/LdSigLift.lean).
  `battV_mm`, `battV_goodM_sig`: see their statements.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
-/
import Cb.Ld.LdBattV
import Cb.Ld.LdBattProofs
import Cb.Ld.LdLineAt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Ten
variable {E J Rw : Type} [Field E] [Fintype Rw] {k : ℕ} (mAt : Rw × (Fin k → Bool) → J)

theorem tenCol_congr {m m' : J → E} (h : ∀ a, m (mAt a) = m' (mAt a)) (v : Rw → E) :
    tenCol mAt m v = tenCol mAt m' v :=
  funext fun b => Finset.sum_congr rfl fun r _ => by rw [h]

theorem tenAt_corner (v : Rw → E) (b : Fin k → Bool) (m : J → E) :
    tenAt mAt v (Alg.corner b) m = tenCol mAt m v b :=
  Alg.mle_corner _ _

theorem tenCol_comb {Q : Type} [Fintype Q] (m : J → E) (c : Q → E) (g : Q → Rw → E) :
    tenCol mAt m (fun r => ∑ q, c q * g q r) = fun b => ∑ q, c q * tenCol mAt m (g q) b := by
  funext b
  unfold tenCol
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

theorem tenAt_comb {Q : Type} [Fintype Q] (m : J → E) (c : Q → E) (g : Q → Rw → E) (z : Fin k → E) :
    tenAt mAt (fun r => ∑ q, c q * g q r) z m = ∑ q, c q * tenAt mAt (g q) z m := by
  unfold tenAt
  rw [tenCol_comb]
  unfold Alg.mle
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring

end Ten

/-- the product of the public polynomials, with one more variable at the end -/
theorem hPsi_snocV {E : Type} [Field E] :
    ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f)
        (X : HPt (pVars (l ++ [f]) (PDats.snoc l d f e))),
      hPsi (pVars (l ++ [f]) (PDats.snoc l d f e)) X =
        hPsi (pVars l d) (hInit l d f e X) * hev e.psi (hLast l d f e X)
  | [], _, _, e, X => by
      show hev e.psi X.1 * 1 = 1 * hev e.psi X.1
      ring
  | _ :: l, d, f, e, X => by
      show hev d.1.psi X.1 * hPsi (pVars (l ++ [f]) (PDats.snoc l d.2 f e)) X.2 =
        hev d.1.psi X.1 * hPsi (pVars l d.2) (hInit l d.2 f e X.2) * hev e.psi (hLast l d.2 f e X.2)
      rw [hPsi_snocV l d.2 f e X.2]
      ring

namespace BattVPar
variable {E : Type} [Field E] [Fintype E] (B : BattVPar E)

/-- there is no map that is not revealed -/
theorem sumE (f : B.our.B → E) : ∑ b, f b = 0 := by
  haveI : IsEmpty B.our.B := inferInstanceAs (IsEmpty Empty)
  exact Fintype.sum_empty f

theorem sum_eq (st : B.our.St) (m : B.J → E) (X : HPt (B.our.vars st)) :
    B.our.sum st m X = B.bmap st m (B.fn X) := by
  have h : B.our.sum st m X =
      B.bmap st m (B.fn X) + ∑ b, B.our.S1 st X (fun a => B.our.F st m a X) b * B.our.Fb st m b X :=
    rfl
  rw [h, B.sumE, add_zero]

theorem inc_eq (st : B.our.St) (m : B.J → E) :
    ∑ j, B.our.slS st j * m j = ∑ q, B.Z.ze st.2 q * ∑ j, B.slM q st.1 j * m j := by
  show ∑ j, (∑ q, B.Z.ze st.2 q * B.slM q st.1 j) * m j = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by ring

theorem sumAll_eq (st : B.our.St) (m : B.J → E) :
    hSumAll (B.our.vars st) (B.our.sum st m) =
      ∑ q, B.Z.ze st.2 q * tenForm B.mAt (B.g st.1 q) (B.cf st.1 q) m := by
  have h := psv_plains_sum E B.n B.k (B.our.sum st m)
  refine h.trans ?_
  have e : ∀ b : Fin B.k → Bool,
      B.our.sum st m (pH _ (pdPlains E B.n B.k) (ppOf (pfCube E B.n) B.k (Alg.corner b))) =
        ∑ q, B.Z.ze st.2 q * (B.cf st.1 q b * tenCol B.mAt m (B.g st.1 q) b) := by
    intro b
    rw [sum_eq]
    have hb : B.fn (pH _ (pdPlains E B.n B.k) (ppOf (pfCube E B.n) B.k (Alg.corner b))) =
        Alg.corner b :=
      psv_fn_pt E _ _ _ _
    rw [hb]
    unfold bmap
    exact Finset.sum_congr rfl fun q _ => by rw [Alg.mle_corner, tenAt_corner, mul_assoc]
  rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => by rw [← Finset.mul_sum]; rfl

theorem sumHolds_iff (x : (B.Q → E) × B.St) (ρ : B.Z.D) (m : B.J → E) :
    B.our.SumHolds (B.nx x ρ) m ↔ ∑ q, B.Z.ze ρ q * B.lhs x.2 q m = ∑ q, B.Z.ze ρ q * x.1 q := by
  show hSumAll (B.our.vars (x.2, ρ)) (B.our.sum (x.2, ρ) m) + ∑ j, B.our.slS (x.2, ρ) j * m j = _ ↔
    _
  rw [sumAll_eq, inc_eq, ← Finset.sum_add_distrib]
  have e : ∀ q, B.Z.ze ρ q * tenForm B.mAt (B.g x.2 q) (B.cf x.2 q) m +
        B.Z.ze ρ q * ∑ j, B.slM q x.2 j * m j =
      B.Z.ze ρ q * B.lhs x.2 q m := fun q => by
    unfold lhs
    ring
  rw [Finset.sum_congr rfl fun q _ => e q]
  exact Iff.rfl

/-- a form reads the entries at which it is not 0 -/
theorem form_congr {sl : B.J → E} {m m' : B.J → E} (h : ∀ j, sl j ≠ 0 → m j = m' j) :
    ∑ j, sl j * m j = ∑ j, sl j * m' j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : sl j = 0
  · rw [hj, zero_mul, zero_mul]
  · rw [h j hj]

/-- the left sides read the matrix and what the incoming forms read -/
theorem lhs_congr {st : B.St} {q : B.Q} {m m' : B.J → E} (h1 : ∀ a, m (B.mAt a) = m' (B.mAt a))
    (h2 : ∀ j, B.slM q st j ≠ 0 → m j = m' j) :
    B.lhs st q m = B.lhs st q m' := by
  unfold lhs tenForm
  rw [tenCol_congr B.mAt h1, B.form_congr h2]

theorem bmap_congr (st : B.St × B.Z.D) {m m' : B.J → E} (h : ∀ a, m (B.mAt a) = m' (B.mAt a)) :
    B.bmap st m = B.bmap st m' := by
  funext z
  unfold bmap tenAt
  exact Finset.sum_congr rfl fun q _ => by rw [tenCol_congr B.mAt h]

theorem bmap_deg (hn : 2 ≤ B.n) (st : B.St × B.Z.D) (m : B.J → E) :
    Alg.DegLE (fun _ => B.n) (B.bmap st m) := by
  show Alg.DegLE (fun _ => B.n) fun z =>
    ∑ q, B.Z.ze st.2 q * Alg.mle (B.cf st.1 q) z * Alg.mle (tenCol B.mAt m (B.g st.1 q)) z
  exact Alg.DegLE.sum _ fun q _ =>
    Alg.DegLE.mono
      (Alg.DegLE.mul (Alg.DegLE.const_mul _ (Alg.DegLE.mle (B.cf st.1 q)))
        (Alg.DegLE.mle (tenCol B.mAt m (B.g st.1 q)))) fun _ => hn

/-- the batched map at a point is a tensor form at that point -/
theorem bmap_ten (st : B.St × B.Z.D) (m : B.J → E) (z : Fin B.k → E) :
    B.bmap st m z =
      tenAt B.mAt (fun r => ∑ q, B.Z.ze st.2 q * Alg.mle (B.cf st.1 q) z * B.g st.1 q r) z m := by
  rw [tenAt_comb]
  rfl

end BattVPar

section Main
open IOR
variable (E : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem battV_at_point : Spec.battV_at_point E := fun _ _ _ _ _ _ _ _ => rfl

theorem battV_first : Spec.battV_first E := fun _ _ _ _ => rfl

theorem battV_sum : Spec.battV_sum E := fun B x ρ m => B.sumHolds_iff x ρ m

theorem battV_fwd : Spec.battV_fwd E := fun B x ρ m h =>
  (B.sumHolds_iff x ρ m).2 (Finset.sum_congr rfl fun q _ => by rw [h q])

theorem battV_cnt : Spec.battV_cnt E := by
  intro B hZ x m hx
  have hv : (fun q => B.lhs x.2 q m - x.1 q) ≠ 0 := fun h =>
    hx fun q => sub_eq_zero.1 (congrFun h q)
  refine le_trans (le_of_eq (cnt_congr fun ρ => ?_)) (hZ _ hv)
  rw [B.sumHolds_iff, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact Eq.congr (Finset.sum_congr rfl fun q _ => by ring) rfl

theorem battV_ok : Spec.battV_ok E := by
  intro B hn
  refine ⟨fun _ => psv_plains_ok E B.n B.k (by omega), fun st m u => ?_,
    fun st X v u r => ?_, fun f hf => ?_⟩
  · have e : (fun X : HPt (B.our.vars st) =>
      B.our.S0 st X (fun a => B.our.F st m a X + u a) +
        ∑ b, B.our.S1 st X (fun a => B.our.F st m a X + u a) b * B.our.Fb st m b X)
        = fun X => (fun z => B.bmap st m z + u ()) (B.fn X) := funext fun X => by
      rw [B.sumE, add_zero]
      rfl
    refine (congrArg (HDeg (B.our.vars st)) e).mpr ?_
    exact kit_deg E (pfCube E B.n) B.k (pdPlains E B.n B.k) (fun z => B.bmap st m z + u ())
      (Alg.DegLE.add (B.bmap_deg hn st m) (Alg.DegLE.const _ (u ())))
  · refine ⟨fun t => if t = 0 then v () else u (), fun y => ?_⟩
    rw [B.sumE, add_zero]
    show v () + u () * y = ∑ t : Fin 2, y ^ (t : ℕ) • (if t = 0 then v () else u ())
    rw [Fin.sum_univ_two]
    simp
    ring
  · rw [List.eq_of_mem_replicate hf]
    exact fun _ _ h => h

theorem battV_rows : Spec.battV_rows E := by
  intro B hn o m
  have h1 : hU (B.our.par.vars o.st) (B.our.par.W o.st m) (B.our.par.hp o.st o.pt) =
      ∑ i, hSl (B.our.par.vars o.st) (B.our.par.hp o.st o.pt) i *
        m (B.wAt (pIx (B.fmt ++ [pDummy E 1]) (B.our.datD o.st) i)) :=
    hide_form E E _ _ _
  have h2 : hPsi (B.our.par.vars o.st) (B.our.par.hp o.st o.pt) = ∏ i, B.outPt o i := by
    refine (hPsi_snocV B.fmt (pdPlains E B.n B.k) (pDummy E 1)
      (pDummyD E 1) (B.our.par.hp o.st o.pt)).trans ?_
    have hd : hev (pDummyD E 1).psi
          (hLast B.fmt (pdPlains E B.n B.k) (pDummy E 1) (pDummyD E 1) (B.our.par.hp o.st o.pt)) =
        1 := hev_const 1 _
    rw [hd, mul_one]
    exact kit_psi_plains E B.n B.k hn _
  have h3 : B.our.par.inc o.st m = ∑ q, B.chi o q * ∑ j, B.slM q (B.stOf o) j * m j :=
    B.inc_eq o.st m
  have hA : B.our.par.UHolds o m ↔ B.RowA o m := by
    show hU (B.our.par.vars o.st) (B.our.par.W o.st m) (B.our.par.hp o.st o.pt) +
          o.eps * hPsi (B.our.par.vars o.st) (B.our.par.hp o.st o.pt) * B.our.par.inc o.st m +
          o.eps * ∑ b, B.our.par.S1 o.st (B.our.par.hp o.st o.pt) o.vals b *
              B.our.par.Gb o.st m b (B.our.par.hp o.st o.pt) =
        o.fin - o.eps * o.vals () ↔
      _
    have hE : ∑ b, B.our.par.S1 o.st (B.our.par.hp o.st o.pt) o.vals b *
          B.our.par.Gb o.st m b (B.our.par.hp o.st o.pt) = 0 := B.sumE _
    rw [h1, h2, h3, hE, mul_zero, add_zero]
    exact Iff.rfl
  have hB : (∀ a, B.our.par.EHolds o m a) ↔ B.RowB o m := by
    refine ⟨fun h => ?_, fun h _ => ?_⟩
    · have h' : B.bmap o.st m (B.outPt o) + m B.cAt * B.beta o = o.vals () := h ()
      unfold BattVPar.RowB
      rw [B.bmap_ten] at h'
      rw [mul_comm (B.beta o)]
      exact h'
    · show B.bmap o.st m (B.outPt o) + m B.cAt * B.beta o = o.vals ()
      rw [B.bmap_ten, mul_comm (m B.cAt)]
      exact h
  exact and_congr hA hB

theorem battV_rowA_reads : Spec.battV_rowA_reads E := by
  intro B o m m' h1 h2
  have e1 : ∑ i, hSl (B.our.par.vars o.st) (B.our.par.hp o.st o.pt) i *
        m (B.wAt (pIx (B.fmt ++ [pDummy E 1]) (B.our.datD o.st) i)) =
      ∑ i, hSl (B.our.par.vars o.st) (B.our.par.hp o.st o.pt) i *
        m' (B.wAt (pIx (B.fmt ++ [pDummy E 1]) (B.our.datD o.st) i)) :=
    Finset.sum_congr rfl fun i _ => by rw [h1]
  have e2 : ∑ q, B.chi o q * ∑ j, B.slM q (B.stOf o) j * m j =
      ∑ q, B.chi o q * ∑ j, B.slM q (B.stOf o) j * m' j :=
    Finset.sum_congr rfl fun q _ => by rw [B.form_congr (h2 q)]
  unfold BattVPar.RowA
  rw [e1, e2]

theorem battV_rowA_off : Spec.battV_rowA_off E := by
  intro B Rd hO hF o m m' h
  refine battV_rowA_reads E B o m m' (fun i => h _ (fun a => hO.wM i a) (hO.wc i))
    fun q j hj => h j (fun a e => hj (e ▸ hF q _ a)) fun e => hj (e ▸ hO.cS q _)

theorem battV_rowB_reads : Spec.battV_rowB_reads E := by
  intro B o m m' h1 h2
  unfold BattVPar.RowB tenAt
  rw [tenCol_congr B.mAt h1, h2]

theorem battV_nz : Spec.battV_nz E := by
  intro B Ex x y τ o h
  obtain ⟨x₂, -, h2⟩ := Option.bind_eq_some_iff.1 ((seq_out _ _ x y τ).symm.trans h)
  obtain ⟨z, h3, h4⟩ := Option.bind_eq_some_iff.1
    ((seq_out (B.our.par.core Ex) (B.our.par.ends Ex) x₂ _ _).symm.trans h2)
  have h3' : B.our.par.outC x₂ (Tr.fst (Tr.snd (s := [drawRound B.Z.D]) τ)) = some z := h3
  have hz := psc_our_nz E B.our x₂ _ z h3'
  rw [← Option.some.inj h4]
  exact hz

open Classical in
theorem battV_pend : Spec.battV_pend E := by
  intro B o St' Q' _ g' pt' slM' Z' n' wAt' st' q' hg hp hs m
  show _ ↔ tenAt B.mAt (g' st' q') (pt' st' q') m + ∑ j, slM' q' st' j * m j = B.shown o
  rw [hg, hp]
  have e : ∑ j, slM' q' st' j * m j = B.beta o * m B.cAt := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hs j, ite_mul, zero_mul]]
    simp
  rw [e]
  exact Iff.rfl

theorem battV_own : Spec.battV_own E := by
  intro B Rd h
  have hF : ∀ (st : B.our.St) (m m' : B.J → E),
      (∀ a, m (B.mAt a) = m' (B.mAt a)) → B.our.F st m = B.our.F st m' := by
    intro st m m' hm
    funext _ X
    exact congrFun (B.bmap_congr st hm) _
  have hne : ∀ (i : B.WIx ⊕ Unit) a, Sum.elim B.wAt (fun _ : Unit => B.cAt) i ≠ B.mAt a := by
    rintro (i | _) a
    · exact h.wM i a
    · exact h.cM a
  exact
    { inj := by
        rintro (i | _) (j | _) e
        · exact congrArg Sum.inl (h.inj e)
        · exact absurd e (h.wc i)
        · exact absurd e.symm (h.wc j)
        · rfl
      own := by
        rintro (i | _)
        · exact h.own i
        · exact h.ownC
      rdF := fun st m m' hm => hF st m m' fun a => hm _ (h.rdM a)
      rdFb := fun _ _ _ _ => funext fun b => b.elim
      rdS := fun st j hj => Finset.sum_eq_zero fun q _ => by rw [h.rdS q st.1 j hj, mul_zero]
      oF := fun st m m' hm => hF st m m' fun a => hm _ fun i e => hne i a e.symm
      oFb := fun _ _ _ _ => funext fun b => b.elim
      oS := by
        rintro st (i | _)
        · exact Finset.sum_eq_zero fun q _ => by
            show B.Z.ze st.2 q * B.slM q st.1 (B.wAt i) = 0
            rw [h.wS q st.1 i, mul_zero]
        · exact Finset.sum_eq_zero fun q _ => by
            show B.Z.ze st.2 q * B.slM q st.1 B.cAt = 0
            rw [h.cS q st.1, mul_zero] }

theorem battV_two : Spec.battV_two E := by
  intro B Ex Wt msg Rd hi hwc M k
  have hat : Function.Injective (Sum.elim B.wAt fun _ : Unit => B.cAt) := by
    rintro (i | _) (j | _) e
    · exact congrArg Sum.inl (hi e)
    · exact absurd e (hwc i)
    · exact absurd e.symm (hwc j)
    · rfl
  have hc : Function.Injective fun _ : Unit => B.cAt := fun _ _ _ => rfl
  show Function.extend (Sum.elim B.wAt fun _ : Unit => B.cAt) (Sum.elim M.1 M.2) k = _
  funext j
  by_cases h1 : ∃ i, B.wAt i = j
  · obtain ⟨i, rfl⟩ := h1
    rw [hi.extend_apply]
    exact hat.extend_apply _ _ (Sum.inl i)
  · rw [Function.extend_apply' _ _ _ h1]
    by_cases h2 : B.cAt = j
    · subst h2
      rw [hc.extend_apply _ _ ()]
      exact hat.extend_apply _ _ (Sum.inr ())
    · have a1 : ¬ ∃ u : Unit, (fun _ : Unit => B.cAt) u = j := by
        rintro ⟨_, e⟩
        exact h2 e
      have a2 : ¬ ∃ i, (Sum.elim B.wAt fun _ : Unit => B.cAt) i = j := by
        rintro ⟨i | _, e⟩
        · exact h1 ⟨i, e⟩
        · exact h2 e
      rw [Function.extend_apply' _ _ _ a1, Function.extend_apply' _ _ _ a2]

theorem battV_join : Spec.battV_join E := by
  intro B Ex Wt msg Rd X hi hwc hW hC
  have hj := MaskFact.JCl.join (X := X) (B.J → E) (fun w => B.cut Rd (msg w)) (B.WIx → E)
    (Unit → E) (fun M k => Function.extend B.wAt M k)
    (fun M k => Function.extend (fun _ : Unit => B.cAt) M k) hW hC
  have hput : (B.maskData Ex msg Rd).put =
      fun M k => Function.extend B.wAt M.1 (Function.extend (fun _ : Unit => B.cAt) M.2 k) :=
    funext fun M => funext fun k => battV_two E B Ex Wt msg Rd hi hwc M k
  have he := @MaskFact.JCl.equiv Wt X _ ((B.WIx → E) × (Unit → E)) (B.maskData Ex msg Rd).finMk
    (B.maskData Ex msg Rd).neMk (Equiv.refl _) hj
  have key : (B.maskData Ex msg Rd).fact =
      @MaskFact.mk Wt (B.J → E) (fun w => B.cut Rd (msg w)) ((B.WIx → E) × (Unit → E))
        (B.maskData Ex msg Rd).finMk (B.maskData Ex msg Rd).neMk
        (fun M k => Function.extend B.wAt M.1 (Function.extend (fun _ : Unit => B.cAt) M.2 k)) :=
    congrArg (fun p =>
      @MaskFact.mk Wt (B.J → E) (fun w => B.cut Rd (msg w)) ((B.WIx → E) × (Unit → E))
        (B.maskData Ex msg Rd).finMk (B.maskData Ex msg Rd).neMk p) hput
  rw [key]
  exact he

/-- Under `hn` (1 ≤ `B.n`): the joint of the two rows is the sumcheck's own output joint. -/
theorem BattVPar.baseOut_eq {E : Type} [Field E] [Fintype E] (B : BattVPar E) (hn : 1 ≤ B.n)
    (Ex : ExtSpec) {Kc Wt : Type} (A0 : Rels Kc B.St Ex Wt) (msg : Wt → B.J → E) :
    B.baseOut Ex A0 msg = B.our.par.baseOut (A0.keepX B.Z.D) msg := by
  have hr : ∀ o m, (B.RowA o m ∧ B.RowB o m) = B.our.par.OutHolds o m := fun o m =>
    propext (battV_rows E B hn o m).symm
  unfold BattVPar.baseOut
  simp only [hr]
  rfl

theorem battV_goodAt : Spec.battV_goodAt E := by
  intro B Ex M Wp Kc A0 msg hn hZ
  obtain ⟨hV, hX, hY, hI⟩ := battV_ok E B hn
  rw [B.baseOut_eq (by omega) Ex A0 fun w => msg w.1]
  refine goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp (IOR.draw B.Z.D B.nx Ex) (B.our.par.psc Ex)
    _ _ _ (B.our.baseIn (A0.keepX B.Z.D) fun w => msg w.1) _ (fun _ _ _ wp => wp)
    (fun _ _ _ wp => wp) _ _ _ (goodAt_draw Kc M _ _ Ex Wp B.Z.D B.nx _ _ B.Z.err ?_ ?_ ?_ ?_)
    (psc_our_goodAt E B.our Ex M Wp Kc (A0.keepX B.Z.D) msg hV hX hY hI) fun _ _ _ _ _ _ _ => rfl
  · exact fun x y w β h => ⟨h.1, battV_fwd E B x β _ h.2⟩
  · exact fun x y β h => h
  · exact fun _ => rfl
  · intro x y m _
    by_cases hx : B.InHolds x (msg m)
    · refine le_trans (le_of_eq (cnt_false fun β hβ => ?_)) (Nat.zero_le _)
      obtain ⟨wp, h1, h2⟩ := hβ
      exact h2 ⟨h1.1, hx⟩
    · refine le_trans (cnt_mono fun β hβ => ?_) (battV_cnt E B hZ x (msg m) hx)
      obtain ⟨wp, h1, -⟩ := hβ
      exact h1.2

open Classical in
theorem battV_mm : Spec.battV_mm E := by
  intro B Ex Wt msg Rd hn hO
  obtain ⟨hV, hX, hY, -⟩ := battV_ok E B hn
  refine mm_draw_seq _ _ _ Ex Ex Wt Wt (B.our.par.psc Ex) (B.our.par.hon Ex msg)
    (B.our.par.maskData Ex msg (B.our.own Rd)) B.Z.D B.nx B.InHolds
    (psc_our_mm E B.our Ex Wt msg Rd hV (psc_our_deg E B.our hX hY) (battV_own E B Rd hO)) ?_ ?_
  · exact fun x k β h => (psc_our_sum E B.our (B.nx x β) k).2 (battV_fwd E B x β k h)
  · intro x k Mv h q
    rw [← h q]
    have hne : ∀ j, (∀ i, B.wAt i ≠ j) → B.cAt ≠ j →
        (B.our.par.maskData Ex msg (B.our.own Rd)).put Mv k j = k j := by
      intro j h1 h2
      refine Function.extend_apply' _ _ _ ?_
      rintro ⟨i | _, e⟩
      · exact h1 i e
      · exact h2 e
    exact B.lhs_congr (fun a => hne _ (fun i => hO.wM i a) (hO.cM a)) fun j hj =>
      hne j (fun i e => hj (e ▸ hO.wS q x.2 i)) fun e => hj (e ▸ hO.cS q x.2)

open Classical in
theorem battV_goodM_sig : Spec.battV_goodM_sig E := fun S B E₀ Wp Kc A0 msg Rd hn hZ hO =>
  { base := sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ (B.battV E₀) _ _ _ _ _
      (battV_goodAt E B E₀ S.Msg Wp Kc A0 msg hn hZ)
    mm := mm_mapW _ _ _ _ _ _ _ _ _ _ _ _ _
      (mm_keep _ _ _ _ _ _ _ _ _ S.Smp S.ext
        (battV_mm E B E₀ (S.Msg × Wp) (fun w => msg w.1) Rd hn hO))
    claim := fun x _ w h q => by
      show B.lhs x.1.2 q (fun j => if Rd j then msg (S.msgs w.1) j else 0) = x.1.1 q
      rw [← h.2.2.2 q]
      exact B.lhs_congr (fun a => if_pos (hO.rdM a)) fun j hj =>
        if_pos (by by_contra hr; exact hj (hO.rdS q x.1.2 j hr)) }

theorem battV_len : Spec.battV_len E := fun B Ex => by
  show ([IOR.drawRound B.Z.D] ++
      ((pRound0 E :: pRounds (B.fmt ++ [pDummy E 1])) ++ [pRoundV E Unit])).length = _
  simp [pRounds]

theorem battV_err : Spec.battV_err E := fun B Ex Kc =>
  ⟨rfl, by rw [List.map_append, List.map_replicate]; rfl, psc_our_card E 1⟩

theorem battV_own_card : Spec.battV_own_card E := fun B => by
  have h : Fintype.card B.WIx = B.k * B.n + 2 := by
    rw [psc_own_card E (B.fmt ++ [pDummy E 1]), List.map_append, List.map_replicate,
      List.sum_append, List.sum_replicate, smul_eq_mul]
    show 1 + (B.k * B.n + (1 + 0)) = _
    omega
  exact ⟨h, by rw [Fintype.card_sum, h, Fintype.card_unit]⟩

end Main
end Cb
