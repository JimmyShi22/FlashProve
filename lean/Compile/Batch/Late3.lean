-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Late3.lean: from the chains to the proof strings: `finishSlot`, `finishAll`, `proveB`
(Compile/Batch/Prover.lean) and their late forms (Compile/Batch/Mirror.lean) are related by
`Rom.Late`, under the hypotheses below (words of this library: lean/GLOSSARY.md; context, closure:
`Ctx`, `Clo`, Rom/DeferLate.lean).
With proof-of-work bits: the slot's one reveal also shows the chaining values of the attempts before
the final one (for them the context has nothing but closures without data: the last clause of
`FinHyp`), and so releases these attempts; `ctxB` is given the numbers of the final attempts that
the accumulators have noted. ("One reveal", in this sense: the `Step.reveal` in the body of
`finishSlot`; `openT`, `openE` are further ones.) One hypothesis on the protocol is added (`hRP`,
the clause `readsPut` of `GrFitP`, Compile/Batch/SpecFit.lean): the positions that the verifier
reads do not depend on the nonces. The prover opens the positions read at the plain parts with the
nonces written in (`putB`); the late form takes the symbols from the view of the interactive
protocol, which has those read at the plain parts as the interactive prover sends them.
-/
import Compile.Batch.Late2b
import Iop.ShapeKit

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Openings -/

theorem late_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (tr : TTree) (isRead : r.Pos → Bool) (depth : ℕ) {n : ℕ}
    {Γ : Cx lam K L} (hsym : ∀ p, isRead p = true → sym p = some (r.rd o p))
    (hK : OpenK Γ depth (bodyAt posAt emb o) tr)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, (∀ j ∈ js, j < 2 ^ depth) →
      Late (Same n Γ) n Γ (opensComp dec posAt o tr isRead f js)
        (opensCompL dec posAt sym zero emb tr isRead f js) := by
  intro js
  induction js with
  | nil => exact fun _ => Late.pure ⟨rfl, rfl, rfl⟩
  | cons j js ih =>
    intro hjs
    refine Late.bind (ih fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')) fun n' Γ' g g' hg => ?_
    obtain ⟨rfl, rfl, rfl⟩ := hg
    have hj := hjs j List.mem_cons_self
    cases hp : posAt j with
    | none => exact Late.pure ⟨rfl, rfl, rfl⟩
    | some p =>
      by_cases hr : isRead p = true
      · simp only [hr, if_true, hsym p hr, Option.getD_some]
        have hb : bodyAt posAt emb o j = emb p (r.rd o p) := by unfold bodyAt; rw [hp]
        refine Late.bind
          (late_openT tr j _ _ (by rw [← hb]; exact hK.salts j hj) fun u hu =>
            hK.digs u (sized_mem depth tr.levels j hK.sized hj u hu))
          fun n'' Γ'' x y hxy => ?_
        obtain ⟨rfl, rfl, rfl⟩ := hxy
        exact Late.pure ⟨rfl, rfl, rfl⟩
      · simp only [hr, Bool.false_eq_true, if_false]
        exact Late.pure ⟨rfl, rfl, rfl⟩

theorem late_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (tr : Option TTree) (isRead : r.Pos → Bool) {n : ℕ}
    {Γ : Cx lam K L} (hsym : ∀ p, isRead p = true → sym p = some (r.rd o p))
    (hK : ∀ tr', tr = some tr' → OpenK Γ depth (bodyAt posAt emb o) tr')
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Late (Same n Γ) n Γ (opensOpt dec posAt depth o tr isRead f)
      (opensOptL dec posAt depth sym zero emb tr isRead f) := by
  cases tr with
  | none => exact Late.pure ⟨rfl, rfl, rfl⟩
  | some tr' =>
    exact late_opensComp dec posAt o sym zero emb tr' isRead depth hsym (hK tr' rfl)
      f _ fun j hj => List.mem_range.1 hj

/-- The openings in a component with a list of trees, from tree number k on, under two hypotheses:
the late form is given the symbols at the positions read (`hsym`); the context knows each tree that
is opened (`OpensK`, Compile/Batch/Late2.lean, at the leaves `bodyAt (posAt j) emb o` of tree number
j). Both programs stop where the depths or the trees end, and so does `OpensK`. -/
theorem late_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool) {n : ℕ} {Γ : Cx lam K L}
    (hsym : ∀ p, isRead p = true → sym p = some (r.rd o p)) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree),
      OpensK Γ (fun j => bodyAt (posAt j) emb o) k ds trs →
      ∀ f : (p : r.Pos) → Option (Opening lam (r.Sym p)),
        Late (Same n Γ) n Γ (opensTrees dec posAt o isRead k ds trs f)
          (opensTreesL dec posAt sym zero emb isRead k ds trs f)
  | _, [], _, _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | _, _ :: _, [], _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | k, d :: ds, tr :: trs, hK, f =>
    Late.bind (late_opensTrees dec posAt o sym zero emb isRead hsym (k + 1) ds trs hK.2 f)
      fun n' Γ' g g' hg => by
        obtain ⟨rfl, rfl, rfl⟩ := hg
        exact late_opensComp dec (posAt k) o sym zero emb tr isRead d hsym hK.1 g _
          fun j hj => List.mem_range.1 hj

theorem late_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (orc : (p : OPos s) → Option (OSym s p)) (emb : (p : OPos s) → OSym s p → Body L)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool) (n : ℕ) (Γ : Cx lam K L),
      (∀ p, isRead p = true → orc p = some (τ.read p)) → TreesKB Γ s A W emb τ tjs t0s →
      Late (Same n Γ) n Γ (opensB s A W τ tjs t0s isRead) (opensBL s A W orc emb tjs t0s isRead)
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | _ :: s, (_, A), (w, W), (m, _, τ), orc, emb, tjs, t0s, isRead, n, Γ, hsym, hK => by
      refine Late.bind
        (late_opensOpt w.pt.decPos w.posAt0 w.depth0 m.1 (fun p => orc (.inl p)) w.pt.zero
          (fun p => emb (.inl p)) (t0s.headD none) (fun p => isRead (.inl p))
          (fun p hp => hsym (.inl p) hp) hK.1 _)
        fun n' Γ' f0 f0' h0 => ?_
      obtain ⟨rfl, rfl, rfl⟩ := h0
      refine Late.bind
        (late_opensOpt w.pt.decPos w.posAtJ w.depthJ m.1 (fun p => orc (.inl p)) w.pt.zero
          (fun p => emb (.inl p)) (tjs.headD none) (fun p => isRead (.inl p))
          (fun p hp => hsym (.inl p) hp) hK.2.1 _)
        fun n'' Γ'' f f' h1 => ?_
      obtain ⟨rfl, rfl, rfl⟩ := h1
      refine Late.bind
        (late_opensB s A W τ (fun p => orc (.inr p)) (fun p => emb (.inr p)) tjs.tail t0s.tail
          (fun p => isRead (.inr p)) _ _ (fun p hp => hsym (.inr p) hp) hK.2.2)
        fun n3 Γ3 g g' h2 => ?_
      obtain ⟨rfl, rfl, rfl⟩ := h2
      exact Late.pure ⟨rfl, rfl, rfl⟩

theorem late_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str) (ans : E.Pos → Option E.Sym)
    (embE : E.Sym → Body L) (trees : List (TreeH lam)) (isRead : E.Pos → Bool) {n : ℕ}
    {Γ : Cx lam K L} (hans : ∀ p, isRead p = true → ans p = some (E.rd y p))
    (hk : ∀ p s d, (trees.getD (we.which p) ⟨[], []⟩).salts.getD (we.leaf p) none = some (s, d) →
      KSalt Γ (embE (E.rd y p)) s ∧ Base Γ d) :
    ∀ ps, Late (Same n Γ) n Γ (opensExtB we y trees isRead ps)
      (opensExtBL we ans embE trees isRead ps) := by
  intro ps
  induction ps with
  | nil => exact Late.pure ⟨rfl, rfl, rfl⟩
  | cons p ps ih =>
    refine Late.bind ih fun n' Γ' f g hfg => ?_
    obtain ⟨rfl, rfl, rfl⟩ := hfg
    by_cases hr : isRead p = true
    · simp only [hr, if_true, hans p hr]
      refine Late.bind (late_openE _ _ _ _ fun s d hs => hk p s d hs) fun n'' Γ'' x y' hxy => ?_
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      exact Late.pure ⟨rfl, rfl, rfl⟩
    · simp only [hr, Bool.false_eq_true, if_false]
      exact Late.pure ⟨rfl, rfl, rfl⟩

/-! ## The proof string of one slot -/

theorem roots_base (Γ : Cx lam K L) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
        (τ : Tr s) (tjs t0s : List (Option TTree)),
      TreesKB Γ s A W emb τ tjs t0s → ∀ u ∈ rootToks tjs t0s, Base Γ u
  | [], _, _, _, _, _, _, h, u, hu => by
      obtain ⟨rfl, rfl⟩ := h
      simp [rootToks] at hu
  | _ :: _, (_, _), (_, _), _, (_, _, _), [], _, _, u, hu => by simp [rootToks] at hu
  | _ :: _, (_, _), (_, _), _, (_, _, _), _ :: _, [], _, u, hu => by simp [rootToks] at hu
  | _ :: s, (_, A), (w, W), emb, (m, _, τ), tj :: tjs, t0 :: t0s, h, u, hu => by
      simp only [rootToks, List.mem_append] at hu
      rcases hu with (hu | hu) | hu
      · cases tj with
        | none => simp at hu
        | some tr =>
          have e : u = tr.root := by simpa using hu
          rw [e]
          exact (h.2.1 tr rfl).digs _ (sized_root _ _ (h.2.1 tr rfl).sized)
      · cases t0 with
        | none => simp at hu
        | some tr =>
          have e : u = tr.root := by simpa using hu
          rw [e]
          exact (h.1 tr rfl).digs _ (sized_root _ _ (h.1 tr rfl).sized)
      · exact roots_base Γ s A W _ τ tjs t0s h.2.2 u hu

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

theorem late_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) {n n₀ : ℕ} {Γ : Cx lam K L}
    (hne : acc.toks ≠ [])
    (h1 : ∀ u ∈ acc.toks ++ ((a0.req.map TTree.root).toList ++ a0.toks),
      Cov Γ u (ctxB t (trees.map TreeH.root) (xin x) Q.loc.shape Q.ann wq.sh embP 0 .first acc.toks
          ((a0.req.map TTree.root).toList ++ a0.toks) acc.nons.reverse a0.nons.reverse
        ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains baseC))
    (h3 : TreesKB Γ Q.loc.shape Q.ann wq.sh embS
      ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1
      acc.trees a0.trees)
    (h4 : ∀ rq, a0.req = some rq → ReqK Γ n₀ depthReq rq ∧ j < 2 ^ depthReq)
    (h5 : ∀ u ∈ acc.dead ++ a0.dead, Base Γ u)
    (hRP : ∀ x ρ pl ph nJ n0,
      Q.loc.reads x ρ (putB Q.loc.shape Q.ann wq.sh ph nJ n0 pl) = Q.loc.reads x ρ pl)
    (hExt : ∀ p s d, (trees.getD (wq.ext.which p) ⟨[], []⟩).salts.getD (wq.ext.leaf p) none =
        some (s, d) →
      KSalt Γ (embE (E.rd (H.ext w) p)) s ∧ Base Γ d) :
    Late (Same n Γ) n Γ (finishSlot Q H wq wp trees w c0 a0 j x cj acc)
      (haveI := wp.decW w x (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)
       if rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x then pure none
       else finishBL t Q wq embS embP xin embE trees x (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)
         (Q.loc.dview x (H.ext w)
             ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1)
           a0 j acc) := by
  unfold finishSlot
  by_cases hw : rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x
  · simp only [if_pos hw]
    exact Late.pure ⟨rfl, rfl, rfl⟩
  · simp only [if_neg hw]
    unfold finishBL
    have hbase : ∀ u, Base Γ u →
        Cov Γ u (ctxB t (trees.map TreeH.root) (xin x) Q.loc.shape Q.ann wq.sh embP 0 .first
            acc.toks ((a0.req.map TTree.root).toList ++ a0.toks) acc.nons.reverse a0.nons.reverse
            ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains
            baseC) :=
      fun u h => Base.cov h (baseUp_ctxB t _ _ _ _ _ _ _ _ _ _ _ _ _ _ u (baseUp_base u))
    have hreqT : ∀ u,
        (u ∈ (a0.req.map fun rq => pathOf rq.levels j).getD [] ∨
          u ∈ (a0.req.map fun rq => ancOf rq.levels j).getD []) →
        Cov Γ u (ctxB t (trees.map TreeH.root) (xin x) Q.loc.shape Q.ann wq.sh embP 0 .first
            acc.toks ((a0.req.map TTree.root).toList ++ a0.toks) acc.nons.reverse a0.nons.reverse
            ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains
            baseC) := by
      intro u hu
      cases hq : a0.req with
      | none => rw [hq] at hu; simp at hu
      | some rq =>
        rw [hq] at hu
        obtain ⟨hRK, hj⟩ := h4 rq hq
        have hmem : u ∈ rq.levels.flatten :=
          sized_mem depthReq rq.levels j hRK.1 hj u (List.mem_append.2 (by simpa using hu))
        by_cases hur : u = rq.root
        · rw [← hq]
          exact h1 u
            (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl (by rw [hq, hur]; simp)))))
        · rw [← hq]
          exact hbase u (hRK.2.2 u hmem hur)
    refine Late.reveal (fun u hu => ?_) fun vs => ?_
    · simp only [List.mem_cons, List.mem_append] at hu
      rcases hu with hu | (((((hu | hu) | hu) | hu) | hu) | hu) | hu
      · rw [hu]
        refine h1 _ (List.mem_append.2 (Or.inl ?_))
        cases hl : acc.toks with
        | nil => exact absurd hl hne
        | cons b l => simp
      · exact hbase u (roots_base Γ _ _ _ _ _ _ _ h3 u hu)
      · exact hreqT u (Or.inl hu)
      · exact h1 u (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hu))))
      · exact hreqT u (Or.inr hu)
      · exact h1 u (List.mem_append.2 (Or.inl hu))
      · exact h1 u (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr hu))))
      · exact hbase u (h5 u (List.mem_append.2 hu))
    · refine Late.bind (late_opensB _ _ _ _ _ embS _ _ _ n Γ (fun p hp => ?_) h3)
        fun n' Γ' f f' hf => ?_
      · have hp' := @of_decide_eq_true _ (@Finset.decidableMem _ wq.decO _ _) hp
        rw [hRP] at hp'
        simp only [InteractiveOracleProof.dview]
        rw [if_pos (Or.inl (by rw [Strat.rho_run]; exact hp'))]
      obtain ⟨rfl, rfl, rfl⟩ := hf
      refine Late.bind (late_opensExtB wq.ext (H.ext w) _ embE trees _ (fun p hp => ?_) hExt _)
        fun n'' Γ'' g g' hg => ?_
      · have hp' := @of_decide_eq_true _ (@Finset.decidableMem _ wq.ext.dec _ _) hp
        simp only [InteractiveOracleProof.dview, InteractiveOracleProof.extAns]
        rw [if_pos (by rw [Strat.rho_run]; exact hp')]
      obtain ⟨rfl, rfl, rfl⟩ := hg
      exact Late.pure ⟨rfl, rfl, rfl⟩

end Prove

section Prove2
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- what `late_finishSlot` asks of a slot's accumulator (`hne`, `h1`, `h3`, `h5`) -/
def FinHyp (Γ : Cx lam K L) (c0 : H.Coin0) (a0 : Acc0)
    (acc : SlotAcc lam K (Y × H.Coin)) (x : Y) (cj : H.Coin) : Prop :=
  acc.toks ≠ [] ∧
  (∀ u ∈ acc.toks ++ ((a0.req.map TTree.root).toList ++ a0.toks),
    Cov Γ u (ctxB t (trees.map TreeH.root) (xin x) Q.loc.shape Q.ann wq.sh embP 0 .first acc.toks
        ((a0.req.map TTree.root).toList ++ a0.toks) acc.nons.reverse a0.nons.reverse
        ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains
        baseC)) ∧
  TreesKB Γ Q.loc.shape Q.ann wq.sh embS
    ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1
    acc.trees a0.trees ∧
  ∀ u ∈ acc.dead ++ a0.dead, Base Γ u

theorem late_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) {n n₀ : ℕ} {Γ : Cx lam K L}
    (hreq : ∀ rq, a0.req = some rq → ReqK Γ n₀ depthReq rq)
    (hRP : ∀ x ρ pl ph nJ n0,
      Q.loc.reads x ρ (putB Q.loc.shape Q.ann wq.sh ph nJ n0 pl) = Q.loc.reads x ρ pl)
    (hExt : ∀ p s d, (trees.getD (wq.ext.which p) ⟨[], []⟩).salts.getD (wq.ext.leaf p) none =
        some (s, d) →
      KSalt Γ (embE (E.rd (H.ext w) p)) s ∧ Base Γ d) :
    ∀ (accs : List (SlotAcc lam K (Y × H.Coin))) (j : ℕ), j + accs.length ≤ 2 ^ depthReq →
      (∀ acc ∈ accs,
        ∀ x cj, acc.x = some (x, cj) → FinHyp t Q H wq embS embP xin trees w Γ c0 a0 acc x cj) →
      Late (Same n Γ) n Γ (finishAll Q H wq wp trees w fl c0 a0 j accs)
        (finishAllL t Q H wq wp embS embP xin embE trees w fl c0 a0 j accs)
  | [], _, _, _ => Late.pure ⟨rfl, rfl, rfl⟩
  | acc :: accs, j, hj, hall => by
      have hj' : j + (accs.length + 1) ≤ 2 ^ depthReq := hj
      refine Late.bind (post := Same n Γ) ?_ fun n' Γ' π π' hπ => ?_
      · cases hx : acc.x with
        | none => exact Late.pure ⟨rfl, rfl, rfl⟩
        | some xc =>
          obtain ⟨x, cj⟩ := xc
          by_cases hf : fl j = true
          · simp only [hf, if_true]
            obtain ⟨g1, g2, g3, g4⟩ := hall acc List.mem_cons_self x cj hx
            exact late_finishSlot t Q H wq wp embS embP xin embE depthReq trees w c0 a0 j x cj acc
              g1 g2 g3 (fun rq hq => ⟨hreq rq hq, by omega⟩) g4 hRP hExt
          · simp only [hf, Bool.false_eq_true, if_false]
            exact Late.pure ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl, rfl⟩ := hπ
        refine Late.bind
          (late_finishAll fl c0 a0 hreq hRP hExt accs (j + 1) (by omega) fun a' ha' =>
            hall a' (List.mem_cons_of_mem _ ha'))
          fun n'' Γ'' r r' hr => ?_
        obtain ⟨rfl, rfl, rfl⟩ := hr
        exact Late.pure ⟨rfl, rfl, rfl⟩

/-- a slot at the start -/
def slot0 (c0 : H.Coin0) (x : Option Y) (cj : H.Coin) (salt : ℕ) :
    SlotSt lam K (Y × H.Coin) Q.loc.shape :=
  (match x with
    | some x => H.one.strat w x (c0, cj)
    | none => Strat.dflt Q.loc.shape (), ⟨x.map fun x => (x, cj), salt, 0, [], [], [salt], [], []⟩)

theorem late_eachInit (c0 : H.Coin0) :
    ∀ (xs : List (Option Y)) (n : ℕ) (Γ : Cx lam K L), Late
      (fun n' Γ' zs ys =>
        ys = zs.map (fun z => ((none : Option (Rho Q.loc.shape)), z.2)) ∧
        n ≤ n' ∧ Γ' = Γ ∧
        (zs.map fun z => z.2.tk).Pairwise (fun u v : ℕ => u < v) ∧
        (∀ z ∈ zs, n ≤ z.2.tk ∧ n' > z.2.tk) ∧
        List.Forall₂ (fun x z => ∃ (cj : H.Coin) (salt : ℕ), z = slot0 Q H w c0 x cj salt) xs zs)
      n Γ (eachM (initSlot sFS Q H wp w c0) xs) (eachL (initL sFS Q H wp) xs)
  | [], n, Γ =>
    Late.pure
      ⟨rfl, le_rfl, rfl, List.Pairwise.nil, fun z hz => absurd hz (by simp), List.Forall₂.nil⟩
  | x :: xs, n, Γ => by
      refine Late.sample fun rc => Late.fresh fun salt hs => ?_
      refine Late.bind (late_eachInit c0 xs (salt + 1) Γ) fun n' Γ' zs ys h => Late.pure ?_
      obtain ⟨rfl, a1, rfl, hpw, hb, hall⟩ := h
      refine ⟨rfl, by omega, rfl, ?_, fun z hz => ?_,
        List.Forall₂.cons ⟨wp.coin.e rc, salt, rfl⟩ hall⟩
      · rw [List.map_cons, List.pairwise_cons]
        refine ⟨fun v hv => ?_, hpw⟩
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self salt) (hb z hz).1
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨hs, by show n' > salt; omega⟩
        · exact ⟨by have := (hb z hz).1; omega, (hb z hz).2⟩

end Prove2

theorem forall₂_left_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, b, hb => absurd hb (by simp)
  | _, _, .cons h t, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨a, ha, hr⟩ := forall₂_left_of_mem t b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

section Prove3
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- Under the hypotheses below, one execution of the compiled prover and its late form are related.
Below the bound the context gets nothing but closures without data. -/
theorem late_proveB (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh) (hA : Q.ann.Coherent)
    (hRP : ∀ x ρ pl ph nJ n0,
      Q.loc.reads x ρ (putB Q.loc.shape Q.ann wq.sh ph nJ n0 pl) = Q.loc.reads x ρ pl)
    (fl : ℕ → Bool) (xs : List (Option Y)) {n : ℕ} {Γ : Cx lam K L} (hF : Fut n Γ)
    (hlen : HasSh Q.loc.shape Q.ann → xs.length = 2 ^ depthReq) (hle : xs.length ≤ 2 ^ depthReq)
    (hExt : ∀ p s d, (trees.getD (wq.ext.which p) ⟨[], []⟩).salts.getD (wq.ext.leaf p) none =
        some (s, d) →
      KSalt Γ (embE (E.rd (H.ext w) p)) s ∧ Base Γ d ∧ n > s ∧ n > d) :
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ') n Γ
      (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      (proveBL sMT sFS t Q H wq wp embS embP xin embE depthReq trees w fl xs) := by
  refine Late.sample fun rc0 => ?_
  refine Late.bind (late_eachInit sFS Q H wp w (wp.coin0.e rc0) xs n Γ) fun n1 Γ1 zs ys h1 => ?_
  obtain ⟨rfl, a1, rfl, hpw, hb, hall0⟩ := h1
  have hactE : actL .first zs = zs.map fun z => z.2.tk := by simp [actL, curOf]
  refine Late.bind
    (late_chainT sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq _ _ _ hW hA
      embS embP 0 .first (H.strat0 w (wp.coin0.e rc0)) zs ⟨[], [], none, [], []⟩ n1 Γ1 (hF.mono a1)
      (by rw [hactE]; exact hpw) (fun a' ha' => ?_)
      (fun h => by rw [← hall0.length_eq]; exact hlen h) (fun _ => rfl))
    fun n2 Γ2 out out' h2 => ?_
  · rw [hactE] at ha'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha'
    exact ⟨(hb z hz).2, cov_of_none fun o => hF _ (hb z hz).1 o⟩
  obtain ⟨e0, b1, hF2, hFr, new0, ntr0, nN0, nD0, e1, e2, hn0, e3, e4, hD0, hrq, hallK⟩ := h2
  rw [e0]
  obtain rfl : new0 = out.2.toks := by simpa using e1.symm
  obtain rfl : ntr0 = out.2.trees := by simpa using e2.symm
  obtain rfl : nN0 = out.2.nons.reverse := by rw [e3]; simp
  obtain rfl : nD0 = out.2.dead := by simpa using e4.symm
  have hE : Ext n Γ1 Γ2 := fun u hu => hFr u (by omega) fun hm => by
    rw [hactE] at hm
    obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
    have h3 : n ≤ u := e ▸ (hb z hz).1
    omega
  refine Late.mono
    (late_finishAll t Q H wq wp embS embP xin embE depthReq trees w fl (wp.coin0.e rc0) out.2
      (n := n2) (n₀ := n1) (Γ := Γ2) hrq hRP
      (fun p s d h =>
        ⟨(hExt p s d h).1.ext hE (hExt p s d h).2.2.1,
          (hExt p s d h).2.1.ext hE (hExt p s d h).2.2.2⟩)
      out.1 0 (by rw [Nat.zero_add, ← hallK.length_eq, ← hall0.length_eq]; exact hle)
      fun acc hacc x cj hx => ?_)
    fun n' Γ' a b hab =>
      ⟨hab.1, by rw [hab.2.1]; omega,
        by rw [hab.2.1, hab.2.2]; exact hF2, by rw [hab.2.2]; exact hE⟩
  obtain ⟨z, hz, hS⟩ := forall₂_left_of_mem hallK acc hacc
  obtain ⟨xo, -, cj', salt, rfl⟩ := forall₂_left_of_mem hall0 z hz
  obtain ⟨nb, ntr, new, nN, nD, x1, x2, x3, x4, hnew, x5, x6, hnD, C1, C23⟩ := hS
  have hxo : xo.map (fun x => (x, cj')) = some (x, cj) := x1.symm.trans hx
  obtain ⟨rfl, rfl⟩ : xo = some x ∧ cj' = cj := by
    cases xo with
    | none => simp at hxo
    | some x' =>
      have := Option.some.inj hxo
      exact ⟨by rw [(Prod.mk.inj this).1], (Prod.mk.inj this).2⟩
  obtain rfl : nb = acc.blocks := by simpa [slot0] using x2.symm
  obtain rfl : ntr = acc.trees := by simpa [slot0] using x3.symm
  obtain rfl : nN = acc.nons.reverse := by rw [x5]; simp [slot0]
  obtain rfl : nD = acc.dead := by simpa [slot0] using x6.symm
  have ht : salt :: new = acc.toks := x4.symm
  have D1 := C1 baseC (fun u => baseUp_base u)
  obtain ⟨D2, D3⟩ := C23 (H.strat w (wp.coin0.e rc0) x cj') rfl
  have D2' := D2 baseC (fun u => baseUp_base u)
  have hcur : curOf .first
        (slot0 (lam := lam) (K := K) Q H w (wp.coin0.e rc0) (some x) cj' salt).2 = salt := rfl
  rw [hcur, ht] at D1 D2'
  refine ⟨by rw [← ht]; simp, fun u hu => ?_, D3, fun u hu => ?_⟩
  · rcases List.mem_append.1 hu with h | h
    · exact D1 u h
    · exact D2' u h
  · rcases List.mem_append.1 hu with h | h
    · exact (hnD u h).2
    · exact (hD0 u h).2

end Prove3

end Compile.Batch
