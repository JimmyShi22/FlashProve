-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HeadSkel.lean: THE SKELETON OF THE OUTPUT HEAD's LIST OF TABLES IS A
TERM OFF PUBLIC
NUMBERS. The text that makes the head's tables (`tables`, Johnson/Desc/K8/ReadsQuiet.lean) folds
fifteen
asks, each with weights that come of what was heard; `tabsOfPlan h hp`
(Johnson/Desc/Kinds/Law/TablesPlanCode.lean) folds the same fifteen with no weights: "a function of
public numbers". HERE: wherever the text returns, `tabsOfPlan` returns, and the two lists have one
skeleton (`shapesOf`: matrix, rows in a block, first entry), every table on the third vector. Then
to the states. Statements and proofs.

  `parts_skel`, `added_skel`, `fold_skel`: adding a table, and a list of tables: whether it can be
added,
    where the next begins, AND THE SKELETON hang on no weight; the new tables lie on the third
    vector.
  `tables_skel`: **tables h L hp cov x = .ok tt ⊢ ∃ t0, tabsOfPlan h hp = some t0 ∧ shapesOf tt.funs
=
    shapesOf t0.funs ∧ every table of tt on the third vector.**
  `quietHead_skel`: so behind a yes of the head's quiet step (`ReadsQuiet.head P`).
  `headSkel_at_reads`: **at every state reached at 343 (behind the sending of the reads at the
head's
    segment): ∃ funs t0, s.funs? = some funs ∧ tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 ∧ shapesOf
    funs = shapesOf t0.funs ∧ every table on the third vector.**
  `headSkel_at_batch`: **the same at every state reached at 347, in front of the head's batching**
(by
    `funs_from_reads_head`, FunsAtBatch.lean).
  `reads_length_head`: so the number of reads there (`reads_length`, ReadsLenOfSkel.lean).
Limits. Nothing on the weights. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.ReadsLenOfSkel
import Johnson.Desc.Kinds.Law.TablesPlanCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Head (Shape HL HPlanH2 Tables Covered Heard)
open OnBytes.Tie.Pv.Tail.Port (readsList)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription need named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (skeleton tabsOfPlan)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- Two lists of tables with one skeleton, all on the third vector, and one next free entry. -/
def SkelAlike (s s' : Array HFun × ℕ) : Prop :=
  s.2 = s'.2 ∧ shapesOf s.1 = shapesOf s'.1 ∧ ∀ Fn ∈ s.1.toList, Fn.tree = 2

theorem shapesOf_push (A : Array HFun) (Fn : HFun) :
    shapesOf (A.push Fn) = shapesOf A ++ [(⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)] := by
  unfold shapesOf
  simp

/-- The parts of one table. -/
theorem parts_skel (mats : Array TMat) (M0 Lf : ℕ) (phi phi' : Array E) :
    ∀ (l : List ℕ) (s s' : Array HFun × ℕ), SkelAlike s s' →
      SkelAlike
        (l.foldl (fun (s : Array HFun × ℕ) q =>
          (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
            s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s)
        (l.foldl (fun (s : Array HFun × ℕ) q =>
          (s.1.push { mat := M0 + q, len := Lf, phi := phi', tree := 2, start := s.2 },
            s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s')
  | [], _, _, h => h
  | q :: l, s, s', h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine parts_skel mats M0 Lf phi phi' l _ _ ⟨?_, ?_, ?_⟩
    · show s.2 + _ = s'.2 + _
      rw [h.1]
    · show shapesOf (s.1.push _) = shapesOf (s'.1.push _)
      rw [shapesOf_push, shapesOf_push, h.2.1, h.1]
    · intro Fn hFn
      have hFn' : Fn ∈ (s.1.push
          { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 }).toList := hFn
      rw [Array.toList_push, List.mem_append] at hFn'
      rcases hFn' with k | k
      · exact h.2.2 Fn k
      · rw [List.mem_singleton.1 k]

/-- One table more. -/
theorem added_skel (mats : Array TMat) (t t' u : Tables) (M0 parts Lf : ℕ) (phi phi' : Array E)
    (nm : String) (hA : SkelAlike (t.funs, t.p) (t'.funs, t'.p))
    (h : Own.tableAdded mats t M0 parts Lf phi nm = some u) :
    ∃ u', Own.tableAdded mats t' M0 parts Lf phi' nm = some u' ∧
      SkelAlike (u.funs, u.p) (u'.funs, u'.p) := by
  have K := parts_skel mats M0 Lf phi phi' (List.range parts) _ _ hA
  unfold Own.tableAdded at h ⊢
  dsimp only at h ⊢
  have hp : t.p = t'.p := hA.1
  split at h
  · exact nomatch h
  · rename_i hne
    obtain rfl := Option.some.inj h
    rw [if_neg (by rw [← K.1, ← hp]; exact hne)]
    exact ⟨_, rfl, K⟩

/-- A list of tables. -/
theorem fold_skel (mats : Array TMat) :
    ∀ (asks : List (ℕ × ℕ × ℕ × Array E × String)) (t t' u : Tables),
      SkelAlike (t.funs, t.p) (t'.funs, t'.p) →
      asks.foldlM (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t =
        some u →
      ∃ u', (asks.map fun a => (a.1, a.2.1, a.2.2.1, a.2.2.2.2)).foldlM
          (fun t (a : ℕ × ℕ × ℕ × String) =>
            Own.tableAdded mats t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) t' = some u' ∧
        SkelAlike (u.funs, u.p) (u'.funs, u'.p)
  | [], t, t', u, hA, h => by
    obtain rfl := Option.some.inj h
    exact ⟨t', rfl, hA⟩
  | a :: asks, t, t', u, hA, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨m', k1, kA⟩ := added_skel mats t t' m a.1 a.2.1 a.2.2.1 a.2.2.2.1 #[] a.2.2.2.2 hA h1
    obtain ⟨u', k2, kB⟩ := fold_skel mats asks m m' u kA h2
    refine ⟨u', ?_, kB⟩
    rw [List.map_cons, List.foldlM_cons]
    exact Option.bind_eq_some_iff.2 ⟨m', k1, k2⟩

/-- **THE TEXT's LIST HAS THE PLAN's SKELETON.** -/
theorem tables_skel (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) (tt : Tables)
    (e : K8.ReadsQuiet.tables h L hp cov x = .ok tt) :
    ∃ t0, tabsOfPlan h hp = some t0 ∧ shapesOf tt.funs = shapesOf t0.funs ∧
      ∀ Fn ∈ tt.funs.toList, Fn.tree = 2 := by
  unfold K8.ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := K9L.ok_bind e
  obtain ⟨ZV, _, e⟩ := K9L.ok_bind e
  obtain ⟨lowN, _, e⟩ := K9L.ok_bind e
  obtain ⟨_, _, e⟩ := K9L.ok_bind e
  dsimp only at e
  obtain ⟨qFC, _, e⟩ := K9L.ok_bind e
  obtain ⟨qROW, _, e⟩ := K9L.ok_bind e
  obtain ⟨b0, _, e⟩ := K9L.ok_bind e
  obtain ⟨b1, _, e⟩ := K9L.ok_bind e
  obtain ⟨t, ht, e⟩ := K9L.ok_bind e
  obtain ⟨_, _, e⟩ := K9L.ok_bind e
  obtain rfl := Except.ok.inj e
  obtain ⟨u', k1, kA⟩ := fold_skel hp.tl.mats _ {} {} t
    ⟨rfl, rfl, fun _ hh => by simp at hh⟩ (named_some ht)
  exact ⟨u', k1, kA.2.1, kA.2.2⟩

/-- Behind a yes of the head's quiet step. -/
theorem quietHead_skel (P : K8.ReadsQuiet.PH) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (K8.ReadsQuiet.head P).decide s rs gs = .ok s') :
    ∃ funs t0, s'.funs? = some funs ∧ tabsOfPlan P.h P.hp = some t0 ∧
      shapesOf funs = shapesOf t0.funs ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  have h' : (match s.here with
      | .head a => do
        need "reads: the head's link is not opened" a.opened
        let cov ← K8.ReadsQuiet.under "reads: the covered positions cannot be said"
          (s.covered P.h.T P.h.V)
        let x ← (a.x.elim (.error "reads: what the head heard is not laid") .ok : Except String _)
        let t ← K8.ReadsQuiet.tables P.h P.L P.hp cov x
        let tl ← K8.ReadsQuiet.closed P.hp.tl t.funs a.L s.st
        pure { s with here := .head { a with t := some t, tl := tl } }
      | _ => .error "reads: the head's link is not open" : Except String S) = .ok s' := h
  split at h'
  · rename_i a ha
    obtain ⟨_, ho, h'⟩ := K9L.ok_bind h'
    obtain ⟨cov, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨t, ht, h'⟩ := K9L.ok_bind h'
    obtain ⟨tl, _, h'⟩ := K9L.ok_bind h'
    obtain rfl := Except.ok.inj h'
    have hop : a.opened = true := by
      cases e : a.opened with
      | true => rfl
      | false =>
        rw [e] at ho
        exact nomatch ho
    obtain ⟨t0, k1, k2, k3⟩ := tables_skel P.h P.L P.hp cov x t ht
    exact ⟨t.funs, t0, by simp [S.funs?, hop], k1, k2, k3⟩
  · exact nomatch h'

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **BEHIND THE SENDING OF THE READS AT THE HEAD's SEGMENT.** -/
theorem headSkel_at_reads (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 343 (z, s')) :
    ∃ funs t0, s'.funs? = some funs ∧ tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 ∧
      shapesOf funs = shapesOf t0.funs ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨z', s, s'', b₀, e, _, hb, hy⟩ := reach_pred (k := 342) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, _, e4⟩ := IM.k1_reads_of hS hR O 24 (by omega)
  have hf : c.blocksInOrder[342]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) _] at this
    exact this
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' : (IM.k1Reads Z Bs.G₀ 24 Xl (IM.k1Ix 24 false + 1) reads).decide s rs gs = .ok s' :=
    ((IM.yes_alone e4 (fun k => nomatch k) s _ rs gs).1 hd).1
  unfold IM.k1Reads at hd'
  obtain ⟨m, _, h2⟩ := Keeps.ebind_ok hd'
  unfold IM.k1Quiet at h2
  obtain ⟨l24, f24, k24, -⟩ := (IM.ground_named hS hR O.pub O.blank).2
  rcases First.K8.Ready.quiet_arms Bs.G₀ 24 Xl _ _ _ _ h2 with ⟨k1, _⟩ | ⟨_, Y, hY, hc⟩
  · rw [← Option.some.inj (f24.symm.trans hX), k24] at k1
    exact absurd k1 (by decide)
  · rcases hc with ⟨k0, _⟩ | ⟨_, hq⟩
    · rw [← Option.some.inj (f24.symm.trans hY), k24] at k0
      exact absurd k0 (by decide)
    · obtain ⟨funs, t0, a1, a2, a3, a4⟩ := quietHead_skel
        ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ hq
      exact ⟨funs, t0, a1, a2, a3, a4⟩

/-- **IN FRONT OF THE HEAD's BATCHING.** -/
theorem headSkel_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ funs t0, s'.funs? = some funs ∧ tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 ∧
      shapesOf funs = shapesOf t0.funs ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨s, r, q⟩ := funs_from_reads_head hS hR O h
  obtain ⟨funs, t0, f1, f2, f3, f4⟩ := headSkel_at_reads hS hR O r
  exact ⟨funs, t0, q.trans f1, f2, f3, f4⟩

/-- So the number of reads there. -/
theorem reads_length_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ funs t0, s'.funs? = some funs ∧ tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 ∧
      ∀ tl : HTailF2,
        (readsList tl funs).length = readsLenOf tl.NM tl.mats (shapesOf t0.funs) := by
  obtain ⟨funs, t0, f1, f2, f3, f4⟩ := headSkel_at_batch hS hR O h
  exact ⟨funs, t0, f1, f2, fun tl => by rw [reads_length tl funs f4, f3]⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shapesOf_push
#print axioms VerifiableInference.Desc.LinkJoin.parts_skel
#print axioms VerifiableInference.Desc.LinkJoin.added_skel
#print axioms VerifiableInference.Desc.LinkJoin.fold_skel
#print axioms VerifiableInference.Desc.LinkJoin.tables_skel
#print axioms VerifiableInference.Desc.LinkJoin.quietHead_skel
#print axioms VerifiableInference.Desc.LinkJoin.headSkel_at_reads
#print axioms VerifiableInference.Desc.LinkJoin.headSkel_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.reads_length_head
