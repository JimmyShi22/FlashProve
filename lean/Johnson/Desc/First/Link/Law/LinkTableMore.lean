-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LinkTableMore.lean: BESIDE LinkTable.lean: THE LAW OF A LINK AS THREE
CORE LAWS IN THE TABLE's LETTERS, WITH A SENTENCE MORE IN FRONT OF THE FIRST; AND WHAT A YES OF A
LINK's TWO ROWS OF MOVES SAYS OF THE FIRST FOUR CLAIMS OF THE APPROXIMATE RANGE PROOF's RUN.
Theorems. For the two items of the sort "worth" (of the lookup on the digits) that the batching's
row of the table of joints closes beside the forms.

What is said.
  `link_table_more`: `link_table` with a letter Wq beside the forms in front of the batching, under
    hW: Wq follows from the front of kind K9's law (every term's coefficient is 0), a yes of the
    batching's sub-protocol and the relation behind it: `cores_table_more`
    (Johnson/Desc/First/Batch/Law/CoresTable.lean) at the link's moves.
  `four_at_link`: **from a yes of the link's two rows of moves, begun at a good state that goes on
    from q, ended at a full state t with the part b; every term's coefficient 0 at the data y; the
    run at an entry of the order stands under the approximate range proof's run of equations, with
    the terms "the four values numbered, then the single equations": that run said yes at some state
    of the gathering (which goes on from q, as t does; t is later than the state behind the run),
    and THE FIRST FOUR CLAIMS OF ITS LIST ARE
    WORTH 0 IN THE BATCHING's OWN WORLD AT t**: by `gather_mem`, `later_add` (Law/GatherMem.lean)
    and `four_zero_full` (Law/K8FourZero.lean).

Limits. Implications. hW is paid at no sentence here: between `four_at_link`'s end and the table's
two items stands another file's exchange (the four claims for what the lookup on the digits puts
out: `digits_planesKeys_at_world`, Johnson/Top/H/Keep/EquationsPlanesKeys.lean).
hFu4 (the entries' half of the four values) is taken as given, as in Law/K8Four.lean. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTable
import Johnson.Desc.First.Link.Law.Under
import Johnson.Desc.First.Batch.Law.GatherMem
import Johnson.Desc.First.Batch.Law.K8FourZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)

variable {α W : Type} {F : Frame}

/-- **THE LAW OF A LINK AS THREE CORE LAWS, WITH A SENTENCE MORE IN FRONT OF THE FIRST.** -/
theorem link_table_more (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes L φ tmOf lenOf on0 on1 on2 Rd own rdW items)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a)
    (Wq : S × F.E.Str → W → Prop)
    (hW : ∀ a τ b' w₀, on0 a → pb.ior.red.out a τ = some b' → on1 b' →
      ((totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own b'.1 (rdW w₀) ∧ Rw b') ∧
        ctx b' w₀) →
      ∀ y, boundAt atS (fun a w => tabAt own (rdW w) a.1) ctx a (pb.ext a τ w₀) y →
        (∀ x ∈ termsRuns (fixed9 φ a.1) y (rlOf L tmOf lenOf) 0, x.2 = 0) →
        Wq a (pb.ext a τ w₀)) :
    pb.GoodIn on0 on1 (fun a w => (∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w)) ∧ Wq a w)
        (fun b w =>
          (totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own b.1 (rdW w) ∧ Rw b) ∧
            ctx b w) ∧
      pq.GoodIn on1 on2
        (fun a w => totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own a.1 (rdW w) ∧ Rw a)
        (fun b w => totalQ own b.1 (rdW w) ∧ Rw b) ∧
      pe.GoodIn on2 on3 (fun a w => totalQ own a.1 (rdW w) ∧ Rw a)
        (fun e w => rowEqQ own N e.1 (rdW w)) :=
  cores_table_more C Rw φ Ok Fu p pw (moves₁ L (rlOf L tmOf lenOf)) (moves₂ L) (rlOf L tmOf lenOf)
    (fun q y => terms_link q y L (rlOf L tmOf lenOf)) d N L.batchB L.behindB b₃ pb pq pe on0 on1 on2
    on3 ctx Rd own rdW items (joinAsks_of_runs (runsAsk_of_owes h A)) h01 hR1 hR2 hR3 T.hs2
    T.hbook₂ T.htin T.hitems Wq hW

/-- **A YES OF THE LINK's TWO ROWS OF MOVES, AND THE FIRST FOUR CLAIMS.** -/
theorem four_at_link (L : Link S Claim) (φ : S → α) (hφ : ∀ s a, φ (atS.set s a) = φ s)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ)
    (hrun : ∀ r ∈ rlOf L tmOf lenOf,
      RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) r.run.2 r.tm r.len)
    (hms : ∀ m ∈ moves₁ L (rlOf L tmOf lenOf) ++ moves₂ L,
      MoveOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) m)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (o : ℕ × String) (ho : o ∈ L.order) (run : ℕ → S → Except String (List Claim × S))
    (hAt : At L o run) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y)
    (q : α × Option Pub9) (s₀ t : S) (cls : List Claim) (a₀ : K9.Part) (hf : Fx9 φ Ok q s₀)
    (hg : good9 s₀) (ha₀ : atS.get? s₀ = some a₀) (hs : a₀.F.LS.size = a₀.F.ns)
    (hy : MovesYes atS ((moves₁ L (rlOf L tmOf lenOf) ++ moves₂ (α := α) L).map (·.move)) s₀ t cls)
    (hfull : Fu t) (b : K9.Part) (hb : atS.get? t = some b) (y : Bound GE8)
    (h0 : ∀ x ∈ termsRuns q y (rlOf L tmOf lenOf) 0, x.2 = 0) :
    ∃ front e ae c e₁, Fx9 φ Ok q e ∧ Fx9 φ Ok q t ∧ atS.get? e = some ae ∧
      k8Run.2 front e = .ok (c, e₁) ∧ laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t ∧
      ∀ k ∈ c.take 4, claimValue Reading.gl (worldAt Reading.gl b.L b.F y) k = 0 := by
  have HF := fitsM_atS (K := Cb.Gl.E) φ hφ Ok Fu p
  obtain ⟨uS, c, c', h1, h2, _⟩ := hy
  obtain ⟨_, bu, A1⟩ := move_adv Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF
    ⟨.add (claimsInBy L.each L.hear L.order), fun n q y => termsRuns q y (rlOf L tmOf lenOf) n,
      fun q => lenRuns q (rlOf L tmOf lenOf)⟩
    (hms _ (List.mem_append_left _ List.mem_cons_self)) q s₀ uS a₀ c hf hg ha₀ hs h1
  obtain ⟨bt, A2⟩ := moves_adv Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF q (moves₂ L)
    (fun m hm => hms m (List.mem_append_right _ hm)) uS t bu c' A1.fixed A1.good A1.part A1.sized h2
  have hlu : laterK atS (O9 (K := GE8) φ Ok Fu) uS t :=
    ⟨by simp only [planOf, A1.part, A2.part, Option.map_some, A2.plan], A2.more,
      by simp only [thetaOf, A1.part, A2.part, Option.map_some, A2.theta]⟩
  obtain ⟨e, s, G, hgat, hse, hG, rfl⟩ := h1
  have hfold := fold_gstep L.each L.hear L.order ([], s₀) (c, e) hgat
  rw [← rlOf_runs L tmOf lenOf] at hfold
  obtain ⟨_, a₂, _, ha₂, k', _, g2, _, f2, _, _⟩ :=
    gather_fold Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF (fun _ => []) [] q _ hrun ([], s₀)
      (c, e) a₀ hf hg ha₀ hs hfold
  have es : a₂ = s := Option.some.inj (ha₂.symm.trans hse)
  subst es
  obtain ⟨_, _, _, _, k5, k6⟩ := core_parts k'
  have hle : laterK atS (O9 (K := GE8) φ Ok Fu) e t :=
    later_add Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF q e a₂ G c f2 g2 ha₂
      (by rw [k5, k6]; exact hs) hG t hlu
  have hr : (⟨(o.2, run), tmOf o, lenOf o⟩ : TermedRun S (α × Option Pub9) Cb.Gl.E) ∈
      rlOf L tmOf lenOf := by
    refine List.mem_filterMap.2 ⟨o, ho, ?_⟩
    rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
    rfl
  obtain ⟨front, er, ae, cr, e₁, fx, _, hae, _, hyes, hlat⟩ :=
    gather_mem Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF (fun _ => []) [] q _ hrun ([], s₀)
      (c, e) a₀ hf hg ha₀ hs hfold _ hr
  have hk8 := hu front er cr e₁ hyes
  obtain ⟨m, hm⟩ := zero_of_termsRuns q y _ 0 h0 _ hr
  have hv : ∀ v ∈ vals4 π ent q y, v = 0 := by
    intro v hv
    rw [← numbered_snd (vals4 π ent q y) m] at hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    refine hm x ?_
    show x ∈ tmOf o m q y
    rw [ht]
    exact List.mem_append_left _ hx
  exact ⟨front, er, ae, cr, e₁, fx, A2.fixed, hae, hk8, hlat t hle,
    four_zero_full φ Ok Fu u π hπ hkeep ent hOk4 hFu4 q front er ae cr e₁ fx hae hk8 t y b
      (hlat t hle) hfull hb hv⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.link_table_more
#print axioms VerifiableInference.Desc.LinkJoin.four_at_link
