-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Chain.lean: a local round of the compiled prover, for the lemma on deferred
programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). A local round of the
chains of a batch (Compile/Batch/Prover.lean: `withTree`, `fbSlotG`, `slotLo`, eachM slotLo) obeys
the discipline with joint charges (`SafeO2`) and leaves every slot's record standing both ways
(`SlotI2`), if the round's number of later tries is at most mG; each under the hypotheses of its
statement.

The analogue for `SafeO2` (CompileK/Defer2Safe.lean) of Compile/Batch/DisciplineChain.lean. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs. In a
local round every slot makes the tree over its component, if by the round's wire the component has
one (`withTree`, w.hasJ), and then its own Fiat-Shamir evaluation (`fbSlotG`).

Part A, the state's side: the way upwards:
  `SlotI2.toI`, `SlotI2.fit`, `SlotI2.frame`: a slot is not disturbed, both ways: the conditions of
    `SlotI.frame` (Compile/Batch/DisciplineChain.lean), with the state orderly both ways, and: what
    the run adds at the vertex oracles (`GJ ChJ`) holds no sealed token and no token of the slot.
  `SlotF2.after_tries`: under the hypotheses of its statement, the slot's set after a loop of tries
    stays closed upwards: the tries stand at no vertex oracle; an old vertex evaluation cannot hold
    a new tail, a failed try's tail, nor the new tree's root, which was untouched.
Part B, the programs: `safe2_withTree`, `lo_post2`, `safe2_fbSlotG`, `safe2_slotLo`, `safe2_eachLo`
(and `safe2_withTrees`, with `NewTree2`, `NewTs2` in Part A: for a component with a list of trees:
`withTrees`, Compile/Batch/Prover.lean; no lemma on a round uses them);
Part C: the record `ChainInv2`. Against Compile/Batch/DisciplineChain.lean `safe2_slotLo` and
`safe2_eachLo` have the premise moreOf w.grJ ≤ mG, and one more clause in the ends: `GJ NoTok d d'`:
the round adds at the vertex oracles only evaluations whose further tokens are new. `lo_post2` has
n ≤ mG (hnG), `safe2_fbSlotG` g.more ≤ mG (hm). In `safe2_withTree`, `lo_post2`, `safe2_slotLo`,
`safe2_eachLo` the state is orderly both ways (`TidyBoth`) where that file has `TidyO`; they have
`SlotI2` where it has `SlotI`, `NewT2` where it has `NewT`; `ChainInv2` has `SlotI2` and `Trees02`
where `ChainInv` has `SlotI` and `Trees0`.

For a local round none of the statements named above says that the chains' tokens (tails, failed
tries' tails) and the roots of the trees over messages are no vertex's further tokens.

Limits: This file gives no instance of `SlotI2`. The start of the chains is another file's:
CompileK/Defer2Init.lean (`safe2_initAll`) gives one, under the hypotheses of its statement. This
file says nothing on the shared rounds, the joining of the chains (the request tree enters there),
the start, the whole prover.

Words used in this file. The discipline with joint charges is `SafeO2` (CompileK/Defer2Safe.lean),
here at `rulesT`, `Jt`, `ellT` (CompileK/Defer2Tree.lean): a recursion along the program, for all
coins, answers and tables, that requires the token language's rules at every step and, at the
oracles named by `Jt`, what a charge to two tokens asks more. These are the vertex oracles
`OracleName.node`, `OracleName.rnode`. A state is orderly both ways (`TidyBoth`, CompileK/Defer2Tree.lean) if it has
`TidyO` at `rulesT` and `Tidy2` at `Jt`, `ellT`. A set V of tokens is closed upwards (`ClUp d V`,
CompileK/Defer2Slot.lean) if every evaluation at a vertex oracle that holds a token of V among its
further tokens is charged to a token of V. Both ways: the condition of Compile/Batch/, which follows
a token down its charges, and a second one at the vertex oracles: the head of
CompileK/Defer2Kit.lean. Tokens, evaluations, charges: Rom/Defer.lean.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Loop
import CompileK.Defer2Slot
import Compile.Batch.DisciplineChain

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {Y : Type}

/-! ## Part A. The state's side: the way upwards -/

/-- orderly at `rulesT` is orderly at `rulesB` -/
theorem TidyO.toB {d : DSt (spec lam K L)} (h : TidyO (rulesT K L lam p mG) d) :
    TidyO (rulesB K L lam p) d :=
  ⟨h.viol, h.shown_lt, h.charged_lt, h.tail_lt, h.others_lt, h.released, h.closed_tail,
    h.closed_others, h.bits, fun e he => osBG_mk (h.point e he)⟩

theorem TTUp.keepsJ {d d' : DSt (spec lam K L)} {n₀ depth : ℕ} {t : TTree} (h : TTUp d depth t)
    (hok : TTOK d n₀ depth t) (hj : GJ NoTok d d') : TTUp d' depth t :=
  fun j hj' u hu => (h j hj' u hu).keepsJ ((hok.open_ j hj').lt u hu) hj fun x => x

/-- the tree over a component, just made, both ways -/
def NewT2 (d : DSt (spec lam K L)) (lo depth : ℕ) (x : Option TTree) : Prop :=
  NewT d lo depth x ∧ ∀ tr, x = some tr → TTUp d depth tr

theorem NewT2.unt {d : DSt (spec lam K L)} {lo depth : ℕ} {x : Option TTree}
    (h : NewT2 d lo depth x) {u : Tok} (hu : u ∈ rtL x) : Untouched d u := h.1.unt hu
theorem NewT2.lt {d : DSt (spec lam K L)} {lo depth : ℕ} {x : Option TTree} (h : NewT2 d lo depth x)
    {u : Tok} (hu : u ∈ rtL x) : u < d.vals.length := h.1.lt hu
theorem NewT2.le {d : DSt (spec lam K L)} {lo depth : ℕ} {x : Option TTree} (h : NewT2 d lo depth x)
    {u : Tok} (hu : u ∈ rtL x) : lo ≤ u := h.1.le hu

theorem ClUp.congr {d : DSt (spec lam K L)} {V V' : Tok → Prop}
    (h : ClUp d V) (hV : ∀ u, V' u ↔ V u) : ClUp d V' :=
  fun e he hJ b hb hb' => (hV _).2 (h e he hJ b hb ((hV _).1 hb'))

theorem NewT2.tts_tries {d d' : DSt (spec lam K L)} {n₀ lo depth : ℕ} {x : Option TTree}
    (h : NewT2 d lo depth x) (hn : n₀ ≤ lo) {os : List OracleName} (ho : ∀ o ∈ os, ¬ Wk o)
    (hJ : ∀ o ∈ os, Jt o = false) {t : Tok} (ht : t < lo) {us tls : List Tok}
    (hrm : ∀ u ∈ rtL x, u ∈ us) (hT : Tries (split lam K L) t us d os tls d')
    (tr : TTree) (e : x = some tr) :
    TTS2 d' n₀ depth tr :=
  ⟨h.1.tts_tries hn ho ht hrm hT tr e, (h.2 tr e).keepsJ (h.1 tr e).1 (hT.gj hJ)⟩

/-- one tree over a component, just made, both ways -/
def NewTree2 (d : DSt (spec lam K L)) (lo depth : ℕ) (tr : TTree) : Prop :=
  NewTree d lo depth tr ∧ TTUp d depth tr

theorem NewTree2.mono {d : DSt (spec lam K L)} {lo lo' depth : ℕ} {tr : TTree}
    (h : NewTree2 d lo depth tr) (hl : lo' ≤ lo) : NewTree2 d lo' depth tr :=
  ⟨h.1.mono hl, h.2⟩

/-- What is known of a new tree, both ways, survives a run that charges no old token, whose
evaluations hold no old token, and that shows no old token. -/
theorem NewTree2.keeps {d d' : DSt (spec lam K L)} {lo depth : ℕ} {tr : TTree} {e M : OracleName → ℕ}
    (h : NewTree2 d lo depth tr) (hr : Run NoTok NoTok NoTok e M d d') :
    NewTree2 d' lo depth tr :=
  ⟨h.1.keeps hr, h.2.keeps h.1.1 hr.grows fun _ hu => hu.elim⟩

theorem NewTree2.tts_tries {d d' : DSt (spec lam K L)} {n₀ lo depth : ℕ} {tr : TTree}
    (h : NewTree2 d lo depth tr) (hn : n₀ ≤ lo) {os : List OracleName} (ho : ∀ o ∈ os, ¬ Wk o)
    (hJ : ∀ o ∈ os, Jt o = false) {t : Tok} (ht : t < lo) {us tls : List Tok}
    (hrm : tr.root ∈ us) (hT : Tries (split lam K L) t us d os tls d') : TTS2 d' n₀ depth tr :=
  ⟨h.1.tts_tries hn ho ht hrm hT, h.2.keepsJ h.1.1 (hT.gj hJ)⟩

/-- the trees over a component, just made, both ways: one for each depth of ds, in this order -/
def NewTs2 (d : DSt (spec lam K L)) (lo : ℕ) (ds : List ℕ) (trs : List TTree) : Prop :=
  List.Forall₂ (NewTree2 d lo) ds trs

theorem NewTs2.nil (d : DSt (spec lam K L)) (lo : ℕ) : NewTs2 d lo [] [] :=
  List.Forall₂.nil

theorem NewTs2.cons {d : DSt (spec lam K L)} {lo depth : ℕ} {tr : TTree} {ds : List ℕ}
    {trs : List TTree} (h : NewTree2 d lo depth tr) (ht : NewTs2 d lo ds trs) :
    NewTs2 d lo (depth :: ds) (tr :: trs) :=
  List.Forall₂.cons h ht

/-- the way downwards alone -/
theorem NewTs2.toTs {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) : NewTs d lo ds trs :=
  List.Forall₂.imp (fun _ _ hx => hx.1) h

theorem NewTs2.length_eq {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) : trs.length = ds.length := h.toTs.length_eq

theorem NewTs2.unt {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) : Untouched d u :=
  h.toTs.unt hu

theorem NewTs2.lt {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) : u < d.vals.length :=
  h.toTs.lt hu

theorem NewTs2.le {d : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) {u : Tok} (hu : u ∈ trs.map TTree.root) : lo ≤ u := h.toTs.le hu

theorem NewTs2.mono {d : DSt (spec lam K L)} {lo lo' : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) (hl : lo' ≤ lo) : NewTs2 d lo' ds trs :=
  List.Forall₂.imp (fun _ _ hx => hx.mono hl) h

/-- the same as `NewTree2.keeps`, of all trees of the list -/
theorem NewTs2.keeps {d d' : DSt (spec lam K L)} {lo : ℕ} {ds : List ℕ} {trs : List TTree}
    {e M : OracleName → ℕ} (h : NewTs2 d lo ds trs) (hr : Run NoTok NoTok NoTok e M d d') :
    NewTs2 d' lo ds trs :=
  List.Forall₂.imp (fun _ _ hx => hx.keeps hr) h

/-- the same as `NewTree2.tts_tries`, of all trees of the list: the tries hold all their roots -/
theorem NewTs2.tts_tries {d d' : DSt (spec lam K L)} {n₀ lo : ℕ} {ds : List ℕ} {trs : List TTree}
    (h : NewTs2 d lo ds trs) (hn : n₀ ≤ lo) {os : List OracleName} (ho : ∀ o ∈ os, ¬ Wk o)
    (hJ : ∀ o ∈ os, Jt o = false) {t : Tok} (ht : t < lo) {us tls : List Tok}
    (hrm : ∀ u ∈ trs.map TTree.root, u ∈ us) (hT : Tries (split lam K L) t us d os tls d') :
    List.Forall₂ (TTS2 d' n₀) ds trs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih =>
    exact List.Forall₂.cons (hx.tts_tries hn ho hJ ht (hrm _ List.mem_cons_self) hT)
      (ih fun u hu => hrm u (List.mem_cons_of_mem _ hu))

theorem SlotI2.toI {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0}
    {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI2 p d n₀ done ph a0 j acc) :
    SlotI p d n₀ done ph a0 j acc :=
  ⟨h.fin.toF, h.cap, h.alive⟩

theorem SlotI2.fit {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0}
    {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI2 p d n₀ done ph a0 j acc) : Fit d (live ph acc) :=
  h.toI.fit

/-- Under the hypotheses below, a slot is not disturbed, both ways. -/
theorem SlotI2.frame {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} {Cc Ch ChJ : Tok → Prop} {e M : OracleName → ℕ}
    (h : SlotI2 p d n₀ done ph a0 j acc) (hd : TidyBoth p mG d) (hr : Run Cc Ch NoTok e M d d')
    (hc : ∀ u, Cc u → Fit d u ∧ ¬ OpenOf ph acc u) (hh : ¬ Ch (live ph acc)) (hj : GJ ChJ d d')
    (hcj : ∀ u, ChJ u → ¬ Sealed d u ∧ ¬ InU a0 j acc u) :
    SlotI2 p d' n₀ done ph a0 j acc :=
  have h1 := h.toI.frame hd.1.toB hr hc hh
  ⟨h.fin.keeps hr hc hj hcj, h1.cap, h1.alive⟩

/-- The set of tokens of a slot after a loop of tries, both ways. The way upwards: the tries stand
at no vertex oracle (hJ); an old evaluation cannot hold a new tail, nor the new tree's root, which
was untouched. (not all hypotheses are named here: see the statement below) -/
theorem SlotF2.after_tries {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {Op : Tok → Prop} {a0 : Acc0} {j : ℕ} {acc acc' : SlotAcc lam K Y} (hd : TidyBoth p mG d)
    (h : SlotF2 d n₀ done Op a0 j acc) {os : List OracleName} (ho : ∀ o ∈ os, o ≠ OracleName.rleaf)
    (hJ : ∀ o ∈ os, Jt o = false) {t : Tok} {us : List Tok} {tr : Option TTree} {lo depth x : ℕ}
    (hn : n₀ ≤ lo) (hlo : lo ≤ d.vals.length) (ht : t < lo) (hts : ¬ Sealed d t)
    (hop : ∀ u, Op u → u = t ∨ u ∈ us) (hus : ∀ u ∈ us, u ∈ rtL tr ∨ u ∈ a0.toks)
    (hrm : ∀ u ∈ rtL tr, u ∈ us) (htr : NewT2 d lo depth tr) {dd : List Tok} {tl : Tok}
    (hT : Tries (split lam K L) t us d os (dd.reverse ++ [tl]) d')
    (htoks : acc'.toks = acc.toks ++ [tl]) (htrees : acc'.trees = acc.trees ++ [tr])
    (hdead : acc'.dead = dd ++ acc.dead) :
    SlotF2 d' n₀ (done ++ [(depth, x)]) (fun u => u = tl) a0 j acc' := by
  have h1 :=
    h.toF.after_tries (x := x) hd.1.toB ho hn hlo ht hts hop hus hrm htr.1 hT htoks htrees hdead
  have hrun : Run (fun t' => t' = t) (fun t' => t' = t ∨ t' ∈ us) NoTok zr
      (fun o => os.count o) d d' := hT.run
  have hmono : ∀ u, InU a0 j acc u → InU a0 j acc' u := by
    intro u hu
    unfold InU at hu ⊢
    rw [htoks, htrees, hdead]
    rcases hu with h1 | h1 | ⟨tr', h1, h2⟩ | h1 | h1 | h1 | h1
    · exact Or.inl (List.mem_append_left _ h1)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨tr', List.mem_append_left _ h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_append_right _ h1))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))
  refine ⟨h1.cl, ?_, h1.new, ?_, h1.ne⟩
  · intro e he hJe b hb hV
    have he₀ : e ∈ d.evs := by
      rcases hT.mem_evs e he with he | ⟨_, _, _, hoo⟩
      · exact he
      · rw [hJ _ hoo] at hJe
        simp at hJe
    have hblt : b < d.vals.length := hd.1.others_lt e he₀ b hb
    have hnew : ∀ u ∈ dd.reverse ++ [tl], b ≠ u := fun u hu hbu =>
      absurd hblt (Nat.not_lt.mpr (hbu ▸ hT.tail_ge u hu))
    refine hmono _ (h.up e he₀ hJe b hb ?_)
    unfold InU at hV ⊢
    rw [htoks, htrees, hdead] at hV
    rcases hV with h2 | h2 | ⟨tr', h2, h3⟩ | h2 | h2 | h2 | h2
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact Or.inl h2
      · exact absurd (List.mem_singleton.mp h2)
          (hnew tl (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    · exact Or.inr (Or.inl h2)
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact Or.inr (Or.inr (Or.inl ⟨tr', h2, h3⟩))
      · exact absurd hb
          (h3 ▸
            ((htr.1.unt (mem_rtL.2 ⟨tr', (List.mem_singleton.mp h2).symm, rfl⟩)).not_held e he₀).2)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact absurd rfl (hnew b (List.mem_append_left _ (List.mem_reverse.mpr h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2)))))
  · rw [htrees]
    exact forall₂_append
      (List.Forall₂.cons (htr.tts_tries hn (fun o hm => ho o hm) hJ ht hrm hT) List.Forall₂.nil)
      (h.trees.keeps hrun (fun u hu => hu ▸ hts) (hT.gj hJ) fun _ hu => hu.elim)

/-- Under the hypotheses below, the state after the tries of a loop is orderly, both ways. -/
theorem LoopPre.tidy2 {d d' : DSt (spec lam K L)} {t : Tag} {tk : Tok} {vs tls : List Tok} {n : ℕ}
    (h : LoopPre p d t tk vs) (hn : n ≤ mG) (hd : TidyBoth p mG d)
    (hT : Tries (split lam K L) tk vs d (osTry t n) tls d') : TidyBoth p mG d' :=
  ⟨hT.tidy hd.1 h.lt h.not_mem h.free_all (osTry_nodup t n) (n := (d.val tk).length)
      ⟨h.free.lt, rfl⟩
      (fun o ho => by rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩ <;> exact h.bits)
      (fun o ho _ => osTry_memG t hn o ho),
    hT.tidy2 hd.1 hd.2 (osTry_notJ t n)⟩

/-! ## Part B. The rounds -/

/-- The tree over a component, if it has one, and then k: from a state d that is orderly both ways
(hd), it is enough (hk) that k is safe after any tree that is as safe2_commitT leaves it, and that k
none is safe from every state d₁ that is orderly both ways and for which the `Run` in hk holds from
d to d₁ (d is one such state). -/
theorem safe2_withTree {β : Type} (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    (k : Option TTree → St lam K L β) (d : DSt (spec lam K L))
    (hd : TidyBoth p mG d) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ x d₁, TidyBoth p mG d₁ →
      Run NoTok NoTok NoTok zr
        (fun o =>
          cnt1 (S := spec lam K L) OracleName.leaf (2 ^ depth) o +
            cnt1 (S := spec lam K L) OracleName.node (2 ^ depth) o)
        d d₁ →
      NewT2 d₁ d.vals.length depth x → SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k x) d₁ Q) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (withTree p.sMT has depth leaf k) d Q := by
  cases has with
  | true =>
    refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_commitT depth leaf d hd))
    rintro tr d₁ ⟨hd₁, hr₁, h1, h2, h3⟩
    exact hk (some tr) d₁ hd₁ hr₁
      ⟨fun tr' e => (by cases e; exact ⟨h1, h3⟩), fun tr' e => (by cases e; exact h2)⟩
  | false => exact hk none d hd (Run.refl d) ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩

/-- The trees over a component, one after the other, and then k: from a state that is orderly both
ways it is enough that k is safe after any trees that are as safe2_commitT leaves them (`NewTs2`).
-/
theorem safe2_withTrees {β : Type} :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) (k : List TTree → St lam K L β)
      (d : DSt (spec lam K L)), TidyBoth p mG d →
      ∀ (Q : β → DSt (spec lam K L) → Prop),
      (∀ trs d₁, TidyBoth p mG d₁ →
        Run NoTok NoTok NoTok zr (MTrees lam K L ds) d d₁ →
        NewTs2 d₁ d.vals.length ds trs →
        SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k trs) d₁ Q) →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (withTrees p.sMT ds leaf k) d Q
  | [], _, _, d, hd, _, hk => hk [] d hd (Run.refl d) (NewTs2.nil d _)
  | depth :: ds, leaf, k, d, hd, Q, hk => by
      rw [withTrees]
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_commitT depth (leaf 0) d hd))
      rintro tr d₁ ⟨hd₁, hr₁, h1, h2, h3⟩
      refine safe2_withTrees ds (fun n => leaf (n + 1)) (fun trs => k (tr :: trs)) d₁ hd₁ Q
        fun trs d₂ hd₂ hr₂ hts => ?_
      have h₂ : NewTree2 d₂ d.vals.length depth tr := NewTree2.keeps ⟨⟨h1, h3⟩, h2⟩ hr₂
      exact hk (tr :: trs) d₂ hd₂
        (hr₁.trans hr₂ (fun _ hu => Or.inl hu) (fun _ hu => Or.inl hu) (fun _ hu => Or.inl hu)
          (fun _ => le_rfl) fun o => le_of_eq (MTrees_cons depth ds o).symm)
        (NewTs2.cons h₂ (hts.mono hr₁.length_le))

section Lo2
variable {d d₁ : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0} {j : ℕ}
  {acc : SlotAcc lam K Y} {tr : Option TTree}

/-- the slot after the tries of a local round -/
theorem lo_post2 (t : Tag) (hd₁ : TidyBoth p mG d₁) (h : SlotI2 p d₁ n₀ done ph a0 j acc)
    (hn : n₀ ≤ d.vals.length) (hle : d.vals.length ≤ d₁.vals.length)
    (hlt : live ph acc < d.vals.length) {depth x : ℕ}
    (htr : NewT2 d₁ d.vals.length depth tr) (bl : List (Blk lam K)) (nc : Option ℕ) {n : ℕ}
    (hnG : n ≤ mG) {dd : List Tok} {tl : Tok} {d' : DSt (spec lam K L)}
    (hT : Tries (split lam K L) (live ph acc) (usOf ph (tr.map TTree.root)) d₁ (osTry t n)
      (dd.reverse ++ [tl]) d') :
    SlotI2 p d' n₀ (done ++ [(depth, x)]) ph.afterLo a0 j (accLo acc tl bl tr nc dd) := by
  have hpre := lo_pre (p := p) t h.toI hlt htr.1
  have hd' := hpre.tidy2 hnG hd₁ hT
  have hF := h.fin.after_tries (acc' := accLo acc tl bl tr nc dd) (x := x) hd₁ (osTry_ne_rleaf t n)
    (osTry_notJ t n) (t := live ph acc)
    (us := usOf ph (tr.map TTree.root)) hn hle hlt
    h.cap.not_sealed
    (fun u hu => by
      cases ph with
      | shr tk0 =>
        exact (show u = acc.c ∨ u = tk0 from hu).imp_right fun h1 => by
          rw [h1]; exact List.mem_cons_self
      | first => exact Or.inl hu
      | loc => exact Or.inl hu
      | aft => exact Or.inl hu)
    (fun u hu => by
      cases ph with
      | shr tk0 =>
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inr h.cap.2.2.2.2.2.1
        · exact Or.inl hu
      | first => exact Or.inl hu
      | loc => exact Or.inl hu
      | aft => exact Or.inl hu)
    (fun u hu => by
      cases ph with
      | shr tk0 => exact List.mem_cons_of_mem _ hu
      | first => exact hu
      | loc => exact hu
      | aft => exact hu) htr hT rfl rfl rfl
  have hcap : Untouched d' tl ∧ Len d' tl lam ∧ tl ∈ acc.toks ++ [tl] :=
    ⟨hT.untouched_last hd₁.1 (lt_of_lt_of_le hlt hle) hpre.lt,
      hT.len_last (osTry_tl lam K L t n),
      List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  have hal : ¬ Dead d' tl := hT.not_dead_last hd'.1
  cases ph with
  | shr tk0 => exact ⟨hF, hcap, hal⟩
  | first => exact ⟨hF, hcap, hal⟩
  | loc => exact ⟨hF, hcap, hal⟩
  | aft => exact ⟨hF, hcap, hal⟩

end Lo2

/-- the Fiat-Shamir evaluation of a slot in a local round, with a test or without: fbG, charged to
the live token, with the other tokens usOf -/
theorem safe2_fbSlotG {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C)
    (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT)
    (acc : SlotAcc lam K Y) (root : Option Tok) (emb : P → PlainPart (shapeOf L t) (annOf L t))
    (α : P) (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β)
    {d : DSt (spec lam K L)} (h : LoopPre p d t (live ph acc) (usOf ph root))
    (hm : ∀ g, gr = some g → g.more ≤ mG) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ nc dd bl tl d', Kept gr nc dd →
      Tries (split lam K L) (live ph acc) (usOf ph root) d (osTry t (nc.getD 0))
        (dd.reverse ++ [tl]) d' →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k nc dd bl tl) d' Q) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
      (fbSlotG gr chal t i cms x ph acc.tk acc.c root emb α k) d Q := by
  cases ph with
  | shr tk0 => exact safe2_fbG (us := [tk0]) h gr hm k Q hk
  | first => exact safe2_fbG (us := []) h gr hm k Q hk
  | loc => exact safe2_fbG (us := []) h gr hm k Q hk
  | aft => exact safe2_fbG (us := []) h gr hm k Q hk

/-- A local round, in one slot. -/
theorem safe2_slotLo {r : Round} {s : Shape} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)
    (a : RAnn r) (w : WireRB lam K r a)
    (emb : (q : r.Pos) → r.Sym q → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (z : SlotSt lam K Y (r :: s))
    (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (a0 : Acc0) (j : ℕ)
    (hd : TidyBoth p mG d) (hn : n₀ ≤ d.vals.length)
    (h : SlotI2 p d n₀ done ph a0 j z.2) (hmG : moreOf w.grJ ≤ mG) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (slotLo p.sMT t cms xin a w emb plJ i ph z) d fun z' d' =>
      TidyBoth p mG d' ∧
      Run (fun u => u = live ph z.2) (OpenOf ph z.2) NoTok zr
        (MLo lam K L t w.depthJ (moreOf w.grJ)) d d' ∧
      SlotI2 p d' n₀ (done ++ [(w.depthJ, w.depth0)]) ph.afterLo a0 j z'.2 ∧
      d.vals.length ≤ z'.2.tk ∧
      GJ NoTok d d' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  show SafeO2 _ _ _
    (withTree p.sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
      fbSlotG w.grJ w.chal t i cms (acc.x.bind xin) ph acc.tk acc.c (tr.map TTree.root) plJ
        (a.plain m.2).2 fun nc dd bl tl =>
          Step.pure (k (w.chal bl),
              { acc with
                tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [tr],
                toks := acc.toks ++ [tl], nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead }))
    d _
  refine safe2_withTree w.hasJ w.depthJ _ _ d hd _ fun tr d₁ hd₁ hr₁ htr => ?_
  have hI₁ : SlotI2 p d₁ n₀ done ph a0 j acc :=
    h.frame hd hr₁ (fun _ hu => hu.elim) (fun hu => hu)
      (GJ.of_grows hr₁.grows) (fun _ hu => hu.elim)
  have hlt : live ph acc < d.vals.length := h.cap.lt
  have hpre := lo_pre (p := p) t hI₁.toI hlt htr.1
  refine safe2_fbSlotG w.grJ w.chal t i cms _ ph acc _ plJ _ _ hpre
    (fun g hg => by rw [hg] at hmG; exact hmG) _ fun nc dd bl tl d' hK hT => ?_
  have hnc : nc.getD 0 ≤ moreOf w.grJ := by
    cases hg : w.grJ with
    | none =>
      have h0 : nc = none := by
        have := hK.1
        rw [hg] at this
        cases nc with
        | none => rfl
        | some _ => cases this
      rw [h0]
      exact Nat.zero_le _
    | some g => exact hK.2.2 g hg
  refine ⟨hpre.tidy2 (le_trans hnc hmG) hd₁ hT,
    ?_,
    lo_post2 t hd₁ hI₁ hn hr₁.length_le hlt htr (acc.blocks ++ [bl]) nc (le_trans hnc hmG) hT,
    le_trans hr₁.length_le (hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))),
    (GJ.of_grows hr₁.grows).trans (hT.gj (osTry_notJ t _)) fun _ hu => hu.elim⟩
  refine (hr₁.mono (Cc := fun u => u = live ph acc) (Ch := OpenOf ph acc) (R := NoTok) (e := zr)
      (M := fun o => cnt1 OracleName.leaf (2 ^ w.depthJ) o + cnt1 OracleName.node (2 ^ w.depthJ) o)
      (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ => le_rfl)
      (fun _ => le_rfl)).trans
    (hT.run (R := NoTok) (e := zr)) (fun _ hu => Or.inl hu) (fun u hu => ?_) (fun _ hu => hu.elim)
    (fun _ => le_rfl) (fun o => Nat.add_le_add_left (count_osTry_le t hnc o) _)
  rcases hu with rfl | hu
  · refine Or.inl ?_
    cases ph with
    | shr tk0 => exact Or.inl rfl
    | first => rfl
    | loc => rfl
    | aft => rfl
  · cases ph with
    | shr tk0 =>
      rcases List.mem_cons.mp hu with rfl | hu
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (htr.1.le hu)
    | first => exact Or.inr (htr.1.le hu)
    | loc => exact Or.inr (htr.1.le hu)
    | aft => exact Or.inr (htr.1.le hu)

/-! ### All slots, in a local round -/

theorem safe2_eachLo {r : Round} {s : Shape} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)
    (a : RAnn r) (w : WireRB lam K r a) (emb : (q : r.Pos) → r.Sym q → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (n₀ : ℕ) (done : List (ℕ × ℕ))
    (a0 : Acc0) (hmG : moreOf w.grJ ≤ mG) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (j : ℕ) (d : DSt (spec lam K L)), TidyBoth p mG d →
      n₀ ≤ d.vals.length → AllFrom (fun j z => SlotI2 p d n₀ done ph a0 j z.2) j zs →
      (zs.map fun z => live ph z.2).Nodup →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (eachM (slotLo p.sMT t cms xin a w emb plJ i ph) zs) d fun zs' d' =>
      TidyBoth p mG d' ∧
      Run (fun u => ∃ z ∈ zs, u = live ph z.2) (fun u => ∃ z ∈ zs, OpenOf ph z.2 u) NoTok zr
        (fun o => zs.length * MLo lam K L t w.depthJ (moreOf w.grJ) o) d d' ∧
      AllFrom (fun j z => SlotI2 p d' n₀ (done ++ [(w.depthJ, w.depth0)]) ph.afterLo a0 j z.2)
        j zs' ∧
      (zs'.map fun z => z.2.tk).Nodup ∧
      (∀ z ∈ zs', d.vals.length ≤ z.2.tk) ∧ zs'.length = zs.length ∧ GJ NoTok d d'
  | [], _, d, hd, _, _, _ =>
    ⟨hd, Run.refl d, trivial, List.nodup_nil,
      fun _ h => absurd h List.not_mem_nil, rfl, GJ.refl _ d⟩
  | z :: zs, j, d, hd, hn, hall, hnd => by
      show SafeO2 _ _ _ ((slotLo p.sMT t cms xin a w emb plJ i ph z).bind fun b =>
        (eachM (slotLo p.sMT t cms xin a w emb plJ i ph) zs).bind fun r => Step.pure (b :: r)) d _
      have hnd' := List.nodup_cons.mp hnd
      have hne : ∀ x ∈ zs, live ph z.2 ≠ live ph x.2 := fun x hx he =>
        hnd'.1 (List.mem_map.mpr ⟨x, hx, he.symm⟩)
      refine SafeO2.bind _ _ d
        (SafeO2.mono ?_ _ d
          (safe2_slotLo t cms xin a w emb plJ i ph z d n₀ done a0 j hd hn hall.1 hmG))
      rintro z' d₁ ⟨hd₁, hr₁, hI', hnew, hj₁⟩
      have hall₁ : AllFrom (fun j z => SlotI2 p d₁ n₀ done ph a0 j z.2) (j + 1) zs :=
        AllFrom.mono_mem (j + 1) zs
          (fun j' x hx hIx =>
            hIx.frame hd hr₁ (fun u hu => hu ▸ ⟨hall.1.fit, hall.1.toI.live_not_open (hne x hx)⟩)
              (hIx.toI.live_not_open (hne x hx).symm) hj₁ (fun _ hu => hu.elim)) hall.2
      refine SafeO2.bind _ _ d₁
        (SafeO2.mono ?_ _ d₁
          (safe2_eachLo t cms xin a w emb plJ i ph n₀ done a0 hmG zs (j + 1) d₁ hd₁
            (le_trans hn hr₁.length_le) hall₁ hnd'.2))
      rintro r' d₂ ⟨hd₂, hr₂, hall₂, hnd₂, hnew₂, hlen₂, hj₂⟩
      have hz'lt : z'.2.tk < d₁.vals.length := live_afterLo ph z'.2 ▸ hI'.cap.lt
      refine ⟨hd₂, ?_, ⟨?_, hall₂⟩, ?_, ?_, by simp [hlen₂], hj₁.trans hj₂ fun _ hu => hu.elim⟩
      · refine (hr₁.mono (Cc := fun u => ∃ x ∈ z :: zs, u = live ph x.2)
            (Ch := fun u => ∃ x ∈ z :: zs, OpenOf ph x.2 u) (R := NoTok) (e := zr)
            (M := MLo lam K L t w.depthJ (moreOf w.grJ))
            (fun u hu => Or.inl ⟨z, List.mem_cons_self, hu⟩)
            (fun u hu => Or.inl ⟨z, List.mem_cons_self, hu⟩) (fun _ hu => hu.elim)
            (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₂ (fun u ⟨x, hx, hu⟩ => Or.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩)
          (fun u ⟨x, hx, hu⟩ => Or.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩) (fun _ hu => hu.elim)
          (fun _ => le_rfl) (fun o => ?_)
        rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
      · refine hI'.frame hd₁ hr₂ (fun u ⟨x, hx, hu⟩ => ?_) (fun ⟨x, hx, hu⟩ => ?_)
          hj₂ (fun _ hu => hu.elim)
        · obtain ⟨j', hIx⟩ := AllFrom.of_mem (j + 1) zs hall₁ x hx
          obtain ⟨j'', hIx0⟩ := AllFrom.of_mem (j + 1) zs hall.2 x hx
          refine hu ▸ ⟨hIx.fit, fun ho => ?_⟩
          exact absurd hnew (Nat.not_le.mpr (((openOf_afterLo ph z'.2 _).1 ho) ▸ hIx0.cap.lt))
        · obtain ⟨j'', hIx0⟩ := AllFrom.of_mem (j + 1) zs hall.2 x hx
          rw [live_afterLo] at hu
          exact absurd hnew (Nat.not_le.mpr (hIx0.toI.open_lt hu))
      · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd₂⟩
        obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
        exact absurd (hnew₂ x hx) (Nat.not_le.mpr (he ▸ hz'lt))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnew
        · exact le_trans hr₁.length_le (hnew₂ x hx)

/-! ## Part C. What holds between two rounds -/

/-- Between two rounds. done: the depths of the trees of the rounds made; ph: the phase; a0: what
the shared part has gathered; zs: the slots. -/
structure ChainInv2 {s : Shape} (p : Params) (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ))
    (ph : PhT) (a0 : Acc0) (zs : List (SlotSt lam K Y s)) : Prop where
  slots : AllFrom (fun j z => SlotI2 p d n₀ done ph a0 j z.2) 0 zs
  trees0 : Trees02 d n₀ done a0.trees
  nodup : (zs.map fun z => live ph z.2).Nodup
  le : n₀ ≤ d.vals.length
  /-- in the shared rounds: the last shared tail can be charged -/
  shr : ∀ tk0, ph = PhT.shr tk0 → Untouched d tk0 ∧ Len d tk0 lam ∧ ¬ Dead d tk0
  /-- before the chains join there is no request tree -/
  req : ph = PhT.first ∨ ph = PhT.loc → a0.req = none


end Compile.Batch.Disc
