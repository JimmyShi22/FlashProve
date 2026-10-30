-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/MoreProofs.lean: further reads of the prover's oracles as one more round: proofs of the
statements of Ior/More.lean.

For `R.more`, implicit instance and plan see the head of Ior/More.lean.

Main names (statements and hypotheses: Ior/More.lean):
  `know_more`: round-by-round knowledge soundness of `R.more`
  `output_more`, `outputT_more`, `exact_more`, `exactT_more`, `hvzk_more`, `hvzkB_more`: see their
    statements.

The two facts with content are `given_more` (what the simulator of `R.more` is given of the
implicit instance is what R's simulator is given at the further positions plan d and T) and
`view_more`, `dviewT_more` (what is shown).

Limits: see Limits in the head of Ior/More.lean.
-/
import Ior.More
import Ior.ToProtoProofs
import Ior.OnlineHon

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

variable {D : Type} [Fintype D] [Nonempty D]

theorem OPos.mem_tail {s : Shape} {T : Finset (OPos (askRound D :: s))} {p : OPos s} :
    p ∈ OPos.tail T ↔ (Sum.inr p : Empty ⊕ OPos s) ∈ T :=
  Finset.mem_preimage

namespace IOR
variable {Xi Xo X : Type} {Ei Eo E : ExtSpec} {R : IOR Xi Ei Xo Eo}
  {Wi Wo : Type} {plan : D → Finset (OPos R.shape)}

theorem mem_given_iff (R : IOR Xi Ei Xo Eo) (ρ : Rho R.shape)
    (T : Finset (OPos R.shape)) (q : Ei.Pos) :
    q ∈ R.given ρ T ↔ q ∈ R.extReads ρ ∨ ∃ p, (p ∈ R.reads ρ ∨ p ∈ T) ∧ q ∈ R.tie ρ p := by
  unfold given
  simp only [Finset.mem_union, Finset.mem_biUnion]

open Classical in
theorem mem_reads_more {d : D} {ρ : Rho R.shape} {p : OPos R.shape} :
    (Sum.inr p : Empty ⊕ OPos R.shape) ∈ (R.more D plan).reads ((d, ρ) : D × Rho R.shape) ↔
    p ∈ R.reads ρ ∨ p ∈ plan d := by
  constructor
  · intro h
    obtain ⟨p', hp', he⟩ := Finset.mem_image.1 h
    cases he
    exact Finset.mem_union.1 hp'
  · intro h
    exact Finset.mem_image.2 ⟨p, Finset.mem_union.2 h, rfl⟩

open Classical in
theorem mem_srcO_more {d : D} {ρ : Rho R.shape} {q : Eo.Pos} {p : OPos R.shape} :
    (Sum.inr p : Empty ⊕ OPos R.shape) ∈ (R.more D plan).srcO ((d, ρ) : D × Rho R.shape) q ↔
    p ∈ R.srcO ρ q := by
  constructor
  · intro h
    obtain ⟨p', hp', he⟩ := Finset.mem_image.1 h
    cases he
    exact hp'
  · intro h
    exact Finset.mem_image.2 ⟨p, h, rfl⟩

open Classical in
theorem given_more (d : D) (ρ : Rho R.shape) (T : Finset (OPos (askRound D :: R.shape))) :
    (R.more D plan).given ((d, ρ) : D × Rho R.shape) T = R.given ρ (plan d ∪ OPos.tail T) := by
  ext q
  rw [mem_given_iff, mem_given_iff]
  constructor
  · rintro (h | ⟨(p : Empty ⊕ OPos R.shape), hp, hq⟩)
    · rcases (mem_given_iff R ρ (plan d) q).1 h with h' | ⟨p, hp, hq⟩
      · exact Or.inl h'
      · exact Or.inr ⟨p, hp.elim Or.inl fun h => Or.inr (Finset.mem_union_left _ h), hq⟩
    · rcases p with e | p
      · exact e.elim
      · refine Or.inr ⟨p, ?_, hq⟩
        rcases hp with hp | hp
        · exact (mem_reads_more.1 hp).elim Or.inl fun h => Or.inr (Finset.mem_union_left _ h)
        · exact Or.inr (Finset.mem_union_right _ (OPos.mem_tail.2 hp))
  · rintro (h | ⟨p, hp, hq⟩)
    · exact Or.inl ((mem_given_iff R ρ (plan d) q).2 (Or.inl h))
    · rcases hp with hp | hp
      · exact Or.inl ((mem_given_iff R ρ (plan d) q).2 (Or.inr ⟨p, Or.inl hp, hq⟩))
      · rcases Finset.mem_union.1 hp with h | h
        · exact Or.inl ((mem_given_iff R ρ (plan d) q).2 (Or.inr ⟨p, Or.inr h, hq⟩))
        · exact Or.inr ⟨(Sum.inr p : Empty ⊕ OPos R.shape), Or.inr (OPos.mem_tail.1 h), hq⟩

open Classical in
/-- Which symbols are shown. -/
theorem shown_more (d : D) (ρ : Rho R.shape)
    (T : Finset (OPos (askRound D :: R.shape))) (p : OPos R.shape) :
    ((Sum.inr p : Empty ⊕ OPos R.shape) ∈ (R.more D plan).reads ((d, ρ) : D × Rho R.shape) ∨
      (Sum.inr p : Empty ⊕ OPos R.shape) ∈ T ∨
      R.blinded p = false) ↔
    (p ∈ R.reads ρ ∨ p ∈ plan d ∪ OPos.tail T ∨ R.blinded p = false) := by
  rw [mem_reads_more, Finset.mem_union, OPos.mem_tail]
  tauto

open Classical in
theorem view_more (m : Unit × Unit) (d : D) (τ : Tr R.shape)
    (T : Finset (OPos (askRound D :: R.shape))) :
    (R.more D plan).view T ((m, d, τ) : (Unit × Unit) × D × Tr R.shape) =
      View.more plan (R.view (plan d ∪ OPos.tail T) τ) := by
  refine congrArg (fun o => (⟨((), τ.plains), o⟩ : View (R.more D plan)))
    (funext fun (p : Empty ⊕ OPos R.shape) => ?_)
  rcases p with e | p
  · exact e.elim
  · exact if_congr (shown_more d τ.rho T p) rfl rfl

end IOR

open IOR

theorem output_more : Spec.output_more := by
  intro Xi Xo Wi Wo Ei Eo R D _ _ plan H w x d ρ T
  unfold IOR.Honest.output
  by_cases h : ρ ∈ H.withheld w x
  · have h' : ((d, ρ) : D × Rho R.shape) ∈ (H.more plan).withheld w x := h
    rw [if_pos h, PMF.pure_map]
    exact if_pos h'
  · have h' : ((d, ρ) : D × Rho R.shape) ∉ (H.more plan).withheld w x := h
    rw [if_neg h, PMF.map_comp]
    refine (if_neg h').trans ?_
    refine congrArg (fun f => (unif H.Coin).map f) (funext fun c => ?_)
    exact congrArg some (view_more ((), ()) d ((H.strat w x c).run ρ).1 T)

theorem exact_more : Spec.exact_more := by
  intro Xi Xo Wi Wo Ei Eo R D _ _ plan H Ri bud S hS x y w hR ρ hρ T hb
  obtain ⟨d, ρ⟩ : D × Rho R.shape := ρ
  rw [output_more, hS x y w hR ρ hρ _ hb, given_more]
  rfl

open Classical in
theorem isLocal_more : Spec.isLocal_more := by
  intro Xi Xo Ei Eo R D _ _ plan h
  constructor
  · intro x y y' τ τ' hρ hp he hr
    obtain ⟨m, d, t⟩ : (Unit × Unit) × D × Tr R.shape := τ
    obtain ⟨m', d', t'⟩ : (Unit × Unit) × D × Tr R.shape := τ'
    exact h.out x y y' t t' (congrArg Prod.snd hρ) (congrArg Prod.snd hp)
      (fun p hp' => he p ((mem_given_iff R t.rho (plan d) p).2 (Or.inl hp')))
      fun p hp' => hr (Sum.inr p : Empty ⊕ OPos R.shape) (mem_reads_more.2 (Or.inl hp'))
  · intro y y' τ τ' q hρ hp he hr
    obtain ⟨m, d, t⟩ : (Unit × Unit) × D × Tr R.shape := τ
    obtain ⟨m', d', t'⟩ : (Unit × Unit) × D × Tr R.shape := τ'
    exact h.imp y y' t t' q (congrArg Prod.snd hρ) (congrArg Prod.snd hp) he
      fun p hp' => hr (Sum.inr p : Empty ⊕ OPos R.shape) (mem_srcO_more.2 hp')

theorem know_more : Spec.know_more := by
  intro Xi Xo WA WB Ei Eo R D _ _ plan on RA RB ext ε h a ha m
  exact le_of_eq (cnt_false fun c hc => hc (h a ha))

theorem acc_more : Spec.acc_more := by
  intro Xi Xo Wi Wo Ei Eo R D _ _ plan H Ri Ro h x y w c ρ hR hρ
  obtain ⟨d, ρ⟩ : D × Rho R.shape := ρ
  exact h x y w c ρ hR hρ

theorem tied_more : Spec.tied_more := by
  intro Xi Xo Ei Eo R D _ _ plan ρ p hp q hq
  obtain ⟨d, ρ⟩ : D × Rho R.shape := ρ
  rcases (p : Empty ⊕ OPos R.shape) with e | p
  · exact e.elim
  · exact (mem_given_iff R ρ (plan d) q).2 (Or.inr ⟨p, mem_reads_more.1 hp, hq⟩)

theorem pr_more : Spec.pr_more := fun D _ _ _ S => prRho_cylSnd [askRound D] S

/-! ## Batches, and the compiler's form -/

section Batch
variable {X Wt : Type} {E : ExtSpec}

theorem dview_eq {Q : InteractiveOracleProof X E} {a b : DView Q} (h1 : a.plains = b.plains)
    (h2 : a.ext = b.ext) (h3 : a.orc = b.orc) : a = b := by
  cases a
  cases b
  cases h1
  cases h2
  cases h3
  rfl

open Classical in
theorem dviewT_more {R : IOR X E Unit extNone} {plan : D → Finset (OPos R.shape)} (m : Unit × Unit)
    (d : D) (τ : Tr R.shape) (T : Finset (OPos (askRound D :: R.shape))) (y : E.Str) :
    (R.more D plan).dviewT T y ((m, d, τ) : (Unit × Unit) × D × Tr R.shape) =
      DView.more plan (R.dviewT (plan d ∪ OPos.tail T) y τ) := by
  refine dview_eq rfl ?_ (funext fun (p : Empty ⊕ OPos R.shape) => ?_)
  · show E.ans ((R.more D plan).given ((d, τ.rho) : D × Rho R.shape) T) y =
      E.ans (R.given τ.rho (plan d ∪ OPos.tail T)) y
    rw [given_more]
  · rcases p with e | p
    · exact e.elim
    · exact if_congr (shown_more d τ.rho T p) rfl rfl

end Batch

open Classical in
theorem outputT_more : Spec.outputT_more := by
  intro X Wt E Q D _ _ plan H N w x v ρ J Ts
  unfold BIOP.outputT
  rw [PMF.map_comp]
  refine congrArg (fun f => (unif (H.Coin0 × (Fin N → H.Coin))).map f)
    (funext fun c => funext fun j => ?_)
  show (match x j with
    | none => none
    | some xj => if ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape) ∈
          (Q.moreHonest H plan).one.withheld w xj then none
        else
          some ((Q.ior.more D plan).dviewT (Ts j) (H.ext w)
              (((Q.moreHonest H plan).one.strat w xj (c.1, c.2 j)).run
                ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape)).1))
    = Option.map (DView.more plan) (match x j with
    | none => none
    | some xj => if ρ.slot j.1 ∈ H.one.withheld w xj then none
        else
          some (Q.ior.dviewT (plan (v j.1) ∪ OPos.tail (Ts j)) (H.ext w)
              ((H.one.strat w xj (c.1, c.2 j)).run (ρ.slot j.1)).1))
  cases x j with
  | none => rfl
  | some xj =>
    by_cases h : ρ.slot j.1 ∈ H.one.withheld w xj
    · have h' : ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape) ∈
          (Q.moreHonest H plan).one.withheld w xj := h
      simp only [if_pos h, if_pos h']
      rfl
    · have h' : ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape) ∉
          (Q.moreHonest H plan).one.withheld w xj := h
      simp only [if_neg h, if_neg h']
      exact congrArg some
        (dviewT_more ((), ()) (v j.1)
          ((H.one.strat w xj (c.1, c.2 j)).run (ρ.slot j.1)).1 (Ts j) (H.ext w))

open Classical in
theorem exactT_more : Spec.exactT_more := by
  intro X Wt E Q D _ _ plan H N valid bud S hS w x hv J xs hxs ρ hH Ts hb
  obtain ⟨v, ρ⟩ : (Fin N → D) × BRho N Q.ior.shape Q.ann := ρ
  have h1 := hS w x hv J xs hxs ρ hH (fun j => plan (v j.1) ∪ OPos.tail (Ts j)) hb
  rw [outputT_more, h1]
  have e : (Q.more plan).ansJ J (fun j => ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape)) Ts (H.ext w)
      = Q.ansJ J (fun j => ρ.slot j.1) (fun j => plan (v j.1) ∪ OPos.tail (Ts j)) (H.ext w) := by
    funext p
    unfold BIOP.ansJ
    exact if_congr (exists_congr fun j => by
      show p ∈ (Q.ior.more D plan).given ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape) (Ts j) ↔ _
      rw [given_more]) rfl rfl
  show _ = (S J xs (fun j => ρ.slot j.1) (fun j => plan (v j.1) ∪ OPos.tail (Ts j))
        ((Q.more plan).ansJ J
          (fun j => ((v j.1, ρ.slot j.1) : D × Rho Q.ior.shape)) Ts (H.ext w))).map
      fun o => fun j => (o j).map (DView.more plan)
  rw [e]

theorem OPos.tail_empty {s : Shape} : OPos.tail (∅ : Finset (OPos (askRound D :: s))) = ∅ :=
  Finset.preimage_empty

open Classical in
/-- The budget of R.more bears "no further reads" if R's budget bears every plan. -/
theorem IOR.budMore_empty {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (plan : D → Finset (OPos R.shape)) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
    (hb : ∀ d ρ, bud ρ (plan d)) (ρ : Rho (R.more D plan).shape) : IOR.budMore R plan bud ρ ∅ := by
  obtain ⟨d, ρ⟩ : D × Rho R.shape := ρ
  show bud ρ (plan d ∪ OPos.tail ∅)
  rw [OPos.tail_empty, Finset.union_empty]
  exact hb d ρ

open Classical in
theorem IOR.tied_more_union {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (plan : D → Finset (OPos R.shape)) (ρ : Rho (R.more D plan).shape) :
    ((R.more D plan).reads ρ).biUnion ((R.more D plan).tie ρ) ⊆ (R.more D plan).extReads ρ :=
  Finset.biUnion_subset.2 fun p hp => tied_more _ _ _ _ R D plan ρ p hp

open Classical in
theorem BIOP.budMore_empty {X : Type} {E : ExtSpec} (Q : BIOP X E)
    (plan : D → Finset (OPos Q.ior.shape)) {N : ℕ} (bud : BudB Q.ior.shape N)
    (hb : ∀ (J : Finset (Fin N)) (ρs : J → Rho Q.ior.shape) (ds : J → D),
      bud J ρs fun j => plan (ds j))
    (J : Finset (Fin N)) (ρs : J → Rho (Q.more plan).ior.shape) :
    Q.budMore plan bud J ρs fun _ => ∅ := by
  show bud J (fun j => (ρs j : D × Rho Q.ior.shape).2)
    (fun j => plan (ρs j : D × Rho Q.ior.shape).1 ∪ OPos.tail ∅)
  simp only [OPos.tail_empty, Finset.union_empty]
  exact hb J _ fun j => (ρs j : D × Rho Q.ior.shape).1

open Classical in
theorem hvzk_more : Spec.hvzk_more := by
  intro X Wt Wi E R D _ _ plan H ext inp valid Ri bud z hE hb hv hz
  obtain ⟨S, hS⟩ := hE
  refine hvzk_toProto X Wt Wi E (R.more D plan) (H.more plan) ext inp valid Ri
    (IOR.budMore R plan bud) z ⟨_, exact_more _ _ _ _ _ _ R D plan H Ri bud S hS⟩ ?_ ?_ hv ?_
  · intro ρ
    obtain ⟨d, ρ⟩ : D × Rho R.shape := ρ
    show bud ρ (plan d ∪ OPos.tail ∅)
    rw [OPos.tail_empty, Finset.union_empty]
    exact hb d ρ
  · exact fun ρ => Finset.biUnion_subset.2 fun p hp => tied_more _ _ _ _ R D plan ρ p hp
  · exact fun w x h => le_trans (le_of_eq (pr_more D R.shape (H.Hid (inp w x) x))) (hz w x h)

open Classical in
theorem hvzkB_more : Spec.hvzkB_more := by
  intro X Wt E Q D _ _ plan H N valid bud z hE hb hz
  obtain ⟨S, hS⟩ := hE
  refine hvzk_of_exactT X Wt E (Q.more plan) (Q.moreHonest H plan) N valid (Q.budMore plan bud) z
    ⟨_, exactT_more _ _ _ Q D plan H N valid bud S hS⟩ ?_ (tied_more _ _ _ _ Q.ior D plan) ?_
  · intro J ρs
    show bud J (fun j => (ρs j : D × Rho Q.ior.shape).2)
      (fun j => plan (ρs j : D × Rho Q.ior.shape).1 ∪ OPos.tail ∅)
    simp only [OPos.tail_empty, Finset.union_empty]
    exact hb J _ fun j => (ρs j : D × Rho Q.ior.shape).1
  · exact fun w x h => le_trans (le_of_eq (pr_more D Q.ior.shape (H.one.Hid w x))) (hz w x h)

end Iop
