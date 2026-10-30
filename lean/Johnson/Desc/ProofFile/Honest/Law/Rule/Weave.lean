-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Weave.lean: the blocks of coins that a list of the book's
entries cuts from their owners' coins (Honest/Frame.lean: `Ahead`, `lend`, `cutAll`), as one tuple
(`runs`); that tuple cut by owner; and a lemma (`runs_afresh`): if, owner by owner, the blocks of
one owner are as drawn afresh beside the other owners' blocks and a given function `W` of the coins,
then the whole tuple is as drawn afresh beside W. Honest/Law/Rule/Kit.lean says what equation "as
drawn afresh" stands for. No part, no run of a protocol and no description occurs here.

Why. `lend` gives a part its blocks by spender, in the book's order, whoever owns them; `cutAll`
cuts blocks from one owner's coins. A condition on an owner speaks of the second; a condition on a
spender of the first.

  1  `CsAll.hd`, `CsAll.tl`, `CsAll.cons`, `CsAll.hd_cons`, `CsAll.tl_cons`, `CsAll.cons_hd_tl`   a
     tuple's first entry, the others, and back
  2  `runs`, `lend_runs`, `runs_congr`, `runs_one`   the tuple, as an option; it is what `lend`
     gives at the entries' own names and counts; it reads the coins through the cuts alone; where
     all entries have one owner it is `cutAll`
  3  `Weave`, `Weave.join`, `Weave.split`, `Weave.split_join`, `Weave.join_split`, `Weave.equiv`,
     `runs_weave`, `Weave.byOwner`   a list of entries as two lists woven into each other; the
     blocks of the woven list are the two lists' blocks, woven in the same way; a list cut by one
     owner
  4  `afresh_sub`, `runs_afresh`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Johnson.Desc.ProofFile.Honest.Law.Rule.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob

/-! ## 1 A tuple's entries -/

section
variable {d : String × Due} {ds : List (String × Due)}

/- The first block of a non-empty list of blocks. -/
def CsAll.hd (c : CsAll (d :: ds)) : Cs d.2 := (show Cs d.2 × CsAll ds from c).1
/- The other blocks. -/
def CsAll.tl (c : CsAll (d :: ds)) : CsAll ds := (show Cs d.2 × CsAll ds from c).2
/- A block in front of a list of blocks. -/
def CsAll.cons (x : Cs d.2) (t : CsAll ds) : CsAll (d :: ds) := (x, t)

theorem CsAll.hd_cons (x : Cs d.2) (t : CsAll ds) : (CsAll.cons x t).hd = x := rfl
theorem CsAll.tl_cons (x : Cs d.2) (t : CsAll ds) : (CsAll.cons x t).tl = t := rfl
theorem CsAll.cons_hd_tl (c : CsAll (d :: ds)) : CsAll.cons c.hd c.tl = c := rfl

end

/-! ## 2 The blocks of a list of entries -/

/-- **The blocks that entries cut from their owners' coins**, entry by entry; `none` where a block
is not within its owner's count. `look`: coins, by address. -/
def runs (look : Addr → (d : Due) × Cs d) : (es : List Ahead) → Option (CsAll (es.map Ahead.named))
  | [] => some ()
  | e :: es => ((look e.owner).2.cut e.start e.count).bind fun x =>
      (runs look es).map fun y => (x, y)

/-- It is what `lend` gives, at the entries' own names and counts. -/
theorem lend_runs (look : Addr → (d : Due) × Cs d) : ∀ es : List Ahead,
    (lend look (es.map Ahead.named) es).toOption = runs look es
  | [] => rfl
  | e :: es => by
    have ih := lend_runs look es
    show (lend look (e.named :: es.map Ahead.named) (e :: es)).toOption = _
    simp only [lend, runs, Ahead.named, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    cases h : (look e.owner).2.cut e.start e.count with
    | none => rfl
    | some x =>
      rw [← ih]
      cases lend look (es.map Ahead.named) es <;> rfl

/-- It reads the coins through the cuts alone. -/
theorem runs_congr (look look' : Addr → (d : Due) × Cs d) : ∀ es : List Ahead,
    (∀ e ∈ es, (look e.owner).2.cut e.start e.count = (look' e.owner).2.cut e.start e.count) →
    runs look es = runs look' es
  | [], _ => rfl
  | e :: es, h => by
    show ((look e.owner).2.cut e.start e.count).bind (fun x => (runs look es).map fun y => (x, y)) =
      ((look' e.owner).2.cut e.start e.count).bind fun x => (runs look' es).map fun y => (x, y)
    rw [h e (List.mem_cons_self ..),
      runs_congr look look' es fun t ht => h t (List.mem_cons_of_mem _ ht)]

/-- Where all entries have one owner, it is `cutAll` of that owner's coins. -/
theorem runs_one (look : Addr → (d : Due) × Cs d) (o : Addr) : ∀ es : List Ahead,
    (∀ e ∈ es, e.owner = o) → runs look es = cutAll (look o).2 es
  | [], _ => rfl
  | e :: es, h => by
    have ho : e.owner = o := h e (List.mem_cons_self ..)
    show ((look e.owner).2.cut e.start e.count).bind (fun x => (runs look es).map fun y => (x, y)) =
      ((look o).2.cut e.start e.count).bind fun x => (cutAll (look o).2 es).map fun y => (x, y)
    rw [ho, runs_one look o es fun t ht => h t (List.mem_cons_of_mem _ ht)]

/-! ## 3 Two lists woven into each other -/

/-- E is es and rest woven into each other, each in its own order. -/
inductive Weave : List Ahead → List Ahead → List Ahead → Type
  | nil : Weave [] [] []
  | left (e : Ahead) {E es rest : List Ahead} (w : Weave E es rest) : Weave (e :: E) (e :: es) rest
  | right (e : Ahead) {E es rest : List Ahead} (w : Weave E es rest) : Weave (e :: E) es (e :: rest)

/-- The two tuples woven in the same way. -/
def Weave.join : {E es rest : List Ahead} → Weave E es rest → CsAll (es.map Ahead.named) →
    CsAll (rest.map Ahead.named) → CsAll (E.map Ahead.named)
  | _, _, _, .nil, _, _ => ()
  | _, _, _, @Weave.left e E es _ w, a, b =>
    CsAll.cons (d := e.named) (ds := E.map Ahead.named)
      (CsAll.hd (d := e.named) (ds := es.map Ahead.named) a)
      (w.join (CsAll.tl (d := e.named) (ds := es.map Ahead.named) a) b)
  | _, _, _, @Weave.right e E _ rest w, a, b =>
    CsAll.cons (d := e.named) (ds := E.map Ahead.named)
      (CsAll.hd (d := e.named) (ds := rest.map Ahead.named) b)
      (w.join a (CsAll.tl (d := e.named) (ds := rest.map Ahead.named) b))

/-- The inverse. -/
def Weave.split : {E es rest : List Ahead} → Weave E es rest → CsAll (E.map Ahead.named) →
    CsAll (es.map Ahead.named) × CsAll (rest.map Ahead.named)
  | _, _, _, .nil, _ => ((), ())
  | _, _, _, @Weave.left e E es _ w, c =>
    (CsAll.cons (d := e.named) (ds := es.map Ahead.named)
        (CsAll.hd (d := e.named) (ds := E.map Ahead.named) c)
        (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).1,
      (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).2)
  | _, _, _, @Weave.right e E _ rest w, c =>
    ((w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).1,
      CsAll.cons (d := e.named) (ds := rest.map Ahead.named)
        (CsAll.hd (d := e.named) (ds := E.map Ahead.named) c)
        (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).2)

theorem Weave.split_join : ∀ {E es rest : List Ahead} (w : Weave E es rest)
    (a : CsAll (es.map Ahead.named)) (b : CsAll (rest.map Ahead.named)),
    w.split (w.join a b) = (a, b)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, @Weave.left e E es _ w, a, b => by
    have ih := Weave.split_join w (CsAll.tl (d := e.named) (ds := es.map Ahead.named) a) b
    show (CsAll.cons (d := e.named) (ds := es.map Ahead.named)
        (CsAll.hd (d := e.named) (ds := es.map Ahead.named) a)
        (w.split (w.join (CsAll.tl (d := e.named) (ds := es.map Ahead.named) a) b)).1,
      (w.split (w.join (CsAll.tl (d := e.named) (ds := es.map Ahead.named) a) b)).2) = (a, b)
    rw [ih]
    rfl
  | _, _, _, @Weave.right e E _ rest w, a, b => by
    have ih := Weave.split_join w a (CsAll.tl (d := e.named) (ds := rest.map Ahead.named) b)
    show ((w.split (w.join a (CsAll.tl (d := e.named) (ds := rest.map Ahead.named) b))).1,
      CsAll.cons (d := e.named) (ds := rest.map Ahead.named)
        (CsAll.hd (d := e.named) (ds := rest.map Ahead.named) b)
        (w.split (w.join a (CsAll.tl (d := e.named) (ds := rest.map Ahead.named) b))).2) = (a, b)
    rw [ih]
    rfl

theorem Weave.join_split : ∀ {E es rest : List Ahead} (w : Weave E es rest)
    (c : CsAll (E.map Ahead.named)), w.join (w.split c).1 (w.split c).2 = c
  | _, _, _, .nil, _ => rfl
  | _, _, _, @Weave.left e E es _ w, c => by
    have ih := Weave.join_split w (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)
    show CsAll.cons (d := e.named) (ds := E.map Ahead.named)
      (CsAll.hd (d := e.named) (ds := E.map Ahead.named) c)
      (w.join (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).1
        (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).2) = c
    rw [ih]
    rfl
  | _, _, _, @Weave.right e E _ rest w, c => by
    have ih := Weave.join_split w (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)
    show CsAll.cons (d := e.named) (ds := E.map Ahead.named)
      (CsAll.hd (d := e.named) (ds := E.map Ahead.named) c)
      (w.join (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).1
        (w.split (CsAll.tl (d := e.named) (ds := E.map Ahead.named) c)).2) = c
    rw [ih]
    rfl

/-- The whole tuple, as the pair of the two. -/
def Weave.equiv {E es rest : List Ahead} (w : Weave E es rest) :
    CsAll (E.map Ahead.named) ≃ CsAll (es.map Ahead.named) × CsAll (rest.map Ahead.named) where
  toFun := w.split
  invFun := fun p => w.join p.1 p.2
  left_inv := w.join_split
  right_inv := fun p => w.split_join p.1 p.2

/-- The blocks of the woven list are the two lists' blocks, woven in the same way. -/
theorem runs_weave (look : Addr → (d : Due) × Cs d) : ∀ {E es rest : List Ahead}
    (w : Weave E es rest),
    runs look E = (runs look es).bind fun a => (runs look rest).map fun b => w.join a b
  | _, _, _, .nil => rfl
  | _, _, _, @Weave.left e E es rest w => by
    have ih := runs_weave look w
    show ((look e.owner).2.cut e.start e.count).bind (fun x => (runs look E).map fun y => (x, y)) =
      (((look e.owner).2.cut e.start e.count).bind fun x =>
        (runs look es).map fun y => (x, y)).bind fun a =>
          (runs look rest).map fun b => (Weave.left e w).join a b
    rw [ih]
    cases (look e.owner).2.cut e.start e.count with
    | none => rfl
    | some x =>
      cases runs look es with
      | none => rfl
      | some a =>
        cases runs look rest with
        | none => rfl
        | some b => rfl
  | _, _, _, @Weave.right e E es rest w => by
    have ih := runs_weave look w
    show ((look e.owner).2.cut e.start e.count).bind (fun x => (runs look E).map fun y => (x, y)) =
      (runs look es).bind fun a =>
        (((look e.owner).2.cut e.start e.count).bind fun x =>
          (runs look rest).map fun y => (x, y)).map fun b => (Weave.right e w).join a b
    rw [ih]
    cases (look e.owner).2.cut e.start e.count with
    | none =>
      cases runs look es <;> rfl
    | some x =>
      cases runs look es with
      | none => rfl
      | some a =>
        cases runs look rest with
        | none => rfl
        | some b => rfl

/-- A list cut by one owner: what that owner has in it, and the rest. -/
theorem Weave.byOwner (o : Addr) : ∀ E : List Ahead, ∃ rest : List Ahead,
    Nonempty (Weave E (E.filter fun t => t.owner == o) rest) ∧ (∀ t ∈ rest, t.owner ≠ o) ∧
      rest.length + (E.filter fun t => t.owner == o).length = E.length ∧
      ∀ o', o' ≠ o → (rest.filter fun t => t.owner == o') = E.filter fun t => t.owner == o'
  | [] => ⟨[], ⟨.nil⟩, fun _ h => (by cases h), rfl, fun _ _ => rfl⟩
  | e :: E => by
    obtain ⟨rest, ⟨w⟩, h1, h2, h3⟩ := Weave.byOwner o E
    by_cases h : e.owner = o
    · have e1 : ((e :: E).filter fun t => t.owner == o) = e :: E.filter fun t => t.owner == o := by
        simp [h]
      refine ⟨rest, ?_, h1, ?_, ?_⟩
      · rw [e1]
        exact ⟨.left e w⟩
      · rw [e1]
        simp only [List.length_cons]
        omega
      · intro o' ho'
        have e2 : ((e :: E).filter fun t => t.owner == o') = E.filter fun t => t.owner == o' := by
          have : ¬ o = o' := fun hh => ho' hh.symm
          simp [h, this]
        rw [e2]
        exact h3 o' ho'
    · have e1 : ((e :: E).filter fun t => t.owner == o) = E.filter fun t => t.owner == o := by
        simp [h]
      refine ⟨e :: rest, ?_, ?_, ?_, ?_⟩
      · rw [e1]
        exact ⟨.right e w⟩
      · intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h
        · exact h1 t ht
      · rw [e1]
        simp only [List.length_cons]
        omega
      · intro o' ho'
        simp only [List.filter_cons]
        rw [h3 o' ho']

/-! ## 4 The main lemma -/

section
variable {K Ω : Type} [Fintype K] [Nonempty K]

/-- Beside an element of a type that has only one element. -/
theorem afresh_sub {U : Type} [Fintype U] [Nonempty U] (u : U) (hu : ∀ v : U, v = u) (W : K → Ω) :
    (unif K).map (fun k => (some u, W k)) = (unif (U × K)).map fun z => (some z.1, W z.2) := by
  have e : (fun z : U × K => (some z.1, W z.2)) = (fun k => (some u, W k)) ∘ Prod.snd :=
    funext fun z => by
      show (some z.1, W z.2) = (some u, W z.2)
      rw [hu z.1]
  have h : (unif (U × K)).map ((fun k => (some u, W k)) ∘ Prod.snd) =
      (unif K).map fun k => (some u, W k) := by
    rw [← PMF.map_comp, map_snd_unif]
  rw [e]
  exact h.symm

/-- **Owner by owner.** `look`: a run's coins, by address. `spent`: for each owner a list of
entries. `hstep`: the blocks that `spent o` cuts from o's coins are as drawn afresh beside the pair
(the blocks of any list of other owners' entries, W). Then the blocks of a list E, which holds of
each owner either no entry or exactly `spent o`, in order, are as drawn afresh beside W. -/
theorem runs_afresh (look : K → Addr → (d : Due) × Cs d) (W : K → Ω) (spent : Addr → List Ahead)
    (hstep : ∀ (o : Addr) (rest : List Ahead), (∀ e ∈ rest, e.owner ≠ o) →
      (unif K).map (fun k => (cutAll (look k o).2 (spent o), (runs (look k) rest, W k))) =
        (unif (CsAll ((spent o).map Ahead.named) × K)).map fun z =>
          (some z.1, (runs (look z.2) rest, W z.2))) :
    ∀ (n : Nat) (E : List Ahead), E.length ≤ n →
      (∀ o, (E.filter fun t => t.owner == o) = [] ∨ (E.filter fun t => t.owner == o) = spent o) →
      (unif K).map (fun k => (runs (look k) E, W k)) =
        (unif (CsAll (E.map Ahead.named) × K)).map fun z => (some z.1, W z.2)
  | _, [], _, _ =>
    afresh_sub (U := CsAll (([] : List Ahead).map Ahead.named)) () (fun _ => rfl) W
  | 0, _ :: _, h, _ => absurd h (by simp)
  | n + 1, e :: E', hn, hE => by
    have hne : ((e :: E').filter fun t => t.owner == e.owner) ≠ [] := by
      simp
    have hes : ((e :: E').filter fun t => t.owner == e.owner) = spent e.owner :=
      (hE e.owner).resolve_left hne
    obtain ⟨rest, ⟨w₀⟩, hro, hsum, hfil⟩ := Weave.byOwner e.owner (e :: E')
    have hpos : 0 < ((e :: E').filter fun t => t.owner == e.owner).length := by
      cases hf : ((e :: E').filter fun t => t.owner == e.owner) with
      | nil => exact absurd hf hne
      | cons _ _ => simp
    have hlen : rest.length ≤ n := by omega
    rw [hes] at w₀
    have hrE : ∀ o, (rest.filter fun t => t.owner == o) = [] ∨
        (rest.filter fun t => t.owner == o) = spent o := by
      intro o
      by_cases ho : o = e.owner
      · left
        rw [List.filter_eq_nil_iff]
        intro t ht hc
        exact hro t ht ((beq_iff_eq.1 hc).trans ho)
      · rw [hfil o ho]
        exact hE o
    have h1 := hstep e.owner rest hro
    have h2 := runs_afresh look W spent hstep n rest hlen hrE
    have h3 := Kit.afresh_pair (X := fun k => cutAll (look k e.owner).2 (spent e.owner))
      (Y := fun k => runs (look k) rest) (W := W) (ι := some) (κ := some) h1 h2
    have h4 := Kit.afresh_map (X := fun k => (cutAll (look k e.owner).2 (spent e.owner),
        runs (look k) rest)) (ι := fun z : CsAll ((spent e.owner).map Ahead.named) ×
        CsAll (rest.map Ahead.named) => (some z.1, some z.2)) (W := W) h3
      (fun t => (t.1.1.bind fun a => t.1.2.map fun b => w₀.join a b, t.2))
    have hL : ∀ k, runs (look k) (e :: E') =
        (cutAll (look k e.owner).2 (spent e.owner)).bind fun a =>
          (runs (look k) rest).map fun b => w₀.join a b := by
      intro k
      have hown : ∀ t ∈ spent e.owner, t.owner = e.owner := by
        intro t ht
        rw [← hes] at ht
        exact beq_iff_eq.1 (List.mem_filter.1 ht).2
      rw [runs_weave (look k) w₀, runs_one (look k) e.owner (spent e.owner) hown]
    have h5 : (unif K).map (fun k => (runs (look k) (e :: E'), W k)) =
        (unif ((CsAll ((spent e.owner).map Ahead.named) × CsAll (rest.map Ahead.named)) × K)).map
          fun z => (some (w₀.join z.1.1 z.1.2), W z.2) :=
      (congrArg (fun f => (unif K).map f)
        (funext fun k => congrArg (fun r => (r, W k)) (hL k))).trans h4
    have h6 := Kit.afresh_equiv w₀.equiv (X := fun k => runs (look k) (e :: E')) (W := W)
      (ι := fun z : CsAll ((spent e.owner).map Ahead.named) × CsAll (rest.map Ahead.named) =>
        some (w₀.join z.1 z.2)) h5
    refine h6.trans ?_
    refine congrArg (fun f => (unif (CsAll ((e :: E').map Ahead.named) × K)).map f)
      (funext fun z => ?_)
    show (some (w₀.join (w₀.split z.1).1 (w₀.split z.1).2), W z.2) = (some z.1, W z.2)
    rw [w₀.join_split]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.CsAll.hd_cons
#print axioms ProofFile.Honest.CsAll.tl_cons
#print axioms ProofFile.Honest.CsAll.cons_hd_tl
#print axioms ProofFile.Honest.lend_runs
#print axioms ProofFile.Honest.runs_congr
#print axioms ProofFile.Honest.runs_one
#print axioms ProofFile.Honest.Weave.split_join
#print axioms ProofFile.Honest.Weave.join_split
#print axioms ProofFile.Honest.Weave.byOwner
#print axioms ProofFile.Honest.runs_weave
#print axioms ProofFile.Honest.afresh_sub
#print axioms ProofFile.Honest.runs_afresh
