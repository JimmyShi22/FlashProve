-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldIsRowProof.lean: the very fold is the row: the proof of `FoldIsRow`
(Johnson/Desc/Sound/ChainRule.lean), and with it of `ChainRule` and `ChainRuleAt`.

The road. `rowJoin`: a row's transcript as one of the chain's own written rounds, made by
`Fo.Peel.joinR`, stretch by stretch; it is the transcript itself (`rowJoin_heq`), so it is what the
sheet's cast gives (`cast_eq_rowJoin`). `foldIsRow_join`: by induction on the row: at each border
the stage is cut (`stage_cut`, StageCut.lean) and the fold is cut (`foldRun_cons`,
FoldLawBlock.lean).

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StageCut
import Johnson.Desc.Sound.FoldLawBlock
import Johnson.Desc.Sound.ChainRuleProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- The first entry that passes a test, from the list of all that pass. -/
theorem find_of_filter (P : LeftT → Bool) (v : ℕ) : ∀ l : List LeftT,
    (l.filter P).map (·.a) = [v] → (l.find? P).map (·.a) = some v
  | [], h => by simp at h
  | x :: xs, h => by
    by_cases hP : P x = true
    · simp [hP] at h
      simp [hP, h.1]
    · simp [hP] at h
      simp [hP, find_of_filter P v xs (by simpa using h)]

theorem Piece.listedAt (p : Piece C F S Cl W) (h : p.Listed) : ListedAt F p.base p.ds :=
  fun n sh hs => find_of_filter _ _ _ (h.1 n sh hs)

theorem Piece.opensBelow (p : Piece C F S Cl W) (h : p.Listed) : OpensBelow p.base p.ds := h.2

/-- The name of a chain is in a refusal's words alone. -/
theorem foldRun_name (F : Frame) (n n' : String) (bs : List (Block S Cl)) (back : List Fmt.RoundView) :
    foldRun F n bs back = foldRun F n' bs back := by
  funext s v
  simp only [foldRun, chainAt_toOption]

theorem app_unit_heq : ∀ (s : Shape) (τ : Iop.Tr s), HEq (Iop.Tr.app (t := []) τ ()) τ
  | [], _ => HEq.rfl
  | _ :: s, (m, c, τ) => heq_consR (List.append_nil s) m c _ _ (app_unit_heq s τ)

theorem app_heq {s t t' : Shape} (h : t = t') (a : Iop.Tr s) (u : Iop.Tr t) (v : Iop.Tr t')
    (huv : HEq u v) : HEq (Iop.Tr.app a u) (Iop.Tr.app a v) := by
  subst h
  rw [eq_of_heq huv]

/-- A row's transcript as one of the chain's own written rounds. -/
def rowJoin : (p : Piece C F S Cl W) → (l : List (Piece C F S Cl W)) →
    Iop.Tr (rowIOR p l).shape → Iop.Tr (uLT C (rowData p l))
  | p, [], τ => joinR C p.ds [] τ ()
  | p, q :: l, τ =>
    joinR C p.ds (rowData q l) (Iop.Tr.fst (s := uLT C p.ds) (t := (rowIOR q l).shape) τ)
      (rowJoin q l (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ))

theorem rowJoin_heq : ∀ (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (τ : Iop.Tr (rowIOR p l).shape), HEq (rowJoin p l τ) τ
  | p, [], τ => (joinR_heq C p.ds [] τ ()).trans (app_unit_heq _ τ)
  | p, q :: l, τ => by
    have h1 := joinR_heq C p.ds (rowData q l)
      (Iop.Tr.fst (s := uLT C p.ds) (t := (rowIOR q l).shape) τ)
      (rowJoin q l (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ))
    have h2 := app_heq (shapeIsChain S Cl W C F q l).symm
      (Iop.Tr.fst (s := uLT C p.ds) (t := (rowIOR q l).shape) τ) _ _
      (rowJoin_heq q l (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ))
    have h3 := Iop.Tr.app_fst_snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ
    exact (h1.trans h2).trans (heq_of_eq h3)

theorem cast_eq_rowJoin (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) (τ : Iop.Tr (rowIOR p l).shape) :
    (cast (congrArg Iop.Tr h) τ : Iop.Tr (uLT C (rowData p l))) = rowJoin p l τ :=
  eq_of_heq ((cast_heq _ _).trans (rowJoin_heq p l τ).symm)

/-- A stage hangs on its data and its transcript alone. -/
theorem stage_congr (b : ℕ) (r : S → Fmt.View → Option S) (a : S × F.E.Str) (xs ys : List RDT)
    (e : xs = ys) (τ : Iop.Tr (uLT C xs)) (τ' : Iop.Tr (uLT C ys)) (h : HEq τ τ') :
    (stageIOR C (stg F b xs) r).red.out a τ = (stageIOR C (stg F b ys) r).red.out a τ' := by
  subst e
  rw [eq_of_heq h]

/-- The fold's own law at three views of which the first is the other two in a row. -/
theorem foldRun_views (F : Frame) (name : String) (b : Block S Cl) (bs : List (Block S Cl))
    (back : List Fmt.RoundView) (s : S) (v v₁ v₂ : Fmt.View) (hr : v.rounds = v₁.rounds ++ v₂.rounds)
    (ho : v.opened = v₁.opened ++ v₂.opened) (hne : bs ≠ [])
    (hlen : v₁.rounds.length = b.rounds.length)
    (hc : ((b.reads F.ft (v₁.rounds.map (·.drawn))).flatMap id).length = v₁.opened.length) :
    foldRun F name (b :: bs) back s v =
      (foldRun F b.name [b] [] s v₁).bind fun s' => foldRun F name bs back s' v₂ := by
  obtain ⟨r, o⟩ := v
  obtain ⟨r₁, o₁⟩ := v₁
  obtain ⟨r₂, o₂⟩ := v₂
  simp only at hr ho hlen hc
  subst hr
  subst ho
  exact foldRun_cons F name b bs back s r₁ r₂ o₁ o₂ hne hlen hc

/-- One border: the very fold through a stage over a piece's stretch and a further stretch is the
piece's own reduction, then the very fold of the other blocks through a stage over the further
stretch. -/
theorem fold_stage_cut (name : String) (p : Piece C F S Cl W) (bs : List (Block S Cl))
    (hne : bs ≠ []) (back : List Fmt.RoundView) (es : List RDT) (hOw : p.Owed) (hLi : p.Listed)
    (hb : p.back = []) (s : S) (y : F.E.Str) (π : Iop.Tr (uLT C p.ds)) (σ : Iop.Tr (uLT C es)) :
    (stageIOR C (stg F p.base (p.ds ++ es)) (foldRun F name (p.b :: bs) back)).red.out (s, y)
        (joinR C p.ds es π σ) =
      (p.ior.red.out (s, y) π).bind fun a' =>
        (stageIOR C (stg F (p.base + nTrees p.ds) es) (foldRun F name bs back)).red.out a' σ := by
  have e3 : p.ior.red.out (s, y) π =
      (stageIOR C (stg F p.base p.ds) (foldRun F p.b.name [p.b] [])).red.out (s, y) π := by
    show (stageIOR C (stg F p.base p.ds) (foldRun F p.b.name [p.b] p.back)).red.out (s, y) π = _
    rw [hb]
  have hlen : (sView C (stg F p.base p.ds) y π).rounds.length = p.b.rounds.length := by
    have t := hOw.1
    rw [hb] at t
    exact (rvT_length C p.ds π).trans t
  have hc := hOw.2 y π
  rw [hb, List.append_nil] at hc
  rw [e3]
  exact stage_cut C F p.base (p.listedAt hLi) (p.opensBelow hLi) _ _ _ s y π σ
    (foldRun_views F name p.b bs back s _ _ _ (sView_rounds_join C F p.base y _ π σ)
      (sView_opened_join C F p.base (p.listedAt hLi) (p.opensBelow hLi) y π σ) hne hlen hc)

theorem rowData_cons (p q : Piece C F S Cl W) (l : List (Piece C F S Cl W)) :
    rowData p (q :: l) = p.ds ++ rowData q l := rfl

theorem rowBack_cons (p q : Piece C F S Cl W) (l : List (Piece C F S Cl W)) :
    rowBack p (q :: l) = rowBack q l := rfl

/-- The very fold is the row, at the joined transcript. -/
theorem foldIsRow_join (name : String) : ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W),
    Tiled p l → ∀ (a : S × F.E.Str) (τ : Iop.Tr (rowIOR p l).shape),
      (chainIOR C F name ((p :: l).map (·.b)) p.base (rowData p l) (rowBack p l)).red.out a
        (rowJoin p l τ) = (rowIOR p l).red.out a τ
  | [], p, _, a, τ => by
    show (stageIOR C (stg F p.base (p.ds ++ [])) (foldRun F name [p.b] p.back)).red.out a
        (joinR C p.ds [] τ ()) =
      (stageIOR C (stg F p.base p.ds) (foldRun F p.b.name [p.b] p.back)).red.out a τ
    rw [foldRun_name F name p.b.name]
    exact stage_congr p.base _ a _ _ (List.append_nil _) _ _ (rowJoin_heq p [] τ)
  | q :: l, p, ht, (s, y), τ => by
    obtain ⟨hOw, hLi, hb, hq, ht'⟩ := ht
    have hq' : q.base = p.base + nTrees p.ds := hq
    have k := fold_stage_cut name p ((q :: l).map (·.b)) (List.cons_ne_nil _ _) (rowBack q l)
      (rowData q l) hOw hLi hb s y (Iop.Tr.fst (s := uLT C p.ds) (t := (rowIOR q l).shape) τ)
      (rowJoin q l (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ))
    have hf : (fun a' : S × F.E.Str =>
        (stageIOR C (stg F (p.base + nTrees p.ds) (rowData q l))
          (foldRun F name ((q :: l).map (·.b)) (rowBack q l))).red.out a'
          (rowJoin q l (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ))) =
        fun a' => (rowIOR q l).red.out a'
          (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ) := by
      funext a'
      have ih := foldIsRow_join name l q ht' a'
        (Iop.Tr.snd (s := uLT C p.ds) (t := (rowIOR q l).shape) τ)
      rw [hq'] at ih
      exact ih
    rw [hf] at k
    exact k.trans (IOR.red_seq_out p.ior (rowIOR q l) (s, y) τ).symm

theorem foldIsRow : FoldIsRow := by
  intro S Cl W C F name p l h ht a τ
  show (chainIOR C F name ((p :: l).map (·.b)) p.base (rowData p l) (rowBack p l)).red.out a
      (cast (congrArg Iop.Tr h) τ : Iop.Tr (uLT C (rowData p l))) = _
  rw [cast_eq_rowJoin p l h τ]
  exact foldIsRow_join name l p ht a τ

/-- **The rule of composition at one chain, of the very fold.** -/
theorem chainRule : ChainRule := chainRule_of foldIsRow

theorem chainRuleAt : ChainRuleAt := chainRuleAt_of chainRule

end VerifiableInference.Desc.Sound
