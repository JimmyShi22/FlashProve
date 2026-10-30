-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlannedAtDraw.lean: AT THE PROOF FILE's SEAT, AT EVERY STATE THAT IS
REACHED IN FRONT OF THE APPROXIMATE RANGE PROOF's DRAW OF LINK l, AND ON TO THE LINK's BATCHING:
EVERY «PLANNED» READING OF THAT PROOF's STRUCTURE IN THE VERIFIER's STATE HAS THE VALUE THAT IT HAS
AT THE BUILT LINK's OWN PLANNED STRUCTURE. General in the reading. Definitions and theorems. It
changes no other file.

Why. `k8LaidOwn` (Johnson/P1K8R/FrontAtSeat.lean) says it of seven fields
(`Ready.seven`). The link's table and the batching's law read planned fields beside these (the
number of combinations, the number of blocks, the pieces of the two lookups on the digits). The
three arms here are `own_head`, `own_layers`, `own_att`, step for step, with the reading
as a letter; what the step behind the reads' sending lays is read off
`layers_lays_tl`, `head_lays_tl` (Johnson/Desc/First/K8/LawCondText.lean) and `attO_yes_tree`
(LawCondAtt.lean), which give the WHOLE structure but for the list of tables and its mark.

  `Planned g`: g reads none of: the four fields that the lookup on the digits lays (`Keeps4`) · the
    drawn matrix (`KeepsDraw`) · the list of tables and its mark «closed» · the mark «closed» with
    the count of drawn folds, as an attention link's frame resets them. At a written g each is rfl.
  `reads_makes`: behind a yes of the block at the place of the reads' sending: at a layers' link
    readTl g is some (g hp.tl), hp the group's plan; at the head's some (g G.W.H.tl); at an
    attention link it is as it was.
  `planned_head`, `planned_layers`, `planned_att`, `planned_at_place`: along the fold from the first
    state, at the 25 numbers of `places`: ∃ tlP, PlanAt W l tlP ∧ readTl g = some (g tlP).
  `planned_at_draw`: **Reach 0 c.blocksInOrder (startS Z) (14 l + i + 2) a · built[l]? = some Xl ⊢
    readTl g a.2 = some (g Xl.tl).**
  `planned_at_batch`: **the same at 14 l + i + 3 + n: the batching's entry's number.**
Limits. In scope, at secondHashFunction alone. The batching's own step and the runs behind it are not treated.
No member: that a state is reached there is shown of no proof. Nothing on soundness.

-/
import Johnson.P1K8R.FrontAtSeat
import Johnson.Desc.First.Link.Law.PlannedToBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8 (readTl Keeps4 theStated_leaves_tl)
open VerifiableInference.Desc.First.K8.Ready (quiet_arms layers_lays_tl head_lays_tl attO_yes_tree)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- A reading of the planned fields alone. -/
structure Planned {α : Type} (g : HTailF2 → α) : Prop where
  four : Keeps4 g
  draw : KeepsDraw g
  funs : ∀ (tl : HTailF2) (c : Bool) (f : Array HFun),
    g { tl with funClosed := c, funs := f } = g tl
  reset : ∀ tl : HTailF2, g { tl with funClosed := false, foldDrawn := 0 } = g tl

section
variable {α : Type} {g : HTailF2 → α}

theorem read_of_tl {s : S} {tl : HTailF2} (h : s.tl? = some tl) : readTl g s = some (g tl) := by
  unfold readTl
  rw [h]
  rfl

/-- **Behind a yes of the block at the place of the reads' sending.** -/
theorem reads_makes (hg : Planned g) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (lk pr mo : Nat) (reads : Option (List Nat)) (nm : String) (G : ProofFile.Ground) (l : Nat)
    (X : LinkH) (piece : Nat) (n : String) (a : Place) (w : String) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hX : G.built[l]? = some X)
    (h : (Block.andThen nm (K1.laterAt q gp lk pr mo reads)
      (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs = .ok s') :
    (X.kind = 0 ∧ ∃ hp, G.W.G[X.g]? = some hp ∧ readTl g s' = some (g hp.tl)) ∨
      (X.kind = 2 ∧ readTl g s' = some (g G.W.H.tl)) ∨
      (X.kind = 1 ∧ readTl g s' = readTl g s) := by
  obtain ⟨m, hm, H⟩ := VerifiableInference.Desc.bindOk
    (x := (K1.laterAt q gp lk pr mo reads : Block S Unit).decide s
      (rs.take (K1.laterAt q gp lk pr mo reads : Block S Unit).rounds.length)
      (gs.take (K1.laterAt q gp lk pr mo reads : Block S Unit).openings)) h
  rcases quiet_arms G l X piece n a w H with ⟨h1, A, _, hd⟩ | ⟨_, Y, hY, hL | hH⟩
  · obtain ⟨tl, funs, t1, t2, _⟩ := attO_yes_tree A m s' hd
    refine Or.inr (Or.inr ⟨h1, ?_⟩)
    rw [read_of_tl t2, hg.funs]
    have e : m.tl? = s.tl? := (K1.laterAt_tl q gp lk pr mo reads s m _ _ hm).1
    rw [← read_of_tl t1]
    unfold readTl
    rw [e]
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    obtain ⟨h0, hp, hhp, hd⟩ := hL
    obtain ⟨_, _, _, _, ht⟩ := layers_lays_tl _ hd
    exact Or.inl ⟨h0, hp, hhp, by rw [read_of_tl ht, hg.funs]⟩
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    obtain ⟨_, _, _, _, ht⟩ := head_lays_tl _ hH.2
    exact Or.inr (Or.inl ⟨hH.1, by rw [read_of_tl ht, hg.funs]⟩)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The head's link.** -/
theorem planned_head (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) R C = .ok out) :
    readTl g out.1 = some (g Bs.G₀.W.H.tl) := by
  obtain ⟨b, Xl, pr, reads, hf, e3, hu⟩ := P1K8S.reads_under hS hR O (l := 24) (by omega) .head
    (IM.subs_head hS hR O.pub O.blank) 4 (by unfold kindsBeforeBatching; rfl) (Or.inr rfl)
  obtain ⟨_, X', e3', hk, _⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := 342) f
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next (k := 342) hf f₃ f
  rcases reads_makes hg _ _ _ _ _ _ _ Bs.G₀ 24 X' _ _ _ _ e3 (hu _ _ _ _ d) with
    ⟨h0, _⟩ | ⟨_, h⟩ | ⟨h1, _⟩
  · omega
  · exact h
  · omega

/-- **A layers' link.** -/
theorem planned_layers (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {γ : ℕ} (hγ : γ < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * γ) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    ∃ hp, Bs.G₀.W.G[γ]? = some hp ∧ readTl g out.1 = some (g hp.tl) := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, e3, hk, hXg, _, hla⟩ :=
    IM.k1_reads_layers hS hR O γ hγ
  have hf : c.blocksInOrder[14 * (2 * γ) + 5]? = some b := by
    have := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (by omega) 3] at this
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := 14 * (2 * γ) + 5) f
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next hf f₃ f
  rcases reads_makes hg _ _ _ _ _ _ _ Bs.G₀ (2 * γ) Xl _ _ _ _ e3
      (P1K8S.alone_retype_under hla _ _ _ _ d) with ⟨_, hp, ehp, h⟩ | ⟨h2, _⟩ | ⟨h1, _⟩
  · rw [hXg] at ehp
    exact ⟨hp, ehp, h⟩
  · omega
  · omega

/-- **An attention link.** -/
theorem planned_att (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {γ : ℕ} (hγ : γ < 12) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * γ + 1) + 6)) (ProofFile.startS Z p) R C = .ok out) :
    ∃ q, Bs.G₀.W.A[γ]? = some q ∧ readTl g out.1 = some (g q.seam.tl) := by
  obtain ⟨b, Xl, pr, reads, hf, e3, hu⟩ := P1K8S.reads_under hS hR O (l := 2 * γ + 1) (by omega)
    .attention (IM.subs_att hS hR O.pub O.blank (g := γ) hγ) 3
    (by unfold kindsBeforeBatching; cases (2 * γ + 1 == 0) <;> rfl) (Or.inl rfl)
  obtain ⟨hN, _⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨_, X', _, _, _, _, e3', hk, hXg, _⟩ := hN γ hγ
  obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
  obtain ⟨Lk, b1, b1', eL, e1, k3, la1⟩ := IM.k3_of hS hR O (2 * γ + 1) (by omega) false
  have ix1 : IM.k3Ix (2 * γ + 1) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * γ + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * γ + 1 = 24)]
    rfl
  rw [ix1] at e1
  have i1 : c.blocksInOrder[14 * (2 * γ + 1) + 3]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [IM.flatIx_scope hS hR O (by omega) 1] at k
  obtain ⟨Lk', b2, b2', a, eL', e2, k5, la2, _⟩ := IM.k5_of hS hR O γ hγ
  have i2 : c.blocksInOrder[14 * (2 * γ + 1) + 4]? = some b2 := by
    have k := IM.hear_at_flat eL' e2
    rwa [IM.flatIx_scope hS hR O (by omega) 2] at k
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := 14 * (2 * γ + 1) + 5) f
  obtain ⟨t₂, R₂, C₂, f₂⟩ := Meaning.K2.fold_back (k := 14 * (2 * γ + 1) + 4) f₃
  obtain ⟨t₁, R₁, C₁, f₁⟩ := Meaning.K2.fold_back (k := 14 * (2 * γ + 1) + 3) f₂
  obtain ⟨rs1, gs1, d1⟩ := Meaning.K2.fold_next i1 f₁ f₂
  obtain ⟨rs2, gs2, d2⟩ := Meaning.K2.fold_next i2 f₂ f₃
  obtain ⟨rs3, gs3, d3⟩ := Meaning.K2.fold_next hf f₃ f
  have ha : IM.subAt (2 * γ + 1) = ModelPart.attention := by
    unfold IM.subAt
    rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨X, q, eX, _, eq, ht1⟩ := P1L20.att_tl_at_fold hS hR O (l := 2 * γ + 1) (by omega) ha f₁
  have hg' : X.g = γ := by
    obtain ⟨ls, _, _, eB, _⟩ := IM.blank_ground O.blank
    rw [eB] at e3
    obtain ⟨b', hb', hbg⟩ := P1K8S.zipped_g e3
    obtain rfl : b' = X := Option.some.inj (hb'.symm.trans eX)
    rw [hbg]
    exact hXg
  rw [hg'] at eq
  have h1 : readTl g t₁ = some (g q.seam.tl) := by rw [read_of_tl ht1, hg.reset]
  have h2 : readTl g t₂ = readTl g t₁ :=
    P1K8S.leaves_of_under (IM.alone_underR la1).2 (theStated_leaves_tl hg.four k3) _ _ _ _ d1
  have h3 : t₃.tl? = t₂.tl? :=
    VerifiableInference.Desc.First.Att.P.k5AtN_leaves_tl k5 _ _ _ _
      ((IM.alone_underR la2).2 _ _ _ _ d2)
  have h3' : readTl g t₃ = readTl g t₂ := by
    unfold readTl
    rw [h3]
  refine ⟨q, by rw [O.W]; exact eq, ?_⟩
  rcases reads_makes hg _ _ _ _ _ _ _ Bs.G₀ (2 * γ + 1) X' _ _ _ _ e3 (hu _ _ _ _ d3) with
    ⟨h0, _⟩ | ⟨h2', _⟩ | ⟨_, h⟩
  · omega
  · omega
  · exact h.trans (h3'.trans (h2.trans h1))

/-- **AT ALL 25 PLACES, ALONG THE FOLD FROM THE FIRST STATE.** -/
theorem planned_at_place (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ P1K8S.places) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    ∃ tlP, P1K8S.PlanAt Bs.G₀.W x.1 tlP ∧ readTl g out.1 = some (g tlP) := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases h24 : l = 24
  · subst h24
    exact ⟨_, Or.inl ⟨rfl, rfl⟩, planned_head hg hS hR O p R C out f⟩
  · simp only [h24, if_false] at f
    by_cases he : l % 2 = 0
    · obtain ⟨γ, rfl⟩ : ∃ γ, l = 2 * γ := ⟨l / 2, by omega⟩
      obtain ⟨hp, e, h⟩ := planned_layers hg hS hR O (γ := γ) (by omega) p R C out f
      exact ⟨_, Or.inr (Or.inl ⟨γ, hp, by omega, rfl, e, rfl⟩), h⟩
    · obtain ⟨γ, rfl⟩ : ∃ γ, l = 2 * γ + 1 := ⟨l / 2, by omega⟩
      obtain ⟨q, e, h⟩ := planned_att hg hS hR O (γ := γ) (by omega) p R C out f
      exact ⟨_, Or.inr (Or.inr ⟨γ, q, by omega, rfl, e, rfl⟩), h⟩

/-- **AT EVERY STATE REACHED IN FRONT OF THE DRAW.** -/
theorem planned_at_draw (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ P1K8S.places) {Xl : LinkH} (e3 : Bs.G₀.built[x.1]? = some Xl)
    (a : ProofFile.InstPub × S) (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2 + 2) a) :
    readTl g a.2 = some (g Xl.tl) := by
  obtain ⟨_, rs, cols, f⟩ := Reach.fold h
  obtain ⟨tlP, hv, e⟩ := planned_at_place hg hS hR O hx a.1 rs cols _ f
  rw [← P1K8S.planAt_built hS hR O e3 hv]
  exact e

/-- **AT EVERY STATE REACHED AT THE BATCHING's ENTRY's NUMBER.** -/
theorem planned_at_batch (hg : Planned g) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2) a) :
    readTl g a.2 = some (g Xl.tl) := by
  have hp : (x.1, x.2.1) ∈ P1K8S.places := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map.2 ⟨l, hl, rfl⟩
  exact planned_to_batch hS hR O hx g hg.four hg.draw (fun _ => some (g Xl.tl))
    (fun b hb => planned_at_draw hg hS hR O hp e3 b hb) a h

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.reads_makes
#print axioms VerifiableInference.Desc.LinkJoin.planned_at_place
#print axioms VerifiableInference.Desc.LinkJoin.planned_at_draw
#print axioms VerifiableInference.Desc.LinkJoin.planned_at_batch
