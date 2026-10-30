-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ToldCount.lean: A CHAIN's BLOCKS TELL OF AS MANY TREES AS THE CHAIN SENDS.
Statements (`def … : Prop`) and their proofs.

`OraclesAre` (OraclesAre.lean) and `ShownOfData` (ShownOfData.lean) take as premises that the first
two chains tell of as many trees as they send: else `FileDescription.oracleAt`, which counts through the
three chains' told trees in a row, would part from the data's numbers through the file. Here the two
premises are paid from a clause of `planOk`: every block is shaped (`Block.shaped`, in `blocksOk`:
`oracles` has a list for each round, with a member for each of the round's roots).
  `told_len`: shaped blocks tell of as many trees as their declared rounds' entries say roots.
  `rootsIn_decl`: written rounds send as many roots as the declared rounds' entries say, where each
    written round has as many root items as its entry says (a clause of the makers' test).
  `ToldCount`: FOR EVERY DESCRIPTION F and D with `F.data file = .ok D`: if the first chain's blocks
    are in order (`blocksOk`), they tell of D.t₁ trees; the shared chain's likewise of D.t₂.
  `OraclesAreOk`, `ShownOfOk`: `OraclesAre` and `ShownOfData` with `blocksOk` of the two chains in
    the two counts' place: three clauses of `planOk` and `F.data`'s yes are then all that is asked
    of the description.
Limits: those of the two files. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ShownOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.G.OfPlan Johnson.Pack
open OnBytes.Params (Rounds)
open OnBytes.Three (rootsIn)
open _root_.Run.PQ (CK SgX)

theorem zip_len : ∀ (rs : List Fmt.DeclaredRound) (os : List (List Oracle)), os.length = rs.length →
    (∀ x ∈ rs.zip os, x.2.length = x.1.entry.roots) →
    (os.flatMap id).length = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, o :: os, h, g => by
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      zip_len rs os (by simpa using h) fun x hx => g x (by
        rw [List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hx)]
    have e : o.length = r.entry.roots := g (r, o) (by
      rw [List.zip_cons_cons]
      exact List.mem_cons_self)
    show o.length + _ = _
    rw [e]

theorem told_len {S Cl : Type} : ∀ (bs : List (Block S Cl)), blocksOk bs = true →
    (oraclesOf bs).length = ((bs.flatMap (·.rounds)).map (·.entry.roots)).sum
  | [], _ => rfl
  | b :: bs, h => by
    unfold blocksOk at h
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨-, hs⟩, ht⟩ := h
    unfold Block.shaped at hs
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
    have e := zip_len b.rounds b.oracles hs.1 fun x hx => by
      have t := hs.2 x hx
      rw [Bool.and_eq_true, beq_iff_eq] at t
      exact t.1
    have ih := told_len bs ht
    unfold oraclesOf at ih ⊢
    rw [List.flatMap_cons, List.length_append, List.flatMap_cons, List.map_append, List.sum_append,
      e, ih]

theorem rootsIn_decl (e : List (List ByteArray × ByteArray)) : ∀ (dl : List Fmt.DeclaredRound)
    (R : Rounds), WrittenAs e dl R →
    (∀ r ∈ R, r.1.items.countP (· == .root) = r.1.entry.roots) →
    rootsIn R = (dl.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, w, _ => by cases w
  | _ :: _, [], w, _ => by cases w
  | d :: dl, x :: R, w, g => by
    obtain ⟨⟨hx, -⟩, wt⟩ := List.forall₂_cons.1 w
    have ih := rootsIn_decl e dl R wt fun r hr => g r (List.mem_cons_of_mem _ hr)
    unfold rootsIn at ih ⊢
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, g x List.mem_cons_self,
      round_entry e d x.1 hx]

/-- **A chain's blocks tell of as many trees as the chain sends.** -/
def ToldCount : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    (blocksOk F.first.blocksInOrder = true → (oraclesOf F.first.blocksInOrder).length = D.t₁) ∧
      (blocksOk F.shared.blocksInOrder = true → (oraclesOf F.shared.blocksInOrder).length = D.t₂)

theorem toldCount : ToldCount := by
  intro Xi F file D h
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, -⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  have P := okAt_parts (R := (R₁, R₂, R₃)) hok
  have hcn : countsFit F.tableDepth (Three.Whole.of R₁ R₂ R₃) = true := P.counts
  unfold countsFit at hcn
  simp only [Bool.and_eq_true, beq_iff_eq] at hcn
  have t₁ : (dataOf F.tableDepth R₁ R₂ R₃).t₁ = rootsIn R₁ := hcn.1
  have t₂ : (dataOf F.tableDepth R₁ R₂ R₃).t₂ = rootsIn R₂ := hcn.2
  obtain ⟨r₁, r₂, -⟩ := fits_roots_all (P.fits : Three.Whole.fits R₁ R₂ R₃ 2 = true)
  refine ⟨fun b => ?_, fun b => ?_⟩
  · rw [t₁, rootsIn_decl _ _ R₁ w₁ r₁]
    exact told_len _ b
  · rw [t₂, rootsIn_decl _ _ R₂ w₂ r₂]
    exact told_len _ b

/-- `OraclesAre`, from clauses of `planOk` and `F.data`'s yes alone. -/
def OraclesAreOk : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sentFit = true → blocksOk F.first.blocksInOrder = true → blocksOk F.shared.blocksInOrder = true →
    ∀ (j : ℕ) (o : Oracle), F.oracleAt j = some o →
      ∃ sh, D.shape j = some sh ∧ o.logLength = sh.a ∧ o.words = sh.W

theorem oraclesAreOk : OraclesAreOk := by
  intro Xi F file D h hs b₁ b₂
  obtain ⟨c₁, c₂⟩ := toldCount Xi F file D h
  exact oraclesAre Xi F file D h hs (c₁ b₁) (c₂ b₂)

/-- `ShownOfData`, likewise. -/
def ShownOfOk : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sentFit = true → blocksOk F.first.blocksInOrder = true → blocksOk F.shared.blocksInOrder = true →
    ∀ (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (seat : Fin m.length → ℕ × ℕ),
      SeatFits F cs m seat →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r →
      (∀ p ∈ T.p₁ :: T.l₁, p.ShownAll F cs m seat) ∧ (∀ p ∈ T.p₂ :: T.l₂, p.ShownAll F cs m seat) ∧
        ∀ p ∈ T.p₃ :: T.l₃, p.ShownAll F cs m seat

theorem shownOfOk : ShownOfOk := by
  intro Xi F file D h hs k₁ k₂
  obtain ⟨c₁, c₂⟩ := toldCount Xi F file D h
  exact shownOfData Xi F file D h hs (c₁ k₁) (c₂ k₂)

end VerifiableInference.Desc.Sound
