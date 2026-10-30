-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/BackFile.lean: the stored positions at a file, and tools for a
file's transcript. Where the plan passes its tests and the data fit the description, `asksIn_of`
proves `AsksIn` (Honest/Law/Rule/StOff.lean): at a verifier's message whose list of challenges is
such as the rounds can draw, every stored position that the declared rounds read is below the
external string's length and among the positions that the protocol reads of it. The tools give a
file's plain parts from those of its six parts, and a tree's position in the file's oracles from the
chain that sent it and its number there.

What this is. Lemmas about the library's typed transcripts and about lists of positions. The
conclusion of `asksIn_of` is a definition of ours, meant as a hypothesis of other lemmas. They are
none of the library's goals.

  1  `plains_cons`, `plains_of_parts`   a file's plain parts, from those of its six parts
  2  `own_pos₁`, `own_pos₂`, `own_pos₃`   a tree's position, from the chain that sent it and its
     number there
  3  `first_reads`, `asksIn_of`   the stored positions

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import OnBytes.Maker.ChainsLaws
import Johnson.Desc.ProofFile.Honest.Law.BackParts
import Johnson.Desc.ProofFile.Honest.Law.WantsReads
import Johnson.Desc.ProofFile.Honest.Law.Rule.BackPl
import Johnson.Desc.ProofFile.Honest.Law.Rule.StOff
import Johnson.Desc.ProofFile.Honest.Law.Rule.OneSim
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads
import Johnson.Desc.ProofFile.Honest.Law.Rule.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD Want uLT chainsOf drawnT posAtST ownPosOf extPosOf wants₁ wants₂
  wants₃ wantsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 A file's plain parts -/

theorem plains_cons {r : Iop.Round} {s : Iop.Shape} (τ : Iop.Tr (r :: s)) :
    τ.plains = (τ.1.2, τ.2.2.plains) := by
  obtain ⟨m, c, a⟩ := τ
  rfl

/-- Two transcripts of a file's rounds whose six parts have the same plain parts have the same plain
parts. -/
theorem plains_of_parts (G : Compile.Joined.Chains) (τ τ' : Iop.Tr G.sh)
    (hF : (G.msgF τ).2 = (G.msgF τ').2) (h1 : (G.tr₁ τ).plains = (G.tr₁ τ').plains)
    (hJ : (G.msgJ τ).2 = (G.msgJ τ').2) (h2 : (G.tr₂ τ).plains = (G.tr₂ τ').plains)
    (hS : (G.msg3 τ).2 = (G.msg3 τ').2) (h3 : (G.tr₃ τ).plains = (G.tr₃ τ').plains) :
    τ.plains = τ'.plains := by
  have e3 : (Iop.Tr.snd (s := G.s₂) (G.trJ τ).2.2).plains =
      (Iop.Tr.snd (s := G.s₂) (G.trJ τ').2.2).plains := by
    rw [plains_cons, plains_cons]
    exact Prod.ext hS h3
  have eJ2 : (G.trJ τ).2.2.plains = (G.trJ τ').2.2.plains :=
    Iop.Tr.plains_eq_of _ _ h2 e3
  have eJ : (G.trJ τ).plains = (G.trJ τ').plains := by
    rw [plains_cons, plains_cons]
    exact Prod.ext hJ eJ2
  have e1 : τ.2.2.plains = τ'.2.2.plains := Iop.Tr.plains_eq_of _ _ h1 eJ
  rw [plains_cons, plains_cons]
  exact Prod.ext hF e1

/-! ## 2 A tree's position -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

theorem own_pos₁ (n k : Nat) (h : n < D.t₁) : ownPosOf C D tF tJ t3 (.tree n k) =
    (posAtST C D.ds₁ n k).map (chainsOf C D tF tJ t3).i₁ := by
  show (if n < D.t₁ then _ else _) = _
  rw [if_pos h]

theorem own_pos₂ (n k : Nat) (h : n < D.t₂) : ownPosOf C D tF tJ t3 (.tree (D.t₁ + n) k) =
    (posAtST C D.ds₂ n k).map (chainsOf C D tF tJ t3).i₂ := by
  show (if D.t₁ + n < D.t₁ then _ else if D.t₁ + n - D.t₁ < D.t₂ then _ else _) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

theorem own_pos₃ (n k : Nat) : ownPosOf C D tF tJ t3 (.tree (D.t₁ + D.t₂ + n) k) =
    (posAtST C D.ds₃ n k).map (chainsOf C D tF tJ t3).i₃ := by
  show (if D.t₁ + D.t₂ + n < D.t₁ then _
    else if D.t₁ + D.t₂ + n - D.t₁ < D.t₂ then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega)]
  have e : D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n := by omega
  rw [e]

/-! ## 3 The stored positions -/

variable (F : FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)

/-- What the first chain's declared rounds read at the challenges in the form of Honest/Frame.lean
(`drawsAt`) is what they read without the sealing round. -/
theorem first_reads (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (hd : (drawsAt C D tF tJ t3 ρ).due F = true) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    readsOf 0 0 stored tree F.roundsDeclaredByBlocks.1 (drawsAt C D tF tJ t3 ρ).first =
      readsOf 0 0 stored tree F.roundsDeclaredByBlocks.1.dropLast (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)) ∧
    F.roundsDeclaredByBlocks.1.dropLast.length = (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).length := by
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨d1, -⟩, -⟩, -⟩ := hd
  have q1 := drawsFit_length _ _ d1
  have q1' : (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++
      ([⟨[], [], [], none⟩] : List Fmt.Drawn)).length = F.roundsDeclaredByBlocks.1.length := q1
  rw [List.length_append, List.length_singleton] at q1'
  have hne : F.roundsDeclaredByBlocks.1 ≠ [] := by
    intro h0
    rw [h0] at q1'
    simp at q1'
  have hl : F.roundsDeclaredByBlocks.1.dropLast.length =
      (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).length := by
    rw [List.length_dropLast]
    omega
  refine ⟨?_, hl⟩
  show readsOf 0 0 stored tree F.roundsDeclaredByBlocks.1 (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++
                      [⟨[], [], [], none⟩]) = _
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [readsOf_append _ _ _ _ _ _ _ _ hl, reads_seal, List.append_nil]

/-- **`AsksIn` holds**, if the plan passes its tests and the data fit the description. -/
theorem asksIn_of (hp : F.planOk = true) (hD : DataFits F D) : AsksIn C D tF tJ t3 F silent := by
  intro x ρ hdue q hq
  have P := (F.planOk_ok).1 hp
  unfold storedAsks at hq
  obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hq
  cases hi : b.item with
  | none =>
    rw [hi] at e
    cases e
  | some i =>
    rw [hi] at e
    cases e
    have key : ∃ r ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∃ s ∈ r.stored, b.pos < 2 ^ s.sh.a ∧
        Want.table i b.pos ∈ wants₁ C D tF tJ t3 ρ ++
          (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ) := by
      unfold allBare bareReads at hb
      rcases List.mem_append.1 hb with g | g
      · rcases List.mem_append.1 g with g | g
        · rw [(first_reads C D tF tJ t3 F ρ hdue _ _).1] at g
          obtain ⟨a, r, hr, s, hs, lt⟩ := read_table (numAt F.t₁ F.t₂ 0) 0 0 _ _ _ _ b g i hi
          refine ⟨r, List.mem_append_left _ (List.mem_append_left _
            (List.mem_of_mem_dropLast hr)), s, hs, lt, List.mem_append_left _ ?_⟩
          show _ ∈ wantsOf D.a D.depth D.ds₁ _
          rw [hD.wants.1]
          exact a
        · obtain ⟨a, r, hr, s, hs, lt⟩ := read_table (numAt F.t₁ F.t₂ 1) 1 0 _ _ _ _ b g i hi
          refine ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), s, hs, lt,
            List.mem_append_right _ (List.mem_append_left _ ?_)⟩
          show _ ∈ wantsOf D.a D.depth D.ds₂ _
          rw [hD.wants.2.1]
          exact a
      · obtain ⟨a, r, hr, s, hs, lt⟩ :=
          read_table (numAt F.t₁ F.t₂ 2) 2 F.lastChainFirstTreeNumber _ _ _ _ b g i hi
        refine ⟨r, List.mem_append_right _ hr, s, hs, lt,
          List.mem_append_right _ (List.mem_append_right _ ?_)⟩
        show _ ∈ wantsOf D.a D.depth D.ds₃ _
        rw [hD.wants.2.2]
        exact a
    obtain ⟨r, hr, s, hs, lt, hw⟩ := key
    have ha : s.sh.a = D.a := (P.depth r hr s hs).trans hD.depth.symm
    rw [ha] at lt
    refine ⟨lt, ?_⟩
    show _ ∈ ((wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++
      wants₃ C D tF tJ t3 ρ)).filterMap (extPosOf D)).toFinset
    refine List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hw, ?_⟩)
    show (if h : b.pos < 2 ^ D.a then some (⟨b.pos, h⟩ : Fin (2 ^ D.a)) else none) = _
    rw [dif_pos lt]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.plains_cons
#print axioms ProofFile.Honest.plains_of_parts
#print axioms ProofFile.Honest.own_pos₁
#print axioms ProofFile.Honest.own_pos₂
#print axioms ProofFile.Honest.own_pos₃
#print axioms ProofFile.Honest.first_reads
#print axioms ProofFile.Honest.asksIn_of
