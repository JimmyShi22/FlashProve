-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PieceSeated.lean: THE PIECE's FOUR FACTS AT THE PIECES THAT THE FILE's RULE TAKES: piecesAt (Johnson/Desc/Sound/PaidAtDesc.lean) AT A DESCRIPTION's OWN BLOCKS AND DATA, WITH THE REST AT THE CAP (restCap, Johnson/Desc/Sound/BoundsAtCap.lean): all four, in the laws' forms, READ OFF THE DESCRIPTION's OWN BLOCKS. Eleven theorems.

  held_rounds · held_oracles · held_planOk: a block as a piece holds it (held) declares the same rounds, tells the same oracles, passes the same test on the plan: rfl · rootsOf_held · toldOf_held · blocksOk_held: so the three numbers and tests of PieceMore | PieceFence are the description's own blocks'.
  seated_more: **FOR EVERY DESCRIPTION F, D WITH F.data file = .ok D, THE SEAL LAST, AT T := piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd WITH THE THREE FLAT LISTS b₁ :: l₁ …: at every place of the first chain but the last, and at every place of the two later chains: PieceMore … ∧ q.err = Err.cap 128 (uLT C q.ds).**
    WHO LAYS THE CAP: whoever calls piecesAt at restCap: the end theorems' tower does (its three rows of pieces are written so).
  seated_base: q.base = base₀ + the oracles that the DESCRIPTION's blocks in front tell.
  seated_fenced: **the first chain: under blocksOk F.first.blocksInOrder · bookFit N ps (toldOf F.first.blocksInOrder) · fenceFit N links ps: every tenant of an open pin with a sample at border k sits in a tree below q.base.**
The pieces of atDesc F T are T's own (atDesc turns the starts alone): seated_atDesc: rfl.

Limits. Those of PieceMore.lean | PieceFence.lean. F.data's yes, the seal, blocksOk and the two tests are premises. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PieceFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)
open VerifiableInference.Desc.First (Numbers ModelPart bookFit fenceFit sampledIn openSets start)

section Held
variable {P S Cl : Type}

theorem held_rounds (b : Block S Cl) : (held (P := P) b).rounds = b.rounds := rfl
theorem held_oracles (b : Block S Cl) : (held (P := P) b).oracles = b.oracles := rfl
theorem held_planOk (b : Block S Cl) : (held (P := P) b).planOk = b.planOk := rfl

theorem rootsOf_held (b : Block S Cl) : rootsOf (held (P := P) b) = rootsOf b := rfl

theorem toldOf_held (bs : List (Block S Cl)) : toldOf (bs.map (held (P := P))) = toldOf bs := by
  unfold toldOf
  rw [List.map_map]
  rfl

theorem blocksOk_held (bs : List (Block S Cl)) : blocksOk (bs.map (held (P := P))) = blocksOk bs := by
  unfold blocksOk
  rw [List.all_map]
  rfl

theorem oraclesOf_held (bs : List (Block S Cl)) : oraclesOf (bs.map (held (P := P))) = oraclesOf bs := by
  unfold oraclesOf
  rw [List.flatMap_map]
  rfl

end Held

variable {Xi W : Type}

/-- The pieces of atDesc F T are T's own. -/
theorem seated_atDesc {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ : Type} (F : FileDescription Xi)
    (T : ThreeAt C D all F X₁ X₂ W) :
    (atDesc F T).p₁ = T.p₁ ∧ (atDesc F T).l₁ = T.l₁ ∧ (atDesc F T).p₂ = T.p₂ ∧ (atDesc F T).l₂ = T.l₂ ∧
      (atDesc F T).p₃ = T.p₃ ∧ (atDesc F T).l₃ = T.l₃ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section Seated
variable (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
  (hs : F.sealLast = true) (C : CK)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl) (l₂ : List (Block F.S₂ F.Cl))
  (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (q₁ : F.first.blocksInOrder = b₁ :: l₁) (q₂ : F.shared.blocksInOrder = b₂ :: l₂) (q₃ : F.second.blocksInOrder = b₃ :: l₃)
  (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
    Iop.Tr (uLT C ds) → W → W)
  (e₂ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁) × F.S₂) × (frameAt D (allOf D) D.key₂ 0).E.Str →
    Iop.Tr (uLT C ds) → W → W)
  (e₃ : (i : ℕ) → (ds : List RDT) →
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str →
    Iop.Tr (uLT C ds) → W → W)
  (d wEnd : W)

include h hs q₁ q₂ q₃

/-- **All four, at the pieces that the file's rule takes.** -/
theorem seated_more :
    (∀ k q, ((piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₁ ::
          (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₁)[k]? = some q →
        k + 1 < F.first.blocksInOrder.length →
        PieceMore (numAt D.t₁ D.t₂ 0) 0 (F.first.blocksInOrder.map held) k q ∧ q.err = Err.cap 128 (uLT C q.ds)) ∧
      (∀ k q, ((piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₂ ::
          (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₂)[k]? = some q →
        PieceMore (numAt D.t₁ D.t₂ 1) D.t₁ (F.shared.blocksInOrder.map held) k q ∧
          q.err = Err.cap 128 (uLT C q.ds)) ∧
      ∀ k q, ((piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₃ ::
          (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₃)[k]? = some q →
        PieceMore (numAt D.t₁ D.t₂ 2) (D.t₁ + D.t₂) (F.second.blocksInOrder.map held) k q ∧
          q.err = Err.cap 128 (uLT C q.ds) := by
  have hc := ofCuts_isCut C D (allOf D) 0 0 F.lastChainFirstTreeNumber (held b₁) (l₁.map held) (held b₂) (l₂.map held)
    (held b₃) (l₃.map held) (restCap e₁) (restCap e₂) (restCap e₃) sealRound (besideAt F d wEnd)
  obtain ⟨m₁, m₂, m₃⟩ := more_of_data Xi F file D h hs C _ _ _ _ _ _ _ W _ (held b₁) (l₁.map held)
    (held b₂) (l₂.map held) (held b₃) (l₃.map held) _ _ _ sealRound
    (by rw [q₁]; exact held_map_rounds (b₁ :: l₁)) (by rw [q₂]; exact held_map_rounds (b₂ :: l₂))
    (by rw [q₃]; exact held_map_rounds (b₃ :: l₃)) hc
  obtain ⟨c₁, c₂, c₃⟩ := cap_of_cut C D (allOf D) _ _ _ _ _ _ _ W _ (held b₁) (l₁.map held)
    (held b₂) (l₂.map held) (held b₃) (l₃.map held) _ _ _ sealRound hc
  refine ⟨fun k q hq hk => ⟨?_, c₁ (atCap_restCap e₁) q (List.mem_of_getElem? hq)⟩,
    fun k q hq => ⟨?_, c₂ (atCap_restCap e₂) q (List.mem_of_getElem? hq)⟩,
    fun k q hq => ⟨?_, c₃ (atCap_restCap e₃) q (List.mem_of_getElem? hq)⟩⟩
  · rw [q₁]
    refine m₁ k q hq ?_
    rw [q₁] at hk
    simpa using hk
  · rw [q₂]
    exact m₂ k q hq
  · rw [q₃]
    exact m₃ k q hq

omit h hs q₁ q₂ q₃

end Seated

section Fence
variable {C : CK} {Fr : Frame} {P S Cl : Type} {num : Fmt.TreeSource → ℕ} {base₀ k : ℕ} {bs : List (Block S Cl)}
  {q : Piece C Fr (P × S) Cl W}

/-- **The base, off the description's own blocks.** -/
theorem seated_base (h : PieceMore num base₀ (bs.map held) k q) (hb : blocksOk bs = true) :
    q.base = base₀ + (oraclesOf (bs.take k)).length := by
  rw [base_told h (by rw [blocksOk_held]; exact hb), ← List.map_take, oraclesOf_held]

/-- **The laws' form, at the first chain, off the description's own blocks.** -/
theorem seated_fenced (h : PieceMore num 0 (bs.map held) k q) (hb : blocksOk bs = true) (N : Numbers)
    (links : List ModelPart) (ps : List Place) (hf : bookFit N ps (toldOf bs) = true)
    (hg : fenceFit N links ps = true) (hk : k ≤ ps.length) :
    ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []), x.1 < q.base :=
  fenced_at h (by rw [blocksOk_held]; exact hb) N links ps (by rw [toldOf_held]; exact hf) hg hk

end Fence

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.toldOf_held
#print axioms VerifiableInference.Desc.Sound.blocksOk_held
#print axioms VerifiableInference.Desc.Sound.seated_atDesc
#print axioms VerifiableInference.Desc.Sound.seated_more
#print axioms VerifiableInference.Desc.Sound.seated_base
#print axioms VerifiableInference.Desc.Sound.seated_fenced
