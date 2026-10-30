-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowStretchPairs.lean: FOR THE KEY FILE's ROWS, WHICH ASK THE FORM hpair: THE STRETCH LEMMA IS GENERAL IN THE BLOCK's NUMBER: AT EVERY DESCRIPTION, AT EVERY BLOCK OF CHAINS 2 AND 3, AND AT EVERY BLOCK OF CHAIN 1 BUT ITS LAST.
  stretch_pairs₁ | ₂ | ₃   the maker's stretch at block n bears, round by round, just the entries that block n declares and the kinds that their names say: as ONE equation of lists of (entry, some kind): stretch116_pairs' form, general in F, D and n
  hpair₁ | ₂ | ₃           THE ASKED FORM, WHERE THE STRETCH IS ONE ROUND's DATA [d]: the block declares just one round r, and (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name)
  …_held                   the same at the held blocks (the form in which the maker cuts: cutDs … (held c) (k.map held) n)
BY: stretch_of_data₁ | ₂ | ₃ · pairs_of_as · cutDs_held: ALL IN RowStretch.lean (over roundsOfData). THIS FILE DOES NOT STAND OVER ROW 1.16's LAW. PREMISES: the description's own data are D (F.data file = .ok D) · the chain's head (q) · the block at n.
OBJECT: the maker's cut of a description's own data · USER: r2_7_scope | r2_4_scope | r2_1_scope · LETTERS: F file D; c k; n b d. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker

/-- One round's data against a block's declared rounds. -/
theorem one_of_as (d : RDT) (rs : List Fmt.DeclaredRound) (h : List.Forall₂ RoundAsG [d] rs) :
    ∃ r, rs = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) := by
  obtain ⟨r, l, h1, h2, e⟩ := List.forall₂_cons_left_iff.1 h
  obtain rfl := List.forall₂_nil_left_iff.1 h2
  exact ⟨r, e, Prod.ext h1.1 h1.2.1.symm⟩

section
variable {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
include h

theorem stretch_pairs₂ (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b) :
    (cutDs D.ds₂ c₂ k₂ n).map (fun d => (d.entry, some d.kind)) = b.rounds.map (fun r => (r.entry, Fmt.kindOf r.entry.name)) :=
  pairs_of_as _ _ (stretch_of_data₂ F file D h c₂ k₂ q₂ n b hb)

theorem stretch_pairs₃ (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some b) :
    (cutDs D.ds₃ c₃ k₃ n).map (fun d => (d.entry, some d.kind)) = b.rounds.map (fun r => (r.entry, Fmt.kindOf r.entry.name)) :=
  pairs_of_as _ _ (stretch_of_data₃ F file D h c₃ k₃ q₃ n b hb)

theorem stretch_pairs₁ (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (q₁ : F.first.blocksInOrder = c₁ :: k₁) (hlast : 1 ≤ lastRounds c₁ k₁) (n : ℕ) (hn : n < k₁.length)
    (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b) :
    (cutDs D.ds₁ c₁ k₁ n).map (fun d => (d.entry, some d.kind)) = b.rounds.map (fun r => (r.entry, Fmt.kindOf r.entry.name)) :=
  pairs_of_as _ _ (stretch_of_data₁ F file D h c₁ k₁ q₁ hlast n hn b hb)

/-- **THE ASKED FORM, at the shared chain.** -/
theorem hpair₂ (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b)
    (d : RDT) (hd : cutDs D.ds₂ c₂ k₂ n = [d]) : ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) :=
  one_of_as d b.rounds (hd ▸ stretch_of_data₂ F file D h c₂ k₂ q₂ n b hb)

theorem hpair₃ (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some b)
    (d : RDT) (hd : cutDs D.ds₃ c₃ k₃ n = [d]) : ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) :=
  one_of_as d b.rounds (hd ▸ stretch_of_data₃ F file D h c₃ k₃ q₃ n b hb)

theorem hpair₁ (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (q₁ : F.first.blocksInOrder = c₁ :: k₁) (hlast : 1 ≤ lastRounds c₁ k₁) (n : ℕ) (hn : n < k₁.length)
    (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b) (d : RDT) (hd : cutDs D.ds₁ c₁ k₁ n = [d]) :
    ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) :=
  one_of_as d b.rounds (hd ▸ stretch_of_data₁ F file D h c₁ k₁ q₁ hlast n hn b hb)

/-- The same where the maker's cut is said at the held blocks. -/
theorem hpair₂_held {Pb : Type} (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b)
    (d : RDT) (hd : cutDs D.ds₂ (held c₂ : Block (Pb × F.S₂) F.Cl) (k₂.map held) n = [d]) :
    ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) :=
  hpair₂ F file D h c₂ k₂ q₂ n b hb d ((cutDs_held k₂ n _ c₂).symm.trans hd)

theorem hpair₃_held {Pb : Type} (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (b : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some b)
    (d : RDT) (hd : cutDs D.ds₃ (held c₃ : Block (Pb × F.S₃) F.Cl) (k₃.map held) n = [d]) :
    ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name) :=
  hpair₃ F file D h c₃ k₃ q₃ n b hb d ((cutDs_held k₃ n _ c₃).symm.trans hd)

end

end LPFD

#print axioms LPFD.one_of_as
#print axioms LPFD.stretch_pairs₁
#print axioms LPFD.stretch_pairs₂
#print axioms LPFD.stretch_pairs₃
#print axioms LPFD.hpair₁
#print axioms LPFD.hpair₂
#print axioms LPFD.hpair₃
#print axioms LPFD.hpair₂_held
#print axioms LPFD.hpair₃_held
