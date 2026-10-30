-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/FoldChain.lean: `fold_chain`: the rule of composition for ONE CHAIN, of the
chain's own decision (`chainAt`, Johnson/Desc/Block.lean), in the plain form of
Johnson/Desc/Plain/Leads.lean:
no witness, no extractor.

What is taken from Johnson/Desc/Sound/: the DEFINITIONS of a
block at its stretch as a reduction (`Piece`, `Piece.ior`), of the blocks in a row (`rowIOR`,
`rowErr`), of the chain's decision as a reduction (`foldRed`), of "the stretches tile the chain"
(`Tiled`); and ONE THEOREM, an equation of the whole verdict (`foldIsRow`). A piece's fields W and
ext are idle here. What is NOT taken: `BK.Good`, `EachGood`, `GoodIn`, `rowExt`, `KnowInto`.

  `EachLeads on Q`: one premise for each block: at its own stretch, at its own errors, from the
    statements with `on i`: but for the errors, what it puts out stands in `Q i` to what it was
    handed; and what stands in `Q i` to a statement with `on i` has `on (i + 1)`.
  `fold_chain`: then the chain's decision leads from `on 0` into the relations in a row: THERE ARE
    STATEMENTS AT ALL THE BOUNDARIES BETWEEN, each in its block's relation to the one before.
  `EachKeeps`, `fold_chain_keeps`: the case "promise, and true behind → true in front".

Limits: those of Leads.lean and of ChainRule.lean's (1), (2), (3), (5), (6), (7).

-/
import Johnson.Desc.Plain.Leads
import Johnson.Desc.Sound.FoldIsRowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **One premise for each block.** -/
def EachLeads (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.Leads (on i) (Q i) p.err ∧ (∀ a b, on i a → Q i a b → on (i + 1) b) ∧
      EachLeads on Q (i + 1) l

/-- The blocks' reductions in a row. -/
theorem row_leads (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ), EachLeads on Q i (p :: l) →
      (rowIOR p l).red.Leads (on i) (Reduction.steps Q i l.length) (rowErr p l)
  | [], _, _, h => h.1
  | q :: l, p, i, h => by
      have hs := Reduction.Leads.seq h.1 (row_leads on Q l q (i + 1) h.2.2) h.2.1
      intro a ha
      refine Doomed.mono _ _ ?_ (hs a ha)
      intro τ hτ b hb
      exact hτ b ((IOR.red_seq_out p.ior (rowIOR q l) a τ).symm.trans hb)

/-- **fold_chain: the rule of composition for one chain, of the chain's own decision.** -/
theorem fold_chain (name : String) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (ht : Tiled p l) (he : EachLeads on Q 0 (p :: l)) :
    (foldRed name ((p :: l).map (·.b)) p l h).Leads (on 0) (Reduction.steps Q 0 l.length)
      (rowErr p l) := by
  intro a ha
  refine Doomed.mono _ _ ?_ (row_leads on Q l p 0 he a ha)
  intro τ hτ b hb
  exact hτ b ((foldIsRow S Cl W C F name p l h ht a τ).symm.trans hb)

/-- The case "promise, and true behind → true in front". -/
def EachKeeps (on L : ℕ → S × F.E.Str → Prop) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.Keeps (on i) (on (i + 1)) (L i) (L (i + 1)) p.err ∧ EachKeeps on L (i + 1) l

theorem EachKeeps.leads {on L : ℕ → S × F.E.Str → Prop} :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachKeeps on L i l →
      EachLeads on (fun i a b => on (i + 1) b ∧ (L (i + 1) b → L i a)) i l
  | [], _, _ => trivial
  | _ :: l, i, h => ⟨h.1, fun _ _ _ hq => hq.1, EachKeeps.leads l (i + 1) h.2⟩

theorem steps_keeps {A : Type} (on L : ℕ → A → Prop) : ∀ (n i : ℕ) (a c : A),
    Reduction.steps (fun i a b => on (i + 1) b ∧ (L (i + 1) b → L i a)) i n a c →
      on (i + 1 + n) c ∧ (L (i + 1 + n) c → L i a)
  | 0, _, _, _, h => h
  | n + 1, i, a, c, ⟨_, hb, hc⟩ => by
      have ih := steps_keeps on L n (i + 1) _ c hc
      have e : i + 1 + 1 + n = i + 1 + (n + 1) := by omega
      rw [e] at ih
      exact ⟨ih.1, fun h => hb.2 (ih.2 h)⟩

/-- **fold_chain, for promises and truth.** -/
theorem fold_chain_keeps (name : String) (on L : ℕ → S × F.E.Str → Prop) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (ht : Tiled p l) (he : EachKeeps on L 0 (p :: l)) :
    (foldRed name ((p :: l).map (·.b)) p l h).Keeps (on 0) (on (1 + l.length)) (L 0)
      (L (1 + l.length)) (rowErr p l) :=
  (fold_chain name on _ p l h ht (EachKeeps.leads _ 0 he)).conseq (fun _ h => h)
    fun a _ c _ _ hq => by
      have := steps_keeps on L l.length 0 a c hq
      rwa [Nat.zero_add] at this

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.fold_chain
#print axioms VerifiableInference.Desc.Plain.fold_chain_keeps
