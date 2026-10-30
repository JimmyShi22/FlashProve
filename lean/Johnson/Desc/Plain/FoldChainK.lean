-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/FoldChainK.lean: `fold_chainK`: `fold_chain` (Johnson/Desc/Plain/FoldChain.lean)
WITH
KEYS: one "the prover has lost" for all the statements with one key (`LeadsK`,
Johnson/Desc/Plain/Keyed.lean): the form in which a shared chain is paid once for a batch.

  `EachLeadsK key on Q`: for each block: `LeadsK` at the key of the boundary in front of it; the
    hand-over of the condition; and the law of keys: the key behind the block is a function of the
    key in front and of the block's own transcript (`KeyLaw`).
  `fold_chainK`, `fold_chain_keyLaw`: then the chain's own decision has both.
Limits: those of FoldChain.lean and Keyed.lean.

-/
import Johnson.Desc.Plain.FoldChain
import Johnson.Desc.Plain.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S Cl W κ : Type} {C : CK} {F : Frame}

/-- **One premise for each block, with keys.** -/
def EachLeadsK (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.LeadsK (key i) (on i) (Q i) p.err ∧ (∀ a b, on i a → Q i a b → on (i + 1) b) ∧
      p.ior.red.KeyLaw (key i) (key (i + 1)) ∧ EachLeadsK key on Q (i + 1) l

theorem EachLeadsK.leads {key : ℕ → S × F.E.Str → κ} {on : ℕ → S × F.E.Str → Prop}
    {Q : ℕ → S × F.E.Str → S × F.E.Str → Prop} :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachLeadsK key on Q i l → EachLeads on Q i l
  | [], _, _ => trivial
  | _ :: l, i, h => ⟨h.1.leads, h.2.1, EachLeadsK.leads l (i + 1) h.2.2.2⟩

theorem row_leadsK (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ),
      EachLeadsK key on Q i (p :: l) →
      (rowIOR p l).red.LeadsK (key i) (on i) (Reduction.steps Q i l.length) (rowErr p l)
  | [], _, _, h => h.1
  | q :: l, p, i, h => by
      have hs := Reduction.LeadsK.seq' h.1 (row_leadsK key on Q l q (i + 1) h.2.2.2) h.2.1 h.2.2.1
      intro k
      refine Doomed.mono _ _ ?_ (hs k)
      intro τ hτ a hk ha b hb
      exact hτ a hk ha b ((IOR.red_seq_out p.ior (rowIOR q l) a τ).symm.trans hb)

theorem row_keyLaw (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ),
      EachLeadsK key on Q i (p :: l) →
      (rowIOR p l).red.KeyLaw (key i) (key (i + 1 + l.length))
  | [], _, _, h => h.2.2.1
  | q :: l, p, i, h => by
      have ih := row_keyLaw key on Q l q (i + 1) h.2.2.2
      have e : i + 1 + 1 + l.length = i + 1 + (q :: l).length := by
        simp only [List.length_cons]
        omega
      rw [e] at ih
      obtain ⟨g, lw⟩ := Reduction.KeyLaw.seq h.2.2.1 ih
      exact ⟨g, fun a τ b hb =>
        lw a τ b ((IOR.red_seq_out p.ior (rowIOR q l) a τ).symm.trans hb)⟩

/-- **fold_chain with keys.** -/
theorem fold_chainK (name : String) (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (ht : Tiled p l) (he : EachLeadsK key on Q 0 (p :: l)) :
    (foldRed name ((p :: l).map (·.b)) p l h).LeadsK (key 0) (on 0)
      (Reduction.steps Q 0 l.length) (rowErr p l) := by
  intro k
  refine Doomed.mono _ _ ?_ (row_leadsK key on Q l p 0 he k)
  intro τ hτ a hk ha b hb
  exact hτ a hk ha b ((foldIsRow S Cl W C F name p l h ht a τ).symm.trans hb)

theorem fold_chain_keyLaw (name : String) (key : ℕ → S × F.E.Str → κ)
    (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop)
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (h : (rowIOR p l).shape = uLT C (rowData p l)) (ht : Tiled p l)
    (he : EachLeadsK key on Q 0 (p :: l)) :
    (foldRed name ((p :: l).map (·.b)) p l h).KeyLaw (key 0) (key (0 + 1 + l.length)) := by
  obtain ⟨g, lw⟩ := row_keyLaw key on Q l p 0 he
  exact ⟨g, fun a τ b hb => lw a τ b ((foldIsRow S Cl W C F name p l h ht a τ).symm.trans hb)⟩

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.fold_chainK
#print axioms VerifiableInference.Desc.Plain.fold_chain_keyLaw
