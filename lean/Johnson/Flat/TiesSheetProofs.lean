-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TiesSheetProofs.lean: proofs of the six statements of the sheet
Johnson/Flat/TiesSheet.lean: what `RowTies` (Johnson/Flat/ProofOfRow.lean) rests on.

Statements and proofs. Each theorem has the sheet's proposition of the same name as its type. All
are joinings at letters or closed small laws.

Main names. `tiesOfFive`: the five premises give `RowTies`. `readsOfFirst`: `TieReads` from
`FirstReads` and the conclusion of `RowDecides`. `passesOf`, `setsOf`: each is one call of the frame
rule for reductions (`Iop.know_frame`, Ior/FrameProofsBasic.lean). `decodedInRange`: by the text of
the configuration's index decoder (OnBytes/Slice/ConfOf.lean). `tokenOfReply`: one call of
`OnBytes.K.token_of_reply` (OnBytes/K/ReplyToken.lean).

Limits.
- AT LETTERS: NO VALUE OF THIS FRAME HAS RUN ON A REAL PROOF. What the sheet's head lists
  holds here too.
- `tiesOfFive` moves the load, it does not carry it: the five premises are shown of no description
  of a file.
- `passesOf` and `setsOf` carry a clause that is given: that any block of a description has its
  clause, or that the transport holds at its relations, is not shown.
- Nothing on acceptance, on an honest prover or on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesSheet
import OnBytes.TypedOracleCompiler.Joined.DecidesThree
import Ior.FrameProofsBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)

section Letters
variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)
  (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)
  {Tok : Type} (drop : Kc.conf.X → Tok) (put : Kc.conf.X → Tok → Kc.conf.X) (tokW : S.W₀ → Tok)
  (said : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh → Option Tok)
  (toW : S.W₀ → Kc.conf.Cells)

/-- **The five give `RowTies`.** By cases on what the word decodes to. -/
theorem tiesOfFive :
    TiesOfFive Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S drop put tokW said toW := by
  intro glue onOk tells hReads hFins x rec y τ hyes hr
  by_cases hn : Kc.conf.D y rec = none
  · exact Or.inl hn
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hn
    refine Or.inr ⟨i, hi, ?_⟩
    have hs := tells (early x) rec y _ (hr (onOk x rec y τ hyes hn)) i hi
    have ht := Option.some.inj ((hReads x rec y τ hyes).symm.trans (hFins x rec y τ hyes))
    rw [ht, glue] at hs
    exact hs

variable (said₁ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁ → Option Tok)

/-- `TieReads` from the law on the first chain's extractor: where all three chains put out, the
first does, and there the composed extractor is the first one's, at what the later ones yield. -/
theorem readsOfFirst :
    ReadsOfFirst Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S tokW said₁ := by
  intro dec first x rec y τ hyes
  obtain ⟨b₁, _, h₁, -, -⟩ := (Links.all_out_iff _ _ τ).1 (dec x rec y τ hyes)
  have h₁' : (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).out₁ ((early x, rec), y)
      (Tr.fst (s := (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁) τ) = some b₁ := h₁
  unfold Links.ext Reduction.extSeq
  simp only
  split
  · rename_i b hb
    exact first _ _ _ b hb
  · rename_i hn
    have e := h₁'.symm.trans hn
    cases e

end Letters

end VerifiableInference.OnPublicFiles

namespace Iop.Reduction

/-- A block in front of the reply's round hands the token on: the frame rule, with the further part
left as it is. -/
theorem passesOf : PassesOf :=
  fun A B WA WB Tok K on RA RB ext ε Φ Φ' hK hΦ =>
    Iop.know_frame A B WA WB Tok K on RA RB ext ε Φ Φ' (fun _ _ _ t => t) hK hΦ

/-- The block of the reply's round lays the token: the frame rule, with the further part read off
the block's own transcript. -/
theorem setsOf : SetsOf :=
  fun A B WA WB Tok K on RA RB ext ε Φ Φ' saidK hK hΦ =>
    Iop.know_frame A B WA WB Tok K on RA RB ext ε Φ (fun b w _ => Φ' b w)
      (fun _ τ _ _ => saidK τ) hK (fun a τ b w _ ha hb hB hA h => hΦ a τ b w ha hb hB hA h)

end Iop.Reduction

namespace OnBytes.Slice

/-- What a word decodes to is in range. -/
theorem decodedInRange : DecodedInRange := by
  classical
  intro D X A R y rec M h
  rw [DecR.conf_D] at h
  split at h
  · cases h
  · obtain ⟨u, _, hu⟩ := Option.bind_eq_some_iff.1 h
    have hu' : (if A.inRange (A.mat u) then some (A.mat u) else none) = some M := hu
    split at hu'
    · rename_i hr
      cases hu'
      exact hr
    · cases hu'

end OnBytes.Slice

namespace OnBytes.Flat

/-- The reply as the programs compare it, read as a token, is the instance's own. -/
theorem tokenOfReply : TokenOfReply :=
  fun _ x hV =>
    OnBytes.K.token_of_reply (plain := #[replyOf x]) (got := replyOf x) (y := x.y.val) rfl
      (beq_self_eq_true _) (Nat.lt_of_lt_of_le x.y.isLt hV)

end OnBytes.Flat

#print axioms VerifiableInference.OnPublicFiles.tiesOfFive
#print axioms VerifiableInference.OnPublicFiles.readsOfFirst
#print axioms Iop.Reduction.passesOf
#print axioms Iop.Reduction.setsOf
#print axioms OnBytes.Slice.decodedInRange
#print axioms OnBytes.Flat.tokenOfReply
