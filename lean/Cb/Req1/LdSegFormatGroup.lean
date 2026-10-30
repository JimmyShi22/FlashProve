-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFormatGroup.lean: a run on a group (the bridge, then a block beside the carried part)
leaves the encoded index alone, hands the record on, and its honest prover hands the prover encoded
index on.

Statements (in `Cb.Spec`) and proofs, for `ldRunG`, `ldRunGH` (Cb/Ld/LdGroup.lean) with any block,
on a group G with `G.P` nonempty.
Book-keeping in the sense of Cb/Req1/LdReqFormat.lean, for the first steps of a proximity test on a
group of oracle messages.

Why: the move "fold" of a preamble (`LdFoldD`, Cb/Req1/LdSegKit.lean) takes a link l up to the
joint "the folded word, beside what is carried"; `Spec.ldFmt_fold` (Cb/Req1/LdSegFormatMoves.lean)
requires that l has the format up to that joint. When l is a run on a group, three of the four
clauses hold whatever the block is.

Main names:
  `Spec.ldFmt_run_idx`: whatever is at a place i among the further oracles E₀ is left alone, and
    afterwards is at that place among the carried oracles, beside the block's word.
  `Spec.ldFmt_run_pass`: what is read off St₀ is handed on.
  `Spec.ldFmt_run_hands`: what is read off the further witness Wp is handed on by the honest prover
    (`Hands`, Cb/Ld/LdWfPre.lean), at every Ri.
The fourth clause, that the run bears what follows, is in the theorems on runs, under their
hypotheses (`Spec.ldGroup_run`, stated in Cb/Ld/LdGroup.lean; `Spec.ldGroup_fold`, stated in
Cb/Ld/LdGroupFold.lean: a piece of a chain).

Limits: this file says nothing on relations, nothing on the block.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroup
import Cb.Req1.LdSegFormatKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S) (kp : S.O → Prop)
  [DecidablePred kp] {E0 : ExtSpec}

omit [Field E] [Fintype E] in
/-- the bridge's step without rounds moves what is among the further oracles -/
theorem ldBrG_moves (E₀ : ExtSpec) (i : IxAt E0 E₀) :
    (ldBrG G kp E₀).Moves (i.inl S.ext) ((i.inl (S.sub kp).ext).inr G.C.ext) :=
  ExtMap.Moves.pair_right (ExtMap.Avoids.comp (ExtMap.Avoids.snd i S.ext) _)
    (ExtMap.Moves.pair_left (ExtMap.Moves.fst i S.ext)
      (ExtMap.Avoids.comp (ExtMap.Avoids.snd i S.ext) _))

end

namespace Spec

def ldFmt_run_idx : Prop :=
  ∀ (E B St₀ : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (E₀ E0 : ExtSpec) (b : LdJoint E)
      (Bk : LdBlock (G.joint Sb sl Z) b) (i : IxAt E0 E₀),
    (ldRunG G kp Sb sl Z St₀ E₀ Bk).IdxLink (i.inl S.ext) ((i.inl (S.sub kp).ext).inr b.C.ext)

def ldFmt_run_pass : Prop :=
  ∀ (E B St₀ Rc : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (b : LdJoint E)
      (Bk : LdBlock (G.joint Sb sl Z) b) (rc : St₀ → Rc),
    (ldRunG G kp Sb sl Z St₀ E₀ Bk).Passes (fun x => rc x.1.2) (fun x => rc x.2.1)

def ldFmt_run_hands : Prop :=
  ∀ (E B St₀ Wp Pw : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (b : LdJoint E) (Bk : LdBlock (G.joint Sb sl Z) b)
      (px : Wp → Pw)
      (Ri : (((B → E) × (∀ b, Sb b)) × St₀) × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop),
    (ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk).Hands Ri (fun w => px w.2) (fun w => px w.2.2)

end Spec

theorem ldFmt_run_idx : Spec.ldFmt_run_idx := by
  intro E B St₀ _ _ _ S G _ kp _ Sb sl Z E₀ E0 b Bk i
  refine idxLink_seq _ _ _ _ _ _ _ _ _ (i.inl S.ext) ((i.inl (S.sub kp).ext).inr G.C.ext) _ ?_ ?_
  · exact IdxLink.pre (ldBrG_moves G kp E₀ i)
      (IdxLink.of_copies (OnlyCopies.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀)) _) _
  · exact IdxLink.keepE_right (Bk.R.keepX (LdCarX kp St₀)) (i.inl (S.sub kp).ext)

theorem ldFmt_run_pass : Spec.ldFmt_run_pass := by
  intro E B St₀ Rc _ _ _ S G _ kp _ Sb sl Z E₀ b Bk rc
  refine Passes.seq (r₂ := fun x : LdBrXo G kp Sb Z St₀ => rc x.2.1) ?_ ?_
  · refine Passes.pre (r₂ := fun x : LdBrXm G kp Sb St₀ => rc x.2.1)
      (Passes.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀) _ _ fun _ _ => rfl) _ _ ?_
    intro x x' hx
    cases hx
    rfl
  · exact Passes.keepE (Passes.keepX_snd Bk.R fun z : LdCarX kp St₀ => rc z.1) _

theorem ldFmt_run_hands : Spec.ldFmt_run_hands := by
  intro E B St₀ Wp Pw _ _ _ S G _ kp _ Sb sl Z E₀ b Bk px Ri
  refine Honest.Hands.seq (Rb := fun _ _ _ => True) (p₂ := fun w : LdBrW G kp Wp => px w.2.2) ?_
    (fun _ _ _ _ _ _ _ => ⟨rfl, trivial⟩) ?_
  · exact fun _ _ _ _ _ _ _ => rfl
  · exact Honest.Hands.carry_snd _ _ fun w : LdCarW kp Wp => px w.2

end Cb
