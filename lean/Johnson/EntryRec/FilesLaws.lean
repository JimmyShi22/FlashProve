-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/FilesLaws.lean: laws that the compiler's theorems ask, at three files' protocols
over letters and at the written link over letters.

Statements and their proofs; each proof is a call of lemmas, one with projections. Three
files' protocols whose key file and proof file stand over ANY data of written rounds and ANY
decision on three views lie in
Johnson/EntryRec/AtFiles.lean (`filesOf`), their wiring in OkcFiles.lean (`wireF`), the four laws of
that wiring in AtMakerA.lean (`four_files`), the written link over letters as an entry's part in
Johnson/Top/EntrySib.lean (`linkProtocolWithWireOfRoundData`). `four_files` asks of the entry's part `LinkWireOK` and that
its two maps of bodies read back what they write; AtMakerA.lean shows them of no entry's part;
AtMakerW.lean [not in this library] shows both of the maker's own link (`linkWireOK_X`,
`entryQX_back`), which is not the written link; EntrySib.lean does not claim them at `linkProtocolWithWireOfRoundData`.
Here they are shown of the written link over letters, from numbers. And the two whole files'
verifiers are local and their marks coherent, whatever the data and the decisions: locality of a
whole file's protocol lies at letters (`wholeIOR_local`, OnBytes/Maker/WholeLocal.lean):
`filesOf_keyLocal`, `filesOf_proofLocal` are it at `filesOf`'s two fields.

Main names:
  `linkWireOK_sib`: `LinkWireOK` at `linkProtocolWithWireOfRoundData` at verifier's messages as hash blocks: if no round
    of the link has more than K blocks (bL) or more than 64 bits of work (wLk), and every number of
    a tree that a round opens is below 2 ^ 16 (own). Beside these it takes what `linkProtocolWithWireOfRoundData` itself
    takes: a least number kmin of blocks with kmin ≤ K (hK).
  `bodies_sib`: its two maps read back what they write, if no tree of the link is deeper than 63
    (dL); with hK as above.
  `filesOf_keyLocal`, `filesOf_proofLocal`, `filesOf_coherent`: no premise.

Limits: those of Johnson/EntryRec/OkcFiles.lean's head. NOTHING ON THE SOUNDNESS OF ANY OF THE THREE
PROTOCOLS: at two decisions that say yes to everything all that stands here holds. That the premises
on numbers hold at any list of rounds is not shown here (at the two sizes: Johnson/Flat/
WiresAtSizes.lean). The entry file's own locality and its marks' coherence are not stated here: the
entry's part of `filesOf` is a letter. Nothing on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.EntrySib
import Johnson.EntryRec.AtMakerA
import OnBytes.Maker.WholeLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Compile Hiop OnBytes.Maker OnBytes.Slice OnBytes.Flat
open OnBytes.K.Arm (linkProtocolWithWireOfRoundData)

section
variable {Seed Ans : Type} (f : _root_.Fmt.Fld) (a : ℕ) (ds : List TypedOracleCompiler.Run.PQ.RD)
  (xs : List XO) (dec2 : (Seed × Ans) × (Seed × Ans) → View → Bool) (salt kmin K : ℕ)
  (hK : kmin ≤ K)

/-- **The written link's wire record obeys what the laws of the wires ask of an entry's part**, at
hash blocks: if no round of the link has more than K blocks or more than 64 bits of work, and every
number of a tree that a round opens is below 2 ^ 16. The premise hK : kmin ≤ K is `linkProtocolWithWireOfRoundData`'s own.
-/
theorem linkWireOK_sib (bL : ∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K)
    (wLk : ∀ d ∈ ds, d.entry.work ≤ 64) (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    LinkWireOK K a (linkProtocolWithWireOfRoundData (a := a) (ckP f) ds xs dec2 salt kmin K hK (chalP f K)).toLinkProtocolWithLeafCoding
      (linkProtocolWithWireOfRoundData (a := a) (ckP f) ds xs dec2 salt kmin K hK (chalP f K)).wL :=
  have h := TypedOracleCompiler.Run.PQ.wqX_okg (ckP f) K (chalP f K) ds a xs (fun _ => true)
    (fun _ => true) own (TypedOracleCompiler.Run.planPull_okg f K ds (fun _ => true) bL wLk)
  ⟨⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩, rfl, le_max_right _ _,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- **Its two maps read back what they write**, if no tree of the link is deeper than 63. The
premise hK : kmin ≤ K is `linkProtocolWithWireOfRoundData`'s own. -/
theorem bodies_sib (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) (q) (s) :
    (linkProtocolWithWireOfRoundData (a := a) (ckP f) ds xs dec2 salt kmin K hK (chalP f K)).prjL q
      ((linkProtocolWithWireOfRoundData (a := a) (ckP f) ds xs dec2 salt kmin K hK (chalP f K)).embL q s) = some s :=
  TypedOracleCompiler.StringsList.prjT_embT salt (ckP f) ds dL q s

end

section
attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → View → View → View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)

/-- The key file's verifier reads its oracles at the declared positions alone. -/
theorem filesOf_keyLocal :
    (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early late).key.IsLocal :=
  Iop.isLocal_toProto _ _ _ (wholeIOR_isLocal ..)

/-- The proof file's likewise. -/
theorem filesOf_proofLocal :
    (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
      late).proof.IsLocal :=
  Iop.isLocal_toProto _ _ _ (wholeIOR_isLocal ..)

/-- The two whole files' marks are coherent. -/
theorem filesOf_coherent :
    (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
      late).annT.Coherent ∧
    (filesOf Kc f DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
      late).ann.Coherent :=
  ⟨Compile.Joined.Chains.ann_coherent _ (chainsOf_laws ..),
    Compile.Joined.Chains.ann_coherent _ (chainsOf_laws ..)⟩

end

end OnBytes.RunA

#print axioms OnBytes.RunA.linkWireOK_sib
#print axioms OnBytes.RunA.bodies_sib
#print axioms OnBytes.RunA.filesOf_keyLocal
#print axioms OnBytes.RunA.filesOf_proofLocal
#print axioms OnBytes.RunA.filesOf_coherent
