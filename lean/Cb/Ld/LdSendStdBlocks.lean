-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdBlocks.lean: the standard sender holds the masks of several coming blocks at free
entries of its messages: the layout of its coins, and the three facts that the rules for masks sent
in advance ask.

Definitions, statement (`Cb.Spec.stdL_blocks`) and proof.
Cb/Ld/LdSendStdL.lean defines a layout `Y : N.StdL F` of the messages of a family N of oracle
messages (data, free entries, pad) and the standard sender `Y.snd dat rest w0` on it, which under
`Y.OK t` fills the data entries from the witness (`dat`) and the free entries with coins in E.
That file also has `Y.layout`, `Y.OK t` (four conditions: `enc`, `lay`, `priv`, `hides`; t has a
number for each member) and `stdL_padLaw`, of which (pad) below is a case.
Cb/Ld/LdSendStdOwn.lean has the case of one block, with `Y.entF` and `Y.NoPad`.
Cb/Ld/LdSendFreshMany.lean defines a layout of a sender's coins for several blocks.
A joint seed is an element of `Sd.D`, for a way `Sd : N.Seeds` (Cb/Ld/LdSendFam.lean) to draw the
members' seeds together.
The rules for masks sent in advance: Ior/KnowCollRulesMask.lean; for a sender's coins
Cb/Ld/LdSendFresh.lean and Cb/Ld/LdSendFreshMany.lean.

Main names:
  `pl b i`: the free entry at which the mask i of the block b stands: any family that is injective
    on all pairs (b, i) (the hypothesis `hpl`): different masks, of one block or of two, stand at
    different free entries, in whichever members.
  `Y.layB pl hpl dat rest w0`: the layout of the coins: blocks b in a finite set Bk, each with masks
    I b → E (assumed: these sets of values are finite); further coins: the other free entries; pads:
    all pads.
  `Spec.stdL_blocks`: for `pl`, `hpl`, Bk and I as above, `Y.OK t` ⇒
    (pad) at every joint seed the law of all answers, over the pads alone, is the same for every
          witness and every fixing of all other coins;
    (own) the entry at `Y.entF (pl b i)` of the messages sent is the mask i of the block b;
    (off) an entry that is no pad and stands at none of b's places reads neither b's masks nor the
          pads.

Limits: this file says nothing on any protocol. It says nothing on the readings of the blocks: for
these see `Spec.layout_laws_entries` (Cb/Ld/LdSendFreshMany.lean). Of its five premises (pad),
(own), (off) are three; the other two (the places `Y.entF (pl b i)` of a block are different, and
none is a pad) are not stated here.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdOwn
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {N : Sig E} (Y : N.StdL F)
variable {Bk : Type} {I : Bk → Type} (pl : ∀ b, I b → Σ a, Y.Fr a)
  (hpl : Function.Injective fun x : Σ b, I b => pl x.1 x.2)

open Classical in
/-- The free entries as (the masks of all blocks; all others): an equivalence, given `hpl`. -/
def splitB :
    (∀ a, Y.Fr a → E) ≃ (∀ b, I b → E) × ({x : Σ a, Y.Fr a // ∀ b i, pl b i ≠ x} → E) where
  toFun φ := (fun b i => φ (pl b i).1 (pl b i).2, fun x => φ x.1.1 x.1.2)
  invFun z := fun a j =>
    if h : ∃ y : Σ b, I b,
      pl y.1 y.2 = ⟨a, j⟩ then z.1 h.choose.1 h.choose.2
      else z.2 ⟨⟨a, j⟩, fun b i hi => h ⟨⟨b, i⟩, hi⟩⟩
  left_inv φ := by
    funext a j
    by_cases h : ∃ y : Σ b, I b, pl y.1 y.2 = ⟨a, j⟩
    · simp only [dif_pos h]
      rw [h.choose_spec]
    · simp only [dif_neg h]
  right_inv z := by
    refine Prod.ext (funext fun b => funext fun i => ?_) (funext fun x => ?_)
    · have h : ∃ y : Σ b, I b, pl y.1 y.2 = ⟨(pl b i).1, (pl b i).2⟩ := ⟨⟨b, i⟩, rfl⟩
      simp only [dif_pos h]
      have e : h.choose = ⟨b, i⟩ := hpl h.choose_spec
      rw [e]
    · have h : ¬ ∃ y : Σ b, I b, pl y.1 y.2 = ⟨x.1.1, x.1.2⟩ := fun ⟨y, hy⟩ => x.2 y.1 y.2 hy
      simp only [dif_neg h]

theorem splitB_symm_at (z : (∀ b, I b → E) × ({x : Σ a, Y.Fr a // ∀ b i, pl b i ≠ x} → E)) (b : Bk)
    (i : I b) :
    (Y.splitB pl hpl).symm z (pl b i).1 (pl b i).2 = z.1 b i :=
  congrFun (congrFun (congrArg Prod.fst ((Y.splitB pl hpl).apply_symm_apply z)) b) i

theorem splitB_symm_off (z : (∀ b, I b → E) × ({x : Σ a, Y.Fr a // ∀ b i, pl b i ≠ x} → E))
    (x : Σ a, Y.Fr a) (hx : ∀ b i, pl b i ≠ x) :
    (Y.splitB pl hpl).symm z x.1 x.2 = z.2 ⟨x, hx⟩ :=
  congrFun (congrArg Prod.snd ((Y.splitB pl hpl).apply_symm_apply z)) ⟨x, hx⟩

variable {W W' : Type} (dat : W → ∀ a, Y.Dt a → E) (rest : W → W') (w0 : W) [Fintype Bk]
  [DecidableEq Bk] [∀ b, Fintype (I b → E)]

open Classical in
/-- The layout of the coins. -/
@[reducible] def layB : (Y.snd dat rest w0).Layout :=
  Y.layout dat rest w0 Bk (fun b => I b → E)
    ({x : Σ a, Y.Fr a // ∀ b i, pl b i ≠ x} → E) (Y.splitB pl hpl)

end Sig.StdL

def Spec.stdL_blocks : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
      (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E) (rest : W → W')
      (w0 : W) (Bk : Type) [Fintype Bk] [DecidableEq Bk] (I : Bk → Type) [∀ b, Fintype (I b → E)]
      (pl : ∀ b, I b → Σ a, Y.Fr a) (hpl : Function.Injective fun x : Σ b, I b => pl x.1 x.2),
    Y.OK t →
    (∀ Sd : N.Seeds, (Y.layB pl hpl dat rest w0).PadLaw Sd) ∧
    (∀ b w ms f η i,
      N.ents ((Y.snd dat rest w0).upM
            ((Y.snd dat rest w0).put w ((Y.layB pl hpl dat rest w0).mk' ms f η)))
          (Y.entF (pl b i)) = ms b i) ∧
    ∀ b w ms ms' f η η' n, (Y.layB pl hpl dat rest w0).oth b ms =
        (Y.layB pl hpl dat rest w0).oth b ms' →
      Y.NoPad n → (∀ i, n ≠ Y.entF (pl b i)) →
      N.ents ((Y.snd dat rest w0).upM
            ((Y.snd dat rest w0).put w ((Y.layB pl hpl dat rest w0).mk' ms f η))) n =
        N.ents ((Y.snd dat rest w0).upM
            ((Y.snd dat rest w0).put w ((Y.layB pl hpl dat rest w0).mk' ms' f η'))) n

theorem stdL_blocks : Spec.stdL_blocks := by
  classical
  intro F E _ _ _ _ _ N Y t W W' dat rest w0 Bk _ _ I _ pl hpl h
  obtain ⟨-, aD, aF, -, -, -, -⟩ := stdL_all F E N Y t W W' dat rest w0 h
  refine ⟨fun Sd =>
      stdL_padLaw F E N Y t W W' dat rest w0 Bk (fun b => I b → E) _ (Y.splitB pl hpl) Sd h,
    fun b w ms f η i => ?_,
    ?_⟩
  · exact (aF w _ (pl b i).1 (pl b i).2).trans (Y.splitB_symm_at pl hpl (ms, f) b i)
  · rintro b w ms ms' f η η' ⟨a, j⟩ hoth ⟨x, hx⟩ hoff
    have hx' : j = (Y.ν a).symm (Sum.inl x) := hx
    show (Y.snd dat rest w0).upM
        ((Y.snd dat rest w0).put w ((Y.layB pl hpl dat rest w0).mk' ms f η)) a j =
      (Y.snd dat rest w0).upM
        ((Y.snd dat rest w0).put w ((Y.layB pl hpl dat rest w0).mk' ms' f η')) a j
    rw [hx']
    rcases x with d | u
    · exact (aD w _ a d).trans (aD w _ a d).symm
    · refine (aF w _ a u).trans (Eq.trans ?_ (aF w _ a u).symm)
      show (Y.splitB pl hpl).symm (ms, f) a u = (Y.splitB pl hpl).symm (ms', f) a u
      by_cases hy : ∃ y : Σ b, I b, pl y.1 y.2 = ⟨a, u⟩
      · obtain ⟨⟨b', i'⟩, hy⟩ := hy
        have hb : b' ≠ b := by
          rintro rfl
          exact hoff i' (by rw [hx', show pl b' i' = ⟨a, u⟩ from hy]; rfl)
        have e1 := Y.splitB_symm_at pl hpl (ms, f) b' i'
        have e2 := Y.splitB_symm_at pl hpl (ms', f) b' i'
        rw [show pl b' i' = ⟨a, u⟩ from hy] at e1 e2
        rw [e1, e2]
        exact congrFun (congrFun hoth ⟨b', hb⟩) i'
      · have hz : ∀ b i, pl b i ≠ (⟨a, u⟩ : Σ a, Y.Fr a) := fun b i hi => hy ⟨⟨b, i⟩, hi⟩
        exact (Y.splitB_symm_off pl hpl (ms, f) ⟨a, u⟩ hz).trans
          (Y.splitB_symm_off pl hpl (ms', f) ⟨a, u⟩ hz).symm

end Cb
