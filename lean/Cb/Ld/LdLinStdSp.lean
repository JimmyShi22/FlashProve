-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinStdSp.lean: what the closings with splittings ask, for their masks, of the senders of the
test for linear constraints, all at once, at the standard senders.

In standard terms: the honest senders of the test for linear constraints (a proximity test with
claims on the encoded index) taken as explicit terms; for these the file proves, from conditions on
places and layouts, the conditions that a closing with two splittings asks of the senders for the
masks of its two splittings.

A definition, one statement and its proof (an assembly).
Cb/Ld/LdLinCloseSplitTop.lean (`ldLinSpTop_O`) asks, for the masks of its two splittings: a set Rd
of entries of all oracle messages that holds what the splittings read and the two mask entries;
`Sn.Apart` (`LdLinP.Snd.Apart`, Cb/Ld/LdLinChainFresh.lean); and for the senders of Ω's and of W's
family (the families `NW`, `NU`, `NO` sent with W, G_u, Ω: Cb/Ld/LdLin.lean) a split of the coins
with the conditions `Own.Laws` (`Sig.Sender.Own.Laws`, Cb/Ld/LdSendFresh.lean) at "the family's
messages cut to Rd".

Main names:
  `C.rdNP T`: the set Rd: of the three families of the test: every entry that is no pad entry in
    the layouts of T (Cb/Ld/LdLinStd.lean); of what a preamble has left: every entry.
  `Spec.ldLinStdSp_snd`: for a free entry x₀ of a member of Ω's family (the shared mask) and a free
    entry x₁ of a member of W's family (an instance's mask), from `T.Places` and the conditions of
    these two families' layouts (`T.YW.OK tW`, `T.YO.OK tO`): both entries lie in `C.rdNP T`; so do
    the places lO y, lU k, lW c of ω, u, w; `(T.snd ..).Apart`; the two `Own.Laws`, word for word,
    with the splits `Y.ownOne` (Cb/Ld/LdSendStdOwnCut.lean).

Why all entries of what a preamble has left, its pads among them: these oracle messages are older
than the three families; the readings at which the two masks are fresh hold the whole witness
handed on, so all of them. `ldLinSpTop_O` reads Rd at these entries only through "what the
splittings read lies in Rd". (Masks that stand in a preamble's messages are another matter, and not
this file's.)

Limits: this file says nothing on `Sn.OK`: Cb/Ld/LdLinStd.lean (`ldLinStd_ok`). It says nothing on
the shared mask in G_u's family (the same, with Cb/Ld/LdSendStdOwnCut.lean's `stdL_ownOne` at YU).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdOwnCut

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- Every entry of the three families that is no pad entry; every entry of what a preamble has
left. -/
def LdLinC.rdNP {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (C : LdLinC E ι κ J Y) (T : C.P.Std F) : C.S.Ent → Prop
  | ⟨.inl (.inl (.inl _)), _⟩ => True
  | ⟨.inl (.inl (.inr a)), j⟩ => T.YW.NoPad ⟨a, j⟩
  | ⟨.inl (.inr a), j⟩ => T.YU.NoPad ⟨a, j⟩
  | ⟨.inr a, j⟩ => T.YO.NoPad ⟨a, j⟩

open Classical in
def Spec.ldLinStdSp_snd (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E]
    [Fintype E] [Algebra F E] : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (T : C.P.Std F) (LW : C.P.NW.O → ℕ) (LU : C.P.NU.O → ℕ)
      (LO : C.P.NO.O → ℕ) (tW : C.P.NW.O → ℕ) (tU : C.P.NU.O → ℕ) (tO : C.P.NO.O → ℕ)
      (x₀ : Σ a, T.YO.Fr a) (x₁ : Σ a, T.YW.Fr a),
    T.Places → T.YW.OK tW → T.YO.OK tO →
    (C.rdNP T (C.eO (T.YO.entF x₀)) ∧ C.rdNP T (C.eW (T.YW.entF x₁))) ∧
    ((∀ y, C.rdNP T ⟨C.nO, C.lO y⟩) ∧
      (∀ k, C.rdNP T ⟨C.nU, C.lU k⟩) ∧
      ∀ c, C.rdNP T ⟨C.nW, C.lW c⟩) ∧
    (T.snd LW LU LO tW tU tO).Apart ∧
    (T.YO.ownOne T.datO (fun w => w.2) (fun _ => 0, T.w3) x₀).Laws C.SdO
      (fun m w' => (C.NO.cut (fun n => C.rdNP T (C.eO n)) m, w'))
      (fun u k => (C.NO.ow (fun n => n = T.YO.entF x₀) (fun _ => u) k.1, k.2)) ∧
    (T.YW.ownOne T.datW (fun w => w.2) (fun _ => 0, T.w0) x₁).Laws C.SdW
      (fun m w' => (C.NW.cut (fun n => C.rdNP T (C.eW n)) m, w'))
      (fun u k => (C.NW.ow (fun n => n = T.YW.entF x₁) (fun _ => u) k.1, k.2))

theorem ldLinStdSp_snd {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E]
    [Fintype E] [Algebra F E] :
    Spec.ldLinStdSp_snd F E ι κ J Y := by
  classical
  intro C T LW LU LO tW tU tO x₀ x₁ hP hW hO
  have h0 : C.rdNP T (C.eO (T.YO.entF x₀)) := ⟨Sum.inr x₀.2, rfl⟩
  have h1 : C.rdNP T (C.eW (T.YW.entF x₁)) := ⟨Sum.inr x₁.2, rfl⟩
  exact ⟨⟨h0, h1⟩,
    ⟨fun y => ⟨Sum.inl (T.qO y), hP.lO y⟩,
      fun k => ⟨Sum.inl (T.qU k), hP.lU k⟩,
      fun c => ⟨Sum.inl (T.qW c), hP.lW c⟩⟩,
    ldLinStd_apart C.P T LW LU LO tW tU tO,
    stdL_ownOne F E C.P.NO T.YO tO C.P.W4 C.P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3) x₀ C.P.SdO
      (fun n => C.rdNP T (C.eO n)) hO (fun _ h => h) h0,
    stdL_ownOne F E C.P.NW T.YW tW C.P.WA C.P.W0 T.datW (fun w => w.2) (fun _ => 0, T.w0) x₁ C.P.SdW
      (fun n => C.rdNP T (C.eW n)) hW (fun _ h => h) h1⟩

end Cb
