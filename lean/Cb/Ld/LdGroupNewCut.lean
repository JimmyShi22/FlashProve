-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewCut.lean: this file is for toys (a toy: a small example instance). The cut of a
closing with standard new messages reads no pad entry.

In standard terms: in the code switch that follows the fold of several oracle codewords the prover
sends new codewords whose messages contain the message and the encoding randomness of the old,
folded word. This file shows that none of the coordinates from which these are read back is a pad
entry or an entry of a rider.

Definitions, statements as theorems, proofs. Generic.

Why: the locations of a closing read (message, randomness) of the open word out of the new messages
(Cb/Ld/LdGroupPlace.lean: `GNew.cut`). For facts on fresh masks to pass the locations, the cut must
read entries that the fact's reading shows. (`MaskFact`, Cb/Req1/LdSegFresh.lean;
`Spec.segWide_loc`, Cb/Req1/LdSegCarry.lean.)

Main names:
  `V.IsPad n`: n is the pad entry of the carried message, or of a message encoded anew.
  `stdNew_place_nopad`: no entry of the folded complex (message or randomness) is placed at a pad
    entry.
  `stdNew_cut_congr`: new messages that agree at all entries that are no pads have the same cut.
  `stdNewR_cut_congr`: the same for the closing with riders (Cb/Ld/LdGroupNewRide.lean; it needs
    `G.P`, the group's set of common long positions, to be nonempty): messages that agree at all
    entries ⟨.inl a, j⟩ that are no pads of the new messages have the same cut: no entry of a rider
    is read.

Limits: this file says nothing on a protocol: two facts on where the cut reads.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewRide

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn)

/-- the pad entries of the new messages -/
def StdNew.IsPad : V.N.N₀.Ent → Prop
  | ⟨none, j⟩ => j = V.Mc.place (.inr ())
  | ⟨some k, j⟩ => j = (V.Mn k).place (.inr ())

theorem stdNew_place_nopad (u : Sh.Cf.J ⊕ Sh.Cf.Q) : ¬ V.IsPad (V.N.place (.inl u)) := by
  have hc : ∀ h : ¬ Hd.InNew V.ag V.pad Unit (.inl u),
      ¬ V.IsPad (V.N.place (.inl u)) := fun h hp => by
    rw [V.N.place_not _ h] at hp
    have hne : (⟨.inl u, h⟩ : Hd.Car V.ag V.pad) ≠ Hd.own V.ag V.pad :=
      fun he => by cases congrArg Subtype.val he
    have hp' : V.eC ⟨.inl u, h⟩ = V.Mc.place (.inr ()) := hp
    rw [V.eC_data _ hne] at hp'
    cases V.Mc.place.injective hp'
  by_cases h : Hd.InNew V.ag V.pad Unit (.inl u)
  · rcases u with c | q
    · obtain ⟨n, hn, rfl⟩ := V.N.inNew_msg h
      intro hp
      rw [ldGroup_place_cell E S G Sh kp Hd V.N n.1 n.2 hn] at hp
      have hp' : V.same n.1 n.2 = (V.Mn n.1).place (.inr ()) := hp
      rw [V.same_cell _ _ hn] at hp'
      cases (V.Mn n.1).place.injective hp'
    · obtain ⟨n, hn⟩ := h
      unfold GHeld.toNew at hn
      split_ifs at hn
      cases hn
  · exact hc h

theorem stdNew_cut_congr (m m' : V.N.N₀.Msg)
    (h : ∀ n : V.N.N₀.Ent, ¬ V.IsPad n → m' n.1 n.2 = m n.1 n.2) : V.N.cut m' = V.N.cut m :=
  Prod.ext (funext fun j => h _ (stdNew_place_nopad V (.inl j)))
    (funext fun q => h _ (stdNew_place_nopad V (.inr q)))

end

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp))

theorem stdNewR_cut_congr (m m' : (V.closeR Sb sl Z A₀ w0 L t tl Rd).N.Msg)
    (h : ∀ n : V.N.N₀.Ent, ¬ V.IsPad n → m' (.inl n.1) n.2 = m (.inl n.1) n.2) :
    (V.closeR Sb sl Z A₀ w0 L t tl Rd).cutN m' = (V.closeR Sb sl Z A₀ w0 L t tl Rd).cutN m :=
  stdNew_cut_congr V (fun a => m (.inl a)) (fun a => m' (.inl a)) h

end
end Cb
