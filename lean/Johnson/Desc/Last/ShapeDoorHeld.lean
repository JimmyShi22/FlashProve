-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorHeld.lean: TWO TOOLS FOR THE DOOR OF THE LAST CHAIN: what the first
chain's last promise holds of the out-of-domain (OOD) samples; and which messages are the own
group's members, at the block that lays the group as kind K13's files state it. Statements and
proofs; no definition.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`ocEnd_held`**: inside `ocEnd` (the first chain's whole last promise:
    Johnson/Desc/Sound/TieEnd.lean), at a verifier's state without a mark: `Mg₁.held` says yes at
    every sampled tenant of an item that is open at the last border (`sampledIn`,
    Johnson/Desc/First/Borders.lean: the index masks' tenant where `pinI` is open; W's where `pinV`
    is).
  **`whichMembers_atM4`**: `whichMembers_rowsB` (Johnson/Desc/Last/ShapeWhichMembers.lean) at
    `K13.atM4 P (K1.sendAtS P')`: W's sending leaves the rows on the table: so behind the yes every
    member of the own group is the message idx or the claim's W.

Every "there is": none.
Limits. `ocEnd_held` gives what `Mg₁.held` says: that this is `smpHeld` of the state is the
filling's matter. That `pinI` and `pinV` are open at the last border is a premise (hx). NO MEMBER.
Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeWhichMembers
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Numbers ModelPart openSets sampledIn)
open K13.Law (OnLedger linAt)

/-- **At a state without a mark the first chain's last promise holds the OOD sample of every
sampled tenant of an open item.** -/
theorem ocEnd_held {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
    (links : List ModelPart) (ps : List Place) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) (x : ℕ × ℕ)
    (hx : x ∈ sampledIn N₁ ((openSets links ps (First.start links))[ps.length]?.getD [])) :
    Mg₁.held x.1 x.2 (get p) = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · exact List.all_eq_true.1 h'.2.1 x hx

/-- **Which messages are the own group's members, behind the yes of the block at M:4.** -/
theorem whichMembers_atM4 {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G →
      ∀ i ∈ G.members.toList, i = idx ∨ i = l'.w := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := K13.Law.atM4_mid h
  have e := (K1.sendAtS_rows P' s s₁ r₁ r₂ g₁ h1).2
  exact whichMembers_rowsB h2 hsp (e.trans hr) hon

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.ocEnd_held
#print axioms VerifiableInference.Desc.Last.whichMembers_atM4
