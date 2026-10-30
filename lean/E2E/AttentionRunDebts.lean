-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionRunDebts.lean: at the lists of the attention segments' own rounds (kind K5: the label of
that sub-protocol in the description) at the sides built from a filling's lots, at letters that leave
a row whole: On holds at all arguments, and the bound holds where the rule's clause on positions asks.

  attention_list_is_row   a list of this kind is a row of the lot, its letters forgotten
  attention_list_on       L.On everywhere
  attention_list_bud      the clause on L.bud, at every number of rounds and trees in front and every
                          list of draws, due or not: so that clause's own premises are not spent

What the law says and does not say is in the head of Honest/K5/Law/AttentionAtAFilling.lean.
No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.KindPaysOfALot
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionAtAFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.TheSides
open ProofFile.Honest ProofFile.Honest.K5
open VerifiableInference.Desc (KindName)

variable {W₀ Rc X₀ X : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
  {mine : List (SLot (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst)}
  {named : ∀ s ∈ mine, P.lots.any (fun L => L.name == s.name) = true}
  {apart : (mine.map (·.name)).Nodup}
  {hm : ∀ L ∈ P.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
    (s.rows A.Z A.G).map (·.half) = L.halves A.Z A.G}
  {shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)}
  {hs : shared.map (·.half) = P.shared A.Z A.G}
  {second : List (Unlettered (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst)}
  {h₃ : second.map (·.half) = P.second A.Z A.G}
  {Ls : Letters A.F A.B W₀ Rc OnBytes.TableKey Cells X₀ X}
  {f₁ : List (Fall A.F.S₁)} {f₂ : List (Fall A.F.S₂)} {f₃ : List (Fall A.F.S₃)}

/-- **A list of this kind is a row of the lot, its letters forgotten.** CONDITIONAL: hAlone; hk; hb: the
letters leave a row whole. -/
theorem attention_list_is_row
    (hAlone : ∀ M ∈ P.lots, M = k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 ∨
      ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K5)
    (hk : k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3 ∈ mine)
    (hb : ∀ u, (Ls.first u).bare = u) :
    ∀ L ∈ (theSides A.F Ls (overlaySlots P A.Z A.G mine named apart hm shared hs second h₃).rows
        f₁ f₂ f₃).first, L.place.kind = KindName.K5 → L.bare ∈ rowsOfReturn A := by
  intro L hL hkind
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hL
  rw [hb u]
  have hk' : u.place.kind = KindName.K5 := (Ls.keeps₁ u).1 ▸ hkind
  obtain ⟨l, hl, hul⟩ := rows_of_overlay (Z := A.Z) (Gr := A.G)
    (ls := [k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3])
    apart (fun l h => by rw [List.mem_singleton.1 h]; exact hk) hm (fun M hM => by
      rcases hAlone M hM with rfl | hno
      · exact Or.inl ⟨_, List.mem_singleton.2 rfl,
          congrArg HLot.name (k5SLot_toHLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X)
            (Pb := ProofFile.Inst) id keyOfK3)⟩
      · exact Or.inr hno) u hu hk'
  obtain rfl := List.mem_singleton.1 hl
  exact hul

/-- **At a list of this kind On holds at all arguments.** CONDITIONAL: hl; hAlone; hk; hb. -/
theorem attention_list_on (hl : AttentionLawAt A)
    (hAlone : ∀ M ∈ P.lots, M = k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 ∨
      ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K5)
    (hk : k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3 ∈ mine)
    (hb : ∀ u, (Ls.first u).bare = u) :
    ∀ L ∈ (theSides A.F Ls (overlaySlots P A.Z A.G mine named apart hm shared hs second h₃).rows
        f₁ f₂ f₃).first, L.place.kind = KindName.K5 → ∀ v ca m front, L.On v ca m front :=
  fun L hL hkind v ca m front =>
    hl.on L.bare (attention_list_is_row hAlone hk hb L hL hkind) v ca m front

/-- **At a list of this kind the clause on positions holds**, at every number of rounds and trees in
front and every list of draws. CONDITIONAL: hl; hAlone; hk; hb. -/
theorem attention_list_bud (hl : AttentionLawAt A)
    (hAlone : ∀ M ∈ P.lots, M = k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 ∨
      ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K5)
    (hk : k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3 ∈ mine)
    (hb : ∀ u, (Ls.first u).bare = u) :
    ∀ L ∈ (theSides A.F Ls (overlaySlots P A.Z A.G mine named apart hm shared hs second h₃).rows
        f₁ f₂ f₃).first, L.place.kind = KindName.K5 → ∀ σ, L.side A.F.first.blocksInOrder = some σ →
      ∀ u ∈ σ.members, ∀ (n N : Nat) (ρ : Draws),
        L.bud u.number ((ρ.first.drop n).take u.rounds.length)
          (asksFrom (treeAsks A.F ρ 0) (u.rounds.map (·.2.length)) N) := by
  intro L hL hkind σ hσ u hu n N ρ
  have hr := attention_list_is_row hAlone hk hb L hL hkind
  obtain ⟨-, hall⟩ := hl.rows L.bare hr
  obtain ⟨-, -, hm'⟩ := hall [] σ hσ
  obtain ⟨-, -, -, -, -, -, -, hbud⟩ := hm' u hu
  exact hbud (treeAsks A.F ρ 0) N ((ρ.first.drop n).take u.rounds.length)

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.attention_list_is_row
#print axioms AtPublicFiles.TheSides.attention_list_on
#print axioms AtPublicFiles.TheSides.attention_list_bud
