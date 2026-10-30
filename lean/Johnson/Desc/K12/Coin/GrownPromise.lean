-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GrownPromise.lean: **THE PROMISE MAY GROW INSIDE A CHAIN WITHOUT A LETTER OF
THE FILE's TURNING.** Definitions, statements and proofs. No kind is named.

Why. The rule of composition for a file (`plainOf`, `file_leads₁`:
Johnson/Desc/Plain/FileChains.lean) takes, for the first chain, one premise for each block:
`EachLeads Pl.on₁ Pl.Q₁ 0 …`: block k's law starts from the table's promise at border k. A kind's
law may want more of the public record there than the table's fixed text says (that the book of
trees is in order; that the seats are carried). BUT OF THE TABLE Pl THE FILE's PLAIN FORM READS THE
PROMISES AT THE THREE CHAINS' FIRST BORDERS ALONE (`plainOf`: on₀ · on₁ · on₂): the borders inside a
chain stand in the proof, not in the statement. So a condition X that holds at the chain's first
state and that every block's yes hands on may be laid beside the table's promise at every border,
and the first chain's law comes out AT THE TABLE AS IT IS.
  `leads_and_kept`: a law, and what a yes gives for certain, in one law.
  `EachGrown on Q X`: one premise for each block: ITS LAW FROM THE GROWN PROMISE (on k ∧ X k); A
    YES HANDS X ON (from X k to X (k + 1): no game: a fact on the block's text); the table's own
    step, which may use X k.
  `eachLeads_of_grown`: it gives `EachLeads` at the grown promise and relation.
  `eachGrown_true`: at X := True it is `EachLeads` itself. `grown_live`: X cannot be emptied behind
    a yes.
  `steps_mono`: relations in a row, weakened one by one.
  `grow₁ Pl X`: the table with X laid beside its first chain's promises and relations.
  `file_leads₁_grown`: **`file_leads₁`'s CONCLUSION, TO THE LETTER, AT Pl ITSELF**, from
    `EachGrown Pl.on₁ Pl.Q₁ X`, "X 0 holds at the chain's first state wherever the table's first
    promise does", and the glues AT Pl.
WHAT KEEPS X HONEST. X := False everywhere makes every law free, but fails at the first state. X
true at 0 alone fails at "a yes hands X on" at the first block that ever says yes. X := True is
`EachLeads` itself.
Limits. Nothing on soundness. No X is shown to be handed on by any block here. The like for the
shared chain (in two parts) and the last chain is not typed here; at the last chain the first state
is made of the two earlier chains' ends: X 0 there wants what they hand on.

-/
import Johnson.Desc.Plain.FileChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K12.Coin
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (steps)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

/-- A law, and what a yes gives for certain, in one law. -/
theorem leads_and_kept {A B : Type} {K : Reduction A B} {on : A → Prop} {Q R : A → B → Prop}
    {ε : Err K.shape} (h : K.Leads on Q ε) (hk : ∀ a τ b, on a → K.out a τ = some b → R a b) :
    K.Leads on (fun a b => Q a b ∧ R a b) ε :=
  Reduction.Leads.conseq h (fun _ ha => ha) (fun a τ b ha hb q => ⟨q, hk a τ b ha hb⟩)

/-- Relations in a row, weakened one by one. -/
theorem steps_mono {A : Type} {Q Q' : ℕ → A → A → Prop} (h : ∀ i a b, Q i a b → Q' i a b) :
    ∀ (n i : ℕ) (a c : A), steps Q i n a c → steps Q' i n a c
  | 0, i, a, c, hs => h i a c hs
  | n + 1, i, a, c, ⟨b, h1, h2⟩ => ⟨b, h i a b h1, steps_mono h n (i + 1) b c h2⟩

section
variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **One premise for each block, at a promise that has grown by X.** -/
def EachGrown (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop)
    (X : ℕ → S × F.E.Str → Prop) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.Leads (fun a => on i a ∧ X i a) (Q i) p.err ∧
      (∀ a τ b, on i a → X i a → p.ior.red.out a τ = some b → X (i + 1) b) ∧
      (∀ a b, on i a → X i a → Q i a b → on (i + 1) b) ∧ EachGrown on Q X (i + 1) l

theorem eachLeads_of_grown (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (X : ℕ → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachGrown on Q X i l →
      EachLeads (fun k a => on k a ∧ X k a) (fun k a b => Q k a b ∧ X (k + 1) b) i l
  | [], _, _ => trivial
  | _ :: l, i, h =>
    ⟨leads_and_kept h.1 (fun a τ b ha hb => h.2.1 a τ b ha.1 ha.2 hb),
      fun a b ha hq => ⟨h.2.2.1 a b ha.1 ha.2 hq.1, hq.2⟩,
      eachLeads_of_grown on Q X l (i + 1) h.2.2.2⟩

/-- At X := True the grown premise is `EachLeads` itself: the rule takes nothing away. -/
theorem eachGrown_true (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachLeads on Q i l →
      EachGrown on Q (fun _ _ => True) i l
  | [], _, _ => trivial
  | _ :: l, i, h =>
    ⟨Reduction.Leads.conseq h.1 (fun _ ha => ha.1) (fun _ _ _ _ _ q => q),
      fun _ _ _ _ _ _ => trivial, fun a b ha _ hq => h.2.1 a b ha hq,
      eachGrown_true on Q l (i + 1) h.2.2⟩

/-- **X cannot be emptied behind a yes**: where block i puts out from a statement inside the grown
promise, X (i + 1) holds of what it puts out. So an X that is false at a border makes the law
behind that border free only if no statement inside the grown promise is ever passed on to it. -/
theorem grown_live (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop)
    (X : ℕ → S × F.E.Str → Prop) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (i : ℕ)
    (h : EachGrown on Q X i (p :: l)) (a : S × F.E.Str) (τ : _root_.Iop.Tr p.ior.red.shape)
    (b : S × F.E.Str) (h1 : on i a) (h2 : X i a) (hb : p.ior.red.out a τ = some b) : X (i + 1) b :=
  h.2.1 a τ b h1 h2 hb

end

section Main
variable {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3) {T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W} {Pl : PPlaces D all S₁ S₂ S₃}
  (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
  (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
  (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
  {M : Y × (oneExternalString (2 ^ D.a) SgX).Str → X₁ × (EAll D all).Str → Prop}
  {L₁ : X₁ × (EAll D all).Str → Prop} {L₂ : X₂ × (EAll D all).Str → Prop}
  (d : X₁ × (EAll D all).Str)

/-- The table with X laid beside its first chain's promises and relations. -/
def grow₁ (Pl : PPlaces D all S₁ S₂ S₃) (X : ℕ → S₁ × (EAll D all).Str → Prop) :
    PPlaces D all S₁ S₂ S₃ :=
  { Pl with
    on₁ := fun k a => Pl.on₁ k a ∧ X k a
    Q₁ := fun k a b => Pl.Q₁ k a b ∧ X (k + 1) b }

/-- **The first chain's law at the table as it is, from the blocks' laws at the grown promise.** -/
theorem file_leads₁_grown (hf : T.Fits) (X : ℕ → S₁ × (EAll D all).Str → Prop)
    (hX0 : ∀ (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str),
      Pl.on₁ 0 (T.in₁ x, (y, fun _ => [])) → X 0 (T.in₁ x, (y, fun _ => [])))
    (he : EachGrown Pl.on₁ Pl.Q₁ X 0 (T.p₁ :: T.l₁)) (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).K₁.Leads
      (fun a => Pl.on₁ 0 (T.in₁ a.1, (a.2, fun _ => [])))
      (fun a b => Pl.on₂ 0 (T.in₂ b.1, b.2) ∧ (L₁ b → M a b))
      (0, errOwn T.p₁ T.l₁ D.ds₁ h₁) := by
  have G' : Glues T (grow₁ Pl X) M L₁ L₂ :=
    ⟨fun x y b h hs => G.g₁ x y b h.1 (steps_mono (fun _ _ _ q => q.1) _ _ _ _ hs), G.g₂, G.g₃⟩
  have he0 := eachLeads_of_grown Pl.on₁ Pl.Q₁ X (T.p₁ :: T.l₁) 0 he
  have he' : EachLeads (grow₁ Pl X).on₁ (grow₁ Pl X).Q₁ 0 (T.p₁ :: T.l₁) := he0
  have k := file_leads₁ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf he' G'
  exact Reduction.Leads.conseq k (fun a ha => ⟨ha, hX0 a.1 a.2 ha⟩) (fun _ _ _ _ _ q => q)

end Main

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.eachLeads_of_grown
#print axioms VerifiableInference.Desc.K12.Coin.eachGrown_true
#print axioms VerifiableInference.Desc.K12.Coin.grown_live
#print axioms VerifiableInference.Desc.K12.Coin.file_leads₁_grown
