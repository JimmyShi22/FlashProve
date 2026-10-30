-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/KeysByMake.lean: THE LAWS OF KEYS OF A SHARED CHAIN, BY MAKE: what the plain
form's premise for a batch (`EachLeadsBN`, Johnson/Desc/Plain/BothAtDesc.lean) asks of each kind
beside its law, "the key behind the block is a function of the key in front and of the transcript"
(`KeyLaw`, Johnson/Desc/Plain/Moves.lean), HOLDS OF EVERY CHAIN OF LIFTED BLOCKS at the acting
parts. Definitions, statements written as `def … : Prop`, and their proofs.

Why. A reading of the plain form for a batch found: the key is a letter there, and a law of keys is
left to each kind of the shared chain. In the form with witnesses both come by make, for every
description: the key at border k is the ACTING PART there (the chain's own record · the stored table
· the chain's own trees that are sent: `actsOf`, Johnson/Desc/Sound/SharedRule.lean), and a block
that is typed at the chain's own record and lifted, and opens no tree below the chain's first, hands
it on (`liftHands`; along a row: `each_hands`, Johnson/Desc/Sound/FoldSlotsProofs.lean). Here that
is carried over.

What is said.
  `KeyLawOfHandsAct`: a block that hands its acting part on (`Piece.HandsAct`) has the law of keys
    between the two acting parts. Asked beside: the type of the key behind has a member.
  `keyAt get lo p l k`: the key at border k: ONE type at all borders.
  `EachKeyLaw`, `KeysByMake`: along a row of lifted blocks that tile and open no tree below lo.
  `EachLawsBN`: WHAT IS LEFT TO THE KINDS' FILES: for each block its law and the hand-over of the
    condition.
  `EachLeadsBNOfLaws`: with the laws of keys it is `EachLeadsBN`.
  `OneKeyByMake`: AT A DESCRIPTION: what the first chain hands on has, at border 0 of the shared
    chain, the key (s₂ rec, the stored table, no tree): a function of the record and the stored
    table alone: the plain form's premise `oneKey`: from `OfDesc`, `Fits` and "the shared chain's
    first record reads nothing of a request" (start₂ (pub (x, rec)) = s₂ rec). By
    `firstKeyAtDesc`. An example at the end: the plain file's first output IS the row's first
    stage's, by definition.

Every "there is", walked. `KeyLaw`'s function: read by no verifier. The lifted block's own text b₀:
determined by the block.
Limits. Rules: they close no row. Nothing is said of a law. `OneKeyByMake` leaves "start₂ (pub (x,
rec)) = s₂ rec" as a premise: a fact on the description's text.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Plain.BothAtDesc
import Johnson.Desc.Sound.FoldSlotsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open VerifiableInference.Desc.Plain (EachLeadsBN)

variable {S S₀ Cl W κ : Type} {C : CK} {F : Frame}

/-- **A block that hands its acting part on has the law of keys.** -/
def KeyLawOfHandsAct : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (act act' : BKey F S),
    Nonempty act'.1 → p.HandsAct act act' → p.ior.red.KeyLaw act.2 act'.2

/-- **The key at border k: the acting part there.** One type at all borders. -/
def keyAt (get : S → S₀) (lo : ℕ) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (k : ℕ)
    (a : S × F.E.Str) : S₀ × (oneExternalString (2 ^ F.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)) :=
  (actsOf get lo p l k).2 a

/-- Every block of a row has the law of keys, from the key at its number to the next. -/
def EachKeyLaw (key : ℕ → S × F.E.Str → κ) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => p.ior.red.KeyLaw (key i) (key (i + 1)) ∧ EachKeyLaw key (i + 1) l

/-- **The laws of keys, by make.** a₀: some statement of the chain. -/
def KeysByMake : Prop :=
  ∀ (S S₀ Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (lo : ℕ)
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)), S × F.E.Str →
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') → Tiled p l →
    (∀ q ∈ p :: l, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
    (∀ q ∈ p :: l, ∀ d ∈ q.ds, ∀ j ∈ d.opens, lo ≤ j) →
    EachKeyLaw (keyAt get lo p l) 0 (p :: l)

/-- **What is left to the files of a shared chain's kinds.** -/
def EachLawsBN (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.LeadsBN (key i) (on i) (Q i) N p.err ∧ (∀ a b, on i a → Q i a b → on (i + 1) b) ∧
      EachLawsBN key on Q N (i + 1) l

/-- With the laws of keys it is the plain form's premise. -/
def EachLeadsBNOfLaws : Prop :=
  ∀ (S Cl W κ : Type) (C : CK) (F : Frame) (key : ℕ → S × F.E.Str → κ)
    (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ)
    (l : List (Piece C F S Cl W)) (i : ℕ),
    EachLawsBN key on Q N i l → EachKeyLaw key i l → EachLeadsBN key on Q N i l

/-- **One key at the chain's head, by make, at a description.** -/
def OneKeyByMake : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ W)
    (okF : X × Rec → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (_ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT C D.ds₁)
    (_ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT C D.ds₂)
    (_ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT C D.ds₃) (s₂ : Rec → F.S₂),
    OfDesc F T → (atDesc F T).Fits → (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
    ∀ x rec y τ b,
      ((atDesc F T).row tF tJ t3 okF okJ ok3).S₁.ior.red.out ((x, rec), y) τ = some b →
      keyAt Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂ 0 ((atDesc F T).in₂ b.1, b.2) =
        (s₂ rec, y, fun _ _ => none)

theorem keyLawOfHandsAct : KeyLawOfHandsAct := by
  rintro S Cl W C F p act act' ⟨d⟩ ⟨G, hG⟩
  refine ⟨fun k τ => (G k τ).getD d, fun a τ b hb => ?_⟩
  have h := hG a τ
  rw [hb] at h
  show act'.2 b = (G (act.2 a) τ).getD d
  rw [← h]
  rfl

theorem eachKeyLaw_of_hands (act : ℕ → BKey F S) (hne : ∀ k, Nonempty (act k).1) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachHands act i l →
      ∀ (key : ℕ → S × F.E.Str → κ) (e : ∀ k, (act k).1 = κ),
        (∀ k a, cast (e k) ((act k).2 a) = key k a) → EachKeyLaw key i l
  | [], _, _, _, _, _ => trivial
  | p :: l, i, h, key, e, hk => by
    refine ⟨?_, eachKeyLaw_of_hands act hne l (i + 1) h.2 key e hk⟩
    obtain ⟨g, hg⟩ := keyLawOfHandsAct S Cl W C F p (act i) (act (i + 1)) (hne (i + 1)) h.1
    refine ⟨fun k τ => cast (e (i + 1)) (g (cast (e i).symm k) τ), fun a τ b hb => ?_⟩
    rw [← hk (i + 1) b, ← hk i a, hg a τ b hb]
    simp

theorem keysByMake : KeysByMake := by
  intro S S₀ Cl W C F get set lo p l a₀ g1 g2 ht hb ho
  exact eachKeyLaw_of_hands (actsOf get lo p l) (fun k => ⟨(actsOf get lo p l k).2 a₀⟩) (p :: l) 0
    (each_hands get set g1 g2 lo l p 0 (actsOf get lo p l) (fun k => by rw [Nat.zero_add]; rfl) ht
      hb ho) (keyAt get lo p l) (fun _ => rfl) (fun _ _ => rfl)

theorem eachLeadsBNOfLaws : EachLeadsBNOfLaws := by
  intro S Cl W κ C F key on Q N l
  induction l with
  | nil => exact fun _ _ _ => trivial
  | cons p l ih => exact fun i h k => ⟨h.1, h.2.1, k.1, ih (i + 1) h.2.2 k.2⟩

theorem oneKeyByMake : OneKeyByMake := by
  intro C D all X Rec X₁ X₂ W TF TJ T3 tF tJ t3 F T okF okJ ok3 h₁ h₂ h₃ s₂ hO hF one x rec y τ b hb
  have k := firstKeyAtDesc C D all (X × Rec) X₁ X₂ W TF TJ T3 tF tJ t3 F T
    ⟨fun _ _ => True, fun _ _ _ => True, fun _ _ => True, fun _ _ _ => True, fun _ _ => True,
      fun _ _ _ => True⟩ okF okJ ok3 h₁ h₂ h₃ hO ((x, rec), y) τ b hb
  rw [one] at k
  show (Prod.snd ((atDesc F T).in₂ b.1), b.2.1,
    fun j z => if D.t₁ ≤ j ∧ j < (atDesc F T).p₂.base then _ else none) = _
  refine Prod.ext (Prod.ext_iff.1 k).1 (Prod.ext (Prod.ext_iff.1 k).2 ?_)
  funext j z
  show (if D.t₁ ≤ j ∧ j < (atDesc F T).p₂.base then _ else none) = none
  rw [if_neg]
  rw [hF.base₂]
  omega

-- the plain file's first output, of which the premise `oneKey` speaks, is the row's first stage's
example {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type} (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Pl : Plain.PPlaces D all S₁ S₂ S₃) (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂) (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
    (M : Y × (oneExternalString (2 ^ D.a) SgX).Str → X₁ × (EAll D all).Str → Prop)
    (L₁ : X₁ × (EAll D all).Str → Prop) (L₂ : X₂ × (EAll D all).Str → Prop)
    (d : X₁ × (EAll D all).Str) :
    (Plain.plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).out₁ =
      (T.row tF tJ t3 okF okJ ok3).S₁.ior.red.out :=
  rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.oneKeyByMake
#print axioms VerifiableInference.Desc.Sound.keyLawOfHandsAct
#print axioms VerifiableInference.Desc.Sound.keysByMake
#print axioms VerifiableInference.Desc.Sound.eachLeadsBNOfLaws
