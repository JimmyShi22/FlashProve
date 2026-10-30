-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSeed.lean: THE SAMPLE's TIE OF THE FILLING, FILLED WITH THE SENDING KIND's OWN SeedIs (Johnson/Desc/K1/Law/SeedIs.lean). In Johnson/RunOne/KeyFillBase.lean's baseFam the letter rowIs says «the record x, as message number o, spells the seed ρ and the answers v».
  rowIsK              THE LETTER, FILLED: x is marked as sampled; its sample rows are just the kind's one row at a point z, a factor β and a target t, FOR THE NUMBER o THAT IS HANDED; (z, β) read as ρ; the answer is t's reading. It is SeedIs with «the statement holds x at o, at the codes, at the shape» cut off
  stAt_eq · seed_at · seedIsS_iff₁   THE TWO FORMS ARE ONE TIE: KeyFillSrc.lean's seedIsS at the first chain's source ⟺ the plan gives the member's number a number o and SeedIs holds of the chain's statement at o
  uniqK               (uniq) OF THE TIE IS A THEOREM, UNDER THE SENDING KIND's Tie cs s (Johnson/Desc/K1/Law/Port2.lean: four public Booleans): one record has one row; by coef_port_main | coef_port_mask (Port4.lean) the row's coefficient at every real entry is the library's matrix at ρ: so two seeds that the record spells have one sample map; the answers: the row's target
  rowIsK_ledger | rowIsK_groups · smReadsK | smGroupsK | readsLK   the tie reads neither ledger nor groups: so SmReads | SmGroups | ReadsL hold at baseFam WITHOUT A PREMISE
  seals_seed₁         SealReads at B.h₁ at the tie in the form fun a ρ v => ∃ y₀, SeedIs cs s a.2.d.st o₀ ρ y₀ ∧ v = fun _ => y₀: to the letter the premise of tie_of_sealReads (Johnson/Top/Fire/Code/Row10Tie.lean)
  sealsK_h_j | laysK_h_j | promiseK_h_j   KeyFillBase.lean's nine AT THE FILLED TIE: (uniq) IS NO PREMISE ANY MORE: Tie stands for it
  tieS_fam            so: the sending kind's Sealed (Johnson/Desc/K1/Law/GoodSend3.lean) at the reader symsW ∘ wordOf gives hasSmp ∧ NoColl at the seat at B.h₁: the form of the field tieS of Left10… · idx_one: the index there is 0 at one message
OBJECT: SeedIs | Sealed | Tie; tie_of_sealReads · USER: imported by Johnson/Top/Fire/Code/KeyAtBase.lean, Johnson/RunOne/Law/K12PaysOfLaw210.lean, Johnson/RunOne/KeyFillSmMoves.lean, Johnson/RunOne/KeyFillSeedAt.lean, Johnson/RunOne/KeyFillWords.lean, Johnson/RunOne/KeyFillSmOnly.lean (meant: Left10…'s tieS at B := baseFam) · LETTERS: cs · l · num · at_ · orc₁ · decT · recOf.
NOT SAID: that a block lays such a row (seedIs_behind, Johnson/Desc/K1/Law/SeedIs.lean; not called) · THE FIVE TIES AT THE CALL: the sending's codes · shape · RADIUS are cs, the member's (the radius has the weight: one number must serve the sending kind's condition on the plan and the library's allMeet) · its reader of the words is this one («words»: a functional equation on the reader: open) · the index · the second and third chain's like. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillBase
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Top.Fire.Code.Row10Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs Sealed ReadsOne Tie sampleRow coef_port_main coef_port_mask)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

/-- **THE LETTER rowIs, FILLED WITH THE SENDING KIND's OWN TIE.** -/
def rowIsK (i : Fin l.length) (o : ℕ) (x : OnBytes.Oracle) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) : Prop :=
  ∃ (z : List OnBytes.E) (β t : OnBytes.E), x.sampled = true ∧ x.sampleRows = #[sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o z β 0 t] ∧
    ReadsOne cs (l.get i).1 z β ρ ∧ v = fun _ => readE t

theorem stAt_eq (St : OnBytes.Statement) (o : ℕ) (c : OnBytes.Codes) (o' : ℕ) (x : OnBytes.Oracle) :
    stAt St o = some (c, o', x) ↔ St.codes = c ∧ o = o' ∧ St.oracles[o]? = some x := by
  constructor
  · intro h
    obtain ⟨x₀, hx, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e3, e4⟩ := Prod.mk.inj e2
    exact ⟨e1, e3, e4 ▸ hx⟩
  · rintro ⟨rfl, rfl, hx⟩
    unfold stAt
    rw [hx]
    rfl

/-- **The two forms are one tie**, at a statement and a number that may lack. -/
theorem seed_at (i : Fin l.length) (St : OnBytes.Statement) (n? : Option ℕ) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    (∃ o x, n?.bind (stAt St) = some (cs, o, x) ∧ x.shape = (l.get i).1 ∧ rowIsK cs l i o x ρ v) ↔
      ∃ o, n? = some o ∧ ∃ y₀, SeedIs cs (l.get i).1 St o ρ y₀ ∧ v = fun _ => y₀ := by
  constructor
  · rintro ⟨o, x, h1, h2, z, β, t, h3, h4, h5, h6⟩
    obtain ⟨o₀, ho, hs⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨hc, rfl, hx⟩ := (stAt_eq St o₀ cs o x).1 hs
    exact ⟨o₀, ho, readE t, ⟨hc, x, z, β, t, hx, h2, h3, h4, h5, rfl⟩, h6⟩
  · rintro ⟨o, rfl, y₀, ⟨hc, x, z, β, t, hx, h2, h3, h4, h5, rfl⟩, rfl⟩
    exact ⟨o, x, (stAt_eq St o cs o x).2 ⟨hc, rfl, hx⟩, h2, z, β, t, h3, h4, h5, rfl⟩

/-- **(uniq) OF THE TIE, UNDER THE SENDING KIND's Tie.** -/
theorem uniqK (i : Fin l.length) (hT : Tie cs (l.get i).1) :
    ∀ o x ρ v ρ' v', rowIsK cs l i o x ρ v → rowIsK cs l i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
  rintro o x ρ v ρ' v' ⟨z, β, t, _, hr, hR, rfl⟩ ⟨z', β', t', _, hr', hR', rfl⟩
  have e : #[sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o z β 0 t] = #[sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o z' β' 0 t'] := hr.symm.trans hr'
  have er : sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o z β 0 t = sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o z' β' 0 t' := by
    have h0 := congrArg (fun A : Array OnBytes.Row => A[0]?) e
    exact Option.some.inj h0
  have et : t = t' := congrArg OnBytes.Row.target er
  have hmat : ∀ j, (OmAt cs l i).row () ρ j = (OmAt cs l i).row () ρ' j := by
    intro j
    match (j : (Fin (l.get i).1.mainRows × Fin (pMain cs (l.get i).1).ell) ⊕ (Fin (l.get i).1.maskRows × Fin (pMask cs (l.get i).1).ell)) with
    | .inl q =>
      rw [← coef_port_main hT (l.get i).2 o z β t ρ hR q, ← coef_port_main hT (l.get i).2 o z' β' t' ρ' hR' q, er]
    | .inr q =>
      rw [← coef_port_mask hT (l.get i).2 o z β t ρ hR q, ← coef_port_mask hT (l.get i).2 o z' β' t' ρ' hR' q, er]
  refine ⟨?_, by rw [et]⟩
  funext u s
  show ∑ j, (OmAt cs l i).Z.mat ρ s j * u j = ∑ j, (OmAt cs l i).Z.mat ρ' s j * u j
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (OmAt cs l i).Z.mat ρ s j = (OmAt cs l i).Z.mat ρ' s j := hmat j
  rw [hj]

theorem rowIsK_ledger (i : Fin l.length) (o : ℕ) (x : OnBytes.Oracle) (L : Option OnBytes.Ledger) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    rowIsK cs l i o { x with ledger := L } ρ v ↔ rowIsK cs l i o x ρ v := Iff.rfl

theorem rowIsK_groups (i : Fin l.length) (o : ℕ) (x : OnBytes.Oracle) (g : List ℕ) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    rowIsK cs l i o { x with groups := g } ρ v ↔ rowIsK cs l i o x ρ v := Iff.rfl

variable (num : Fin l.length → ℕ) (at_ : Where) {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- The tables' one reading, with the sample's tie filled. -/
abbrev baseK : BaseSt Cells Fill.Tab (Σ i : Fin l.length, (OmAt cs l i).Smp) Rec := baseFam cs l num at_ (rowIsK cs l) decT recOf orc₁

theorem smReadsK : (baseK cs l num at_ decT recOf orc₁).SmReads := smReads cs l num at_ (rowIsK cs l) decT recOf orc₁ fun i o x L ρ v => rowIsK_ledger cs l i o x L ρ v
theorem smGroupsK : (baseK cs l num at_ decT recOf orc₁).SmGroups := smGroups cs l num at_ (rowIsK cs l) decT recOf orc₁ fun i o x g ρ v => rowIsK_groups cs l i o x g ρ v
theorem readsLK : KeyRows1.ReadsL (baseK cs l num at_ decT recOf orc₁).h₁ := readsL cs l num at_ (rowIsK cs l) decT recOf orc₁ fun i o x L ρ v => rowIsK_ledger cs l i o x L ρ v

/-- **THE TWO FORMS ARE ONE TIE, at the first chain.** -/
theorem seedIsS_iff₁ (i : Fin l.length) (a : Xi × FirstState) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i a ρ v ↔ ∃ o, orc₁ (num i) = some o ∧ ∃ y₀, SeedIs cs (l.get i).1 a.2.d.st o ρ y₀ ∧ v = fun _ => y₀ :=
  seed_at cs l i a.2.d.st (orc₁ (num i)) ρ v

section
variable {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **SealReads AT B.h₁ AT THE TIE IN THE FORM THAT tie_of_sealReads TAKES.** -/
def seals_seed₁ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (o₀ : ℕ) (ho : orc₁ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) :
    SealReads F (baseK cs l num at_ decT recOf orc₁).h₁ str
      (fun y' => (portOmZ cs (l.get i).1 (l.get i).2).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (at_ (num i)).1 (at_ (num i)).2)))
      (portOmZ cs (l.get i).1 (l.get i).2).Z.val (fun a ρ v => ∃ y₀, SeedIs cs (l.get i).1 a.2.d.st o₀ ρ y₀ ∧ v = fun _ => y₀) (at_ (num i)).1 (at_ (num i)).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := fun a ρ v h => (seals_h₁ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).has a ρ v ((seedIsS_iff₁ cs l num orc₁ i a ρ v).2 ⟨o₀, ho, h⟩)
  inj := (seals_h₁ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).inj
  mem := fun a y' o z m ρ v hor hz h hM =>
    (seals_h₁ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).mem a y' o z m ρ v hor hz ((seedIsS_iff₁ cs l num orc₁ i a ρ v).2 ⟨o₀, ho, h⟩) hM

/-- **THE FORM OF THE FIELD tieS**: the sending kind's Sealed, at the reader symsW ∘ wordOf, gives the tables' two facts at the seat, at B.h₁. -/
theorem tieS_fam (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (o₀ : ℕ) (ho : orc₁ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (a : Xi × FirstState) (y : Y')
    (h : Sealed cs (l.get i).1 (l.get i).2 (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y) (at_ (num i)).1 (at_ (num i)).2)) a.2.d.st o₀) :
    hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a = true ∧ NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (str y) :=
  LPFD.tie_of_sealReads F (baseK cs l num at_ decT recOf orc₁).h₁ str cs (l.get i).1 (l.get i).2
    (fun y' => symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (at_ (num i)).1 (at_ (num i)).2)) (fun a => a.2.d.st) (fun _ => o₀) (at_ (num i)).1 (at_ (num i)).2
    (seals_seed₁ cs l num at_ decT recOf orc₁ F str hinj hap i o₀ ho hT hlog hm) a y h

/-- SealReads at B.h₁ at the filled tie: (uniq) is no premise any more: the sending kind's Tie stands for it. -/
def sealsK_h₁ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) :
    SealReads F (baseK cs l num at_ decT recOf orc₁).h₁ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i) (seatAt l num at_ i).1 (seatAt l num at_ i).2 :=
  seals_h₁ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)

/-- LaysReads at B.h₁ at the filled tie. -/
def laysK_h₁ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (told : (F.oracleAt (seatAt l num at_ i).1).isSome = true) :
    LaysReads F (baseK cs l num at_ decT recOf orc₁).h₁ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i) (fun y' => Sound.ShownAt F cs l (seatAt l num at_) (str y') i) (seatAt l num at_ i).1 (seatAt l num at_ i).2
      (toU cs (l.get i).1 (l.get i).2) :=
  lays_h₁ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT) told

/-- SealReads at B.h₂ at the filled tie: (uniq) is no premise any more: the sending kind's Tie stands for it. -/
def sealsK_h₂ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) :
    SealReads F (baseK cs l num at_ decT recOf orc₁).h₂ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i) (seatAt l num at_ i).1 (seatAt l num at_ i).2 :=
  seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)

/-- LaysReads at B.h₂ at the filled tie. -/
def laysK_h₂ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (told : (F.oracleAt (seatAt l num at_ i).1).isSome = true) :
    LaysReads F (baseK cs l num at_ decT recOf orc₁).h₂ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i) (fun y' => Sound.ShownAt F cs l (seatAt l num at_) (str y') i) (seatAt l num at_ i).1 (seatAt l num at_ i).2
      (toU cs (l.get i).1 (l.get i).2) :=
  lays_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT) told

/-- SealReads at B.h₃ at the filled tie: (uniq) is no premise any more: the sending kind's Tie stands for it. -/
def sealsK_h₃ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) :
    SealReads F (baseK cs l num at_ decT recOf orc₁).h₃ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i) (seatAt l num at_ i).1 (seatAt l num at_ i).2 :=
  seals_h₃ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)

/-- LaysReads at B.h₃ at the filled tie. -/
def laysK_h₃ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (told : (F.oracleAt (seatAt l num at_ i).1).isSome = true) :
    LaysReads F (baseK cs l num at_ decT recOf orc₁).h₃ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i) (fun y' => Sound.ShownAt F cs l (seatAt l num at_) (str y') i) (seatAt l num at_ i).1 (seatAt l num at_ i).2
      (toU cs (l.get i).1 (l.get i).2) :=
  lays_h₃ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT) told

end

/-- **PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS AT B.h₁, AT THE FILLED TIE**: (uniq) is no premise any more. -/
theorem promiseK_h₁ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : Sound.SeatFits F cs l (seatAt l num at_)) (hFr : FrameHolds cs l (seatAt l num at_) Fr) (hT : ∀ i, Tie cs (l.get i).1)
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : Xi × FirstState) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₁ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') :=
  promise_h₁ cs l num at_ (rowIsK cs l) decT recOf orc₁ F I Fr hinj hap hnum hS hFr (fun i => uniqK cs l i (hT i)) hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- **PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS AT B.h₂, AT THE FILLED TIE**: (uniq) is no premise any more. -/
theorem promiseK_h₂ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : Sound.SeatFits F cs l (seatAt l num at_)) (hFr : FrameHolds cs l (seatAt l num at_) Fr) (hT : ∀ i, Tie cs (l.get i).1)
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : P₂ × St₂) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₂ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') :=
  promise_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F I Fr hinj hap hnum hS hFr (fun i => uniqK cs l i (hT i)) hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- **PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS AT B.h₃, AT THE FILLED TIE**: (uniq) is no premise any more. -/
theorem promiseK_h₃ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : Sound.SeatFits F cs l (seatAt l num at_)) (hFr : FrameHolds cs l (seatAt l num at_) Fr) (hT : ∀ i, Tie cs (l.get i).1)
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : P₃ × St₃) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num (rowIsK cs l) (src₃ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Fill.Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseK cs l num at_ decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') :=
  promise_h₃ cs l num at_ (rowIsK cs l) decT recOf orc₁ F I Fr hinj hap hnum hS hFr (fun i => uniqK cs l i (hT i)) hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- The index of the field tieS at a statement with one message and a sending of one. -/
theorem idx_one (size len k : ℕ) (h1 : size = 1) (h2 : len = 1) (hk : k < len) : size - len + k = 0 := by omega

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.stAt_eq
#print axioms Johnson.RunOne.KeyRows23.seed_at
#print axioms Johnson.RunOne.KeyRows23.uniqK
#print axioms Johnson.RunOne.KeyRows23.rowIsK_ledger
#print axioms Johnson.RunOne.KeyRows23.rowIsK_groups
#print axioms Johnson.RunOne.KeyRows23.smReadsK
#print axioms Johnson.RunOne.KeyRows23.smGroupsK
#print axioms Johnson.RunOne.KeyRows23.readsLK
#print axioms Johnson.RunOne.KeyRows23.seedIsS_iff₁
#print axioms Johnson.RunOne.KeyRows23.seals_seed₁
#print axioms Johnson.RunOne.KeyRows23.tieS_fam
#print axioms Johnson.RunOne.KeyRows23.idx_one
#print axioms Johnson.RunOne.KeyRows23.sealsK_h₁
#print axioms Johnson.RunOne.KeyRows23.laysK_h₁
#print axioms Johnson.RunOne.KeyRows23.promiseK_h₁
#print axioms Johnson.RunOne.KeyRows23.sealsK_h₂
#print axioms Johnson.RunOne.KeyRows23.laysK_h₂
#print axioms Johnson.RunOne.KeyRows23.promiseK_h₂
#print axioms Johnson.RunOne.KeyRows23.sealsK_h₃
#print axioms Johnson.RunOne.KeyRows23.laysK_h₃
#print axioms Johnson.RunOne.KeyRows23.promiseK_h₃
