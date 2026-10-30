-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- seals_h_j | lays_h_j ARE BUILT FIELD BY FIELD: carried along h_j_eq AS WHOLE RECORDS, their DATA (toU | ofU) would stand stuck behind a cast and be the filling's toU | ofU by no rfl, and no caller could lay the two halves together. promise_h₁ | h₂ | h₃ TAKE A SET I OF MEMBERS (AT THE REAL LETTERS «every member at once» CANNOT BE MET at the first and the last chain: a chain's record holds only some of the family's messages).
/-
Johnson/RunOne/KeyFillBase.lean: THE JOINT BETWEEN THE FILLING AND THE KEY FILE's TABLES' ONE READING: a term of BaseSt (Johnson/RunOne/KeyOneReading.lean: the record that the tables' callers bind: B.h₁ | B.h₂ | B.h₃) whose arr | lay | enc | rad | meets are the filling's
(famG, Johnson/Desc/Key/KeyFillFam.lean; the laying by the pad's places; one number, one seat) and whose sm is filled by the record's shape (Johnson/Desc/Key/KeyFillSrc.lean).
  baseFam                 THE TERM. Letters left in it: rowIs (a message's own record spells its sample) · decT · recOf · orc₁
  stAt · src₁ | src₂ | src₃   which (codes, number, record) chain j's reading reads for the witness's message k: h_j's own text, cut out
  h₁_eq | h₂_eq | h₃_eq   B.h_j IS the reading of KeyFillSrc.lean at src_j: AN EQUATION OF READINGS
  arrOk_h · layIdem_h · kreadFam · readsPinned_h   ArrOk | LayIdem | ReadsPinned at B.h_j: theorems; ONE reader of the witness serves the three chains
  smFam_congr · smReads | smGroups · readsL   sm reads neither ledger nor groups WHERE rowIs READS NEITHER (a premise on the letter); so readsL_h₁ (Johnson/RunOne/KeyReadsL.lean) gives ReadsL B.h₁
  shownAt_iff             the tables' own ShownAt (below 2 ^ the told log-length) is Sound.ShownAt (Johnson/Desc/Sound/MsgSig.lean: below 2 ^ aOf), under SeatFits
  seals_h_j | lays_h_j    SealReads | LaysReads at B.h_j at every member · promise_h_j: PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS (those whose message chain j's record holds; meant: the pins that are open at a border) at B.h_j, at the rule's own oracles · not_seedIsS₁: where orc₁ gives a member's number nothing, the first chain's record never holds its sample
«G := famG» IS NOT CLAIMED AND CANNOT BE: BaseSt fixes smp's form: at a (tree, tenant) that is nobody's seat it reads the message number arr j t, where famG has nothing. Nobody reads there.
OBJECT: BaseSt | h₁ | h₂ | h₃ · USER: imported by Johnson/RunOne/Law/KeyAt2932Scope.lean, Johnson/RunOne/KeyFillSeed.lean, Johnson/RunOne/KeyFillBaseAt.lean (meant: whoever hands B to AtFk | On_j | Cl_j) · LETTERS: cs · l · num · at_ · rowIs · decT · recOf · orc₁ · tab.
NOT SAID: rowIs off a real record, its (uniq) (left to other files) · decT | recOf | tab (the stored table) · SeatFits | FrameHolds | the codes | the messages' shapes at the real description: premises, each by name · a border's whole promise. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillSrc
import Johnson.RunOne.KeyOneReading
import Johnson.RunOne.KeyReadsL
import Johnson.RunOne.KeyLettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
  (rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- Member i's seat: where the tables lay its number. -/
abbrev seatAt : Fin l.length → ℕ × ℕ := fun i => at_ (num i)

/-- **THE TERM.** -/
def baseFam : BaseSt Cells Tab (Σ i : Fin l.length, (OmAt cs l i).Smp) Rec where
  arr := famArr l (seatAt l num at_) num
  lay := famLay cs l (seatAt l num at_)
  enc := (mkG (A := Unit) cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT (fun _ => none) fun _ _ _ => none).enc
  rad := (mkG (A := Unit) cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT (fun _ => none) fun _ _ _ => none).rad
  meets := (mkG (A := Unit) cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT (fun _ => none) fun _ _ _ => none).meets
  decT := decT
  recOf := recOf
  sm := smFam cs l rowIs
  orc₁ := orc₁

/-- A statement's message number o, with the statement's codes and the number. -/
def stAt (St : OnBytes.Statement) (o : ℕ) : Option (OnBytes.Codes × ℕ × OnBytes.Oracle) := (St.oracles[o]?).map fun x => (St.codes, o, x)

theorem smAt_stAt {M Smp : Type} (T : BaseSt Cells M Smp Rec) (St : OnBytes.Statement) (o : ℕ) : T.smAt St o = (stAt St o).bind fun q => T.sm q.1 q.2.1 q.2.2 := by
  unfold BaseSt.smAt stAt
  cases St.oracles[o]? <;> rfl

theorem bind_smAt {M Smp : Type} (T : BaseSt Cells M Smp Rec) (St : OnBytes.Statement) (o? : Option ℕ) :
    o?.bind (T.smAt St) = (o?.bind (stAt St)).bind fun q => T.sm q.1 q.2.1 q.2.2 := by
  cases o? with
  | none => rfl
  | some o => exact smAt_stAt T St o

def src₁ (a : Xi × FirstState) (k : ℕ) : Option (OnBytes.Codes × ℕ × OnBytes.Oracle) := (orc₁ k).bind (stAt a.2.d.st)

def src₂ (a : P₂ × St₂) (k : ℕ) : Option (OnBytes.Codes × ℕ × OnBytes.Oracle) :=
  if k < 3 then (orc₁ k).bind (stAt a.1.2.d.st) else (orc₂ k).bind (stAt a.2.st)

def src₃ (a : P₃ × St₃) (k : ℕ) : Option (OnBytes.Codes × ℕ × OnBytes.Oracle) :=
  if k < 3 then (orc₁ k).bind (stAt a.2.st) else
    match a.2.loc.border with
    | some b => (orc₂ k).bind (stAt b.shared.st)
    | none => if k == 4 then stAt a.2.st (nOwn a.2) else none

/-- The reading of KeyFillSrc.lean at the tables' letters. -/
abbrev gAt {A : Type} (recOf' : A → Option Rec) (src : A → ℕ → Option (OnBytes.Codes × ℕ × OnBytes.Oracle)) : Reading A Cells Tab (Σ i : Fin l.length, (OmAt cs l i).Smp) Rec :=
  mkG cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT recOf' (smpOf cs l rowIs (famArr l (seatAt l num at_) num) src)

theorem h₁_eq : (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ = gAt cs l num at_ rowIs decT (fun a => recOf a.1) (src₁ orc₁) := by
  have hs : (baseFam cs l num at_ rowIs decT recOf orc₁).h₁.smp = smpOf cs l rowIs (famArr l (seatAt l num at_) num) (src₁ orc₁) := by
    funext a j t
    exact bind_smAt (baseFam cs l num at_ rowIs decT recOf orc₁) a.2.d.st (orc₁ (famArr l (seatAt l num at_) num j t))
  calc (baseFam cs l num at_ rowIs decT recOf orc₁).h₁
      = mkG cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT (fun a => recOf a.1) (baseFam cs l num at_ rowIs decT recOf orc₁).h₁.smp := rfl
    _ = _ := by rw [hs]

theorem h₂_eq : (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ = gAt cs l num at_ rowIs decT (fun a => recOf a.1.1) (src₂ orc₁) := by
  have hs : (baseFam cs l num at_ rowIs decT recOf orc₁).h₂.smp = smpOf cs l rowIs (famArr l (seatAt l num at_) num) (src₂ orc₁) := by
    funext a j t
    show (if famArr l (seatAt l num at_) num j t < 3 then (orc₁ (famArr l (seatAt l num at_) num j t)).bind ((baseFam cs l num at_ rowIs decT recOf orc₁).smAt a.1.2.d.st)
      else (orc₂ (famArr l (seatAt l num at_) num j t)).bind ((baseFam cs l num at_ rowIs decT recOf orc₁).smAt a.2.st)) =
      (src₂ orc₁ a (famArr l (seatAt l num at_) num j t)).bind fun q => smFam cs l rowIs q.1 q.2.1 q.2.2
    generalize famArr l (seatAt l num at_) num j t = k
    unfold src₂
    by_cases h : k < 3
    · rw [if_pos h, if_pos h]
      exact bind_smAt _ _ _
    · rw [if_neg h, if_neg h]
      exact bind_smAt _ _ _
  calc (baseFam cs l num at_ rowIs decT recOf orc₁).h₂
      = mkG cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT (fun a => recOf a.1.1) (baseFam cs l num at_ rowIs decT recOf orc₁).h₂.smp := rfl
    _ = _ := by rw [hs]

theorem h₃_eq : (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ = gAt cs l num at_ rowIs decT (fun a => recOf a.1.1) (src₃ orc₁) := by
  have hs : (baseFam cs l num at_ rowIs decT recOf orc₁).h₃.smp = smpOf cs l rowIs (famArr l (seatAt l num at_) num) (src₃ orc₁) := by
    funext a j t
    show (if famArr l (seatAt l num at_) num j t < 3 then (orc₁ (famArr l (seatAt l num at_) num j t)).bind ((baseFam cs l num at_ rowIs decT recOf orc₁).smAt a.2.st)
      else match a.2.loc.border with
        | some b => (orc₂ (famArr l (seatAt l num at_) num j t)).bind ((baseFam cs l num at_ rowIs decT recOf orc₁).smAt b.shared.st)
        | none => if famArr l (seatAt l num at_) num j t == 4 then (baseFam cs l num at_ rowIs decT recOf orc₁).smAt a.2.st (nOwn a.2) else none) =
      (src₃ orc₁ a (famArr l (seatAt l num at_) num j t)).bind fun q => smFam cs l rowIs q.1 q.2.1 q.2.2
    generalize famArr l (seatAt l num at_) num j t = k
    unfold src₃
    by_cases h : k < 3
    · rw [if_pos h, if_pos h]
      exact bind_smAt _ _ _
    · rw [if_neg h, if_neg h]
      cases a.2.loc.border with
      | some b => exact bind_smAt _ _ _
      | none =>
        by_cases h4 : (k == 4) = true
        · simp only [h4, if_true]
          exact smAt_stAt _ _ _
        · simp only [h4]
          rfl
  calc (baseFam cs l num at_ rowIs decT recOf orc₁).h₃
      = mkG cs l (seatAt l num at_) (famArr l (seatAt l num at_) num) (famLay cs l (seatAt l num at_)) decT (fun a => recOf a.1.1) (baseFam cs l num at_ rowIs decT recOf orc₁).h₃.smp := rfl
    _ = _ := by rw [hs]

/-! ## The letters' premises, at B.h_j -/

section
variable (hinj : Function.Injective (seatAt l num at_))
include hinj

theorem arr_at (i : Fin l.length) : famArr l (seatAt l num at_) num (seatAt l num at_ i).1 (seatAt l num at_ i).2 = num i := famArr_seat l (seatAt l num at_) num hinj i

/-- **ArrOk**, at every list of numbers of members; at the three readings (they have one arr). -/
theorem arrOk_h₁ (ks : List ℕ) (hks : ∀ k ∈ ks, ∃ i, num i = k) : ArrOk (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ at_ ks := fun k hk => by
  obtain ⟨i, rfl⟩ := hks k hk
  exact arr_at l num at_ hinj i

theorem arrOk_h₂ (ks : List ℕ) (hks : ∀ k ∈ ks, ∃ i, num i = k) : ArrOk (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ at_ ks := fun k hk => by
  obtain ⟨i, rfl⟩ := hks k hk
  exact arr_at l num at_ hinj i

theorem arrOk_h₃ (ks : List ℕ) (hks : ∀ k ∈ ks, ∃ i, num i = k) : ArrOk (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ at_ ks := fun k hk => by
  obtain ⟨i, rfl⟩ := hks k hk
  exact arr_at l num at_ hinj i

end

theorem layIdem_h₁ : LayIdem (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ :=
  layIdem_famLay cs l (seatAt l num at_) (A := Unit) (fun _ _ _ _ => False) (famArr l (seatAt l num at_) num) decT fun _ => none
theorem layIdem_h₂ : LayIdem (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ :=
  layIdem_famLay cs l (seatAt l num at_) (A := Unit) (fun _ _ _ _ => False) (famArr l (seatAt l num at_) num) decT fun _ => none
theorem layIdem_h₃ : LayIdem (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ :=
  layIdem_famLay cs l (seatAt l num at_) (A := Unit) (fun _ _ _ _ => False) (famArr l (seatAt l num at_) num) decT fun _ => none

/-- What the rows read of the witness's message k: the table that PIN k pins. It reads arr and lay alone: so one serves the three chains. -/
def ofFam (w : Wit Cells Unit Tab) (k : ℕ) : Tab :=
  famLay cs l (seatAt l num at_) (at_ k).1 (at_ k).2 (w.msg (famArr l (seatAt l num at_) num (at_ k).1 (at_ k).2)) (w.pad (at_ k).1 (at_ k).2)

/-- **ReadsPinned**, at every reader of the witness whose «of» is that, at every list, at the three readings. -/
theorem readsPinned_h₁ (R : KRead Cells Tab) (hR : R.of = ofFam cs l num at_) (ks : List ℕ) : ReadsPinned (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ at_ R ks := fun w k _ => by
  rw [hR]
  rfl
theorem readsPinned_h₂ (R : KRead Cells Tab) (hR : R.of = ofFam cs l num at_) (ks : List ℕ) : ReadsPinned (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ at_ R ks := fun w k _ => by
  rw [hR]
  rfl
theorem readsPinned_h₃ (R : KRead Cells Tab) (hR : R.of = ofFam cs l num at_) (ks : List ℕ) : ReadsPinned (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ at_ R ks := fun w k _ => by
  rw [hR]
  rfl

/-- Two records of one shape at which rowIs says the same give one sample. -/
theorem smFam_congr (c : OnBytes.Codes) (o : ℕ) (x x' : OnBytes.Oracle) (hsh : x'.shape = x.shape) (hrow : ∀ i ρ v, rowIs i o x' ρ v ↔ rowIs i o x ρ v) :
    smFam cs l rowIs c o x' = smFam cs l rowIs c o x := by
  classical
  show (if c = cs then
    (if h : ∃ i : Fin l.length, (l.get i).1 = x'.shape then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, rowIs h.choose o x' z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none)
    else none) = (if c = cs then
    (if h : ∃ i : Fin l.length, (l.get i).1 = x.shape then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, rowIs h.choose o x z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none)
    else none)
  rw [hsh]
  by_cases hc : c = cs
  · rw [if_pos hc, if_pos hc]
    by_cases h : ∃ i : Fin l.length, (l.get i).1 = x.shape
    · rw [dif_pos h, dif_pos h]
      exact dite_choose_congr _ _ (funext fun z => propext (hrow h.choose z.1 z.2)) fun z => (⟨h.choose, z⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp)
    · rw [dif_neg h, dif_neg h]
  · rw [if_neg hc, if_neg hc]

/-- **SmReads**, where rowIs does not read the ledger. -/
theorem smReads (hL : ∀ i o (x : OnBytes.Oracle) L ρ v, rowIs i o { x with ledger := L } ρ v ↔ rowIs i o x ρ v) : (baseFam cs l num at_ rowIs decT recOf orc₁).SmReads :=
  fun c o x L => smFam_congr cs l rowIs c o x { x with ledger := L } rfl fun i ρ v => hL i o x L ρ v

/-- **SmGroups**, where rowIs does not read the groups. -/
theorem smGroups (hG : ∀ i o (x : OnBytes.Oracle) g ρ v, rowIs i o { x with groups := g } ρ v ↔ rowIs i o x ρ v) : (baseFam cs l num at_ rowIs decT recOf orc₁).SmGroups :=
  fun c o x g => smFam_congr cs l rowIs c o x { x with groups := g } rfl fun i ρ v => hG i o x g ρ v

/-- **ReadsL B.h₁**: readsL_h₁ (Johnson/RunOne/KeyReadsL.lean) at it. -/
theorem readsL (hL : ∀ i o (x : OnBytes.Oracle) L ρ v, rowIs i o { x with ledger := L } ρ v ↔ rowIs i o x ρ v) : KeyRows1.ReadsL (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ :=
  KeyRows1.readsL_h₁ _ (smReads cs l num at_ rowIs decT recOf orc₁ hL)

/-! ## The two ShownAt's -/

theorem shownAt_iff {XI : Type} (F : FileDescription XI) (hS : Sound.SeatFits F cs l (seatAt l num at_)) (y : Strs) (i : Fin l.length) :
    Key.ShownAt F at_ (num i) y ↔ Sound.ShownAt F cs l (seatAt l num at_) y i := by
  obtain ⟨o, _, ho, _, hlog, _⟩ := hS i
  constructor
  · intro h x hx
    exact h o ho x (by rw [hlog]; exact hx)
  · intro h o' ho' x hx
    obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
    exact h x (by rw [← hlog]; exact hx)

/-! ## The filling's theorems at B.h_j -/

section
variable {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **SealReads at B.h₁, at every member.** -/
def seals_h₁ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    SealReads F (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs (src₁ orc₁) i) (seatAt l num at_ i).1 (seatAt l num at_ i).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := by
    rw [h₁_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₁ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).has
  inj := by
    rw [h₁_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₁ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).inj
  mem := by
    rw [h₁_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₁ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).mem

/-- **LaysReads at B.h₁, at every member.** -/
def lays_h₁ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seatAt l num at_ i).1).isSome = true) :
    LaysReads F (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs (src₁ orc₁) i) (fun y' => Sound.ShownAt F cs l (seatAt l num at_) (str y') i) (seatAt l num at_ i).1 (seatAt l num at_ i).2
      (toU cs (l.get i).1 (l.get i).2) where
  ofU := ofU cs (l.get i).1 (l.get i).2
  sec := fun _ u _ => toU_ofU cs (l.get i).1 (l.get i).2 u
  told := told
  mem := by
    rw [h₁_eq]
    exact (src_lays cs l (seatAt l num at_) num rowIs _ _ decT _ (src₁ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR told).mem

/-- **SealReads at B.h₂, at every member.** -/
def seals_h₂ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    SealReads F (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs (src₂ orc₁) i) (seatAt l num at_ i).1 (seatAt l num at_ i).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := by
    rw [h₂_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₂ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).has
  inj := by
    rw [h₂_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₂ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).inj
  mem := by
    rw [h₂_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₂ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).mem

/-- **LaysReads at B.h₂, at every member.** -/
def lays_h₂ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seatAt l num at_ i).1).isSome = true) :
    LaysReads F (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs (src₂ orc₁) i) (fun y' => Sound.ShownAt F cs l (seatAt l num at_) (str y') i) (seatAt l num at_ i).1 (seatAt l num at_ i).2
      (toU cs (l.get i).1 (l.get i).2) where
  ofU := ofU cs (l.get i).1 (l.get i).2
  sec := fun _ u _ => toU_ofU cs (l.get i).1 (l.get i).2 u
  told := told
  mem := by
    rw [h₂_eq]
    exact (src_lays cs l (seatAt l num at_) num rowIs _ _ decT _ (src₂ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR told).mem

/-- **SealReads at B.h₃, at every member.** -/
def seals_h₃ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    SealReads F (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs (src₃ orc₁) i) (seatAt l num at_ i).1 (seatAt l num at_ i).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := by
    rw [h₃_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₃ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).has
  inj := by
    rw [h₃_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₃ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).inj
  mem := by
    rw [h₃_eq]
    exact (src_seals cs l (seatAt l num at_) num rowIs _ _ decT _ (src₃ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR).mem

/-- **LaysReads at B.h₃, at every member.** -/
def lays_h₃ (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seatAt l num at_ i).1).isSome = true) :
    LaysReads F (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seatAt l num at_ i).1 (seatAt l num at_ i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs (src₃ orc₁) i) (fun y' => Sound.ShownAt F cs l (seatAt l num at_) (str y') i) (seatAt l num at_ i).1 (seatAt l num at_ i).2
      (toU cs (l.get i).1 (l.get i).2) where
  ofU := ofU cs (l.get i).1 (l.get i).2
  sec := fun _ u _ => toU_ofU cs (l.get i).1 (l.get i).2 u
  told := told
  mem := by
    rw [h₃_eq]
    exact (src_lays cs l (seatAt l num at_) num rowIs _ _ decT _ (src₃ orc₁) F str hinj hap (arr_at l num at_ hinj) i hlog hm uniqR told).mem

end

/-- **PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS AT B.h₁, AT THE RULE's OWN ORACLES.** -/
theorem promise_h₁ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : Sound.SeatFits F cs l (seatAt l num at_)) (hFr : FrameHolds cs l (seatAt l num at_) Fr)
    (uniqR : ∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : Xi × FirstState) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num rowIs (src₁ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseFam cs l num at_ rowIs decT recOf orc₁).h₁ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₁_eq]
  exact src_promise cs l (seatAt l num at_) num rowIs _ decT _ (src₁ orc₁) F I Fr hinj hap hnum (arr_at l num at_ hinj) hS hFr uniqR hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- **PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS AT B.h₂, AT THE RULE's OWN ORACLES.** -/
theorem promise_h₂ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : Sound.SeatFits F cs l (seatAt l num at_)) (hFr : FrameHolds cs l (seatAt l num at_) Fr)
    (uniqR : ∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : P₂ × St₂) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num rowIs (src₂ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseFam cs l num at_ rowIs decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₂_eq]
  exact src_promise cs l (seatAt l num at_) num rowIs _ decT _ (src₂ orc₁) F I Fr hinj hap hnum (arr_at l num at_ hinj) hS hFr uniqR hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- **PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS AT B.h₃, AT THE RULE's OWN ORACLES.** -/
theorem promise_h₃ {XI : Type} (F : FileDescription XI) (I : Fin l.length → Prop) (Fr : Sound.Frame) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (hnum : Function.Injective num)
    (hS : Sound.SeatFits F cs l (seatAt l num at_)) (hFr : FrameHolds cs l (seatAt l num at_) Fr)
    (uniqR : ∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : P₃ × St₃) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i))
    (hs : ∀ i, I i → seedIsS cs l num rowIs (src₃ orc₁) i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') W ∧
      hasSmp (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a = true ∧
      NoColl F (baseFam cs l num at_ rowIs decT recOf orc₁).h₃ (at_ (num i)).1 (at_ (num i)).2 a (Sound.strsOf Fr y') := by
  rw [h₃_eq]
  exact src_promise cs l (seatAt l num at_) num rowIs _ decT _ (src₃ orc₁) F I Fr hinj hap hnum (arr_at l num at_ hinj) hS hFr uniqR hB y₀ a m₀ r₀ ρ hsend hs c₀

/-- The two halves' data are the filling's own, by rfl: so they can be laid together. -/
theorem seals_h₁_toU {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs) (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    (seals_h₁ cs l num at_ rowIs decT recOf orc₁ F str hinj hap i hlog hm uniqR).toU = toU cs (l.get i).1 (l.get i).2 := rfl

/-- Where orc₁ gives a member's number nothing, the first chain's record never holds its sample. -/
theorem not_seedIsS₁ (i : Fin l.length) (h : orc₁ (num i) = none) (a : Xi × FirstState) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    ¬ seedIsS cs l num rowIs (src₁ orc₁) i a ρ v := by
  rintro ⟨o, x, h1, _⟩
  have h2 : (orc₁ (num i)).bind (stAt a.2.d.st) = some (cs, o, x) := h1
  rw [h] at h2
  exact nomatch h2

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.h₁_eq
#print axioms Johnson.RunOne.KeyRows23.h₂_eq
#print axioms Johnson.RunOne.KeyRows23.h₃_eq
#print axioms Johnson.RunOne.KeyRows23.arrOk_h₁
#print axioms Johnson.RunOne.KeyRows23.arrOk_h₂
#print axioms Johnson.RunOne.KeyRows23.arrOk_h₃
#print axioms Johnson.RunOne.KeyRows23.layIdem_h₁
#print axioms Johnson.RunOne.KeyRows23.layIdem_h₂
#print axioms Johnson.RunOne.KeyRows23.layIdem_h₃
#print axioms Johnson.RunOne.KeyRows23.readsPinned_h₁
#print axioms Johnson.RunOne.KeyRows23.readsPinned_h₂
#print axioms Johnson.RunOne.KeyRows23.readsPinned_h₃
#print axioms Johnson.RunOne.KeyRows23.smFam_congr
#print axioms Johnson.RunOne.KeyRows23.smReads
#print axioms Johnson.RunOne.KeyRows23.smGroups
#print axioms Johnson.RunOne.KeyRows23.readsL
#print axioms Johnson.RunOne.KeyRows23.shownAt_iff
#print axioms Johnson.RunOne.KeyRows23.seals_h₁
#print axioms Johnson.RunOne.KeyRows23.lays_h₁
#print axioms Johnson.RunOne.KeyRows23.seals_h₂
#print axioms Johnson.RunOne.KeyRows23.lays_h₂
#print axioms Johnson.RunOne.KeyRows23.seals_h₃
#print axioms Johnson.RunOne.KeyRows23.lays_h₃
#print axioms Johnson.RunOne.KeyRows23.promise_h₁
#print axioms Johnson.RunOne.KeyRows23.promise_h₂
#print axioms Johnson.RunOne.KeyRows23.promise_h₃
#print axioms Johnson.RunOne.KeyRows23.not_seedIsS₁
#print axioms Johnson.RunOne.KeyRows23.seals_h₁_toU
