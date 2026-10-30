-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/T5.lean: THE CODE SWITCH's TIE FOR THE CLAIMS THAT STAY OPEN ACROSS IT (the
fifth
tie), AT THE COMPOSED MEANING OF THE OPEN CLAIMS (`mgAll D Mg`,
Johnson/Desc/Sound/MgAll.lean), WITH "REACHED" IN HAND. One definition, one structure of Prop, four
theorems. A law file: no sub-protocol imports it.

Why. What is owed at a sub-protocol in the chain of promises (`TiedAtR`,
Johnson/Desc/Sound/ChainOfPromisesR.lean) has a fifth clause: a claim that is open in front of the
sub-protocol, and that its row in the table of joints neither closes nor reads, holds of the
statement
in front, at the extractor's value, if all that is open behind holds. At a code switch FOUR SORTS OF
CLAIMS ALONE stay open so: the parts of the relations of the segments from the switch's own on; the
index masks' pin; the committed table's pin; "every pending claim on the committed table holds".

How. The rule stands in other files and is called, not typed again: `t5R_of_test`
(Johnson/Desc/Sound/RidersTieR.lean) with `goesBack_four`, `rider_mem`, `fourSortsB`
(RidersTie.lean) and `constrQAt_back_any` (ConstrRidesHead.lean). Its relation between the statement
in front and the one behind is filled by `YesRel`: "there is an accept of the piece from the one to
the other, inside the fence". Each sort's two sides: Dec.lean, PinI.lean, Pile.lean, Constr.lean.

What is said.
  `YesRel on p z`: that relation.
  `K2Owes …`: ALL THAT IS STILL OWED AT ONE PLACE, ONE FIELD A DEBT, each with its payer in its
    docstring.
  `back_four`: under it each of the four sorts goes back over `YesRel`.
  `bears_four`: under it each claim that stays open bears a turn of the pads that the switch lays.
  `k02_t5R`: THE TIE, at any map X of witnesses that turns these pads alone.
  `k02_t5R_table`: at the table's own extractor (`extQAt`), read at the state alone as the field t5
    of `TiesAt` reads it (`atPub`, Johnson/Desc/Sound/TiedLays.lean).

Limits. (1) A SENTENCE WITH PREMISES: NO MEMBER OF `K2Owes` IS SHOWN: not at the closed values of D,
not at any. (2) Rch is a parameter: at Rch := never the tie is free and says nothing. (3) Four of
D's parameters that are read here have no closed term or none at our paths: decT, headPart; H
and
smp are named in other files.
(Where this and lean/THEOREM.md differ, the page
holds.) (4) No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.RidersTieR
import Johnson.Desc.Sound.ConstrRidesHead
import Johnson.Desc.Sound.TiedLays
import Johnson.Top.H0.K2Ties.Dec
import Johnson.Top.H0.K2Ties.PinI
import Johnson.Top.H0.K2Ties.Pile
import Johnson.Top.H0.K2Ties.Constr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Place Wit Strs KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Part Meaning Numbers start laysPads)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (headLink)

/-- There is an accept of the piece from the statement in front to the one behind, inside the fence
`on`; z: the public part. -/
def YesRel {P S Cl W : Type} {C : CK} {Fr : Frame} (on : S × Fr.E.Str → Prop)
    (p : Piece C Fr S Cl W) (z : P) : P × S → Strs → P × S → Strs → Prop :=
  fun A y B y' => ∃ a τ b, on a ∧ p.ior.red.out a τ = some b ∧ A = (z, a.1) ∧
    y = strsOf Fr a.2 ∧ B = (z, b.1) ∧ y' = strsOf Fr b.2

/-- The witnesses of the composed meaning. -/
abbrev Wq (rows cols : ℕ) (Tok : Type) : Type := Wit (CellsQ rows cols) Tok MsgT

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {C : CK}
  {Fr : Frame}

variable (D : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wq rows cols Tok))
  (links : List ModelPart) (ps : List Place) (k : ℕ) (z : P)
  (p : Piece C Fr First.S Cl (Wq rows cols Tok)) (Rch : First.S × Fr.E.Str → Prop)

/-- The fence: the table's promise in front, "reached", no mark. -/
def fenceAt (a : First.S × Fr.E.Str) : Prop :=
  onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a ∧ Rch a ∧ a.1.failed = none

/-- **All that is still owed at one place of the code switch.** pl: the place; m: the number of the
segment that the switch opens; M, L: the listed shapes of the oracle messages and their listed
places.
-/
structure K2Owes (pl : Place) (m : ℕ) (M : List OnBytes.OracleShape) (L : Laid) : Prop where
  /-- ON THE LIST OF PLACES (a closed fact) -/
  place : ps[k]? = some pl
  kind : pl.kind = KindName.K2
  /-- A TEST WITH CODE ON THE TABLE: four sorts alone stay open across the place -/
  riders : (ridersL links ps k).all fourSortsB = true
  /-- A TEST ON THE TABLE: the parts that stay open are those of the segments from m on -/
  fromM : ∀ j q, Item.constr j q ∈ ridersL links ps k → m ≤ j
  /-- OURS: an accept of the seated sub-protocol leaves what `Left` names: `left_of_yes` for the
  kind's decision; its door's two quiet steps owe the like -/
  left : ∀ (a : First.S × Fr.E.Str) τ b, p.ior.red.out a τ = some b → Left a.1 b.1
  /-- WHOEVER CLOSES decT: it does not read the verifier's state -/
  decBlind : DecBlind D.decT
  /-- WHOEVER CLOSES H: of the verifier's state its reader of the request reads the request's words
  alone -/
  reqBlind : ∀ (s s' : First.S), s'.req = s.req → D.H.req (z, s') = D.H.req (z, s)
  /-- WHOEVER CLOSES headPart: it goes back where `Left` holds and the committed table's cells are
  the same -/
  headBack : ∀ q i (s s' : First.S) (y y' : Strs) w, Left s s' → y'.cell = y.cell →
    D.headPart q i (z, s') y' w → D.headPart q i (z, s) y w
  /-- AND it bears a turn of the pads that the switch lays -/
  headBears : HeadBears D.headPart (laysPads D.N links pl)
  /-- WHOEVER CLOSES H: what the parts from m on read of the witness bears that turn -/
  hidBears : HidBears D.H (laysPads D.N links pl) m
  /-- THE PLAN's NUMBERS: the index masks' tree was sent in front of the piece -/
  base : D.N.index.1 < p.base
  /-- THE PLAN's NUMBERS: the switch does not lay the index masks' pad -/
  indexOff : D.N.index ∉ laysPads D.N links pl
  /-- WHOEVER CLOSES smp: inside the fence, where `Left` holds, the reader of OOD samples gives
  behind what it gives in front at the members that sit at the index masks' tenant -/
  smp : ∀ (a : First.S × Fr.E.Str) (s' : First.S), fenceAt D Mg₀ links ps k z Rch a →
    Left a.1 s' → ∀ x ∈ D.ms, SitsAt x D.N.index.1 D.N.index.2 →
    D.smp (z, s') x.1 x.2 = D.smp (z, a.1) x.1 x.2
  /-- THE FACTS ON REACHED STATES, with the table's promise: see `IndexFence` -/
  fence : ∀ a : First.S × Fr.E.Str, fenceAt D Mg₀ links ps k z Rch a → IndexFence D.N M L a.1

variable {D Mg₀ links ps k z p Rch}

/-- **Each of the four sorts goes back over an accept inside the fence.** -/
theorem back_four {pl : Place} {m : ℕ} {M : List OnBytes.OracleShape} {L : Laid}
    (O : K2Owes D Mg₀ links ps k z p Rch pl m M L) (i : Item) (hi : fourSortsB i = true) :
    GoesBack (YesRel (fenceAt D Mg₀ links ps k z Rch) p z) (i.holds D.N (mgAll D Mg₀)) := by
  refine goesBack_four D.N (mgAll D Mg₀) _ (fun j q hq => ?_) ?_ ?_ ?_ i hi
  · rw [mgAll_constr]
    refine constrQAt_back_any _ _ _ _ _ j q hq _ ?_ ?_ fun i => ?_
    · rintro _ _ _ _ ⟨a, τ, b, _, hb, rfl, rfl, rfl, rfl⟩
      exact (O.reqBlind a.1 b.1 (O.left a τ b hb).req).symm
    · rintro _ _ _ _ ⟨a, τ, b, _, hb, rfl, rfl, rfl, rfl⟩
      exact (dec_at_yes D.decT O.decBlind p z a b τ hb).symm
    · rintro _ _ _ _ w ⟨a, τ, b, _, hb, rfl, rfl, rfl, rfl⟩ h
      exact O.headBack q i a.1 b.1 _ _ w (O.left a τ b hb)
        (by rw [out_behind p a b τ hb, cell_behind]) h
  · rw [mgAll_pin]
    rintro _ _ _ _ w ⟨a, τ, b, ha, hb, rfl, rfl, rfl, rfl⟩ h
    exact pin_back D.cs D.G D.arr D.smp p D.ms _ _ O.base z a b τ hb
      (O.smp a b.1 ha (O.left a τ b hb)) w h
  · rw [mgAll_pinW]
    rintro _ _ _ _ w ⟨a, τ, b, _, hb, rfl, rfl, rfl, rfl⟩ h
    exact pinW_of_blind D.decT O.decBlind p z a b τ hb w h
  · rw [mgAll_pile]
    rintro _ _ _ _ w ⟨a, τ, b, ha, hb, rfl, rfl, rfl, rfl⟩ h
    exact pile_back D.arr D.mat13 D.N M L z (O.left a τ b hb) (O.fence a ha) w h

/-- **Each claim that stays open bears a turn of the pads that the switch lays**, inside the fence.
-/
theorem bears_four {pl : Place} {m : ℕ} {M : List OnBytes.OracleShape} {L : Laid}
    (O : K2Owes D Mg₀ links ps k z p Rch pl m M L) (i : Item) (hi : i ∈ ridersL links ps k)
    (a : First.S × Fr.E.Str) (ha : fenceAt D Mg₀ links ps k z Rch a) (w w' : (Wq rows cols Tok))
    (hw : PadsTurn (laysPads D.N links pl) w w')
    (h : meansQ D.N (mgAll D Mg₀) (fun s => (z, s)) i a w) :
    meansQ D.N (mgAll D Mg₀) (fun s => (z, s)) i a w' := by
  have hs : fourSortsB i = true := List.all_eq_true.1 O.riders i hi
  cases i with
  | constr j q =>
    have hq : q ≠ Part.lookDigits := by simpa [fourSortsB] using hs
    exact constr_bears (headLink X) D.put (oneDec D.decT D.H) D.headPart D.digitsPart _ m
      O.hidBears O.headBears j (O.fromM j q hi) q hq _ _ w w' hw h
  | pinI =>
    exact pin_bears D.cs D.G D.arr D.smp D.ms _ _ _ O.indexOff _ _ w w' hw h
  | pinW =>
    have e : w.cells = w'.cells := hw .cells fun _ _ c => nomatch c
    have h' : pinWOf D.decT (z, a.1) (strsOf Fr a.2) w := h
    show pinWOf D.decT (z, a.1) (strsOf Fr a.2) w'
    unfold pinWOf at h' ⊢
    rw [← e]
    exact h'
  | pile =>
    exact pile_bears D.arr D.mat13 D.N M L z (O.fence a ha) _ O.indexOff w w' hw h
  | pin _ _ => simp [fourSortsB] at hs
  | pinKept _ => simp [fourSortsB] at hs
  | pinV => simp [fourSortsB] at hs
  | row _ _ => simp [fourSortsB] at hs
  | carry _ => simp [fourSortsB] at hs
  | pileOne => simp [fourSortsB] at hs
  | wrow => simp [fourSortsB] at hs
  | unmarked => simp [fourSortsB] at hs
  | tie _ => simp [fourSortsB] at hs
  | forms _ _ _ => simp [fourSortsB] at hs
  | formsT _ _ _ => simp [fourSortsB] at hs
  | worth _ _ _ => simp [fourSortsB] at hs
  | wo _ => simp [fourSortsB] at hs
  | totalB _ => simp [fourSortsB] at hs
  | total _ => simp [fourSortsB] at hs

/-- **THE CODE SWITCH's FIFTH TIE, WITH "REACHED" IN HAND**, at any map of witnesses that turns the
pads that the switch lays and nothing else. -/
theorem k02_t5R {pl : Place} {m : ℕ} {M : List OnBytes.OracleShape} {L : Laid}
    (O : K2Owes D Mg₀ links ps k z p Rch pl m M L)
    (Y : First.S × Fr.E.Str → First.S × Fr.E.Str → (Wq rows cols Tok) → (Wq rows cols Tok))
    (hY : ∀ a b w, PadsTurn (laysPads D.N links pl) w (Y a b w)) :
    ∀ a τ b w i, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch a →
      ¬ a.1.failed ≠ none → p.ior.red.out a τ = some b →
      onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) (k + 1) b →
      relQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ D.N (mgAll D Mg₀) (fun s => (z, s)) i a (Y a b w) :=
  t5R_of_test D.N (mgAll D Mg₀) links ps k z (YesRel (fenceAt D Mg₀ links ps k z Rch) p z) p Y Rch
    fourSortsB O.riders (back_four O)
    (fun a τ b ha hR hm hb _ => ⟨a, τ, b, ⟨ha, hR, Classical.not_not.1 hm⟩, hb, rfl, rfl, rfl, rfl⟩)
    (fun i ho hn a _ b w ha hR hm _ _ h =>
      bears_four O i (rider_mem links ps k i ho hn) a ⟨ha, hR, Classical.not_not.1 hm⟩ w _
        (hY a b w) h)

/-- **At the table's own extractor**, read at the state alone. -/
theorem k02_t5R_table {pl : Place} {m : ℕ} {M : List OnBytes.OracleShape} {L : Laid}
    (O : K2Owes D Mg₀ links ps k z p Rch pl m M L) (c₀ : CellsQ rows cols)
    (tokOf : P × First.S → Tok) :
    ∀ a τ b w i, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch a →
      ¬ a.1.failed ≠ none → p.ior.red.out a τ = some b →
      onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) (k + 1) b →
      relQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ D.N (mgAll D Mg₀) (fun s => (z, s)) i a
        (atPub (extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links ps (fun x => x) k) z a b
          w) :=
  k02_t5R O _ fun a b w =>
    padsTurn_extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links ps (fun x => x) k pl
      O.place O.kind ((z, a.1), a.2) ((z, b.1), b.2) w

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.back_four
#print axioms VerifiableInference.Desc.First.K2Ties.bears_four
#print axioms VerifiableInference.Desc.First.K2Ties.k02_t5R
#print axioms VerifiableInference.Desc.First.K2Ties.k02_t5R_table
