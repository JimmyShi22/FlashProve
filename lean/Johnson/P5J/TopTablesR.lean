-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TopTablesR.lean: THE THREE TABLES' FIT, THE PLACES AND THE THREE IMPLICATIONS AT THE
    CHAINS' ENDS, IN THE SECOND FORM, THROUGH ALL THREE CHAINS: Rch stands
beside the first table's promise at every border (ChainOfPromisesR.lean), AND what it says at the
    LAST border of the
first chain goes on to the two later tables, inside their own condition: `ocR` := the first chain's
    whole promise at its
last border ∧ Rc. So a law at the shared or the last table has Rc in hand (meant: facts along the
    fold at the state
that the first chain hands on). TopTables.lean's first two sections again, made from their text by
    program.
  `ocR` · `TablesFitR` · `plTablesR` · **`glues_of_tablesR`**: the three implications at these
      places, from `TablesFitR` and
    hRc : Rch at the first chain's last border gives Rc, and h0 : no reply is heard at a start.
THE FIELD SH ("at the first chain's last border the shared table's first state has the
    right shape") HAS Rc b.1 IN HAND. Why: by reading nothing in the first
table's promise reads "the key fits" , so under that promise alone SH may be unpayable where the
    public part ranges over every key (not shown false). That fact is to ride in Rch and Rc.
The implication at the first chain's end (`Glues.g₁`) is
    shown at the one end statement b, by `onZeroAt` (Johnson/Desc/Sound/OnZeroAt.lean).
Limits. General in Rch and Rc: neither is named. TopTables.lean's own limits. A rule over letters:
    no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopTables
import Johnson.P5J.LeadsFirstTiedR
import Johnson.Desc.Sound.OnZeroAt

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

section Fit
variable {C : CK} {D : WholeD} {all : List LeftT} {Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type}
  (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
  (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
  (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
  (get : P × S₁' → P₀ × VerifiableInference.Desc.First.S) (N₁ : Numbers)
  (Mg₁ : VerifiableInference.Desc.First.Meaning P₀ W) (links : List ModelPart) (ps : List Place)
  (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
  (Mg : MeaningS S₂' (P × S₁') W) (ML : MeaningL S₃' W) (Pm : PromMeaning S₂')
  (PLm : PromMeaningL S₂' S₃' (P × S₁')) (split : Bool)
  (Q₂ : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → ((P × S₁') × S₂') × (EAll D all).Str → Prop)
  (Rc : P × S₁' → Prop)

/-- What the first chain hands to the two later tables as their own condition: its whole promise at
    its last border,
AND Rc: a fact of what was handed alone (the public part and the verifier's state; no oracle
    message). One with
`ocWith (ocEnd …) Rc` (Johnson/Desc/Sound/PointReached.lean) by unfolding. -/
def ocR : P × S₁' → Strs → Prop := fun p y => ocEnd get N₁ Mg₁ links ps p y ∧ Rc p

/-- **The named premises under which the three tables fit together at the chains' ends, the two
    later tables' own
condition being `ocR`.** Against `TablesFit`: SH and SH₃ have more in hand; stepQ owes Rc behind
    each
step. -/
structure TablesFitR : Prop where
  len₁ : 1 + T.l₁.length = ps.length
  len₂ : 1 + T.l₂.length = (sharedPlaces split).length
  len₃ : 1 + T.l₃.length = lastPlaces.length
  END : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) ps.length i →
    i ∈ endFirst
  TP : ∀ b : (P × S₁') × (EAll D all).Str,
    Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
    Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))
  SH : ∀ b : (P × S₁') × (EAll D all).Str,
    (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b → Rc b.1 →
    Pm.shape 0 (start₂ b.1.1) = true
  PW : ∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
    Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
    Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w
  START : ∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → (tiedMeaning get Mg₁ Mg).unmarked1 (p, s₁)
  SH₃ : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂ T.l₂ (1 + T.l₂.length) b →
    start₃ b.1.1.1 b.1.1.2 b.1.2 = some s → PLm.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true
  POf : ∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
    (PromS.noColl .oOmega).holds (tiedNumbers N₁ Ns) Pm
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
      (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
    (PromS.noColl .oOmega).holds (tiedNumbers N₁ Ns) Pm b.1.2
      (strsOf (frameAt D all D.key₃ T.ft₃) b.2)
  POb : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : W),
    (ItemS.pin .oOmega).holdsSh (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) b.1.2
      (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
    muQ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
      ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w
  stepQ : ∀ k a b, Q₂ k a b →
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂ T.l₂ (k + 1) b ∧
      ((∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ (k + 1) b w) →
        ∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ k a w)

/-- The plain road's conditions and relations at the second and the third chain, from their tables;
the first chain's two fields are laid over by whoever calls it. -/
def plTablesR : PPlaces D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') where
  on₁ := fun _ _ => True
  Q₁ := fun _ _ _ => True
  on₂ := onQ₂ (tiedNumbers N₁ Ns) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂ T.l₂
  Q₂ := Q₂
  on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm
    PLm (ocR get N₁ Mg₁ links ps Rc)
  Q₃ := stepQ₃ T (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) ML Pm PLm
    (ocR get N₁ Mg₁ links ps Rc)

end Fit

section Plain

variable {pp : ScalesAndPolicy} {X : Model.Verify.Public} (N : MatrixNums) (DP : WholeD) {Xi : Type}
  (F : FileDescription Xi) (all : List LeftT) {W P : Type} (H : HidAt X P W N.rows (colsAt N))
  (get : F.XiPub × F.S₁ → P × TS) (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
  (Q₀ : PlacesAt (DP.at frS.P.T.a) all F W) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
  {X₁ X₂ : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (Ex : ℕ → (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → W → W)
  (Ns : NumbersS) (MgS : MeaningS F.S₂ (F.XiPub × F.S₁) W) (ML : MeaningL F.S₃ W)
  (Pm : PromMeaning F.S₂) (PLm : PromMeaningL F.S₂ F.S₃ (F.XiPub × F.S₁)) (split : Bool)
  (Q₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str →
    ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)

variable (Rch : ℕ → (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (Rc : F.XiPub × F.S₁ → Prop)

set_option quotPrecheck false in
/-- The last chain's start, as the rule of composition takes it. -/
local notation "ST3" => fun p a b => (F.start₃ p a b).toOption

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from its table. -/
local notation "QM" => placesM (D := DP.at frS.P.T.a) (all := all) T.ft₁ Nn Mg links ps get
  (firstAt pp putReq H T.ft₁ get) Q₀

set_option quotPrecheck false in
/-- The relation of a block's two statements on the first chain. -/
local notation "Q1" => QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁)
  (QM).on₁ (QM).R₁ Ex (TokStep Ex (fun w => (H.hid w).tok) fun b => repS b.1)

set_option quotPrecheck false in
/-- The second and the third chain's, from their tables. -/
local notation "PT" => plTables T get Nn Mg links ps Ns MgS ML Pm PLm split Q₂

set_option quotPrecheck false in
/-- The same with `ocR` as the two later tables' own condition. -/
local notation "PTR" => plTablesR T get Nn Mg links ps Ns MgS ML Pm PLm split Q₂ Rc

set_option quotPrecheck false in
/-- All three. -/
local notation "PL" => ({ PT with on₁ := (QM).on₁, Q₁ := Q1 } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

set_option quotPrecheck false in
/-- All three, second form. -/
local notation "PLR" => ({ PTR with
    on₁ := fun k a => (QM).on₁ k a ∧ Rch k a
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁)
      (fun k a => (QM).on₁ k a ∧ Rch k a) (QM).R₁ Ex
      (TokStep Ex (fun w => (H.hid w).tok) fun b => repS b.1) } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

/-- **THE PLAIN ROAD'S THREE IMPLICATIONS AT THE CHAINS' ENDS, SECOND FORM THROUGH ALL THREE
    CHAINS.** -/
theorem glues_of_tablesR
    (fitT : TablesFitR F.start₂ ST3 T Q₀ get Nn Mg links ps (firstAt pp putReq H T.ft₁ get) Ns MgS
        Pm
      PLm split Q₂ Rc)
    (hRc : ∀ b, Rch (1 + (atDesc F T).l₁.length) b → Rc b.1)
    (h0 : ∀ x, repS (F.pub x, F.start₁ (F.pub x)) = none) :
    Glues (atDesc F T) PLR (meansM pp N DP F all H get T.ft₁ repS)
      (L₁At F.start₂ T (tiedNumbers Nn Ns) (tiedMeaning get Mg MgS) split)
      (L₂At ST3 T (tiedNumbers Nn Ns) (tiedMeaning get Mg MgS) ML) :=
  ⟨fun x y b _ s =>
      have e := steps_on (fun k a => (QM).on₁ k a ∧ Rch k a) (QM).R₁ Ex (fun w => (H.hid w).tok)
        (fun b => repS b.1) _ 0 _ b s
      ⟨onZeroAt _ _ _ _ _ _ _ _ _ _ _ _ _ F.start₂ T Q₀ get Nn Mg links ps
          (firstAt pp putReq H T.ft₁ get) Ns Pm split Rc fitT.len₁ b e.1 (fitT.TP b)
          (fitT.SH b e.1 (hRc b e.2)) (hRc b e.2),
        fun hL => means_of_steps N DP F all H get T.ft₁ repS Q₀ Nn Mg links ps Ex x y b _
          (steps_imp _ _ (fun _ _ _ hq => ⟨⟨hq.1.1.1, hq.1.2⟩, hq.2⟩) _ _ _ _ s) (h0 x)
          (hL.elim fun w hw =>
            ⟨w, relEndOfZero _ _ _ _ _ _ _ _ _ _ _ _ _ F.start₂ T Q₀ get Nn Mg links ps
              (firstAt pp putReq H T.ft₁ get) Ns MgS Pm split fitT.len₁ fitT.END fitT.PW b w hw⟩)⟩,
    glueTwoAt _ _ _ _ _ _ _ _ _ _ _ _ F.pub F.start₁ F.start₂ ST3 T (tiedNumbers Nn Ns)
      (tiedMeaning get Mg MgS) ML Pm PLm (ocR get Nn Mg links ps Rc) split Q₂ fitT.stepQ fitT.len₂
      fitT.START fitT.SH₃ fitT.POf fitT.POb,
    glueThreeAt _ _ _ _ _ _ _ _ _ _ _ _ F.pub F.start₁ F.start₂ ST3 T (tiedNumbers Nn Ns)
      (tiedMeaning get Mg MgS) ML Pm PLm (ocR get Nn Mg links ps Rc) fitT.len₃⟩

end Plain

#print axioms glues_of_tablesR

end P5J
