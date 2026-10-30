-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TieEnd.lean: THE JOINT OF THE FIRST AND THE SHARED CHAIN (`Three.Glue₁`) WITH BOTH TABLES OF JOINTS LAID IN: the first
chain's conditions and relations from its table (`placesM`, Johnson/Desc/Sound/FirstMeans.lean), the shared chain's from its own (`onQ₂`,
`relQ₂`, Johnson/Desc/Sound/BordersSharedQ.lean). Definitions, one small lemma, three statements written as `def … : Prop`, and their proofs. (The promise takes the open public items; frontOk and evalLaid are two of them: ocEnd_pub; ocEnd_laid asks that the promise's table has the two open at the last border. (SH) is asked inside the first chain's last promise alone; the joint's two halves stand apart, for the plain form's rule, which asks them apart; GENERAL IN THE FIRST
CHAIN's RECORD: get: the table's public part and the carried record First.S, in what the first chain hands on: at a real description that record holds more than First.S).

THE TIE OF THE LETTERS. `tiedMeaning`: the shared chain's table's OWN items read the first chain's table's letters AS THEY ARE: W's and the
index masks' pins := its `pin`; the claim on M := its `pileOne`; (Eval) := its `wrow` ("the rows on W": a letter of that table which no row of the first chain opens: it is
opened at the shared chain's point: ONE LETTER FOR BOTH TABLES); "no mark" := its record's field for a failed test is empty.
`tiedNumbers`: W's and the index masks' tenants are its. `ocEnd`: THE SLOT's OWN CONDITION Oc := THE FIRST CHAIN's WHOLE PROMISE AT ITS LAST
BORDER (the table decodes, and: the record is marked, or: the end's book-keeping, the public items that are open there with what each says beside its test, the book's three sizes, held, shown and
no collision at the open pins).

`TieEnd`: `Glue₁` holds at these places, FROM: the first chain is as long as its table · (END) at its last border no item is open but
no mark, the cells' pin, the one claim, the two pins [at a concrete table: by `openIsList` and an evaluation] · (TP) THE ROW table_promise: "the
table decodes with the record" gives the shared chain's promise on the table at `start₂`'s record · (SH) the shared chain's book-keeping at
border 0 holds of the first record that is made inside the first chain's last promise · (PW) the cells' pin at `start₂`'s record (its key) gives the cells' pin at the public part's
record: ONE SENTENCE AT THE JOINT, because `start₂` makes its record of that key.

`ocEnd_laid` (proved): K13's two conditions on the record (`frontOk`: the claim is made of a row; `evalLaid`: (Eval) lies on the own group) stand in the
first chain's promise at its last border WHERE THE TWO ARE AMONG THE PUBLIC ITEMS OPEN THERE (two hypotheses of the theorem): so the slot's own condition gives both at a record without a mark: what the shared chain's point spends.

`OnZeroOfEnd`, `RelEndOfZero`: THE TWO HALVES OF THE JOINT, EACH BY ITSELF: the promise goes forward (from the length, (TP), (SH)); the relation goes back (from the
length, (END), (PW); no promise is asked). `TieEnd` is the two, welded.

ONE PROMISE CAN BE HANDED FROM CHAIN TO CHAIN because `strsOf Fr y` reads of the frame `Fr.a` and `Fr.all` alone (a tree's column is named by the tree's number in
the FILE): at `frameAt D all _ _` the three chains' readings of the strings are one term.

Limits. (END), (TP), (SH), (PW) are premises. (TP) AND (PW) JOIN TWO READERS OF ONE RECORD (the first table's letters read `get b.1`, the shared table's `start₂ b.1.1`): they are payable BY THE MAKE OF
get AND start₂ (the key's record stands in the public part, and `(get (p, s)).1` hangs on p alone); (TP) ONLY WHERE `decodes` IS FILLED BY THE GUARDED DECODER (Johnson/Desc/Sound/TablePromiseAt.lean). (SH) is asked at the records that stand inside the first chain's last promise alone.
WITH Oc FILLED, "Oc IS CARRIED" (asked of every block of the shared chain by the rules for it) IS A DEBT AT `ocEnd`: the first chain's whole last promise still holds at
the oracles behind each block of the shared chain: OWED, under the name ocEnd_rides: it wants that the promise's letters read the stored table and trees below the
shared chain's first alone, and that a block leaves the columns of the trees that it does not send. `wrow` IS A LETTER: its text, place and worth are K13's files' (by report); as a term of this type nobody has
typed it. THAT IT HOLDS IS SHOWN BY NO ROW OF THESE TWO TABLES: it is opened at the shared chain's point and closed on the last chain (the own group's
proximity test). `frontOk`, `evalLaid` are letters too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FirstMeans
import Johnson.Desc.Sound.PromsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start onAt openSets pubSets pubHeld Pub)

/-- What the first chain's table leaves open at its end. -/
def endFirst : List Item := [.unmarked, .pinW, .pileOne, .pinI, .pinV]

/-- The shared chain's table's own items read the first chain's table's letters. -/
def tiedMeaning {A P₀ S₂ W : Type} (get : A → P₀ × First.S) (Mg₁ : Meaning P₀ W) (Mg : MeaningS S₂ A W) :
    MeaningS S₂ A W :=
  { Mg with
    pin₁ := fun j t p => Mg₁.pin j t (get p), claimM := fun p => Mg₁.pileOne (get p)
    ev := fun p => Mg₁.wrow (get p), unmarked1 := fun p => (get p).2.failed = none }

/-- W's and the index masks' tenants are the first chain's table's. -/
def tiedNumbers (N₁ : Numbers) (Ns : NumbersS) : NumbersS := { Ns with w := N₁.w, index := N₁.index }

/-- The slot's own condition: the first chain's whole promise at its last border. -/
def ocEnd {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) : A → Strs → Prop := fun p y =>
  onAt N₁ Mg₁ links none ((openSets links ps (start links))[ps.length]?.getD [])
    ((pubSets Mg₁.more links ps)[ps.length]?.getD []) (get p) y

/-- At a record without a mark the slot's own condition gives every public item that is open at the first chain's last border: K13's two
conditions on the record among them, WHERE THE PROMISE's TABLE HAS THEM OPEN THERE (hq: a test on the table). -/
theorem ocEnd_pub {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
    (links : List ModelPart) (ps : List Place) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) (q : Pub) (hq : q ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) :
    Mg₁.pub q (get p) = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have hb := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h'.1).1).2
    exact List.all_eq_true.1 hb q (List.mem_append_left _ hq)

/-- K13's two conditions on the record. -/
theorem ocEnd_laid {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
    (links : List ModelPart) (ps : List Place) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) (h1 : Pub.frontOk ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) :
    Mg₁.pub .frontOk (get p) = true ∧ Mg₁.pub .evalLaid (get p) = true :=
  ⟨ocEnd_pub get N₁ Mg₁ links ps p y h hm _ h1, ocEnd_pub get N₁ Mg₁ links ps p y h hm _ h2⟩

/-- **THE PROMISE GOES FORWARD** (the first half of the joint, by itself): the first chain's promise at its last border gives the shared chain's at its
first, at the record that `start₂` makes. -/
def OnZeroOfEnd : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type)
    (start₂ : P → S₂')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') W) (Pm : PromMeaning S₂') (split : Bool),
    1 + T.l₁.length = ps.length →
    (∀ b : (P × S₁') × (EAll D all).Str,
      Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))) →
    (∀ b : (P × S₁') × (EAll D all).Str,
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b → Pm.shape 0 (start₂ b.1.1) = true) →
    ∀ b : (P × S₁') × (EAll D all).Str,
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b →
      onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂ 0
        ((b.1, start₂ b.1.1), b.2)

/-- **THE RELATION GOES BACK** (the second half, by itself; NO PROMISE IS ASKED): what the shared chain claims at its first border, at the record that
`start₂` makes, gives what the first chain claims at its last. -/
def RelEndOfZero : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type)
    (start₂ : P → S₂')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') W) (Pm : PromMeaning S₂') (split : Bool),
    1 + T.l₁.length = ps.length →
    (∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) ps.length i → i ∈ endFirst) →
    (∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
      Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
      Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w) →
    ∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
      relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ 0 ((b.1, start₂ b.1.1), b.2) w →
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).R₁ (1 + T.l₁.length) b w

/-- **`Glue₁`, with both tables laid in.** -/
def TieEnd : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') W) (Pm : PromMeaning S₂') (split : Bool),
    1 + T.l₁.length = ps.length →
    (∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) ps.length i → i ∈ endFirst) →
    (∀ b : (P × S₁') × (EAll D all).Str,
      Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))) →
    (∀ b : (P × S₁') × (EAll D all).Str,
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b → Pm.shape 0 (start₂ b.1.1) = true) →
    (∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
      Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
      Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w) →
    (T.ofStarts pub start₁ start₂ start₃).Glue₁
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀
        { Q with
          on₂ := onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂
          R₂ := relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ })

theorem onZeroOfEnd : OnZeroOfEnd := by
  intro C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W start₂ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm split hlen hTP hSh b h
  have hnone : ps[1 + T.l₁.length]? = none := by
    rw [hlen]
    exact List.getElem?_eq_none (Nat.le_refl _)
  have h' : onAt N₁ Mg₁ links ps[1 + T.l₁.length]?
      ((openSets links ps (start links))[1 + T.l₁.length]?.getD [])
      ((pubSets Mg₁.more links ps)[1 + T.l₁.length]?.getD []) (get b.1)
      (strsOf (frameAt D all D.key₁ T.ft₁) b.2) := h
  rw [hnone, hlen] at h'
  have ho : ocEnd get N₁ Mg₁ links ps b.1 (strsOf (frameAt D all D.key₂ T.ft₂) b.2) := h'
  refine ⟨fun c hc => ?_, ho⟩
  rw [promsAt_zero'] at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact hTP b ho.1
  · obtain rfl := List.mem_singleton.1 hc
    exact hSh b h

theorem relEndOfZero : RelEndOfZero := by
  intro C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W start₂ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm split hlen hEnd hPW b w
    hr
  have hp := hr.1 .pinT ⟨rfl, by decide⟩
  have hR : (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).R₁ (1 + T.l₁.length) =
      relQ (Fr := frameAt D all D.key₁ T.ft₁) N₁ Mg₁ links ps get (1 + T.l₁.length) := by
    show frontAt R₀ _ (1 + T.l₁.length) = _
    rw [Nat.add_comm]
    rfl
  rw [hR]
  intro i hi
  rw [hlen] at hi
  have hm := hEnd i hi
  have o : ∀ j ∈ [ItemS.unmarked1, .pinI, .pinV, .claimM],
      j.holdsOwn (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) b.1 (start₂ b.1.1)
        (strsOf (frameAt D all D.key₂ T.ft₂) b.2) w := hr.2
  rcases List.mem_cons.1 hm with rfl | hm
  · exact o .unmarked1 (by decide)
  rcases List.mem_cons.1 hm with rfl | hm
  · exact hPW b w hp
  rcases List.mem_cons.1 hm with rfl | hm
  · exact o .claimM (by decide)
  rcases List.mem_cons.1 hm with rfl | hm
  · exact o .pinI (by decide)
  · obtain rfl := List.mem_singleton.1 hm
    exact o .pinV (by decide)

theorem tieEnd : TieEnd := by
  intro C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W pub start₁ start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm split
    hlen hEnd hTP hSh hPW x b w h
  by_cases hon : (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b
  · refine Or.inl ?_
    have h' : relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ 0
          ((b.1, start₂ b.1.1), b.2) w ∨
        ¬ onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂ 0
          ((b.1, start₂ b.1.1), b.2) := h
    have ho := onZeroOfEnd C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W start₂ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm split
      hlen hTP hSh b hon
    exact relEndOfZero C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W start₂ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm split
      hlen hEnd hPW b w (h'.elim id fun n => absurd ho n)
  · exact Or.inr hon

#check @OnZeroOfEnd
#check @RelEndOfZero
#check @TieEnd

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.onZeroOfEnd
#print axioms VerifiableInference.Desc.Sound.relEndOfZero
#print axioms VerifiableInference.Desc.Sound.tieEnd
#print axioms VerifiableInference.Desc.Sound.ocEnd_pub
#print axioms VerifiableInference.Desc.Sound.ocEnd_laid
