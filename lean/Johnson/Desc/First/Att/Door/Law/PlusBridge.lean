-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/PlusBridge.lean: kind K5: A TIE THAT IS TYPED AT THE WIDER FILLING
mgPlus IS A TIE IN THE TABLE's SECOND FORM (TiedAtR, Johnson/Desc/Sound/ChainOfPromisesR.lean)
AT THE NARROWER FILLING Mg: the kind-free bridge tiedAtR_of_wider
(Johnson/Desc/Sound/PlusDoor.lean) CALLED at a small widening
(Johnson/Desc/First/Att/Door/Plus.lean) BY widenP (Johnson/Desc/Sound/PlusDoorP.lean:
the widening turns what an item says beside its test too), its three
premises on the promise paid by its onQ_down_P | onQ_up_P from its test on the two lists (doorsFitB,
Johnson/Desc/Sound/PlusDoorA.lean) and SEVEN FACTS AT REACHED STATES: five
that are asked at every border (Facts5),
two at border k alone.

IS IT EMPTY HERE? Implications. NO MEMBER IS SHOWN.

Main names:
  `mgPlus Mg M0 D L M base cs`: widenP Mg (morePlus M0) (pubAll D (pubPlus L M D.d3 base)) (pubPPlus
    Mg.pubP) (ioPlus cs Mg.inOrder).
  `three_true`, `wide_true`: where the three | five tests say yes, the wider tower says yes at each
    of the three | five names.
  `k5_tiedR`: **THE BRIDGE AT THE KIND.** NOT BY tiedAtR_of_classAP: its facts are
    asked under Rch alone; here the two facts at border k are asked under the narrower promise too,
    which tiedAtR_of_wider hands.
THE SIXTH AND THE SEVENTH FACT (hbare · hleft): AT BORDER k ALONE (both names are dropped by the
kind's own row): at every state that Rch k admits, THAT MEETS THE NARROWER FILLING's PROMISE AT k
(so "an attention segment is open" is the promise's, not the payer's)
and that bears no mark: bareAttB: the kept rows of what the verifier has received from the lookup
argument name no entry · leftAttB: the test leftAtB (FillBare.lean) at what was received and the
segment's ledger. NAMED PAYERS: rowsBare_reached (K03RowsBare.lean), which speaks at that border;
the lookup argument's files' laws on what its yes leaves: NOT JOINED: Rch has no term here. THE FIVE
FACTS (Facts5), each asked at every state that Rch admits and that bears no mark: the book carries
the plan's seats · the statement's messages have the plan's shapes · the live request's shape and
its rows' layout are the plan's (two) · the statement's codes are the plan's: FIVE FIELDS OF THE
STRUCTURE FoldFacts (seatsCarried · msgShapes · liveShape · liveLayout · codes;
Johnson/Desc/First/FoldFacts.lean [no Lean term joins the two here]), UNDER
FIVE EQUATIONS OF LETTERS THAT ARE NOT TYPED: L = d.L · M = d.M · cs = d.sent.codes · D.d3.shape
= d.sent.shape · D.d3.layout = d.sent.layout. NOT PAID HERE: the debt that takes the place of the
keepings. NO PREMISE ON what the five names say beside
their tests, AT Mg: the widening lays True there itself.
ALSO LEFT, ALL: hpub : Mg.pub = pubAll D base
(mgAll_pub, MgAll.lean, by the make, at its own data and base) · hD | hD': the test on the two lists
at borders k and k + 1, at the class isWideQ (what is open at Mg's list is open at the wider and is
none of the five · what is open at the wider is one of the five or open at Mg's · no tied item is
one of the five) · hopen': at k + 1 what is open at the wider list is open at Mg's or one of THE
THREE (K5's two names are dropped by K5's own row) · HandsOn Rch k q (asked beside every tie by the
chain's rule; kind-free; payer by name, as reported:
rchAt_hand (Johnson/Top/H0/Walk/ReachAt.lean), at its own condition RchAt) · h: the tie at mgPlus
itself. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Sound.PlusDoorP
import Johnson.Desc.First.Att.Door.Law.PlusAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (K3Data liveIsC)
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes)

section
variable {P W : Type}

/-- **The wider filling.** -/
def mgPlus (Mg : Meaning P W) (M0 : More) (D : PubData) (L : Laid) (M : List OracleShape)
    (base : Pub → P × S → Bool) (cs : Codes) : Meaning P W :=
  widenP Mg (morePlus M0) (pubAll D (pubPlus L M D.d3 base)) (pubPPlus Mg.pubP) (ioPlus cs Mg.inOrder)

variable (D : PubData) (L : Laid) (M : List OracleShape) (base : Pub → P × S → Bool)

theorem plus_same {q : Pub} (h : isWideQ q = false) (a : P × S) :
    pubAll D (pubPlus L M D.d3 base) q a = pubAll D base q a :=
  pubAll_plus_else D L M D.d3 base (fun n s e => by subst e; exact h) a

theorem three_true {q : Pub} (h : isThreeQ q = true) {a : P × S} (f1 : atFirstSeats L a.2 = true)
    (f2 : atFirstShapes M a.2 = true) (f3 : liveIsC D.d3 a.2 = true) :
    pubAll D (pubPlus L M D.d3 base) q a = true := by
  cases q with
  | more n s =>
    cases n with
    | none =>
      have h' : (s == "K12.seatsCarried" || s == "K12.msgShapes") = true := h
      rcases Eq.mp (Bool.or_eq_true _ _) h' with e | e
      · rw [beq_iff_eq.1 e, pubAll_plus_seats]
        exact f1
      · rw [beq_iff_eq.1 e, pubAll_plus_shapes]
        exact f2
    | some m =>
      have h' : (s == "frame.liveIs") = true := h
      rw [beq_iff_eq.1 h', pubAll_plus_live]
      exact f3
  | _ => cases h

theorem wide_true {q : Pub} (h : isWideQ q = true) {a : P × S} (f1 : atFirstSeats L a.2 = true)
    (f2 : atFirstShapes M a.2 = true) (f3 : liveIsC D.d3 a.2 = true) (f5 : bareAttB a.2 = true) (f6 : leftAttB a.2 = true) :
    pubAll D (pubPlus L M D.d3 base) q a = true := by
  cases h3 : isThreeQ q with
  | true => exact three_true D L M base h3 f1 f2 f3
  | false =>
    cases q with
    | more n s =>
      have hw : (isThree (n, s) || isOurs (n, s)) = true := h
      have h3' : isThree (n, s) = false := h3
      rw [h3', Bool.false_or] at hw
      cases n with
      | none => cases hw
      | some m =>
        have h' : (s == "K5.rowsBare" || s == "K5.lookLeft") = true := hw
        rcases Eq.mp (Bool.or_eq_true _ _) h' with e | e
        · rw [beq_iff_eq.1 e, pubAll_plus_bare]
          exact f5
        · rw [beq_iff_eq.1 e, pubAll_plus_left]
          exact f6
    | _ => cases h

end

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S) (M0 : More) (D : PubData) (L : Laid)
  (M : List OracleShape) (base : Pub → P × S → Bool) (cs : Codes)

variable (Rch : ℕ → A × Fr.E.Str → Prop)

/-- The five facts, at every state that Rch admits and that bears no mark. -/
structure Facts5 : Prop where
  seats : ∀ k a, Rch k a → (get a.1).2.failed = none → atFirstSeats L (get a.1).2 = true
  shapes : ∀ k a, Rch k a → (get a.1).2.failed = none → atFirstShapes M (get a.1).2 = true
  liveShape : ∀ k a, Rch k a → (get a.1).2.failed = none → (get a.1).2.live.frame.shape = D.d3.shape
  liveLayout : ∀ k a, Rch k a → (get a.1).2.failed = none → (get a.1).2.live.rows.layout = D.d3.layout
  codes : ∀ k a, Rch k a → (get a.1).2.failed = none → (get a.1).2.st.codes = cs

/-- **THE BRIDGE AT THE KIND.** -/
theorem k5_tiedR (hpub : Mg.pub = pubAll D base) (F : Facts5 get D L M cs Rch) (k : ℕ) (q : Piece C Fr A Cl W)
    (hbare : ∀ a, Rch k a → onQ N Mg links ps get k a → (get a.1).2.failed = none → bareAttB (get a.1).2 = true)
    (hleft : ∀ a, Rch k a → onQ N Mg links ps get k a → (get a.1).2.failed = none → leftAttB (get a.1).2 = true)
    (hD : doorsFitB Mg.more (morePlus M0) isWideQ links ps k = true)
    (hD' : doorsFitB Mg.more (morePlus M0) isWideQ links ps (k + 1) = true)
    (hopen' : ∀ x ∈ (pubSets (morePlus M0) links ps)[k + 1]?.getD [],
      x ∈ (pubSets Mg.more links ps)[k + 1]?.getD [] ∨ isThreeQ x = true)
    (hs : HandsOn Rch k q)
    (h : TiedAt N (mgPlus Mg M0 D L M base cs) links ps get k q) : TiedAtR N Mg links ps get Rch k q := by
  have live : ∀ j a, Rch j a → (get a.1).2.failed = none → liveIsC D.d3 (get a.1).2 = true := by
    intro j a hr hm
    unfold liveIsC
    rw [F.liveShape j a hr hm, F.liveLayout j a hr hm]
    simp
  have hhand : ∀ i, isWideQ i = false → ∀ x, pubAll D (pubPlus L M D.d3 base) i x = Mg.pub i x := by
    intro i hi x
    rw [hpub]
    exact plus_same D L M base hi x
  have hhandP : ∀ i, isWideQ i = false → ∀ x, pubPPlus Mg.pubP i x ↔ Mg.pubP i x := by
    intro i hi x
    unfold pubPPlus
    rw [hi]
    simp
  have wP : ∀ i, isWideQ i = true → ∀ x, pubPPlus Mg.pubP i x := by
    intro i hi x
    unfold pubPPlus
    rw [hi]
    simp
  have hio : ∀ x, ioPlus cs Mg.inOrder x = true → Mg.inOrder x = true := fun x hx => (Eq.mp (Bool.and_eq_true _ _) hx).1
  have up : ∀ j a, Rch j a → (get a.1).2.failed = none → Mg.inOrder (get a.1) = true → ioPlus cs Mg.inOrder (get a.1) = true := by
    intro j a hr hm hi
    show (Mg.inOrder (get a.1) && decide ((get a.1).2.st.codes = cs)) = true
    rw [hi, F.codes j a hr hm]
    simp
  exact tiedAtR_of_wider N Mg links ps get Rch (mgPlus Mg M0 D L M base cs) k q rfl rfl
    (fun b => onQ_down_P N Mg (morePlus M0) _ _ _ isWideQ links ps get (k + 1) b hhand hhandP hio hD')
    (fun a hr ho => onQ_up_P N Mg (morePlus M0) _ _ _ isWideQ links ps get k a hhand hhandP hD
      (fun hm => ⟨up k a hr hm, fun x _ hx => ⟨wide_true D L M base hx (F.seats k a hr hm) (F.shapes k a hr hm) (live k a hr hm)
        (hbare a hr ho hm) (hleft a hr ho hm), wP x hx _⟩⟩) ho)
    (fun b hr ho => onQ_up_P N Mg (morePlus M0) _ _ _ isWideQ links ps get (k + 1) b hhand hhandP hD'
      (fun hm => ⟨up (k + 1) b hr hm, fun x hx hw => by
        rcases hopen' x hx with h1 | h1
        · exact absurd hw (by rw [((doorsFitB_parts hD').1 x h1).2]; exact Bool.false_ne_true)
        · exact ⟨three_true D L M base h1 (F.seats _ b hr hm) (F.shapes _ b hr hm) (live _ b hr hm), wP x hw _⟩⟩) ho)
    hs h

end

end H2K5.Door

#print axioms H2K5.Door.k5_tiedR
#print axioms H2K5.Door.three_true
#print axioms H2K5.Door.wide_true
