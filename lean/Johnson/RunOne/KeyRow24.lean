-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow24.lean: ROW 2.4 OF THE KEY FILE's TABLE OF JOINTS (the
shared chain's block «LOC»; borders 4 → 5): THE CHANCE's HALF, at the tables' own letters
(Johnson/RunOne/KeyRows23At.lean: on₂ | R₂ | L₂).

ON EMPTINESS: IT IS NOT SHOWN THAT ANY RECORD, READING AND ORACLES EXIST AT WHICH on₂ … 4 HOLDS, NOR
A WITNESS AT WHICH R₂ … 5 HOLDS. UNTIL A MEMBER IS SHOWN AT F_K's OWN LETTERS, EVERY LAW THAT HAS
PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS
CLOSING NOTHING.
OBJECT: a piece pc of the rule of composition at the record P₂ × St₂ whose block decides by K14's
own text «loc» on the second component and leaves the first (hl): meant: the maker's piece number 4
of the shared chain: pieceOf (held b) base ds back x, b := (c₂ :: k₂)[4].
USER: keeps₂_of_halves (the other half:
Leads (on₂ … k) (fun a b => (L₂ … (k + 1) b → L₂ … k a)) pc.err), then
keepsAt_of_law₂ | KeepsAt.reached: the field r2_4 of The21 (Johnson/Top/Fire/Code/The35.lean).
LETTERS: F Fr₂ G₂ at_ K₁ R enc rad a coll last₁ off₂ (the tables'); the tables' S is p.S, p the
text's own letter; HERE BESIDE: K ρ (a reading of words in a field) · c G (the written round read as
one typed draw of S.fold.columns places).
  open₂_at4 | open₂_at5       the two open sets, by decide
  eval₄_is … columns₄_is      five named claims as their sentences
  rowHolds_kept | srow₂_kept | record_kept   what rides over a yes of «LOC»: the messages and the
    codes are as they were; G_u's list has grown at its end alone
  shape₂_at4                  what is spent of the book-keeping at border 4: G_u is group 0 · o_u is
    message 0 · G_u has just as many open rows as the record has answers
  bitsE | encOf | EncIs | encIs_encOf   A CONDITION ON THE LETTER enc (it reads as row x of the
    code's generator matrix on the message and on the random tail) AND A MEMBER WITH CODE
  nearU_of_nearAt             K14's files' NearAt at the stored table's columns off the oracles
    (tabOf) gives the tables' «NearU»: where the stored table is at least as long as the code
  rowsUL_of_columns           the tables' «columns» gives the rows that loc_core has behind (by
    rowHolds_iff_says_of_rowIn; RowIn out of «in order»)
  ride₂_54                    the ten items that are open on both sides ride back, at one witness
  loc_back₂                   **THE CHANCE's HALF**: by loc_core
    (Johnson/Desc/K14/Law/RowsCore.lean) at T := P₂ × St₂, on := on₂ … 4, PinB := R₂ … 5, PinA :=
    PIN at message 3
WHAT IS SPENT OF THE PROMISE IN FRONT: shape₂ 4's three facts · Free₂ 4's lay · linOk · seatU ·
order · reads · NoColl at message 3.
PREMISES, EACH WITH ITS PAYER, AND, OF EACH THAT IS A BARE «∀», WHY AN INSTANCE THAT IS NOT
DEGENERATE EXISTS: hl [bare ∀ z rs gs z', under the block's yes]: K14's files: b4.decide is
«why (loc p d rs gs)» (loc_of_blocks), seat_decide is rfl, held_decide hands the first component on
· hbase: the frame's numbers (basesOk, Johnson/Top/Fire/Code/BasesOk.lean): base and at_ both count
trees through the file · hsame [bare ∀]: whoever fills KRead: R.same := «ρ x = ρ y» is the meant
filling · hpins [BARE ∀ z z', UNDER THREE EQUATIONS AND NO YES]: A CONDITION ON THE READING: it
reads of the shared chain's own record the messages and the codes alone: BaseSt.h₂ meets it at every
pair [by reading: smp reads a.1.2.d.st and smAt a.2.st = oracles[o]?.bind
(sm codes o); recOf reads a.1.1] · henc [bare ∀ u x]: whoever fills enc: encOf is a member, with
code (encIs_encOf) · hA: logN ≤ the frame's a: UNPAID: the tiling ties the index's tree's a
to the frame's; no text read here ties code.logN to it · c | hc: the
caller's choice of a count · G | fits | hread [∀ x; ∀ under the piece's yes]: the written round:
KeyRow24At.lean pays them (posMaps · pos_reads) · hcols [∀ under the piece's yes]: K14's files:
shown_stored, at a stretch of one written round that opens no tree.
BUT FOR hpins no premise is asked of a statement behind the block without the block's own yes in
front of it. SEEN IN THE TABLES' AND Johnson/Desc/Msg.lean's DEFINITIONS,
NOT IN THIS FILE's: NoColl ends in «m = m'» IN M: if M is filled
by tables of machine words (a word (p, 0, 0) reads as 0) or holds places that enc | meets do not
read, then wherever one member exists a second does, NoColl is false and on₂ 4 ∧ L₂ 5 never hold
together; this file spends of NoColl at message 3 only that the two tables READ ALIKE at o_u's
places. Nothing on soundness by itself.
-/
import Johnson.RunOne.KeyMap23
import Johnson.Desc.Key.KeyKeeps
import Johnson.Desc.Key.KeySumRead
import Johnson.Desc.Key.RowHoldsSays
import Johnson.Desc.K14.Law.OnFront
import Johnson.Desc.Plain.FromGood
import Johnson.RunOne.KeyIdPiece
import Johnson.Desc.K14.Law.LocKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open _root_.Iop.IOR (drawRound)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (LocKept kept_of_loc LocAt NearAt RowsUL rowsOn tabOf loc_core codeVal
    locAt_iff bitsK SeatedU placedU_of_seatedU index_ok_of_linOk shownGroups)

theorem open₂_at4 : open₂ 4 = [.unmarked, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .claim
    2 "NearU", .claim 2 "DotU", .pin 3, .srow 3, .claim 2 "record"] := by decide
theorem open₂_at5 : open₂ 5 = [.unmarked, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .claim
    2 "DotU", .pin 3, .srow 3, .claim 2 "record", .claim 2 "columns"] := by decide

/-! ## The named claims as their sentences -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec)
    (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

theorem eval₄_is (u : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (KItem.claim 1 "Eval").holds F G₂ at_ (meaning₂ S K₁ R enc rad) u y w ↔
      ∃ r, (readers₂ S).eval u.1 = some r ∧ RowHolds R.same ((readers₂ S).st₁ u.1) (valOf K₁ R w) r
          := by
  simp [KItem.holds, meaning₂, claim₂]

theorem nearU₄_is (u : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (KItem.claim 2 "NearU").holds F G₂ at_ (meaning₂ S K₁ R enc rad) u y w ↔
      NearUAt R.same (plan₂ S).lin.fold.index.code.logN rad enc (((readers₂ S).psi u).drop (plan₂
          S).lin.kLo) y
        (uOf (plan₂ S) R ((readers₂ S).st u.2).codes w) := by
  simp [KItem.holds, meaning₂, claim₂]

theorem dotU₄_is (u : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (KItem.claim 2 "DotU").holds F G₂ at_ (meaning₂ S K₁ R enc rad) u y w ↔
      ∃ g, (readers₂ S).g u = some g ∧ DotUAt R.same (plan₂ S).lin g ((readers₂ S).psi u)
        (uOf (plan₂ S) R ((readers₂ S).st u.2).codes w) (vOf' (plan₂ S) R ((readers₂ S).st
            u.2).codes w) := by
  simp [KItem.holds, meaning₂, claim₂]

theorem record₄_is (u : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (KItem.claim 2 "record").holds F G₂ at_ (meaning₂ S K₁ R enc rad) u y w ↔
      rowsHold R.same ((readers₂ S).st u.2) (valOf (plan₂ S) R w) ((readers₂ S).gU u.2) 0 (plan₂
          S).lin.fold.index.answers := by
  simp [KItem.holds, meaning₂, claim₂]

theorem columns₄_is (u : P₂ × St₂) (y : Strs) (w : Wit Cells Unit M) :
    (KItem.claim 2 "columns").holds F G₂ at_ (meaning₂ S K₁ R enc rad) u y w ↔
      rowsHold R.same ((readers₂ S).st u.2) (valOf (plan₂ S) R w) ((readers₂ S).gU u.2) (plan₂
          S).lin.fold.index.answers (plan₂ S).lin.fold.columns := by
  simp [KItem.holds, meaning₂, claim₂]

end

/-! ## What rides over a yes of «LOC» -/

/-- A row's sentence reads of the statement the messages and the codes alone. -/
theorem rowHolds_kept (same : E → E → Prop) (St St' : Statement) (ho : St'.oracles = St.oracles) (hc
    : St'.codes = St.codes)
    (val : Nat → Part → Nat → E) (r : OnBytes.Row) (h : RowHolds same St' val r) : RowHolds same St
        val r := by
  have ht : ∀ o pt, St'.tableBits o pt = St.tableBits o pt := fun o pt => by
    simp [Statement.tableBits, Statement.rowBits, Statement.placeBits, ho, hc]
  unfold RowHolds at h ⊢
  simp only [ho, ht] at h
  exact h

section
variable {Cells M : Type} (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat →
    E) (rad : Nat)

theorem srow₂_kept (k : Nat) (z : P₂) (d d' : St₂) (y y' : Strs) (w : Wit Cells Unit M) (P : LocKept
    d d')
    (h : (meaning₂ S K₁ R enc rad).srow k (z, d') y' w) : (meaning₂ S K₁ R enc rad).srow k (z, d) y
        w := by
  simp only [meaning₂] at h ⊢
  split_ifs at h ⊢
  · exact h
  · obtain ⟨o, x, h1, h2, h3, h4, h5⟩ := h
    exact ⟨o, x, h1, P.oracles ▸ h2, h3, h4, fun r hr => rowHolds_kept _ _ _ P.oracles P.codes _ r
        (h5 r hr)⟩

end

/-- The rows that lay on G_u in front of «LOC» are the first behind it. -/
theorem record_kept (same : E → E → Prop) (val : Nat → Part → Nat → E) (d d' : St₂) (P : LocKept d
    d') (n : Nat) (G : OnBytes.Group)
    (hG : d.st.groups[d.loc.gU]? = some G) (hn : G.rows.size = n) (h : rowsHold same d'.st val
        d.loc.gU 0 n) :
    rowsHold same d.st val d.loc.gU 0 n := by
  obtain ⟨G', hG', _, hne, hall⟩ := h
  obtain ⟨rows, hr⟩ := P.rows
  have e' : rowsOn d' d.loc.gU = G'.rows.toList := by
    unfold rowsOn
    rw [hG']
    rfl
  have e : rowsOn d d.loc.gU = G.rows.toList := by
    unfold rowsOn
    rw [hG]
    rfl
  rw [e', e] at hr
  refine ⟨G, hG, by omega, hne, fun r hrr => rowHolds_kept _ _ _ P.oracles P.codes _ r (hall r ?_)⟩
  rw [hr, List.drop_zero, List.take_append_of_le_length (by rw [Array.length_toList]; omega)]
  rw [List.drop_zero] at hrr
  exact hrr

/-- What is spent of the book-keeping at border 4. -/
theorem shape₂_at4 (S : LinShape) (a : Nat) (d : St₂) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a
    4 d) = true) :
    d.loc.gU = 0 ∧ d.loc.oU.oracle = 0 ∧ ∃ G, d.st.groups[0]? = some G ∧ G.rows.size =
        S.fold.index.answers := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
  obtain ⟨_, _, _, _, _, _, c7, c8, _, _, _, _, c13, _, _, _, _⟩ := h
  have n7 : d.loc.gU = 0 ∧ d.loc.gOmega = 1 := by simpa using c7
  have n8 : d.loc.oU.oracle = 0 ∧ d.loc.firstMask = some 1 := by simpa using c8
  have g13 : LKFU.Shape23.grpIs d.st 0 [0] S.fold.index.answers 0 false = true := by simpa using c13
  refine ⟨n7.1, n8.1, ?_⟩
  unfold LKFU.Shape23.grpIs at g13
  cases hG : d.st.groups[0]? with
  | none =>
    rw [hG] at g13
    cases g13
  | some G =>
    rw [hG] at g13
    simp only [Bool.and_eq_true, beq_iff_eq] at g13
    exact ⟨G, rfl, by omega⟩

/-! ## The letter enc -/

section
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- The product of the factors at the bits that are set in j, the lowest bit first: in the program's
arithmetic. -/
def bitsE : List E → Nat → E
  | [], _ => oneE
  | x :: l, j => mulE (if j % 2 = 1 then x else oneE) (bitsE l (j / 2))

theorem bitsE_val : ∀ (l : List E) (j : Nat), ρ.val (bitsE l j) = bitsK (l.map ρ.val) j
  | [], _ => ρ.one
  | x :: l, j => by
    rw [bitsE, ρ.mul, bitsE_val l]
    simp only [List.map_cons, bitsK]
    by_cases h : j % 2 = 1 <;> simp [h, ρ.one]

/-- **A condition on the letter enc**: at every place of the code it reads as row x of the code's
generator matrix on the message and on the random tail. -/
def EncIs (S : FoldeqShape) (enc : (Nat → E) → Nat → E) : Prop :=
  ∀ u x, x < 2 ^ S.index.code.logN → ρ.val (enc u x) = codeVal ρ S x fun k => ρ.val (u k)

/-- A member, with code. -/
def encOf (S : FoldeqShape) (u : Nat → E) (x : Nat) : E :=
  addE (mulE (ofF (generatorAt S.index.code x).messageScale)
      (sumE S.index.code.ell fun j => mulE (bitsE (((generatorAt S.index.code x).f.map ofF).take
          S.index.code.logEll) j) (u j)))
    (mulE (ofF (generatorAt S.index.code x).tailScale)
      (sumE S.index.code.r fun j => mulE (bitsE (((generatorAt S.index.code x).f.map ofF).take
          S.index.code.logR) j) (u (S.tailFirst + j))))

theorem encIs_encOf (S : FoldeqShape) : EncIs ρ S (encOf S) := by
  intro u x _
  unfold encOf codeVal
  simp only [ρ.add, ρ.mul, sumE_read ρ.val ρ.zero ρ.add, bitsE_val, List.map_take, List.map_map,
      Function.comp_def]

open Classical in
/-- **K14's files' «near» (NearAt) gives the tables' «NearU».** -/
theorem nearU_of_nearAt (Fr : Frame) (p : Par) (same : E → E → Prop) (hsame : ∀ x y, same x y ↔
    ρ.val x = ρ.val y)
    (enc : (Nat → E) → Nat → E) (henc : EncIs ρ p.S.fold enc) (hA : p.S.fold.index.code.logN ≤ Fr.a)
        (d : St₂) (y : Fr.E.Str)
    (m : Means.Words K) (u : Nat → E) (hu : ∀ k, m d.loc.oU.oracle .main (d.loc.oU.lay.index k) =
        ρ.val (u k)) (e : Nat)
    (h : NearAt ρ p d m (tabOf y) e) :
    NearUAt same p.S.fold.index.code.logN e enc (d.loc.psiSh.drop p.S.kLo) (strsOf Fr y) u := by
  refine ⟨(Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) => ¬ LocAt ρ p d m (tabOf
      y) x.val).toList.map (·.val), ?_, fun x hx hB => ?_⟩
  · rw [List.length_map, Finset.length_toList]
    exact h
  · have hL : LocAt ρ p d m (tabOf y) x := by
      by_contra hn
      exact hB (List.mem_map.2 ⟨⟨x, hx⟩, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨Finset.mem_univ
          _, hn⟩), rfl⟩)
    have hxa : x < 2 ^ Fr.a := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hA)
    refine ⟨y.1 ⟨x, hxa⟩, ?_, ?_⟩
    · show cellAt Fr y x = _
      unfold cellAt
      rw [dif_pos hxa]
    · have h1 := (locAt_iff ρ p d m (tabOf y) x).1 hL
      have e1 : tabOf y x = (y.1 ⟨x, hxa⟩).2 := by
        unfold tabOf
        rw [dif_pos hxa]
      rw [e1] at h1
      rw [hsame, henc u x hx, ← h1]
      congr 1
      funext k
      exact (hu k).symm

/-- The words that the rows read off a witness, read in the field. -/
def words₂ {Cells M : Type} (S : LinShape) (R : KRead Cells M) (w : Wit Cells Unit M) : Means.Words
    K :=
  fun o pt i => ρ.val (valOf (plan₂ S) R w o pt i)

/-- **The tables' «columns» gives the rows that the law of «LOC» has behind.** -/
theorem rowsUL_of_columns {Cells M : Type} (S : LinShape) (R : KRead Cells M) (hsame : ∀ x y, R.same
    x y ↔ ρ.val x = ρ.val y)
    (d' : St₂) (w : Wit Cells Unit M) (hord : Means.InOrder d'.st) (i₀ n : Nat)
    (h : rowsHold R.same d'.st (valOf (plan₂ S) R w) d'.loc.gU i₀ n) : RowsUL ρ i₀ n d' (words₂ ρ S
        R w) := by
  obtain ⟨G, hG, _, _, hall⟩ := h
  refine ⟨d'.st, Grows.refl _, fun r hr => ?_⟩
  have e : rowsOn d' d'.loc.gU = G.rows.toList := by
    unfold rowsOn
    rw [hG]
    rfl
  rw [e] at hr
  have hin : Means.RowIn d'.st G r := hord.rows _ G hG r (List.mem_of_mem_drop (List.mem_of_mem_take
      hr))
  have t := hall r hr
  refine (rowHolds_iff_says_of_rowIn ρ d'.st G _ r hin).1 ?_
  unfold RowHolds at t ⊢
  exact (hsame _ _).1 t

end

/-! ## The ten riders -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec)
    (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

/-- **The relation, back, at one witness**: «NearU» handed in; the ten items that are open on both
sides ride. -/
theorem ride₂_54 (z : P₂) (d d' : St₂) (y y' : Strs) (w : Wit Cells Unit M) (P : LocKept d d') (HP :
    SamePins G₂ (z, d) (z, d'))
    (Hy : StrsStay F at_ (open₂ 4) y y') (G0 : OnBytes.Group) (hG0 : d.st.groups[d.loc.gU]? = some
        G0) (hs0 : G0.rows.size = p.S.fold.index.answers)
    (hw : relAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (open₂ 5) (z, d') y' w)
    (hnear : (KItem.claim 2 "NearU").holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) (z, d) y w) :
    relAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (open₂ 4) (z, d) y w := by
  have mem : ∀ j, j ∈ open₂ 5 → j.holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) (z, d') y' w := hw
  have pin : ∀ k, k ∈ pinned (open₂ 4) → (KItem.pin k).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad)
      (z, d') y' w →
      (KItem.pin k).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) (z, d) y w :=
    fun k hk hu => rides_pin2 F G₂ _ _ (z, d) (z, d') y y' w HP (Hy.word k hk) hu
  intro i hi
  rw [open₂_at4] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact pin 0 (by decide) (mem _ (by decide))
  · exact srow₂_kept p.S K₁ R enc rad 0 z d d' y y' w P (mem (.srow 0) (by decide))
  · exact pin 2 (by decide) (mem _ (by decide))
  · exact srow₂_kept p.S K₁ R enc rad 2 z d d' y y' w P (mem (.srow 2) (by decide))
  · exact (eval₄_is F G₂ at_ p.S K₁ R enc rad (z, d) y w).2 ((eval₄_is F G₂ at_ p.S K₁ R enc rad (z,
      d') y' w).1 (mem _ (by decide)))
  · exact hnear
  · obtain ⟨g, hg, hd⟩ := (dotU₄_is F G₂ at_ p.S K₁ R enc rad (z, d') y' w).1 (mem _ (by decide))
    have hd' : DotUAt R.same (plan₂ p.S).lin g d'.loc.psiSh (uOf (plan₂ p.S) R d'.st.codes w) (vOf'
        (plan₂ p.S) R d'.st.codes w) := hd
    rw [P.loc, P.codes] at hd'
    exact (dotU₄_is F G₂ at_ p.S K₁ R enc rad (z, d) y w).2 ⟨g, hg, hd'⟩
  · exact pin 3 (by decide) (mem _ (by decide))
  · exact srow₂_kept p.S K₁ R enc rad 3 z d d' y y' w P (mem (.srow 3) (by decide))
  · have hr := (record₄_is F G₂ at_ p.S K₁ R enc rad (z, d') y' w).1 (mem _ (by decide))
    have hr' : rowsHold R.same d'.st (valOf (plan₂ p.S) R w) d'.loc.gU 0 p.S.fold.index.answers :=
        hr
    rw [P.loc] at hr'
    exact (record₄_is F G₂ at_ p.S K₁ R enc rad (z, d) y w).2 (record_kept _ _ d d' P _ G0 hG0 hs0
        hr')

end

/-! ## The chance's half -/

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- **ROW 2.4, THE CHANCE's HALF.** c: a number that is at least (2 ^ logN - rad - 1) ^ columns. -/
theorem loc_back₂ (pc : Piece C Fr₂ (P₂ × St₂) Cl W)
    (hl : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.loc p z.2 rs gs
        = some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < pc.base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (henc : EncIs ρ p.S.fold enc) (hA : p.S.fold.index.code.logN ≤ Fr₂.a)
    (c : Nat) (hc : (2 ^ p.S.fold.index.code.logN - rad - 1) ^ p.S.fold.columns ≤ c)
    (hcols : ∀ (x : (P₂ × St₂) × Fr₂.E.Str) τ x' cols, pc.ior.red.out x τ = some x' →
      shownGroups Fr₂.ft pc.b (rvT C pc.ds τ ++ pc.back) (sView C pc.stage x.2 τ).opened = [cols] →
      ∀ q col, cols.lookup q = some col → col = tabOf x.2 q)
    (G : (P₂ × St₂) × Fr₂.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin p.S.fold.columns → Fin (2 ^
        p.S.fold.index.code.logN))])
    (fits : ∀ x, (G x).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ x τ x' r4, pc.ior.red.out x τ = some x' → (rvT C pc.ds τ ++ pc.back).map noDigest =
        [r4] →
      ∃ Q, (G x).tr τ = some (((), ()), Q, ()) ∧ r4.drawn.poss = List.ofFn fun i => (Q i).val) :
    pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 4)
      (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 5 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 4 x)
          pc.err := by
  have kept : ∀ (x : (P₂ × St₂) × Fr₂.E.Str) τ x', (idPiece (Wit Cells Unit M) pc).ior.red.out x τ =
      some x' →
      x'.1.1 = x.1.1 ∧ LocKept x.1.2 x'.1.2 := fun x τ x' hb => by
    obtain ⟨e1, k4⟩ := hl _ _ _ _ (piece_decides_at (idPiece (Wit Cells Unit M) pc) x τ x' hb)
    exact ⟨e1, kept_of_loc p _ _ _ _ k4⟩
  have arm : ∀ x, on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 4 x →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ p.S a 4 x.1.2) = true ∧ Free₂ F G₂ at_ p.S K₁ R coll
          last₁ off₂ 4 x.1 (strsOf Fr₂ x.2) ∧
        ∀ k ∈ pinned (open₂ 4), NoColl F G₂ (at_ k).1 (at_ k).2 x.1 (strsOf Fr₂ x.2) := fun x h =>
            by
    rcases h with hn | ⟨h1, _, h3, h4⟩
    · exact absurd trivial hn
    · exact ⟨h1, h3, h4⟩
  have core := loc_core ρ (words₂ ρ p.S R) Prod.snd (idPiece (Wit Cells Unit M) pc) p (fun d rs gs
      d' h => (hl d rs gs d' h).2) (fun _ _ _ => rfl)
    (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 4) (fun _ => True)
    (fun x w => (KItem.pin 3).holds F G₂ at_ (meaning₂ p.S K₁ R enc rad) x.1 (strsOf Fr₂ x.2) w)
    (R₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 5)
    (fun x hx => by
      obtain ⟨hsh, hf, _⟩ := arm x hx
      obtain ⟨_, n8, _⟩ := shape₂_at4 p.S a x.1.2 hsh
      obtain ⟨xU, hxU, shU⟩ : ∃ x0, x.1.2.st.oracles[0]? = some x0 ∧ x0.shape = p.S.fold.u := by
        have hsU := hf.seatU (by decide)
        cases hx0 : x.1.2.st.oracles[0]? with
        | none =>
          rw [hx0] at hsU
          cases hsU
        | some x0 =>
          rw [hx0] at hsU
          exact ⟨x0, rfl, by simpa using hsU⟩
      have hSeat : SeatedU x.1.2.st x.1.2.st.codes p.S x.1.2.loc.oU := ⟨rfl, ⟨xU,
          by rw [n8]; exact hxU, shU⟩, hf.lay (by decide)⟩
      exact ⟨index_ok_of_linOk _ _ (hf.linOk (by decide)), fun T g => placedU_of_seatedU
          (hSeat.grows g) (hf.linOk (by decide))⟩)
    p.S.fold.index.answers
    (fun x hx => by
      obtain ⟨hsh, _, _⟩ := arm x hx
      obtain ⟨n7, _, G0, hG0, hs0⟩ := shape₂_at4 p.S a x.1.2 hsh
      show (rowsOn x.1.2 x.1.2.loc.gU).length = _
      unfold rowsOn
      rw [n7, hG0]
      simpa using hs0)
    (fun _ _ _ _ _ => trivial)
    (fun x τ x' w _ hb hw => by
      obtain ⟨e1, P⟩ := kept x τ x' hb
      have Hy := strsStay_of_out F Fr₂ at_ (idPiece (Wit Cells Unit M) pc) (open₂ 4) hbase x x' τ hb
      exact rides_pin2 F G₂ _ _ x.1 x'.1 _ _ w (hpins x.1 x'.1 e1 P.oracles P.codes) (Hy.word 3
          (by decide)) (hw (.pin 3) (by decide)))
    (fun x w w' hx hp hp' => by
      obtain ⟨hsh, hf, hN⟩ := arm x hx
      obtain ⟨_, n8, _⟩ := shape₂_at4 p.S a x.1.2 hsh
      have e := pin_one F G₂ _ _ x.1 _ w w' (hN 3 (by decide)) hp hp'
      intro i
      show ρ.val (valOf (plan₂ p.S) R w' x.1.2.loc.oU.oracle .main i) = ρ.val (valOf (plan₂ p.S) R w
          x.1.2.loc.oU.oracle .main i)
      rw [n8]
      have v : ∀ w₀ : Wit Cells Unit M, valOf (plan₂ p.S) R w₀ 0 .main i = R.val (msgOf G₂ w₀ (at_
          3).1 (at_ 3).2) .main i := fun w₀ => by
        rw [← hf.reads w₀ 3 (by decide)]
        rfl
      rw [v, v, e])
    tabOf rad p.S.fold.columns c hc hcols G fits hread
  have L := leads_map2_of_goodIn (idPiece (Wit Cells Unit M) pc) _ _ _ _ (fun _ _ w => w) core (fun
      _ _ _ _ _ => rfl)
  refine Reduction.Leads.conseq L (fun _ h => h) fun x τ x' hx hb hq => ?_
  rintro ⟨w, hw⟩
  obtain ⟨e1, P⟩ := kept x τ x' hb
  obtain ⟨hsh, hf, _⟩ := arm x hx
  obtain ⟨n7, n8, G0, hG0, hs0⟩ := shape₂_at4 p.S a x.1.2 hsh
  have hcol := (columns₄_is F G₂ at_ p.S K₁ R enc rad x'.1 (strsOf Fr₂ x'.2) w).1 (hw _ (by decide))
  have hUL : RowsUL ρ p.S.fold.index.answers p.S.fold.columns x'.1.2 (words₂ ρ p.S R w) :=
    rowsUL_of_columns ρ p.S R hsame x'.1.2 w (P.order hf.order) _ _ hcol
  obtain ⟨_, hnear⟩ := hq.2 w ⟨hw, hUL⟩
  have Hy := strsStay_of_out F Fr₂ at_ (idPiece (Wit Cells Unit M) pc) (open₂ 4) hbase x x' τ hb
  have ex' : x'.1 = (x.1.1, x'.1.2) := Prod.ext e1 rfl
  have hw' : relAt F G₂ at_ (meaning₂ p.S K₁ R enc rad) (open₂ 5) (x.1.1, x'.1.2) (strsOf Fr₂ x'.2)
      w := ex' ▸ hw
  have hu : ∀ k, words₂ ρ p.S R w x.1.2.loc.oU.oracle .main (x.1.2.loc.oU.lay.index k) = ρ.val (uOf
      (plan₂ p.S) R x.1.2.st.codes w k) := fun k => by
    simp [words₂, uOf, valOf, plan₂, n8, hf.lay (by decide)]
  refine ⟨w, ride₂_54 F G₂ at_ p K₁ R enc rad x.1.1 x.1.2 x'.1.2 _ _ w P (ex' ▸ hpins x.1 x'.1 e1
      P.oracles P.codes) Hy G0 (by rw [n7]; exact hG0) hs0 hw' ?_⟩
  exact (nearU₄_is F G₂ at_ p.S K₁ R enc rad x.1 (strsOf Fr₂ x.2) w).2
    (nearU_of_nearAt ρ Fr₂ p R.same hsame enc henc hA x.1.2 x.2 (words₂ ρ p.S R w) _ hu rad hnear)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.encIs_encOf
#print axioms Johnson.RunOne.KeyRows23.nearU_of_nearAt
#print axioms Johnson.RunOne.KeyRows23.ride₂_54
#print axioms Johnson.RunOne.KeyRows23.loc_back₂
