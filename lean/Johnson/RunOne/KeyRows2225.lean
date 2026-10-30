-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRows2225.lean: ROWS 2.2 («send o_u»; borders 2 → 3) AND
2.5 («send o_omega»; borders 5 → 6) OF THE KEY FILE's TABLE OF JOINTS, at the tables' own
letters (Johnson/RunOne/KeyRows23At.lean: on₂ | L₂): THE WAY BACK ACROSS A SENDING OF THE SHARED
CHAIN, item by item; a form of the row of a sending THAT OPENS A LIST OF PINS; and the two rows in
the table's own form Keeps.
After the pattern of the tables' files' row 1.0.

ON EMPTINESS: IT IS NOT SHOWN THAT ANY RECORD, READING AND ORACLES EXIST AT WHICH on₂ … 2 | on₂ … 5
HOLDS. UNTIL A MEMBER IS SHOWN AT F_K's OWN LETTERS, EVERY LAW THAT HAS PIN AS AN ITEM OR NoColl IN
ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING.

OBJECT: a piece pc at the record P₂ × St₂ whose block's yes leaves the first component and lays on
the second what a sending lays (hl: SentBack): meant: the maker's pieces number 2 | 5 of the shared
chain.
USER: keepsAt_of_law₂ | KeepsAt.reached: the fields r2_2 | r2_5 of The21
(Johnson/Top/Fire/Code/The35.lean).
LETTERS: the tables'; THIS FILE's OWN BESIDE: K ρ · New Sl Ra Rb (the row
of a sending's own: Johnson/Desc/Key/KeySendRow.lean).
  sendRow_keeps_list   A FORM OF sendRow_keeps_new (Johnson/Desc/Key/KeySendRow.lean):
    the row opens a LIST ks of pins (2.5
    opens 4 and 5 in one piece); at ks := [k] it is that law
  SentBack             what the way back spends of a sending's yes: the codes and the groups are as
    they were; every older message is as it was, whole; the point, the key and G_u's number stay.
    [meant payer: laid22_of_yes | laid25_of_yes (Johnson/Desc/Key/Laid/Laid2.lean: SentAt · Laid22 |
    Laid25), or send_laid (SendLaid.lean beside it) with K14's behindU | behindOmega]
  SmpGrows             A CONDITION ON THE READING (SmpOwn of KeySendYes1.lean, reworded here): a
    sample that is read at a record is read, the same, at every record with the same first component
    and codes in which every older message is as it was; the stored table's record likewise.
    [BaseSt.h₂ meets it at every pair, by reading: smAt St o = (St.oracles[o]?).bind (sm St.codes
    o)]
  rowHolds_back        a row that has passed the tests says in front what it says behind [three
    lines over says_extends and rowHolds_iff_says_of_rowIn: A NEAR TWIN OF
    rowHolds_extends (Johnson/Desc/Key/RowsCarry.lean), which is not
    imported here]
  back22 | back25      **THE WAY BACK**: the nine | eleven items that are open in front ride, at one
    witness
  keeps₂_send2 | keeps₂_send5   the rows: Keeps (on₂ … k) (on₂ … (k + 1)) (L₂ … k) (L₂ … (k + 1))
    pc.err
PREMISES OF THE TWO ROWS, EACH WITH ITS PAYER AND ITS KIND OF «∀»: hl [bare ∀ under the
block's yes]: «the yes gives Laid22 | Laid25» (above) + held_decide · hbase: the frame's numbers (
at the elder pins 0 | 2, the FIRST chain's trees, too) · hsame [bare ∀]: R.same := «ρ x = ρ y» is
the meant filling · hG : SmpGrows [BARE ∀ z z', no yes]: above · yes [under the rounds' test, the
block's yes, New and the promise in front]: THE PROMISE's HALF: KeyRow22.lean's sure22 | sure25 ·
hnew [under the promise and the piece's yes]: Piece.ShownAll · good: K1's files' send_goodIn
(Johnson/Desc/K1/Law/GoodSend3.lean) AT ITS OWN LETTER On' (NEVER True: «the statement has just 2 |
4 messages») · tie [under Sl]: tie_of_sealReads at the message outright.
WHAT IS SPENT OF THE PROMISE IN FRONT: hasSmp at the elder pins · at 2.5: Free₂ 5's order and shape₂
5's «two messages».
Nothing on soundness by itself.
-/
import Johnson.RunOne.KeyRow21
import Johnson.Desc.Means.Keeps
import Johnson.Desc.Key.KeySendRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

section
variable {Xi P S Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription Xi) (Fr : Frame) (G : Reading
           (P × S) Cells M Smp Rec) (at_ : Where)
  (Mg : KMeaning P S (Wit Cells Unit M))

/-- **The row of a sending that opens a list of pins.** A form of sendRow_keeps_new. -/
theorem sendRow_keeps_list (pc : Piece C Fr (P × S) Cl W) (shape shape' : S → Bool) (free free' : P
    × S → Strs → Prop) (O outs : List KItem) (ks : List Nat)
    (hk : pinned (O ++ outs) = pinned O ++ ks) (hbase : ∀ j ∈ pinned O, (at_ j).1 < pc.base)
    (New : Strs → Prop) (hnew : ∀ a τ b, onB F Fr G at_ Mg shape free O a → pc.ior.red.out a τ =
        some b → New (strsOf Fr b.2))
    (sure : ∀ a rs gs b y y', roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs =
        .ok b → StrsStay F at_ O y y' → New y' → onAt F G at_ Mg shape free O a y →
      (Mg.unmarked b → Mg.unmarked a) ∧ (Mg.unmarked a → shape' b.2 = true ∧
        (∀ j ∈ pinned O, G.smp b (at_ j).1 (at_ j).2 = G.smp a (at_ j).1 (at_ j).2) ∧ free' b y'))
    (back : ∀ a rs gs b y y' w, roundsFit pc.b.rounds rs = true → pc.b.decide a (rs.map noDigest) gs
        = .ok b → StrsStay F at_ O y y' → onAt F G at_ Mg shape free O a y →
      relAt F G at_ Mg (O ++ outs) b y' w → relAt F G at_ Mg O a y w)
    (Sl : (P × S) × Fr.E.Str → Prop) (Ra Rb : (P × S) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (onB F Fr G at_ Mg shape free O) Sl Ra Rb)
    (tie : ∀ b, Sl b → ∀ k ∈ ks, hasSmp G (at_ k).1 (at_ k).2 b.1 = true ∧ NoColl F G (at_ k).1 (at_
        k).2 b.1 (strsOf Fr b.2)) :
    pc.ior.red.Keeps (onB F Fr G at_ Mg shape free O) (onB F Fr G at_ Mg shape' free' (O ++ outs))
        (claimB F Fr G at_ Mg O) (claimB F Fr G at_ Mg (O ++ outs)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.conseq (leads_of_goodIn Fr pc _ _ _ _ good) (fun _ h => h) fun a τ b ha hb
      hS => ?_
  have hT := tie b hS
  have hd := piece_decides_at pc a τ b hb
  have hf := (piece_fits_at pc a τ b hb).1
  have Hy := strsStay_of_out F Fr at_ pc O hbase a b τ hb
  obtain ⟨hm, hs⟩ := sure a.1 _ _ b.1 _ _ hf hd Hy (hnew a τ b ha hb) ha
  refine ⟨?_, fun ⟨w, hw⟩ => ⟨w, back a.1 _ _ b.1 _ _ w hf hd Hy ha hw⟩⟩
  by_cases hu : Mg.unmarked a.1
  · obtain ⟨h1, h3, h4⟩ := hs hu
    have hr : shape a.1.2 = true ∧ ((pinned O).all fun k => hasSmp G (at_ k).1 (at_ k).2 a.1) = true
        ∧ free a.1 (strsOf Fr a.2) ∧
        ∀ k ∈ pinned O, NoColl F G (at_ k).1 (at_ k).2 a.1 (strsOf Fr a.2) := ha.resolve_left (fun
            hn => hn hu)
    refine Or.inr ⟨h1, ?_, h4, ?_⟩
    · rw [hk, List.all_append, Bool.and_eq_true]
      refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun k hk' => (hT k hk').1⟩
      have := List.all_eq_true.1 hr.2.1 j hj
      unfold hasSmp at this ⊢
      rw [h3 j hj]
      exact this
    · intro j hj
      rw [hk] at hj
      rcases List.mem_append.1 hj with hj | hj
      · exact noColl_ride F G _ _ a.1 b.1 _ _ (h3 j hj) (Hy.word j hj) (hr.2.2.2 j hj)
      · exact (hT j hj).2
  · exact Or.inl fun hb' => hu (hm hb')

end

end VerifiableInference.Desc.Key

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound

theorem open₂_send2 : open₂ 3 = open₂ 2 ++ [.pin 3, .srow 3] := by decide
theorem open₂_send5 : open₂ 6 = open₂ 5 ++ [.pin 4, .srow 4, .pin 5, .srow 5] := by decide
theorem pinned_send2 : pinned (open₂ 2 ++ [.pin 3, .srow 3]) = pinned (open₂ 2) ++ [3] := by decide
theorem pinned_send5 : pinned (open₂ 5 ++ [.pin 4, .srow 4, .pin 5, .srow 5]) = pinned (open₂ 5) ++
    [4, 5] := by decide

/-- **What the way back spends of a sending's yes.** -/
structure SentBack (d d' : St₂) : Prop where
  codes : d'.st.codes = d.st.codes
  groups : d'.st.groups = d.st.groups
  older : ∀ o, o < d.st.oracles.size → d'.st.oracles[o]? = d.st.oracles[o]?
  psi : d'.loc.psiSh = d.loc.psiSh
  key : d'.loc.key = d.loc.key
  gU : d'.loc.gU = d.loc.gU

theorem SentBack.extends {d d' : St₂} (B : SentBack d d') : Means.Extends d.st d'.st :=
  ⟨B.codes, fun o x hx => ⟨x, (B.older o (Array.getElem?_eq_some_iff.1 hx).1).trans hx, rfl⟩⟩

/-- **A condition on the reading.** -/
def SmpGrows {Cells M Smp Rec : Type} (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) : Prop :=
  ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.codes = z.2.st.codes → (∀ o, o < z.2.st.oracles.size →
      z'.2.st.oracles[o]? = z.2.st.oracles[o]?) →
    (∀ j t s, G₂.smp z j t = some s → G₂.smp z' j t = some s) ∧ G₂.recOf z' = G₂.recOf z

section
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- A row that has passed the tests says in front what it says behind. -/
theorem rowHolds_back (same : E → E → Prop) (hsame : ∀ x y, same x y ↔ ρ.val x = ρ.val y) {St St' :
    Statement} {G : OnBytes.Group} {row : OnBytes.Row}
    (hE : Means.Extends St St') (hr : Means.RowIn St G row) (val : Nat → Part → Nat → E) (h :
        RowHolds same St' val row) : RowHolds same St val row := by
  have t : RowHolds (fun a b => ρ.val a = ρ.val b) St' val row := by
    unfold RowHolds at h ⊢
    exact (hsame _ _).1 h
  have t2 := (rowHolds_iff_says_of_rowIn ρ St G val row hr).2
    ((Means.says_extends ρ hE hr _).1 ((rowHolds_iff_says_of_rowIn ρ St' G val row (hr.extends hE
        fun _ c => c)).1 t))
  unfold RowHolds at t2 ⊢
  exact (hsame _ _).2 t2

variable {Cells M : Type} (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat →
    E) (rad : Nat)

theorem srow₂_sent (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (k : Nat) (z : P₂) (d d' : St₂)
    (y y' : Strs) (w : Wit Cells Unit M) (B : SentBack d d')
    (hord : Means.InOrder d.st) (hlt : ∀ o, (plan₂ S).orc k = some o → o < d.st.oracles.size)
    (h : (meaning₂ S K₁ R enc rad).srow k (z, d') y' w) : (meaning₂ S K₁ R enc rad).srow k (z, d) y
        w := by
  simp only [meaning₂] at h ⊢
  split_ifs at h ⊢
  · exact h
  · obtain ⟨o, x, h1, h2, h3, h4, h5⟩ := h
    have hx : d.st.oracles[o]? = some x := (B.older o (hlt o h1)).symm.trans h2
    exact ⟨o, x, h1, hx, h3, h4, fun r hr => rowHolds_back ρ R.same hsame B.extends (hord.samples o
        x hx r hr) _ (h5 r hr)⟩

theorem rowsHold_sent (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (val : Nat → Part → Nat → E)
    (d d' : St₂) (B : SentBack d d') (hord : Means.InOrder d.st)
    (g lo n : Nat) (h : rowsHold R.same d'.st val g lo n) : rowsHold R.same d.st val g lo n := by
  obtain ⟨G, hG, hle, hne, hall⟩ := h
  have hG' : d.st.groups[g]? = some G := by rw [← B.groups]; exact hG
  exact ⟨G, hG', hle, hne, fun r hr => rowHolds_back ρ R.same hsame B.extends
    (hord.rows g G hG' r (List.mem_of_mem_drop (List.mem_of_mem_take hr))) _ (hall r hr)⟩

end

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec)
    (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- An elder pin rides back. -/
theorem pin_sent (hG : SmpGrows G₂) (O : List KItem) (k : Nat) (hk : k ∈ pinned O) (z : P₂) (d d' :
    St₂) (y y' : Strs) (w : Wit Cells Unit M) (B : SentBack d d')
    (Hy : StrsStay F at_ O y y') (hs : hasSmp G₂ (at_ k).1 (at_ k).2 (z, d) = true)
    (h : (KItem.pin k).holds F G₂ at_ (meaning₂ S K₁ R enc rad) (z, d') y' w) : (KItem.pin k).holds
        F G₂ at_ (meaning₂ S K₁ R enc rad) (z, d) y w := by
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
  have e : G₂.smp (z, d') (at_ k).1 (at_ k).2 = G₂.smp (z, d) (at_ k).1 (at_ k).2 :=
    ((hG (z, d) (z, d') rfl B.codes B.older).1 _ _ s hs').trans hs'.symm
  exact rides_pin2_at F G₂ _ _ (z, d) (z, d') y y' w e (Hy.word k hk) h

/-- **ROW 2.2: THE WAY BACK.** -/
theorem back22 (hG : SmpGrows G₂) (z : P₂) (d d' : St₂) (y y' : Strs) (w : Wit Cells Unit M) (B :
    SentBack d d') (Hy : StrsStay F at_ (open₂ 2) y y')
    (hs : ∀ k ∈ pinned (open₂ 2), hasSmp G₂ (at_ k).1 (at_ k).2 (z, d) = true)
    (hw : relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ 2 ++ [.pin 3, .srow 3]) (z, d') y' w) :
        relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ 2) (z, d) y w := by
  have mem : ∀ j, j ∈ open₂ 2 → j.holds F G₂ at_ (meaning₂ S K₁ R enc rad) (z, d') y' w := fun j hj
      => hw j (List.mem_append_left _ hj)
  intro i hi
  have hi0 := hi
  rw [open₂_at2] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact pin_sent F G₂ at_ S K₁ R enc rad hG (open₂ 2) 0 (by decide) z d d' y y' w B Hy (hs 0
      (by decide)) (mem _ hi0)
  · exact mem _ hi0
  · exact pin_sent F G₂ at_ S K₁ R enc rad hG (open₂ 2) 2 (by decide) z d d' y y' w B Hy (hs 2
      (by decide)) (mem _ hi0)
  · exact mem _ hi0
  · exact (eval₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 ((eval₄_is F G₂ at_ S K₁ R enc rad (z, d')
      y' w).1 (mem _ hi0))
  · have hn := nearU_cell _ _ _ _ _ _ _ _ Hy.cell ((nearU₄_is F G₂ at_ S K₁ R enc rad (z, d') y'
      w).1 (mem _ hi0))
    have hn' : NearUAt R.same (plan₂ S).lin.fold.index.code.logN rad enc (d'.loc.psiSh.drop (plan₂
        S).lin.kLo) y (uOf (plan₂ S) R d'.st.codes w) := hn
    rw [B.psi, B.codes] at hn'
    exact (nearU₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 hn'
  · have hr := (recRow₁_is F G₂ at_ S K₁ R enc rad (z, d') y' w).1 (mem _ hi0)
    have hr' : RecRowAt R.same (plan₂ S).lin.fold.index d'.loc.key (d'.loc.psiSh.drop (plan₂
        S).lin.kLo) (uOf (plan₂ S) R d'.st.codes w) := hr
    rw [B.psi, B.codes, B.key] at hr'
    exact (recRow₁_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 hr'
  · obtain ⟨g, hg, hd⟩ := (dotU₄_is F G₂ at_ S K₁ R enc rad (z, d') y' w).1 (mem _ hi0)
    have hd' : DotUAt R.same (plan₂ S).lin g d'.loc.psiSh (uOf (plan₂ S) R d'.st.codes w) (vOf'
        (plan₂ S) R d'.st.codes w) := hd
    rw [B.psi, B.codes] at hd'
    exact (dotU₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 ⟨g, hg, hd'⟩

/-- **ROW 2.5: THE WAY BACK.** -/
theorem back25 (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (hG : SmpGrows G₂) (z : P₂) (d d' :
    St₂) (y y' : Strs) (w : Wit Cells Unit M) (B : SentBack d d')
    (Hy : StrsStay F at_ (open₂ 5) y y') (hs : ∀ k ∈ pinned (open₂ 5), hasSmp G₂ (at_ k).1 (at_ k).2
        (z, d) = true)
    (hord : Means.InOrder d.st) (h0 : 0 < d.st.oracles.size)
    (hw : relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ 5 ++ [.pin 4, .srow 4, .pin 5, .srow 5])
        (z, d') y' w) : relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ 5) (z, d) y w := by
  have mem : ∀ j, j ∈ open₂ 5 → j.holds F G₂ at_ (meaning₂ S K₁ R enc rad) (z, d') y' w := fun j hj
      => hw j (List.mem_append_left _ hj)
  intro i hi
  have hi0 := hi
  rw [open₂_at5] at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact pin_sent F G₂ at_ S K₁ R enc rad hG (open₂ 5) 0 (by decide) z d d' y y' w B Hy (hs 0
      (by decide)) (mem _ hi0)
  · exact mem _ hi0
  · exact pin_sent F G₂ at_ S K₁ R enc rad hG (open₂ 5) 2 (by decide) z d d' y y' w B Hy (hs 2
      (by decide)) (mem _ hi0)
  · exact mem _ hi0
  · exact (eval₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 ((eval₄_is F G₂ at_ S K₁ R enc rad (z, d')
      y' w).1 (mem _ hi0))
  · obtain ⟨g, hg, hd⟩ := (dotU₄_is F G₂ at_ S K₁ R enc rad (z, d') y' w).1 (mem _ hi0)
    have hd' : DotUAt R.same (plan₂ S).lin g d'.loc.psiSh (uOf (plan₂ S) R d'.st.codes w) (vOf'
        (plan₂ S) R d'.st.codes w) := hd
    rw [B.psi, B.codes] at hd'
    exact (dotU₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 ⟨g, hg, hd'⟩
  · exact pin_sent F G₂ at_ S K₁ R enc rad hG (open₂ 5) 3 (by decide) z d d' y y' w B Hy (hs 3
      (by decide)) (mem _ hi0)
  · exact srow₂_sent ρ S K₁ R enc rad hsame 3 z d d' y y' w B hord (fun o ho => by
      have e : o = 0 := (Option.some.inj ho).symm
      rw [e]
      exact h0) (mem (.srow 3) hi0)
  · have hr := (record₄_is F G₂ at_ S K₁ R enc rad (z, d') y' w).1 (mem _ hi0)
    have hr' : rowsHold R.same d'.st (valOf (plan₂ S) R w) d'.loc.gU 0 (plan₂
        S).lin.fold.index.answers := hr
    rw [B.gU] at hr'
    exact (record₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 (rowsHold_sent ρ R hsame _ d d' B hord _
        _ _ hr')
  · have hr := (columns₄_is F G₂ at_ S K₁ R enc rad (z, d') y' w).1 (mem _ hi0)
    have hr' : rowsHold R.same d'.st (valOf (plan₂ S) R w) d'.loc.gU (plan₂
        S).lin.fold.index.answers (plan₂ S).lin.fold.columns := hr
    rw [B.gU] at hr'
    exact (columns₄_is F G₂ at_ S K₁ R enc rad (z, d) y w).2 (rowsHold_sent ρ R hsame _ d d' B hord
        _ _ _ hr')

end

/-! ## The two rows -/

/-- What is spent of the book-keeping at border 5: two messages. -/
theorem shape₂_at5 (S : LinShape) (a : Nat) (d : St₂) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a
    5 d) = true) : d.st.oracles.size = 2 := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
  obtain ⟨_, c2, _⟩ := h
  simpa using c2

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- The elder pins' samples stay, out of the condition on the reading and the promise's hasSmp. -/
theorem smp_sent (hG : SmpGrows G₂) (O : List KItem) (z z' : P₂ × St₂) (e1 : z'.1 = z.1) (B :
    SentBack z.2 z'.2)
    (hs : ((pinned O).all fun k => hasSmp G₂ (at_ k).1 (at_ k).2 z) = true) :
    ∀ j ∈ pinned O, G₂.smp z' (at_ j).1 (at_ j).2 = G₂.smp z (at_ j).1 (at_ j).2 := fun j hj => by
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hs j hj)
  exact ((hG z z' e1 B.codes B.older).1 _ _ s hs').trans hs'.symm

/-- **ROW 2.2.** -/
theorem keeps₂_send2 (pc : Piece C Fr₂ (P₂ × St₂) Cl W)
    (hl : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ SentBack z.2 z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 2), (at_ j).1 < pc.base) (hG : SmpGrows G₂)
    (New : Strs → Prop) (hnew : ∀ x τ x', (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 2) x →
        pc.ior.red.out x τ = some x' → New (strsOf Fr₂ x'.2))
    (yes : ∀ z rs gs z' y y', roundsFit pc.b.rounds rs = true → pc.b.decide z (rs.map noDigest) gs =
        .ok z' → StrsStay F at_ (open₂ 2) y y' → New y' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 2
          d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 2) (open₂ 2) z y →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 z'.2) = true ∧ Free₂ F G₂ at_ S K₁ R coll last₁
          off₂ 3 z' y')
    (Sl : (P₂ × St₂) × Fr₂.E.Str → Prop) (Ra Rb : (P₂ × St₂) × Fr₂.E.Str → W → Prop)
    (good : pc.GoodIn (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 2) Sl Ra Rb)
    (tie : ∀ x', Sl x' → hasSmp G₂ (at_ 3).1 (at_ 3).2 x'.1 = true ∧ NoColl F G₂ (at_ 3).1 (at_ 3).2
        x'.1 (strsOf Fr₂ x'.2)) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 2) (on₂ F Fr₂ G₂ at_ S K₁ R
        enc rad a coll last₁ off₂ 3) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 2) (L₂ F Fr₂ G₂ at_ S K₁ R enc
        rad 3) pc.err := by
  have key := sendRow_keeps_list F Fr₂ G₂ at_ (meaning₂ S K₁ R enc rad) pc (fun d => LKFU.Shape23.ok
      (LKFU.Shape23.shape₂ S a 2 d)) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 d))
    (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 2) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 3) (open₂ 2)
        [.pin 3, .srow 3] [3] pinned_send2 hbase New hnew
    (fun z rs gs z' y y' hf hd Hy hN ho => by
      obtain ⟨e1, B⟩ := hl z _ gs z' hd
      refine ⟨fun _ => trivial, fun hu => ?_⟩
      obtain ⟨_, h2, _, _⟩ := ho.resolve_left (fun hx => hx hu)
      obtain ⟨g1, g2⟩ := yes z rs gs z' y y' hf hd Hy hN ho
      exact ⟨g1, smp_sent G₂ at_ hG (open₂ 2) z z' e1 B h2, g2⟩)
    (fun z rs gs z' y y' w _ hd Hy ho hw => by
      obtain ⟨e1, B⟩ := hl z _ gs z' hd
      obtain ⟨_, h2, _, _⟩ := ho.resolve_left (fun hx => hx trivial)
      obtain ⟨p, d⟩ := z
      obtain ⟨p', d'⟩ := z'
      have e' : p' = p := e1
      subst e'
      exact back22 F G₂ at_ S K₁ R enc rad hG p' d d' y y' w B Hy (fun k hk => List.all_eq_true.1 h2
          k hk) hw)
    Sl Ra Rb good (fun x' h k hk => by
      obtain rfl : k = 3 := by simpa using hk
      exact tie x' h)
  unfold on₂ L₂ R₂
  rw [open₂_send2]
  exact key

/-- **ROW 2.5.** -/
theorem keeps₂_send5 {K : Type} [Field K] (ρ : Model.Reading K) (pc : Piece C Fr₂ (P₂ × St₂) Cl W)
    (hl : ∀ z rs gs z', pc.b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ SentBack z.2 z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 5), (at_ j).1 < pc.base) (hsame : ∀ x y, R.same x y ↔ ρ.val x =
        ρ.val y) (hG : SmpGrows G₂)
    (New : Strs → Prop) (hnew : ∀ x τ x', (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 5) x →
        pc.ior.red.out x τ = some x' → New (strsOf Fr₂ x'.2))
    (yes : ∀ z rs gs z' y y', roundsFit pc.b.rounds rs = true → pc.b.decide z (rs.map noDigest) gs =
        .ok z' → StrsStay F at_ (open₂ 5) y y' → New y' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 5
          d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 5) (open₂ 5) z y →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 z'.2) = true ∧ Free₂ F G₂ at_ S K₁ R coll last₁
          off₂ 6 z' y')
    (Sl : (P₂ × St₂) × Fr₂.E.Str → Prop) (Ra Rb : (P₂ × St₂) × Fr₂.E.Str → W → Prop)
    (good : pc.GoodIn (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 5) Sl Ra Rb)
    (tie : ∀ x', Sl x' → ∀ k ∈ [4, 5], hasSmp G₂ (at_ k).1 (at_ k).2 x'.1 = true ∧ NoColl F G₂ (at_
        k).1 (at_ k).2 x'.1 (strsOf Fr₂ x'.2)) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 5) (on₂ F Fr₂ G₂ at_ S K₁ R
        enc rad a coll last₁ off₂ 6) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 5) (L₂ F Fr₂ G₂ at_ S K₁ R enc
        rad 6) pc.err := by
  have key := sendRow_keeps_list F Fr₂ G₂ at_ (meaning₂ S K₁ R enc rad) pc (fun d => LKFU.Shape23.ok
      (LKFU.Shape23.shape₂ S a 5 d)) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 d))
    (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 5) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 6) (open₂ 5)
        [.pin 4, .srow 4, .pin 5, .srow 5] [4, 5] pinned_send5 hbase New hnew
    (fun z rs gs z' y y' hf hd Hy hN ho => by
      obtain ⟨e1, B⟩ := hl z _ gs z' hd
      refine ⟨fun _ => trivial, fun hu => ?_⟩
      obtain ⟨_, h2, _, _⟩ := ho.resolve_left (fun hx => hx hu)
      obtain ⟨g1, g2⟩ := yes z rs gs z' y y' hf hd Hy hN ho
      exact ⟨g1, smp_sent G₂ at_ hG (open₂ 5) z z' e1 B h2, g2⟩)
    (fun z rs gs z' y y' w _ hd Hy ho hw => by
      obtain ⟨e1, B⟩ := hl z _ gs z' hd
      obtain ⟨h1, h2, h3, _⟩ := ho.resolve_left (fun hx => hx trivial)
      obtain ⟨p, d⟩ := z
      obtain ⟨p', d'⟩ := z'
      have e' : p' = p := e1
      subst e'
      exact back25 F G₂ at_ S K₁ R enc rad ρ hsame hG p' d d' y y' w B Hy (fun k hk =>
          List.all_eq_true.1 h2 k hk) h3.order
        (by rw [shape₂_at5 S a d h1]; decide) hw)
    Sl Ra Rb good tie
  unfold on₂ L₂ R₂
  rw [open₂_send5]
  exact key

end

end Johnson.RunOne.KeyRows23

#print axioms VerifiableInference.Desc.Key.sendRow_keeps_list
#print axioms Johnson.RunOne.KeyRows23.rowHolds_back
#print axioms Johnson.RunOne.KeyRows23.back22
#print axioms Johnson.RunOne.KeyRows23.back25
#print axioms Johnson.RunOne.KeyRows23.keeps₂_send2
#print axioms Johnson.RunOne.KeyRows23.keeps₂_send5
