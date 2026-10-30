-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyPinsAtBase3.lean: The key file, the last chain: ROW 3.0's ONE PREMISE OF SUBSTANCE, PinsStay across K14's second part, AT THE TABLES' OWN READING BaseSt.h₃ (Johnson/RunOne/KeyOneReading.lean), under ONE NEW CONDITION ON THE LETTER sm. One definition of Prop; theorems.

THE FACT. At the seat of the table's message 4 (Omega) T.h₃ reads the sample IN FRONT in the border's copy of the shared statement, under the shared plan's numeral 2; BEHIND, the border gone, in the own statement under nOwn = w + 2. The block lays there a COPY of Omega's record (Laid.copy: Johnson/Desc/Third/Law/LaidDef.lean): shape and pad as they were · sampled · groups := [own] · its sample rows RENAMED to the new number. So SmOnly (Johnson/RunOne/KeySmOnly.lean: one number, the same rows) does not reach it.

  BaseSt.SmMoves   THE CONDITION, ON THE LETTER sm, GUARDED: a sample is read off the record's shape, its mark and its rows AS ROWS ON THE MESSAGE's OWN NUMBER: carried to another number with its rows renamed, it is the same sample; asked of a message of a statement whose sample rows lie on its own tables alone (SampleIn). IT STANDS BESIDE SmOnly, NOT IN ITS PLACE: like SmOnly it lets sm read shape · sampled · sampleRows alone; whether a guarded SmOnly follows from it at n := o (it would, if renaming to o leaves a row on o's own tables as it was) is shown by nobody.
  pins_laid        T.orc₁ = K₁.orc → T.SmMoves → Laid … → the promise in front → PinsStay T.h₃ at_ [0, 2, 4] (z, s) (z, s').
  r3_0_base        ROW 3.0 WHOLE AT THE SEAT, AT T.h₃: r3_0_seat (Johnson/RunOne/KeyRowsAtSeat.lean) with its premise hp gone.

OBJECT. PinsStay T.h₃ at_ [0, 2, 4] at two records tied by Laid; the tables' Keeps from border 0 to 1 of the last chain at pc.b = held ‹(Key.descriptionFromSource X N P).second.blocksInOrder[0]›.
USER. The field r3_0 of the key file's twenty-one laws, at the tables' one reading.
LETTERS. T : BaseSt …, at_, K₁, R, a, idx, coll, src, off₂, off₃, t₁: free.

THE CAUTION: UNTIL A MEMBER IS SHOWN, EVERY LAW THAT HAS PIN AS AN ITEM OR NoColl IN ITS PROMISE MAY BE TRUE AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING. r3_0_base IS SUCH A LAW.
IS IT EMPTY HERE? (1) SmMoves: an sm that gives every record one sample meets it, so it can be met. WHETHER THE SAMPLE THAT THE LIBRARY WANTS, OR THE TABLES' FILLING baseK, MEETS IT IS NOT SHOWN. If it does not, pins_laid is idle there. (2) T.orc₁ = K₁.orc: a tie of two letters; AtFk.orc. (3) Laid: the block says yes on the honest key file at both stored sizes (our walk; evaluated), and its yes gives Laid. (4) The promise in front: of on₃ 0 as a whole no member is shown by anybody.

WHAT IS SPENT OF THE PROMISE IN FRONT: Free₃.arr (what sits at the three seats) · placed (I and V have places in the own book: so their numbers lie below the count of messages, by Laid.step) · in₀ (the guard) · the book-keeping's «messages = w + 2» and the border's Bool (Omega is number 2 there; one codes).

Limits. Of samples and the stored table's record alone. Nothing on chance. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.RunOne.KeyRowsAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (Laid Border)

/-- A sample moves with its record to another number, its rows renamed. -/
def BaseSt.SmMoves {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec) : Prop :=
  ∀ (St : Statement) (o n : Nat) (x x' : OnBytes.Oracle), St.oracles[o]? = some x → SampleIn St o →
    x'.shape = x.shape → x'.sampled = x.sampled → x'.sampleRows = x.sampleRows.map (·.renamed n) →
    T.sm St.codes n x' = T.sm St.codes o x

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (T : BaseSt Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- An elder message's sample stays. -/
theorem smAt_old {s s' : St₃} {b : Border} {yO : OnBytes.Oracle} {G : OnBytes.Group} {dot : OnBytes.Row}
    (L : Laid S s s' b yO G dot) (o : Nat) (ho : o < s.st.oracles.size) : T.smAt s'.st o = T.smAt s.st o := by
  unfold BaseSt.smAt
  rw [L.codes, L.old o ho]

/-- **The three pins stay across K14's second part, at the tables' own reading.** -/
theorem pins_laid (horc : T.orc₁ = K₁.orc) (hm : T.SmMoves) (z : P₃) (s s' : St₃) (y : Strs)
    {b : Border} {yO : OnBytes.Oracle} {G : OnBytes.Group} {dot : OnBytes.Row} (L : Laid S s s' b yO G dot)
    (hon : onAt F T.h₃ at_ (meaning₃ S K₁ R) (shapeB₃ S K₁ a idx src t₁ 0) (Free₃ F T.h₃ at_ S K₁ R coll off₂ off₃ 0) (open₃ 0) (z, s) y) :
    PinsStay T.h₃ at_ [0, 2, 4] (z, s) (z, s') := by
  obtain hn | ⟨hsh, _, h3, _⟩ := hon
  · exact absurd trivial hn
  have Fr := front_of_shape S K₁ a idx src t₁ s hsh
  obtain ⟨hom, _, _, _, _, hcodes⟩ := border_gives L Fr.bord
  have harr : ∀ k ∈ [0, 2, 4], T.arr (at_ k).1 (at_ k).2 = k := h3.arr
  have hpl := h3.placed (by decide)
  -- the elder two
  have elder : ∀ k ∈ [0, 2], (T.orc₁ k).bind (T.smAt s'.st) = (T.orc₁ k).bind (T.smAt s.st) := by
    intro k hk
    obtain ⟨o, t, ho, ht, _⟩ := hpl k hk
    rw [horc, ho]
    have hlt : o < s.st.oracles.size := by
      rw [L.step]
      exact (Array.getElem?_eq_some_iff.1 ht).1
    exact smAt_old T S L o hlt
  -- Omega
  have om : T.smAt s'.st (nOwn s') = T.smAt b.shared.st 2 := by
    have en : nOwn s' = s.st.oracles.size := by
      unfold nOwn
      rw [L.loc, Fr.msgs]
    obtain ⟨b', hb', hin⟩ := h3.in₀ rfl
    have eb : b' = b := Option.some.inj (hb'.symm.trans L.border)
    rw [eb, hom] at hin
    have hthere : b.shared.st.oracles[2]? = some yO := by
      rw [← hom]
      exact L.there
    unfold BaseSt.smAt
    rw [en, L.copy, hthere, L.codes, ← hcodes]
    exact hm b.shared.st 2 s.st.oracles.size yO _ hthere hin rfl L.sampled.symm rfl
  refine ⟨fun k hk => ?_, rfl⟩
  have e := harr k hk
  show (if T.arr (at_ k).1 (at_ k).2 < 3 then (T.orc₁ (T.arr (at_ k).1 (at_ k).2)).bind (T.smAt s'.st) else
      match s'.loc.border with
      | some b => (orc₂ (T.arr (at_ k).1 (at_ k).2)).bind (T.smAt b.shared.st)
      | none => if T.arr (at_ k).1 (at_ k).2 == 4 then T.smAt s'.st (nOwn s') else none) =
    (if T.arr (at_ k).1 (at_ k).2 < 3 then (T.orc₁ (T.arr (at_ k).1 (at_ k).2)).bind (T.smAt s.st) else
      match s.loc.border with
      | some b => (orc₂ (T.arr (at_ k).1 (at_ k).2)).bind (T.smAt b.shared.st)
      | none => if T.arr (at_ k).1 (at_ k).2 == 4 then T.smAt s.st (nOwn s) else none)
  rw [e]
  have hb' : s'.loc.border = none := by rw [L.loc]
  rw [hb', L.border]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact elder 0 (by decide)
  · exact elder 2 (by decide)
  · exact om

end

section
variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr₃ : Frame)
  (T : BaseSt Cells M Smp Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)
  {K : Type} [Field K] (ρ : Model.Reading K)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **ROW 3.0, WHOLE AT THE SEAT, AT THE TABLES' OWN READING.** -/
theorem r3_0_base (pc : Piece C Fr₃ (P₃ × St₃) Claim W)
    (b : Block VerifiableInference.Desc.Third.S₃ Claim) (hb : (descriptionFromSource X N P).second.blocksInOrder[0]? = some b) (hpb : pc.b = held b)
    (hbase : ∀ j ∈ pinned (open₃ 0), (at_ j).1 < pc.base) (hc : CellOnly coll)
    (hsame : R.same = fun x y => ρ.val x = ρ.val y) (hlin : K₁.lin = (thirdPar X.chains).S)
    (hnum : ∀ o, K₁.orc 2 = some o → K₁.num o = some 2) (hat : AtOk at_ off₂ off₃ t₁)
    (horc : T.orc₁ = K₁.orc) (hm : T.SmMoves) :
    pc.ior.red.Keeps (on₃ F Fr₃ T.h₃ at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ 0) (on₃ F Fr₃ T.h₃ at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ 1)
      (L₃ F Fr₃ T.h₃ at_ (thirdPar X.chains).S K₁ R 0) (L₃ F Fr₃ T.h₃ at_ (thirdPar X.chains).S K₁ R 1) pc.err :=
  r3_0_seat F Fr₃ T.h₃ at_ K₁ R a idx coll src off₂ off₃ t₁ ρ X N P pc b hb hpb hbase hc hsame hlin hnum hat
    fun z s s' y _ _ _ _ L hon => pins_laid F T at_ (thirdPar X.chains).S K₁ R a idx coll src off₂ off₃ t₁ horc hm z s s' y L hon

end

end Johnson.RunOne.KeyRows23
