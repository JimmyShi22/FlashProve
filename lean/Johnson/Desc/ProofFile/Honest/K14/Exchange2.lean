-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Exchange2.lean: kind K14: «EXCHANGE» (Honest/Thread/Pays.lean) AT
THE MEMBERS 1 TO 8 OF THE SHARED CHAIN's THREAD, at this kind's letters (Honest/K14/Thread2.lean:
letters2), EACH UNDER NAMED PREMISES: at 6 under none; at the seven others under the public premises
(Plan2; hN, but at 1): at 7 under these alone; at 1 and 3 also under premises that are shown in no
file; at 2, 4, 5 and 8 also under a premise on what the member's own play shows, which other files
show from other premises. Statements with their proofs.

Behind a member's own step, with the thread in front in hand: the items that the member's row of the
table, read forwards, owes hold of the witness, at every continuation of the challenges heard. The
items that a member opens: from the run of steps up to it, which the thread's clause on how the
state was made hands over (Johnson/Desc/K14/Honest/StepsTwins.lean, ItemsOwn.lean). A pin that a
member reads as context and owes again: from the pin in front, at the continuation that has the
member's own challenges first, by what the step leaves (SmpOwn.quiet, SmpOwn.zeta).

Main names:
  words2_rv, pin_iff, pins_open   small ones; the last by evaluation of the table read forwards
  blank, holds_get, get_wit2   THE WITNESS's TYPE IS A VARIABLE (Thread2.lean: WitLens): what an
                      item other than the committed table's pin says of a witness it says of the
                      words read off it; the words read off the thread's witness are the honest
                      words. By these two each goal below goes over to its form at words
  ShowsU, ShowsCols, ShowsO, ShowsMu   THE PREMISES ON WHAT A MEMBER's OWN PLAY SHOWS: definitions:
                      premises' forms, each at the member's own sub-protocol and at challenges that
                      fit its rounds: what the sending of o_u shows, the columns that "LOC" is
                      handed, what the second sending shows and the scalar at "SPLIT" are the honest
                      values. Not shown in this file
  exchange1           OmU, NearAt at distance 0, RecAll. Asks hkey, hAns, hTab
  exchange2, exchange5   the new messages' pins and sample constraints. Ask ShowsU; ShowsO
  exchange3, exchange4   the constraints laid; o_u's pin. Ask hAns; ShowsCols
  exchange6           nothing is owed
  exchange7           (fold)'s equation; two pins. Asks nothing of what is shown
  exchange8           the two constraints laid; o_sp's pin. Asks ShowsMu. That the two stretches of
                      one constraint each are not empty is not in the items' form: the form behind
                      has the lists' lengths (Debts2.lean: formKeeps8)

The witness in every goal is the letter rest with the honest words laid in (Thread2.lean: witL); the
words read off it: at this kind's four messages' numbers the honest words, at the others the words
of rest (witAll, holdsAt). The four premises on what is shown stand at O.holds; that the OOD answers
do not hang on the words in front: Honest/K14/AnswersAny.lean.

What is assumed, as premises: Plan2 (Debts2.lean); no two messages have one tenant (hN). SHOWN IN NO
FILE: hkey: a valid input's key has sizes that fit; hAns: its answers are its rows' own; hTab: the
committed table's column at every location holds the rows' own symbols (no theorem ties the three to
a committer written in Lean; the library has one that runs, Johnson/Bind/Twin.lean, and one as
mathematics, Johnson/Top/ToldCommitPlain.lean).
EACH OF THE FOUR PREMISES ON WHAT IS SHOWN FOLLOWS FROM OTHER PREMISES IN ANOTHER FILE: ShowsU and
ShowsO: Honest/K14/SendingsShows.lean; ShowsCols, from hTab: Honest/K14/ColsPaid.lean; ShowsMu:
Honest/K14/MuPaid.lean and Holds2.lean. ShowsMu IS SHOWN ONLY UNDER THREE PUBLIC FACTS: the book's
entry by which the part at "SPLIT" spends a coin is the entry number 0 of o_sp's mask row among its
sender's coins (Holds2.lean: he); "LIN point" is the chain's round number 0; "LIN zeta" is its round
number 6 (MuPaid.lean: h0, h6). That ShowsMu fails without them is not proved; it holds vacuously
wherever the list has no member number 8 or the thread holds at no stand in front of it.

What is not claimed. That the thread holds at any run. At these letters, where no two messages have
one tenant (hN), the items pin m and row (.sample m) are one sentence, and no item ties the words
words2 to the tables that stand sent. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Debts2
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.K14.AnswersAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Sound (step_ok_iff)
open VerifiableInference.Desc.Shared (ItemS Msg2 NumbersS MeaningS)
open Desc.K14 (P14 St first)
open Desc.K14.Honest
open Desc.K14.Law (parU parO genK)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice}
  {layO : TreeLay}

/-! ## Small ones -/

/-- The honest words are the same at the two rounds rvOf R.drawn and noDigest R, by unfolding: so
far they read of the first round its challenges alone. Used by no proof of this folder. -/
theorem words2_rv (Q : P14) (sentU : Array OracleNotice) (d0 : St) (R : Fmt.RoundView) (H : Inputs) :
    words2 Q sentU d0 (rvOf R.drawn) H = words2 Q sentU d0 (noDigest R) H := rfl

/-- A meaning that says nothing: it stands where a meaning at words is wanted and none of its own
fields is read: that is so for every item but the committed table's pin (holds_get's hi). Kin:
others0 (Honest/K14/Thread2Member.lean) writes the same eleven fields out again, at P₁ := Unit. -/
def blank (P₁ : Type) : MeaningS St P₁ (Words Cb.Gl.E) :=
  ⟨fun _ _ _ _ _ => True, fun _ _ _ => True, fun _ _ _ _ _ => True, fun _ _ _ => True,
    fun _ _ => True, fun _ _ => True, fun _ _ _ => True, fun _ _ _ => True, fun _ _ _ _ => True,
    fun _ _ _ => True, fun _ => True⟩

/-- **What an item other than the committed table's pin says of a witness, it says of the words
that are read off it**: in the form at words. -/
theorem holds_get (ℓ : WitLens Wt) (Q : P14) (N : NumbersS) (Mg₀ : MeaningS St P₁ Wt) (i : ItemS)
    (hi : i ≠ .pinT) (s : St) (y : VerifiableInference.Desc.Strs) (w : Wt) :
    ItemS.holdsSh N (mgWords ℓ Q N Mg₀) i s y w ↔
      ItemS.holdsSh N (mgWords WitLens.words Q N (blank P₁)) i s y (ℓ.get w) := by
  cases i <;> first | exact Iff.rfl | exact absurd rfl hi

/-- The words that are read off the thread's witness: the honest words. A call of get_witL
(Honest/K14/Thread2.lean) at O's fields. -/
theorem get_wit2 (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (k : Coins Bk) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    O.lens.get (witL O.lens Q sentU O.holds O.rest k w h) =
      words2 Q sentU (first Q.codes w.key) (firstRv h) (holdsAt O k w h) :=
  get_witL O.lens Q sentU O.holds O.rest k w h

/-- What a message's pin says, where no two messages have one tenant. -/
theorem pin_iff {N : NumbersS} (hN : Function.Injective N.tenant)
    (Mg₀ : MeaningS St P₁ (Words Cb.Gl.E)) (m : Msg2) (s : St) (y : VerifiableInference.Desc.Strs)
    (w : Words Cb.Gl.E) :
    ItemS.holdsSh N (mgWords WitLens.words Q N Mg₀) (.pin m) s y w ↔ SmpOwn (num m) s w := by
  constructor
  · intro h
    exact h m rfl
  · intro h m' hm'
    obtain rfl : m' = m := hN hm'
    exact h

/-- o_u's pin is open in front of "(rec_gamma)", "LOC" and "LIN zeta"; o_omega's in front of "LIN
zeta"; o_sp's in front of "SPLIT": by evaluation of the table read forwards. -/
theorem pins_open :
    ItemS.pin .oU ∈ fwdOpen SharedRows.start (SharedRows.rows true) 3 ∧
      ItemS.pin .oU ∈ fwdOpen SharedRows.start (SharedRows.rows true) 4 ∧
      ItemS.pin .oU ∈ fwdOpen SharedRows.start (SharedRows.rows true) 7 ∧
      ItemS.pin .oOmega ∈ fwdOpen SharedRows.start (SharedRows.rows true) 7 ∧
      ItemS.pin .oSp ∈ fwdOpen SharedRows.start (SharedRows.rows true) 8 := by
  decide

/-! ## The premises on what a member's own play shows: named, and not shown here -/

/-- **What the sending of o_u shows is honest**: at the thread in front of it, whatever its play has
returned. A premise's form, to be shown of the part that sends o_u (Honest/K14/SendingsShows.lean).
It reads the first challenge heard by firstRv: the empty challenge where none was heard. Where the
list has no member number 2 it holds vacuously. -/
def ShowsU (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) : Prop :=
  ∀ blk k s m E ds y cols Ra Rb, (letters2 Q sentU O Cl).thread.bs[2]? = some blk →
    drawsFit blk.rounds ds = true → Thr (letters2 Q sentU O Cl).thread 2 k s m E →
    (letters2 Q sentU O Cl).thread.Moved blk k m E ds y cols → roundsOf y.1 = [Ra, Rb] →
    Rb.vals = answersAt (parU Q sentU) s.st Ra (O.holds k m.st.input).w₀
      (rowsU Q (first Q.codes m.st.input.key) (firstRv m.st.heard)
        (O.holds k m.st.input))

/-- **The columns that "LOC" is handed hold the rows' own symbols.** A premise's form
(from hTab: Honest/K14/ColsPaid.lean). A column is read by getD q 0: one that is too short counts as
0 at the rows that it lacks. -/
def ShowsCols (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    Prop :=
  ∀ blk k s m E ds y cols, (letters2 Q sentU O Cl).thread.bs[4]? = some blk →
    drawsFit blk.rounds ds = true → Thr (letters2 Q sentU O Cl).thread 4 k s m E →
    (letters2 Q sentU O Cl).thread.Moved blk k m E ds y cols →
    ∀ x col, (cols.map fun c => (c.2.1, c.2.2)).lookup x = some col →
      ∀ q < Q.par.S.fold.index.rows,
        rdE.val (ofF (col.toArray.getD q 0)) = genK rdE Q.par.S.fold x ((O.holds k m.st.input).Rw q)

/-- **What the sending of o_omega and o_sp shows is honest.** A premise's form, to be shown of the
part that sends them (Honest/K14/SendingsShows.lean). It reads the first challenge heard by firstRv:
the empty challenge where none was heard. -/
def ShowsO (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) : Prop :=
  ∀ blk k s m E ds y cols Ra Rb, (letters2 Q sentU O Cl).thread.bs[5]? = some blk →
    drawsFit blk.rounds ds = true → Thr (letters2 Q sentU O Cl).thread 5 k s m E →
    (letters2 Q sentU O Cl).thread.Moved blk k m E ds y cols → roundsOf y.1 = [Ra, Rb] →
    Rb.vals = answersAt (parO Q) s.st Ra
      (words1 Q sentU (first Q.codes m.st.input.key) (firstRv m.st.heard)
        (O.holds k m.st.input))
      (rowsO Q (first Q.codes m.st.input.key) (firstRv m.st.heard)
        (O.holds k m.st.input))

/-- **The scalar that "SPLIT" is shown is honest.** A premise's form, to be shown of the part at
"SPLIT" (Honest/K14/MuPaid.lean). It reads the first challenge heard by firstRv, and the challenge
number 6 by getD 6 noChallenge: the literal 6 is meant as the number of "LIN zeta"'s round; each is
the empty challenge where so many were not heard. -/
def ShowsMu (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) : Prop :=
  ∀ blk k s m E ds y cols R, (letters2 Q sentU O Cl).thread.bs[8]? = some blk →
    drawsFit blk.rounds ds = true → Thr (letters2 Q sentU O Cl).thread 8 k s m E →
    (letters2 Q sentU O Cl).thread.Moved blk k m E ds y cols → roundsOf y.1 = [R] →
    R.vals = [.e (Slice.ofE (muRun Q (first Q.codes m.st.input.key)
      (firstRv m.st.heard) (rvOf (m.st.heard.getD 6 noChallenge))
      (O.holds k m.st.input)))]

/-! ## «Exchange» -/

/-- **«Exchange» at "LIN point"**, under Plan2 and three premises that are shown in no file: OmU;
NearAt at distance 0; RecAll. The three: a valid input's key has sizes that fit (hkey); its answers
are its rows' own (hAns); the committed table's column at every location holds the rows' own symbols
(hTab). hTab reads the table by getD [] and getD r 0: where the table has no column at a location,
or one that is too short, 0 is read. -/
theorem exchange1 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hkey : ∀ w, O.valid w → keyFits w.key Q.par.S.fold.index = true)
    (hAns : ∀ k w, O.valid w → OwnAnswers Q w.key (O.holds k w))
    (hTab : ∀ k w, O.valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        rdE.val (ofF (((O.stored w Q.item x).getD []).toArray.getD r 0)) =
          genK rdE Q.par.S.fold x ((O.holds k w).Rw r)) :
    Exchange (letters2 Q sentU O Cl).thread 1 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, e1, e2, u⟩ := FlatAt.member1 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [] := hseen
  have h0 : m.st.heard = [] := by rw [← hsm, hseen']; rfl
  have hds : ds = [W.R1.drawn] := by rw [← hdr, hrs]; rfl
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0, hds]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 1).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d1
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hi' : i ∈ ([.omU, .nearU, .recRow] : List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl
  · exact Steps.omU_behind1 S u rfl (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))
  · refine Steps.nearU_behind1 S u rfl (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds'))) _
      (fun x hx r hr => ?_) 0
    have ht : Desc.K14.Law.colsOf (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1)).cell x =
        (O.stored m.st.input Q.item x).getD [] := by
      show (((E.stored Q.item x).map fun c => (x, c)).map (·.2)).getD [] = _
      rw [hH.1]
      show (((O.stored m.st.input Q.item x).map fun c => (x, c)).map (·.2)).getD [] = _
      cases O.stored m.st.input Q.item x <;> rfl
    rw [ht]
    exact hTab k _ hV x hx r hr
  · exact Steps.recRow_behind1 S u rfl (hkey _ hV) (hAns k _ hV)

/-- **«Exchange» at the sending of o_u**, under Plan2, hN and ShowsU: its pin and its sample
constraints. ShowsU is not shown here; from other premises: Honest/K14/SendingsShows.lean. -/
theorem exchange2 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (hU : ShowsU Q sentU O Cl) :
    Exchange (letters2 Q sentU O Cl).thread 2 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, e1, e2, u⟩ := FlatAt.member2 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [W.R1] := hseen
  have h0 : m.st.heard = [W.R1].map (·.drawn) := by rw [← hsm, hseen']
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0]; rfl
  have hf : firstRv (m.st.heard ++ (ds ++ ds')) = rvOf W.R1.drawn := by rw [h0]; rfl
  have hm1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [h0]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 2).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d2
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hsh₀ := hU blk k _ m E ds y cols _ _ hblk hd hA' hMv hrs
  rw [hm1] at hsh₀
  have hsh := hsh₀.trans (answersAt_any _ _ _ _
    (O.lens.get (O.rest k m.st.input (m.st.heard ++ (ds ++ ds')))) _)
  have k2 : SmpOwn 0 D.d2 (words2 Q sentU (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
      (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))) :=
    Steps.sampleOwn2 S u (H := holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds'))) hsh
  have hi' : i ∈ ([.pin .oU, .row (.sample .oU)] : List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl
  · exact (pin_iff hN _ _ _ _ _).2 k2
  · exact k2

/-- **«Exchange» at "(rec_gamma)"**, under Plan2, hN and hAns: the constraints that it lays; o_u's
pin, from the pin in front. hAns, shown in no file: the key's answers are its rows' own. -/
theorem exchange3 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant)
    (hAns : ∀ k w, O.valid w → OwnAnswers Q w.key (O.holds k w)) :
    Exchange (letters2 Q sentU O Cl).thread 3 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, e1, e2, u⟩ := FlatAt.member3 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b] := hseen
  have h0 : m.st.heard = [W.R1, W.R2a, W.R2b].map (·.drawn) := by rw [← hsm, hseen']
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0]; rfl
  have hf : firstRv (m.st.heard ++ (ds ++ ds')) = rvOf W.R1.drawn := by rw [h0]; rfl
  have hm1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [h0]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 3).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d3
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hi' : i ∈ ([.row .recG, .pin .oU] : List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl
  · exact Steps.recGOwn3 S u (hAns k _ hV)
  · exact (pin_iff hN _ _ _ _ _).2 (SmpOwn.quiet (by
      have hl := F.at3 hblk
      rw [hl.step] at hs
      exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _ _).1
        ((step_ok_iff 0 B.b3 _ _ _ _ _).1 hs).2.2.2) (by
      have p := hI (ds ++ ds') (.pin .oU) pins_open.1
      have p' := (holds_get O.lens Q O.N (O.Mg₀ m.st.input) (.pin .oU) (by simp) D.d2
          (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E)
          (witL O.lens Q sentU O.holds O.rest k m.st.input (m.st.heard ++ (ds ++ ds')))).1 p
      rw [get_wit2] at p'
      rw [hf] at p'
      exact (pin_iff hN _ _ _ _ _).1 p'))

/-- **«Exchange» at "LOC"**, under Plan2, hN and ShowsCols: the constraints that it lays; o_u's pin,
from the pin in front. ShowsCols is not shown here; from hTab: Honest/K14/ColsPaid.lean. -/
theorem exchange4 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (hC : ShowsCols Q sentU O Cl) :
    Exchange (letters2 Q sentU O Cl).thread 4 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, hcs, e1, e2, u⟩ := FlatAt.member4 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b] := hseen
  have h0 : m.st.heard = [W.R1, W.R2a, W.R2b].map (·.drawn) := by rw [← hsm, hseen']
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0]; rfl
  have hf : firstRv (m.st.heard ++ (ds ++ ds')) = rvOf W.R1.drawn := by rw [h0]; rfl
  have hm1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [h0]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 4).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d4
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hi' : i ∈ ([.row .loc, .pin .oU] : List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl
  · refine Steps.locOwn4 S u (H := holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))
      fun x _ col hcol q hq => ?_
    have hcol' : (W.cs.map fun c => (c.2.1, c.2.2)).lookup x = some col := hcol
    rw [hcs, List.take_length] at hcol'
    exact hC blk k _ m E ds y cols hblk hd hA' hMv x col hcol' q hq
  · exact (pin_iff hN _ _ _ _ _).2 (SmpOwn.quiet (by
      have hl := F.at4 hblk
      rw [hl.step] at hs
      exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _ _).2.1
        ((step_ok_iff 0 B.b4 _ _ _ _ _).1 hs).2.2.2) (by
      have p := hI (ds ++ ds') (.pin .oU) pins_open.2.1
      have p' := (holds_get O.lens Q O.N (O.Mg₀ m.st.input) (.pin .oU) (by simp) D.d3
          (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E)
          (witL O.lens Q sentU O.holds O.rest k m.st.input (m.st.heard ++ (ds ++ ds')))).1 p
      rw [get_wit2] at p'
      rw [hf] at p'
      exact (pin_iff hN _ _ _ _ _).1 p'))

/-- **«Exchange» at the sending of o_omega and o_sp**, under Plan2, hN and ShowsO: their pins and
their sample constraints. ShowsO is not shown here; from other premises:
Honest/K14/SendingsShows.lean. -/
theorem exchange5 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (hO : ShowsO Q sentU O Cl) :
    Exchange (letters2 Q sentU O Cl).thread 5 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, e1, e2, u⟩ := FlatAt.member5 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b, W.R4] := hseen
  have h0 : m.st.heard = [W.R1, W.R2a, W.R2b, W.R4].map (·.drawn) := by rw [← hsm, hseen']
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0]; rfl
  have hf : firstRv (m.st.heard ++ (ds ++ ds')) = rvOf W.R1.drawn := by rw [h0]; rfl
  have hm1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [h0]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 5).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d5
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hsh₀ := hO blk k _ m E ds y cols _ _ hblk hd hA' hMv hrs
  rw [hm1] at hsh₀
  have hsh := hsh₀.trans (answersAt_any _ _ _ _ (words1 Q sentU (first Q.codes m.st.input.key)
    (rvOf W.R1.drawn) (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))) _)
  have k5 : SmpOwn 2 D.d5 (words2 Q sentU (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
        (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))) ∧
      SmpOwn 3 D.d5 (words2 Q sentU (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
        (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))) :=
    Steps.sampleOwn5 S u (H := holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds'))) hsh
  have hi' : i ∈ ([.pin .oOmega, .row (.sample .oOmega), .pin .oSp, .row (.sample .oSp)] :
      List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl
  · exact (pin_iff hN _ _ _ _ _).2 k5.1
  · exact k5.1
  · exact (pin_iff hN _ _ _ _ _).2 k5.2
  · exact k5.2

/-- **«Exchange» at the joinings**: nothing is owed. -/
theorem exchange6 (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type) :
    Exchange (letters2 Q sentU O Cl).thread 6 := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
  have hi' : i ∈ ([] : List ItemS) := hi
  cases hi'

/-- **«Exchange» at "LIN zeta"**, under Plan2 and hN: (fold)'s equation; o_u's and o_omega's pins,
from the pins in front. -/
theorem exchange7 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) : Exchange (letters2 Q sentU O Cl).thread 7 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, e1, e2, u⟩ := FlatAt.member7 (B := B) F hQ.facts.goes
    0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b] := hseen
  have h0 : m.st.heard = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b].map (·.drawn) := by
    rw [← hsm, hseen']
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0]; rfl
  have hf : firstRv (m.st.heard ++ (ds ++ ds')) = rvOf W.R1.drawn := by rw [h0]; rfl
  have hm1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [h0]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 7).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d7
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hl := F.at7 hblk
  rw [hl.step] at hs
  obtain ⟨R, hR, -, kz, -⟩ := B.back7 hQ.facts.goes 0 _ _ _ _ _ hs
  have hi' : i ∈ ([.row .fold, .pin .oU, .pin .oOmega] : List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl
  · exact Steps.fold_behind7 S u (holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds')))
  · exact (pin_iff hN _ _ _ _ _).2 (SmpOwn.zeta kz (by
      have p := hI (ds ++ ds') (.pin .oU) pins_open.2.2.1
      have p' := (holds_get O.lens Q O.N (O.Mg₀ m.st.input) (.pin .oU) (by simp) D.d6
          (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E)
          (witL O.lens Q sentU O.holds O.rest k m.st.input (m.st.heard ++ (ds ++ ds')))).1 p
      rw [get_wit2] at p'
      rw [hf] at p'
      exact (pin_iff hN _ _ _ _ _).1 p'))
  · exact (pin_iff hN _ _ _ _ _).2 (SmpOwn.zeta kz (by
      have p := hI (ds ++ ds') (.pin .oOmega) pins_open.2.2.2.1
      have p' := (holds_get O.lens Q O.N (O.Mg₀ m.st.input) (.pin .oOmega) (by simp) D.d6
          (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E)
          (witL O.lens Q sentU O.holds O.rest k m.st.input (m.st.heard ++ (ds ++ ds')))).1 p
      rw [get_wit2] at p'
      rw [hf] at p'
      exact (pin_iff hN _ _ _ _ _).1 p'))

/-- **«Exchange» at "SPLIT"**, under Plan2, hN and ShowsMu: the two constraints that it lays; o_sp's
pin, from the pin in front. ShowsMu is not shown here; from other premises: Honest/K14/MuPaid.lean,
Honest/K14/Holds2.lean. -/
theorem exchange8 (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (hMu : ShowsMu Q sentU O Cl) :
    Exchange (letters2 Q sentU O Cl).thread 8 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  revert hi
  revert i
  intro (i : ItemS) hi
  have hA' := hA
  obtain ⟨hH, -, -, hI, hM, -, hV⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  have hMv := hS.1
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hs⟩ := hS
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have ehh : y.2.st.heard ++ ds' = m.st.heard ++ (ds ++ ds') := by rw [eh, List.append_assoc]
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  obtain ⟨W, D, hseen, hrs, -, e1, e2, u⟩ := FlatAt.member8 (B := B) F hQ.facts.goes
    hQ.facts.two 0 _ s s' _ _ c₀ cols cols.length blk hfold hblk hs
  subst e2
  subst e1
  have S := hQ.pub m.st.input.key
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7] := hseen
  have h0 : m.st.heard = [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7].map (·.drawn) := by
    rw [← hsm, hseen']
  have hh : firstRv (y.2.st.heard ++ ds') = rvOf W.R1.drawn := by rw [eh, h0]; rfl
  have hf : firstRv (m.st.heard ++ (ds ++ ds')) = rvOf W.R1.drawn := by rw [h0]; rfl
  have hm1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [h0]; rfl
  have hne : i ≠ .pinT := by
    rintro rfl
    exact absurd (show ItemS.pinT ∈ (SharedRows.rows true 8).owes from hi) (by decide)
  refine (holds_get O.lens Q O.N (O.Mg₀ y.2.st.input) i hne D.d8
    (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) (E.add y.1))
    (witL O.lens Q sentU O.holds O.rest k y.2.st.input (y.2.st.heard ++ ds'))).2 ?_
  rw [get_wit2]
  rw [ei, hh, ehh]
  have hsh := hMu blk k _ m E ds y cols _ hblk hd hA' hMv hrs
  have hm7 : m.st.heard.getD 6 noChallenge = W.R7.drawn := by rw [h0]; rfl
  rw [hm1, hm7] at hsh
  have hi' : i ∈ ([.row .foldU, .row .foldOmega, .pin .oSp] : List ItemS) := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl
  · exact (Steps.foldU_behind8 S u (H := holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds'))) hsh).1
  · exact (Steps.foldOmega_behind8 S u
      (H := holdsAt O k m.st.input (m.st.heard ++ (ds ++ ds'))) hsh).1
  · exact (pin_iff hN _ _ _ _ _).2 (SmpOwn.quiet (by
      have hl := F.at8 hblk
      rw [hl.step] at hs
      exact (quiet_each Q hQ.facts.two B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _ _).2.2.2
        ((step_ok_iff 0 B.b8 _ _ _ _ _).1 hs).2.2.2) (by
      have p := hI (ds ++ ds') (.pin .oSp) pins_open.2.2.2.2
      have p' := (holds_get O.lens Q O.N (O.Mg₀ m.st.input) (.pin .oSp) (by simp) D.d7
          (Env.strs Q.item (srcAt 1 O.n₁ O.n₂) E)
          (witL O.lens Q sentU O.holds O.rest k m.st.input (m.st.heard ++ (ds ++ ds')))).1 p
      rw [get_wit2] at p'
      rw [hf] at p'
      exact (pin_iff hN _ _ _ _ _).1 p'))

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.words2_rv
#print axioms ProofFile.Honest.K14.holds_get
#print axioms ProofFile.Honest.K14.get_wit2
#print axioms ProofFile.Honest.K14.pin_iff
#print axioms ProofFile.Honest.K14.pins_open
#print axioms ProofFile.Honest.K14.exchange1
#print axioms ProofFile.Honest.K14.exchange2
#print axioms ProofFile.Honest.K14.exchange3
#print axioms ProofFile.Honest.K14.exchange4
#print axioms ProofFile.Honest.K14.exchange5
#print axioms ProofFile.Honest.K14.exchange6
#print axioms ProofFile.Honest.K14.exchange7
#print axioms ProofFile.Honest.K14.exchange8
