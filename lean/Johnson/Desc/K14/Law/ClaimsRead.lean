-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/ClaimsRead.lean: WHAT THE SHARED CHAIN's CLAIMS READ OF THE WORDS: the main
tables of o_u and of o_omega, at the numbers that the record notes, AND NOTHING ELSE. Theorems.

WHY. The kind's laws (row3to8, row2to8: Johnson/Desc/K14/Law/Borders.lean, BordersU.lean) have one
reader of the words as a fixed letter. The last chain pays (Dot)'s equation at o_omega's number
(DotOmAt) at another reader: the words at the seat that the shared chain's LAST record's own book
gives the message. Two readers that agree on one message's main table give one claim: so the two
sides meet where the two readers are shown to agree THERE; no law is called again.

  SameMain o m m'   the two words have one main table at the message number o.
  DotOmAt.of_words · DotUAt.of_words · OmegaCol.of_words · FoldAt.of_words · NearAt.of_words ·
  RecAll.of_words   each claim, carried from m to m'.
  claimsB_of_words  **all seven borders' claims at once.**
  SameOmega S d m m'   the two words agree AT THE ENTRIES OF o_omega's MAIN TABLE THAT (Dot) READS:
                    the layout's index of y, for y below the matrix's rows. SameMain asks all
                    entries: TWO READERS OF A WITNESS CAN PART BEYOND A MESSAGE's LENGTH, where
                    nothing pins the witness's table: there SameMain cannot be met, and this can.
  DotOmAt.of_wordsOn   the claim carried under SameOmega alone.
  dotOm_back        **where the two sides meet**: (Dot)'s equation at o_omega's number, had at a
                    LATER record d and at the words m, is the claim at an earlier record d6 and at
                    the words m': given that d keeps d6's codes, point and number of o_omega, and
                    SameOmega of m and m' at d. d: the shared chain's last record, at
                    which the last chain's first block pays; d6: the record behind "SPLIT", at
                    which row3to8's last border stands.
What is not claimed. That any two readers agree. That the two proximity tests and the chain's end,
which stand between "SPLIT" and the last record, keep the three things: their texts' matter. Nothing
on Base (the rows of the two groups hold): that reads the words of every message which a row of a
group names. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame)

/-- The two words have one main table at the message number o. -/
def SameMain (o : Nat) (m m' : Words GE) : Prop := ∀ j, m o .main j = m' o .main j

theorem SameMain.symm {o : Nat} {m m' : Words GE} (h : SameMain o m m') : SameMain o m' m :=
  fun j => (h j).symm

/-- What is read off o_omega. -/
theorem omegaOf_same {l : Lin} {lay : VectorLay} {m m' : Words GE} (h : SameMain l.oOmega m m') :
    omegaOf l lay m = omegaOf l lay m' := funext fun _ => h _

/-- What is read off o_u. -/
theorem uOf_same {l : Lin} {m m' : Words GE} (h : SameMain l.oU.oracle m m') :
    uOf l m = uOf l m' := funext fun _ => h _

theorem DotOmAt.of_words {S : LinShape} {g : Nat → GE} {d : St} {m m' : Words GE} {V : Nat → GE}
    (hO : SameMain d.loc.oOmega m m') (h : DotOmAt S g d m V) : DotOmAt S g d m' V := by
  unfold DotOmAt at h ⊢
  rw [← omegaOf_same hO]
  exact h

theorem DotUAt.of_words {S : LinShape} {g : Nat → GE} {l : Lin} {m m' : Words GE} {V : Nat → GE}
    (hU : SameMain l.oU.oracle m m') (h : DotUAt S g l m V) : DotUAt S g l m' V := by
  unfold DotUAt at h ⊢
  rw [← uOf_same hU]
  exact h

theorem OmegaCol.of_words {S : LinShape} {d : St} {m m' : Words GE}
    (hU : SameMain d.loc.oU.oracle m m') (hO : SameMain d.loc.oOmega m m')
    (h : OmegaCol OnBytes.Model.Reading.gl S d m) : OmegaCol OnBytes.Model.Reading.gl S d m' := by
  unfold OmegaCol at h ⊢
  rw [← omegaOf_same hO, ← uOf_same hU]
  exact h

theorem FoldAt.of_words {S : LinShape} {d : St} {m m' : Words GE}
    (hU : SameMain d.loc.oU.oracle m m') (hO : SameMain d.loc.oOmega m m')
    (h : FoldAt OnBytes.Model.Reading.gl S d m) : FoldAt OnBytes.Model.Reading.gl S d m' := by
  unfold FoldAt at h ⊢
  rw [← omegaOf_same hO, ← uOf_same hU]
  exact h

/-- The function that (loc_x) and (rec_gamma) read. -/
theorem readU_same {d : St} {m m' : Words GE} (hU : SameMain d.loc.oU.oracle m m') :
    (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) =
      fun k => m' d.loc.oU.oracle .main (d.loc.oU.lay.index k) := funext fun _ => hU _

theorem NearAt.of_words {p : Par} {d : St} {m m' : Words GE} {tab : Nat → List UInt64} {e' : Nat}
    (hU : SameMain d.loc.oU.oracle m m') (h : NearAt OnBytes.Model.Reading.gl p d m tab e') :
    NearAt OnBytes.Model.Reading.gl p d m' tab e' := by
  unfold NearAt LocAt at h ⊢
  rw [← readU_same hU]
  exact h

theorem RecAll.of_words {p : Par} {d : St} {m m' : Words GE}
    (hU : SameMain d.loc.oU.oracle m m') (h : RecAll OnBytes.Model.Reading.gl p d m) :
    RecAll OnBytes.Model.Reading.gl p d m' := by
  unfold RecAll RecAt at h ⊢
  rw [← readU_same hU]
  exact h

/-- The two words agree at the entries of o_omega's main table that (Dot) reads. -/
def SameOmega (S : LinShape) (d : St) (m m' : Words GE) : Prop :=
  ∀ y < S.matrixRows, m d.loc.oOmega .main ((linLayOmega d.st.codes S).index y) =
    m' d.loc.oOmega .main ((linLayOmega d.st.codes S).index y)

theorem SameMain.omega {S : LinShape} {d : St} {m m' : Words GE}
    (h : SameMain d.loc.oOmega m m') : SameOmega S d m m' := fun _ _ => h _

/-- The claim, carried under agreement at what it reads. -/
theorem DotOmAt.of_wordsOn {S : LinShape} {g : Nat → GE} {d : St} {m m' : Words GE}
    {V : Nat → GE} (hO : SameOmega S d m m') (h : DotOmAt S g d m V) : DotOmAt S g d m' V := by
  unfold DotOmAt DotEq at h ⊢
  rw [← h]
  refine Finset.sum_congr rfl fun y hy => ?_
  show g y * m' d.loc.oOmega .main _ = g y * m d.loc.oOmega .main _
  rw [hO y (Finset.mem_range.1 hy)]

/-- **Where the two sides meet.** -/
theorem dotOm_back {S : LinShape} {g : Nat → GE} {d6 d : St} {m m' : Words GE} {V : Nat → GE}
    (hc : d.st.codes = d6.st.codes) (hp : d.loc.psiSh = d6.loc.psiSh)
    (ho : d.loc.oOmega = d6.loc.oOmega) (hO : SameOmega S d m m')
    (h : DotOmAt S g d m V) : DotOmAt S g d6 m' V :=
  DotOmAt.of_same hc hp ho (h.of_wordsOn hO)

/-- **All seven borders' claims at once.** -/
theorem claimsB_of_words {F : Frame} (p : Par) (e' : Nat) (g : Nat → GE) (i : Nat)
    (a : St × F.E.Str) {m m' : Words GE} (V : Nat → GE)
    (hU : SameMain a.1.loc.oU.oracle m m') (hO : SameMain a.1.loc.oOmega m m')
    (h : claimsB p e' g i a m V) : claimsB p e' g i a m' V := by
  match i, h with
  | 0, h => exact ⟨h.1.of_words hU, h.2.1.of_words hU, h.2.2.of_words hU⟩
  | 1, h => exact ⟨h.1.of_words hU, h.2.of_words hU⟩
  | 2, h => exact DotUAt.of_words hU h
  | 3, h => exact ⟨h.1.of_words hU hO, h.2.of_words hO⟩
  | 4, h => exact ⟨h.1.of_words hU hO, h.2.of_words hO⟩
  | 5, h => exact ⟨h.1.of_words hU hO, h.2.of_words hO⟩
  | _ + 6, h => exact DotOmAt.of_words hO h

end Desc.K14.Law
