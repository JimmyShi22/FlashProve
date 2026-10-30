-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/AskWipe.lean: what the closing of a segment (K10) hands to a fold (`closeAsk`,
Honest/K10/Job.lean) is one at a statement and at that statement with every row's target set to zero (`wipeSt`,
Honest/K10/StAtZero.lean). Ten definitions with code; the rest are theorems.

What is proved.
  `closeAsk_eq`      `closeAsk` is a function (`askOf`) of the place's public numbers, the challenge of "BAT", the run
                 that is spent and two values: what the job's `stAt` yields and what its `rows` yields
  `askOf_wipe`       that function is one at (S, g) and at (S wiped, g): whole, refusals and their words among them
  `askOf_congr`      it is one at two values of `stAt` that both refuse (with whatever words), or that are (S, g) and
                 (S', g) with S wiped = S' wiped
  `closeAsk_congr`   so `closeAsk` is one at two jobs that differ in `stAt` alone, where the two fields' values are such
  `closeAsk_wiped`   and at a job and that job with its field's statement wiped (`CloseJob.wiped`)
On the way: `rowsFit_wipe`, `wordAt_wipe`, `rowsAt_wipe`, `closeMain_wipe`, `closeMask_wipe`, `closeKept_wipe`: this
folder's own readers of a statement or a group are one at both.

By what. `closeAsk`'s text is cut into pieces (`askTail`, `askBat`, `askSt`, `askOf`: its own lines, with the job's two
values as letters), and the last piece is written a second time as plain choices (`askData`, `askLast`, `askGroup`,
`askFit`; `askTail_eq`). The statement is read four ways: by the verifier's text of the batching (`bat_wipe`,
Honest/K10/BatWipe.lean: one refusal, or rows that are one but for their targets, one layout, and the statement behind,
wiped); for the group; by `rowsFit`; and, behind the batching, by the laying of the tables. Of the batched row its two
vectors of coefficients and its kept forms are taken, which the wiping leaves.

Limits. The pieces are scaffolding for these proofs: no part calls them. Nothing is said of a job's `stAt` or `rows`:
both are letters. Nothing is said of two statements that differ in more than targets. No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Job
import Johnson.Desc.ProofFile.Honest.K10.StAtZero
import Johnson.Desc.ProofFile.Honest.K10.BatWipe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE Statement GroupRow GroupLayout)
open VerifiableInference.Desc.First.Close (Par entries bat)

/-! ## 1 This folder's own readers of a statement -/

/-- The public test on the group's rows is one at both statements. -/
theorem rowsFit_wipe (S : Statement) (G : OnBytes.Group) (R : GroupData) :
    rowsFit (wipeSt S) (wipeGr G) R = rowsFit S G R := by
  unfold rowsFit
  simp only [shape_at_wipe]
  rfl

/-- An entry of an oracle message's own table is one at both statements. -/
theorem wordAt_wipe (S : Statement) : wordAt (wipeSt S) = wordAt S := by
  funext ell at_ o part i
  unfold wordAt
  rw [rowBits_wipe, realRows_wipe]

/-- An entry of a member's rows reads of the group its list of members alone. -/
theorem rowsAt_wipe (G : OnBytes.Group) : rowsAt (wipeGr G) = rowsAt G := by
  funext R f o b p
  unfold rowsAt
  rfl

/-- The laying of the group's main table is one at both statements. -/
theorem closeMain_wipe (S : Statement) : closeMain (wipeSt S) = closeMain S := by
  funext L w
  unfold closeMain
  rw [wipeSt_size, mainWeight_wipe, mainBack_wipe]

/-- The laying of the group's mask table is one at both statements. -/
theorem closeMask_wipe (S : Statement) : closeMask (wipeSt S) = closeMask S := by
  funext L w
  unfold closeMask
  rw [wipeSt_size, maskWeight_wipe, maskBack_wipe]

/-- The value of the kept forms is one at both statements. -/
theorem closeKept_wipe (S : Statement) : closeKept (wipeSt S) = closeKept S := by
  funext Ks w
  unfold closeKept
  rw [tableSize_wipe]

/-! ## 2 `closeAsk`'s last lines, as plain choices -/

/-- The data, of the group, its rows, the batched row's three pieces, the layout and the statement behind. -/
def askData (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (G : OnBytes.Group) (R : GroupData) (c : OnBytes.Form)
    (d : Array E) (kept : Array OnBytes.KeptForm) (L : GroupLayout) (S1 : Statement) : FoldAsk :=
  { k := pub.par.k, h := pub.par.h
    c := c.writeOut (L.k + L.logEll), d := d
    m := closeMain S1 L fun o => wordAt S1 R.base.ell (rowsAt G R (·.main)) o .main
    mu := closeMask S1 L fun o => wordAt S1 R.zk.ell (rowsAt G R (·.mask)) o .mask
    keptV := closeKept S1 kept fun o => wordAt S1 R.base.ell (rowsAt G R (·.main)) o .main
    w := u }

/-- The test `rowsFit`, then the data. -/
def askLast (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (S : Statement) (G : OnBytes.Group) (R : GroupData)
    (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm) (L : GroupLayout) (S1 : Statement) :
    Except String (Option FoldAsk) :=
  if !rowsFit S G R then .error "K10: the group's rows do not fit the statement's group"
  else .ok (some (askData pub u G R c d kept L S1))

/-- The group is there, the rows are there, then `askLast`. -/
def askGroup (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData) (S : Statement)
    (G? : Option OnBytes.Group) (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm) (L : GroupLayout)
    (S1 : Statement) : Except String (Option FoldAsk) :=
  match G? with
  | none => .error "K10: no group"
  | some G =>
    match rows with
    | .error e => .error e
    | .ok R => askLast pub u S G R c d kept L S1

/-- The two tests on the layout and on the batched row's size, then `askGroup`. -/
def askFit (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData) (S : Statement)
    (G? : Option OnBytes.Group) (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm) (L : GroupLayout)
    (S1 : Statement) : Except String (Option FoldAsk) :=
  if L.k != pub.par.k || L.h != pub.par.h then .error "K10: the layout's k, h are not the place's"
  else if d.size != 2 ^ (L.h + L.logEllZk) then .error "K10: the batched row does not fit the mask table"
  else askGroup pub u rows S G? c d kept L S1

/-- The data are one at a group and a statement behind and at both wiped. -/
theorem askData_wipe (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (G : OnBytes.Group) (R : GroupData)
    (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm) (L : GroupLayout) (S1 : Statement) :
    askData pub u (wipeGr G) R c d kept L (wipeSt S1) = askData pub u G R c d kept L S1 := by
  unfold askData
  rw [closeMain_wipe, closeMask_wipe, closeKept_wipe, wordAt_wipe, rowsAt_wipe]

/-- So is `askLast`. -/
theorem askLast_wipe (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (S : Statement) (G : OnBytes.Group)
    (R : GroupData) (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm) (L : GroupLayout)
    (S1 : Statement) :
    askLast pub u (wipeSt S) (wipeGr G) R c d kept L (wipeSt S1) = askLast pub u S G R c d kept L S1 := by
  unfold askLast
  rw [rowsFit_wipe, askData_wipe]

/-- So is `askGroup`. -/
theorem askGroup_wipe (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData)
    (S : Statement) (G? : Option OnBytes.Group) (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm)
    (L : GroupLayout) (S1 : Statement) :
    askGroup pub u rows (wipeSt S) (G?.map wipeGr) c d kept L (wipeSt S1) =
      askGroup pub u rows S G? c d kept L S1 := by
  cases G? with
  | none => exact Eq.refl (Except.error "K10: no group")
  | some G =>
    cases rows with
    | error e => exact Eq.refl (Except.error e)
    | ok R => exact askLast_wipe pub u S G R c d kept L S1

/-- So is `askFit`. -/
theorem askFit_wipe (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData)
    (S : Statement) (G? : Option OnBytes.Group) (c : OnBytes.Form) (d : Array E) (kept : Array OnBytes.KeptForm)
    (L : GroupLayout) (S1 : Statement) :
    askFit pub u rows (wipeSt S) (G?.map wipeGr) c d kept L (wipeSt S1) =
      askFit pub u rows S G? c d kept L S1 := by
  unfold askFit
  rw [askGroup_wipe]

/-! ## 3 `closeAsk`'s text, cut into pieces -/

/-- `closeAsk`'s lines behind the batching, to the letter; rows: what the job's `rows` yields. -/
def askTail (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData) (S : Statement)
    (g : Nat) : GroupRow × GroupLayout × Statement → Except String (Option FoldAsk)
  | (row, L, S1) => do
    if L.k != pub.par.k || L.h != pub.par.h then
      throw "K10: the layout's k, h are not the place's"
    if row.d.size != 2 ^ (L.h + L.logEllZk) then
      throw "K10: the batched row does not fit the mask table"
    let G ← match S.groups[g]? with
      | some G => pure G
      | none => throw "K10: no group"
    let R ← rows
    if !rowsFit S G R then throw "K10: the group's rows do not fit the statement's group"
    let mainW := fun o => wordAt S1 R.base.ell (rowsAt G R (·.main)) o .main
    let maskW := fun o => wordAt S1 R.zk.ell (rowsAt G R (·.mask)) o .mask
    pure (some
      { k := pub.par.k, h := pub.par.h
        c := row.c.writeOut (L.k + L.logEll), d := row.d
        m := closeMain S1 L mainW, mu := closeMask S1 L maskW
        keptV := closeKept S1 row.kept mainW
        w := u })

/-- The batching, then `askTail`. -/
def askBat (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData) (x : Fmt.Drawn)
    (S : Statement) (g : Nat) (eB : Fmt.Entry) : Except String (Option FoldAsk) :=
  ((bat S g eB ⟨[], x⟩).mapError fun e => "K10: the verifier's batching refuses: " ++ e) >>=
    askTail pub u rows S g

/-- Nothing where the statement is not at hand; else `askBat`. st: what the job's `stAt` yields. -/
def askSt (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData) (x : Fmt.Drawn)
    (eB : Fmt.Entry) (st : Except String (Statement × Nat)) : Except String (Option FoldAsk) :=
  match st with
  | .error _ => pure none
  | .ok (S, g) => askBat pub u rows x S g eB

/-- **`closeAsk`, of the values of the job's two fields.** -/
def askOf (pub : ClosePub) (rows : Except String GroupData) (x : Fmt.Drawn) (u : Fin (2 * pub.par.k + 1) → E)
    (st : Except String (Statement × Nat)) : Except String (Option FoldAsk) :=
  match (entries pub.par).head? with
  | some eB => askSt pub u rows x eB st
  | none => .error "K10: no entry"

/-- **`closeAsk` reads of the job its public numbers and the values of its two fields.** -/
theorem closeAsk_eq {W : Type} (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    closeAsk J w seen front x u ca = askOf J.pub (J.rows w front ca) x u (J.stAt w seen front) := by
  unfold closeAsk askOf
  cases (entries J.pub.par).head? with
  | none => rfl
  | some eB => rfl

/-- The lines behind the batching are the plain choices. -/
theorem askTail_eq (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData)
    (S : Statement) (g : Nat) (row : GroupRow) (L : GroupLayout) (S1 : Statement) :
    askTail pub u rows S g (row, L, S1) = askFit pub u rows S (S.groups[g]?) row.c row.d row.kept L S1 := by
  unfold askTail
  cases S.groups[g]? with
  | none => rfl
  | some G =>
    cases rows with
    | error e => rfl
    | ok R => rfl

/-- The lines behind the batching are one at a statement, a batched row and a statement behind, and at the statement
wiped, a row that is the same but for its target, and the statement behind wiped. -/
theorem askTail_wipe (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData)
    (S : Statement) (g : Nat) {row row' : GroupRow} (L : GroupLayout) (S1 : Statement)
    (h : wipeG row' = wipeG row) :
    askTail pub u rows (wipeSt S) g (row', L, wipeSt S1) = askTail pub u rows S g (row, L, S1) := by
  have hc : row'.c = row.c := (congrArg (fun r : GroupRow => r.c) h :)
  have hd : row'.d = row.d := (congrArg (fun r : GroupRow => r.d) h :)
  have hk : row'.kept = row.kept := (congrArg (fun r : GroupRow => r.kept) h :)
  rw [askTail_eq, askTail_eq, wipeSt_group_at, hc, hd, hk]
  exact askFit_wipe pub u rows S _ row.c row.d row.kept L S1

/-- The batching and the lines behind it are one at both statements. -/
theorem askBat_wipe (pub : ClosePub) (u : Fin (2 * pub.par.k + 1) → E) (rows : Except String GroupData)
    (x : Fmt.Drawn) (S : Statement) (g : Nat) (eB : Fmt.Entry) :
    askBat pub u rows x (wipeSt S) g eB = askBat pub u rows x S g eB := by
  have hb := bat_wipe S g eB ⟨[], x⟩
  unfold askBat
  cases h1 : bat S g eB ⟨[], x⟩ with
  | error m =>
    cases h2 : bat (wipeSt S) g eB ⟨[], x⟩ with
    | error m' =>
      rw [h1, h2] at hb
      have hm : m' = m := Except.error.inj hb
      rw [hm]
      exact Eq.refl (Except.error ("K10: the verifier's batching refuses: " ++ m))
    | ok y' =>
      rw [h1, h2] at hb
      cases hb
  | ok y =>
    cases h2 : bat (wipeSt S) g eB ⟨[], x⟩ with
    | error m' =>
      rw [h1, h2] at hb
      cases hb
    | ok y' =>
      rw [h1, h2] at hb
      obtain ⟨row, L, S1⟩ := y
      obtain ⟨row', L', S1'⟩ := y'
      have e : (wipeG row', L', S1') = (wipeG row, L, wipeSt S1) := Except.ok.inj hb
      have e1 : wipeG row' = wipeG row := (congrArg (fun z : GroupRow × GroupLayout × Statement => z.1) e :)
      have e2 : L' = L := (congrArg (fun z : GroupRow × GroupLayout × Statement => z.2.1) e :)
      have e3 : S1' = wipeSt S1 := (congrArg (fun z : GroupRow × GroupLayout × Statement => z.2.2) e :)
      rw [e2, e3]
      exact askTail_wipe pub u rows S g L S1 e1

/-! ## 4 The laws -/

/-- A statement and a group's number, with the statement wiped. -/
def wipeAt (z : Statement × Nat) : Statement × Nat := (wipeSt z.1, z.2)

/-- **`askOf` is one at a statement and at that statement wiped.** -/
theorem askOf_wipe (pub : ClosePub) (rows : Except String GroupData) (x : Fmt.Drawn)
    (u : Fin (2 * pub.par.k + 1) → E) (S : Statement) (g : Nat) :
    askOf pub rows x u (.ok (wipeSt S, g)) = askOf pub rows x u (.ok (S, g)) := by
  unfold askOf
  cases (entries pub.par).head? with
  | none => exact Eq.refl (Except.error "K10: no entry")
  | some eB => exact askBat_wipe pub u rows x S g eB

/-- `askOf` does not read the word of a refusal of `stAt`. -/
theorem askOf_error (pub : ClosePub) (rows : Except String GroupData) (x : Fmt.Drawn)
    (u : Fin (2 * pub.par.k + 1) → E) (a b : String) :
    askOf pub rows x u (.error a) = askOf pub rows x u (.error b) := by
  unfold askOf
  cases (entries pub.par).head? <;> rfl

/-- **`askOf` is one at two values that both refuse, or that hold one number and statements that are one once
wiped.** -/
theorem askOf_congr (pub : ClosePub) (rows : Except String GroupData) (x : Fmt.Drawn)
    (u : Fin (2 * pub.par.k + 1) → E) {st st' : Except String (Statement × Nat)}
    (h : st.toOption.map wipeAt = st'.toOption.map wipeAt) :
    askOf pub rows x u st = askOf pub rows x u st' := by
  cases st with
  | error a =>
    cases st' with
    | error b => exact askOf_error pub rows x u a b
    | ok z' => cases h
  | ok z =>
    cases st' with
    | error b => cases h
    | ok z' =>
      obtain ⟨S, g⟩ := z
      obtain ⟨S', g'⟩ := z'
      have e : wipeAt (S, g) = wipeAt (S', g') := Option.some.inj h
      have e1 : wipeSt S = wipeSt S' := (congrArg (fun z : Statement × Nat => z.1) e :)
      have e2 : g = g' := (congrArg (fun z : Statement × Nat => z.2) e :)
      rw [← askOf_wipe pub rows x u S g, ← askOf_wipe pub rows x u S' g', e1, e2]

/-- **`closeAsk` is one at two jobs that differ in `stAt` alone**, where the two fields' values, at the input, what
was shown and the challenges, both refuse or hold one number and statements that are one once wiped. -/
theorem closeAsk_congr {W : Type} (J : CloseJob W)
    (f f' : W → Seen → List Fmt.Drawn → Except String (Statement × Nat)) (w : W) (seen : Seen)
    (front : List Fmt.Drawn) (x : Fmt.Drawn) (u : Fin (2 * J.pub.par.k + 1) → E)
    (ca : CsAll (closeCarries J.pub))
    (h : (f w seen front).toOption.map wipeAt = (f' w seen front).toOption.map wipeAt) :
    closeAsk { J with stAt := f } w seen front x u ca = closeAsk { J with stAt := f' } w seen front x u ca :=
  (closeAsk_eq { J with stAt := f } w seen front x u ca).trans
    ((askOf_congr J.pub (J.rows w front ca) x u h).trans
      (closeAsk_eq { J with stAt := f' } w seen front x u ca).symm)

/-- A job with the statement that its field `stAt` yields wiped. -/
def CloseJob.wiped {W : Type} (J : CloseJob W) : CloseJob W :=
  { J with stAt := fun w s h => (J.stAt w s h).map fun z => (wipeSt z.1, z.2) }

/-- **`closeAsk` is one at a job and at that job wiped.** -/
theorem closeAsk_wiped {W : Type} (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    closeAsk J.wiped w seen front x u ca = closeAsk J w seen front x u ca := by
  refine (closeAsk_eq J.wiped w seen front x u ca).trans (Eq.trans ?_ (closeAsk_eq J w seen front x u ca).symm)
  show askOf J.pub (J.rows w front ca) x u ((J.stAt w seen front).map fun z => (wipeSt z.1, z.2)) =
    askOf J.pub (J.rows w front ca) x u (J.stAt w seen front)
  cases J.stAt w seen front with
  | error a => rfl
  | ok z =>
    obtain ⟨S, g⟩ := z
    exact askOf_wipe J.pub (J.rows w front ca) x u S g

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.rowsFit_wipe
#print axioms ProofFile.Honest.K10.wordAt_wipe
#print axioms ProofFile.Honest.K10.rowsAt_wipe
#print axioms ProofFile.Honest.K10.closeMain_wipe
#print axioms ProofFile.Honest.K10.closeMask_wipe
#print axioms ProofFile.Honest.K10.closeKept_wipe
#print axioms ProofFile.Honest.K10.askData
#print axioms ProofFile.Honest.K10.askLast
#print axioms ProofFile.Honest.K10.askGroup
#print axioms ProofFile.Honest.K10.askFit
#print axioms ProofFile.Honest.K10.askData_wipe
#print axioms ProofFile.Honest.K10.askLast_wipe
#print axioms ProofFile.Honest.K10.askGroup_wipe
#print axioms ProofFile.Honest.K10.askFit_wipe
#print axioms ProofFile.Honest.K10.askTail
#print axioms ProofFile.Honest.K10.askBat
#print axioms ProofFile.Honest.K10.askSt
#print axioms ProofFile.Honest.K10.askOf
#print axioms ProofFile.Honest.K10.closeAsk_eq
#print axioms ProofFile.Honest.K10.askTail_eq
#print axioms ProofFile.Honest.K10.askTail_wipe
#print axioms ProofFile.Honest.K10.askBat_wipe
#print axioms ProofFile.Honest.K10.wipeAt
#print axioms ProofFile.Honest.K10.askOf_wipe
#print axioms ProofFile.Honest.K10.askOf_error
#print axioms ProofFile.Honest.K10.askOf_congr
#print axioms ProofFile.Honest.K10.closeAsk_congr
#print axioms ProofFile.Honest.K10.CloseJob.wiped
#print axioms ProofFile.Honest.K10.closeAsk_wiped
