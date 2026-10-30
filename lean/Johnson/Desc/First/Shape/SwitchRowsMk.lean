-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchRowsMk.lean: THE MAKES OF A CODE SWITCH's ROWS (Own.swRows,
Johnson/Desc/Own/SwitchRows.lean): the carried claim, the kept members' old sample rows, and a set
of generator rows for each drawn position. General laws; nothing is evaluated.

THE TOP LAW: **`swRows_mk`**: where the maker returns rows: swRowsS (stSh S) (formsOf S) (singleSh
old) T g anew pos.draws.size = some (rows.map rowMk): THE MAKES ARE A FUNCTION OF the statement's
shape, its rows' makes, the carried single rows' make, the target, the new messages' numbers AND
THE NUMBER OF DRAWN POSITIONS: not of the positions, of a symbol read, or of any other value.

  1 `rowMk_addForm`, `rowMk_addUnit`, `rowMk_addRun`.
  2 `switchLiftS` | `switchLift_mk`, `addRestES` | `addRestE_mk`, `addRestFS` | `addRestF_mk`,
    `addKeptS` | `addKept_mk`.
  3 `foldl_mk`, `swFormOnS` | `swFormOn_mk`: a sample row that reads one main table, as a form.
  4 `shapeAtS`, `rowBitsS`, `switchKeptS`, `switchPartsS` | `switchParts_sh`, `swFrameS` |
    **`swFrame_sh`**: the switch's frame is a function of shapes (an equation; both sides may
    refuse).
  5 `swCarriedS` | `swCarried_mk`. 6 `mapM_mk`, `swOldSamplesS` | `swOldSamples_mk`: equations too.
  7 `onMessageS`, `onBoxS`, `gensS` | **`gens_mk`**: the generator rows' makes do not hang on the
    position.
  8 `mapM_all`, `swRowsS`, `swRows_mk`.

It calls tableBitsS (Johnson/Desc/Ground/Shape/More.lean).

Limits. swRows_mk is one way (from the maker's return): the maker asks one thing more than swRowsS:
as many symbols as positions that differ times rows, and each draw among these. Nothing is said of
a coefficient. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.SendP
import Johnson.Desc.Own.SwitchRows
import Johnson.Desc.Ground.Shape.More
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc

/-! ## 1 Three of a row's four ways to grow (the fourth, rowMk_add, is SendForms.lean's) -/

theorem rowMk_addForm (r : OnBytes.Row) (o : Nat) (c : Form) :
    rowMk (r.addForm o c) = { rowMk r with forms := (rowMk r).forms ++ [⟨o, formSh c⟩] } := by
  unfold OnBytes.Row.addForm rowMk
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem rowMk_addUnit (r : OnBytes.Row) (o : Nat) (part : Part) (i : Nat) (c : E) :
    rowMk (r.addUnit o part i c) = { rowMk r with units := (rowMk r).units ++ [⟨o, part, i⟩] } := by
  unfold OnBytes.Row.addUnit rowMk
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem rowMk_addRun (r : OnBytes.Row) (o : Nat) (part : Part) (first step : Nat) (c : Coeffs) :
    rowMk (r.addRun o part first step c) =
      { rowMk r with runs := (rowMk r).runs ++ [⟨o, part, first, step, c.size⟩] } := by
  unfold OnBytes.Row.addRun rowMk
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

/-! ## 2 The switch's own operations -/

def switchLiftS (c : FormSh) (vars : Nat) (cut : RowCut) (tableRowBits tableBits : Nat) : FormSh :=
  (c.insertChoice cut.bits (tableRowBits - cut.bits) (cut.firstRow / 2 ^ cut.bits)).insertChoice
    (vars + (tableRowBits - cut.bits)) (tableBits - (vars + (tableRowBits - cut.bits))) 0

theorem switchLift_mk (c : Form) (vars : Nat) (cut : RowCut) (trb tb : Nat) :
    formSh (switchLift c vars cut trb tb) = switchLiftS (formSh c) vars cut trb tb := by
  unfold switchLift switchLiftS
  dsimp only
  rw [formSh_insertChoice, formSh_insertChoice]

/-- switchAddRestE on makes. n: the vector's size. -/
def addRestES (row : RowMk) (g : Nat) (part : Part) (pieces : List SwitchPiece) (n : Nat) :
    RowMk :=
  { row with runs := row.runs ++ pieces.map fun p =>
      ⟨g, part, p.first, p.step, min p.stop n - p.start⟩ }

theorem addRestE_mk (g : Nat) (part : Part) (coeff : Array E) :
    ∀ (pieces : List SwitchPiece) (row : OnBytes.Row),
      rowMk (switchAddRestE row g part pieces coeff) =
        addRestES (rowMk row) g part pieces coeff.size
  | [], row => by
    unfold switchAddRestE addRestES
    simp
  | p :: pieces, row => by
    have e : switchAddRestE row g part (p :: pieces) coeff =
        switchAddRestE (row.addRun g part p.first p.step (.own (coeff.extract p.start p.stop)))
          g part pieces coeff := rfl
    rw [e, addRestE_mk g part coeff pieces, rowMk_addRun]
    unfold addRestES
    simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append, Coeffs.size,
      Array.size_extract]

/-- switchAddRestF on makes. -/
def addRestFS (row : RowMk) (g : Nat) (part : Part) (pieces : List SwitchPiece) : RowMk :=
  { row with runs := row.runs ++ pieces.map fun p =>
      ⟨g, part, p.first, p.step, p.stop - p.start⟩ }

theorem addRestF_mk (g : Nat) (part : Part) (coeff : Array F) :
    ∀ (pieces : List SwitchPiece) (row : OnBytes.Row),
      rowMk (switchAddRestF row g part pieces coeff) = addRestFS (rowMk row) g part pieces
  | [], row => by
    unfold switchAddRestF addRestFS
    simp
  | p :: pieces, row => by
    have e : switchAddRestF row g part (p :: pieces) coeff =
        switchAddRestF (row.addRun g part p.first p.step
          (.stretch coeff p.start (p.stop - p.start))) g part pieces coeff := rfl
    rw [e, addRestF_mk g part coeff pieces, rowMk_addRun]
    unfold addRestFS
    simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append, Coeffs.size]

/-- switchAddKept on makes. -/
def addKeptS (row : RowMk) (pad : List PadPlace) (anew g : Nat) (restPart : Part)
    (places : SwitchPlaces) (oldPadAt : Nat) (c : FormSh) : RowMk :=
  { row with
    forms := row.forms ++ [⟨anew, c⟩]
    units := row.units ++ pad.zipIdx.flatMap fun p =>
      [⟨anew, .main, p.1.index⟩, ⟨g, restPart, places.get (oldPadAt + p.2)⟩] }

theorem addKept_loop (anew g : Nat) (restPart : Part) (places : SwitchPlaces) (oldPadAt : Nat)
    (c : Form) : ∀ (l : List (PadPlace × Nat)) (r : OnBytes.Row),
      rowMk (l.foldl (fun r p =>
        (r.addUnit anew .main p.1.index (negE (c.entry p.1.index))).addUnit g restPart
          (places.get (oldPadAt + p.2)) (c.entry p.1.index)) r) =
        { rowMk r with units := (rowMk r).units ++ l.flatMap fun p =>
            [⟨anew, .main, p.1.index⟩, ⟨g, restPart, places.get (oldPadAt + p.2)⟩] }
  | [], r => by simp
  | p :: l, r => by
    rw [List.foldl_cons, addKept_loop anew g restPart places oldPadAt c l, rowMk_addUnit,
      rowMk_addUnit]
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem addKept_mk (row : OnBytes.Row) (pad : List PadPlace) (anew g : Nat) (restPart : Part)
    (places : SwitchPlaces) (oldPadAt : Nat) (c : Form) :
    rowMk (switchAddKept row pad anew g restPart places oldPadAt c) =
      addKeptS (rowMk row) pad anew g restPart places oldPadAt (formSh c) := by
  unfold switchAddKept addKeptS
  rw [addKept_loop, rowMk_addForm]

/-! ## 3 A sample row that reads one main table, as a form -/

theorem foldl_mk {α β ι κ : Type} (sh : α → β) (mk : ι → κ) (f : α → ι → α) (fS : β → κ → β)
    (h : ∀ a i, sh (f a i) = fS (sh a) (mk i)) : ∀ (l : List ι) (a : α),
      sh (l.foldl f a) = (l.map mk).foldl fS (sh a)
  | [], _ => rfl
  | i :: l, a => by
    rw [List.foldl_cons, foldl_mk sh mk f fS h l, h, List.map_cons, List.foldl_cons]

/-- Own.swFormOn on makes. -/
def swFormOnS (o : Nat) (row : RowMk) : Option FormSh :=
  if (row.terms.all fun t => t.oracle == o && t.part == .main) &&
      (row.units.all fun u => u.oracle == o && u.part == .main) &&
      (row.runs.all fun r => r.oracle == o && r.part == .main) &&
      row.forms.all fun f => f.oracle == o then
    some (row.forms.foldl (fun c f => c.plus f.c)
      (row.runs.foldl (fun c r =>
          (List.range r.size).foldl (fun c j => c.addEntry (r.first + r.step * j)) c)
        (row.units.foldl (fun c u => c.addEntry u.index)
          (row.terms.foldl (fun c t => c.add t.v) ⟨[], []⟩))))
  else none

theorem swFormOn_mk (o : Nat) (row : OnBytes.Row) :
    (Own.swFormOn o row).map formSh = swFormOnS o (rowMk row) := by
  have hg : ((row.terms.all fun t => t.oracle == o && t.part == .main) &&
      (row.units.all fun u => u.oracle == o && u.part == .main) &&
      (row.runs.all fun r => r.oracle == o && r.part == .main) &&
      row.forms.all fun f => f.oracle == o) =
      (((rowMk row).terms.all fun t => t.oracle == o && t.part == .main) &&
      ((rowMk row).units.all fun u => u.oracle == o && u.part == .main) &&
      ((rowMk row).runs.all fun r => r.oracle == o && r.part == .main) &&
      (rowMk row).forms.all fun f => f.oracle == o) := by
    unfold rowMk
    simp only [List.all_map, ← Array.all_toList]
    rfl
  unfold Own.swFormOn swFormOnS
  rw [hg]
  split
  · show some (formSh _) = some _
    congr 1
    simp only [← Array.foldl_toList]
    rw [foldl_mk formSh mainMk (fun (c : Form) f => c.plus f.c) (fun c f => c.plus f.c)
        (fun a f => formSh_plus a f.c),
      foldl_mk formSh runMk
        (fun (c : Form) r => (List.range r.coeffs.size).foldl
          (fun c j => c.addEntry (r.first + r.step * j) (r.coeffs.get j)) c)
        (fun c r => (List.range r.size).foldl (fun c j => c.addEntry (r.first + r.step * j)) c)
        (fun a r => by
          rw [foldl_mk formSh id
            (fun (c : Form) j => c.addEntry (r.first + r.step * j) (r.coeffs.get j))
            (fun c j => c.addEntry (r.first + r.step * j)) (fun _ _ => rfl), List.map_id]
          rfl),
      foldl_mk formSh unitMk (fun (c : Form) u => c.addEntry u.index u.coeff)
        (fun c u => c.addEntry u.index) (fun _ _ => rfl),
      foldl_mk formSh termMk (fun (c : Form) t => c.add t.v) (fun c t => c.add t.v)
        (fun _ _ => rfl)]
    rfl
  · rfl

/-! ## 4 The switch's frame, off shapes -/

open VerifiableInference.Desc.Ground.Sh (StSh stSh orc_get)

def shapeAtS (a : StSh) (o : Nat) : OracleShape := ((a.oracles[o]?).map (·.shape)).getD default

theorem shapeAt_sh (S : Statement) (o : Nat) :
    (S.oracles.getD o default).shape = shapeAtS (stSh S) o := by
  unfold shapeAtS
  rw [orc_get, Array.getD_eq_getD_getElem?]
  cases S.oracles[o]? <;> rfl

def rowBitsS (a : StSh) (o : Nat) (part : Part) : Nat :=
  match a.oracles[o]? with
  | some x => ceilLog2 (x.shape.rows part)
  | none => 0

theorem rowBits_sh (S : Statement) (o : Nat) (part : Part) :
    S.rowBits o part = rowBitsS (stSh S) o part := by
  unfold Statement.rowBits rowBitsS
  rw [orc_get]
  cases S.oracles[o]? <;> rfl

def switchKeptS (old : SingleSh) : Array Nat :=
  ((old.layout.members.zip old.layout.kept).filter (·.2)).map (·.1)

def switchPartsS (a : StSh) (old : SingleSh) : SwitchParts :=
  let code := a.codes.base.getD old.code default
  let zk := a.codes.mask.getD old.maskCode default
  let x := old.masks * zk.ell
  let b := x + code.r
  let c := b + old.keptRows * code.r
  let d := c + old.masks * zk.r
  let pads := (switchKeptS old).foldl
    (fun (s : Array Nat × Nat) o =>
      (s.1.push s.2, s.2 + (padPlaces a.codes (shapeAtS a o)).length)) (#[], d)
  { maskAt := startsFrom 0 zk.ell old.masks
    mainTailAt := x
    keptTailAt := startsFrom b code.r old.keptRows
    maskTailAt := startsFrom c zk.r old.masks
    oldPadAt := pads.1
    length := pads.2 }

theorem switchParts_sh (S : Statement) (old : SingleRows) :
    switchParts S old = switchPartsS (stSh S) (singleSh old) := by
  unfold switchParts switchPartsS padOf
  simp only [shapeAt_sh]
  rfl

/-- Own.swFrame off shapes. -/
def swFrameS (a : StSh) (old : SingleSh) (T : SwitchTarget) (g : Nat) (anew : Array Nat) :
    Option SwitchFrame :=
  (a.codes.base[old.code]?).bind fun code =>
  (a.codes.mask[old.maskCode]?).bind fun zk =>
  (a.codes.base[T.shape.code]?).bind fun newCode =>
  if anew.size == (switchKeptS old).size then
    let parts := switchPartsS a old
    let places := SwitchPlaces.make a.codes T
    let rowBits := switchRowBits T .main
    let box := (Array.range old.masks).map fun j =>
      if powerOfTwo zk.ell then switchBox places (parts.maskAt.getD j 0) (ceilLog2 zk.ell)
      else none
    some {
      g := g, restPart := T.rest.part, code := code, zk := zk, rowBits := rowBits
      tableBits := rowBits + newCode.logEll
      restBits := Ground.Sh.tableBitsS a g T.rest.part
      mainCut := T.main, places := places, parts := parts
      kept := (List.range (switchKeptS old).size).map fun i =>
        let o := (switchKeptS old).getD i noId
        { old := o, anew := anew.getD i noId, rows := (shapeAtS a o).mainRows,
          rowBits := rowBitsS a o .main, pad := padPlaces a.codes (shapeAtS a o),
          oldPadAt := parts.oldPadAt.getD i 0 }
      mainTail := switchPieces places parts.mainTailAt code.r
      keptTail := parts.keptTailAt.map fun x => switchPieces places x code.r
      box := box
      maskMessage := (Array.range old.masks).map fun j =>
        if (box.getD j none).isSome then [] else switchPieces places (parts.maskAt.getD j 0) zk.ell
      maskTail := parts.maskTailAt.map fun x => switchPieces places x zk.r }
  else none

theorem swFrame_sh (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) :
    Own.swFrame S old T g anew = swFrameS (stSh S) (singleSh old) T g anew := by
  have e1 : (stSh S).codes = S.codes := rfl
  have e2 : (singleSh old).code = old.code := rfl
  have e3 : (singleSh old).maskCode = old.maskCode := rfl
  have e4 : (singleSh old).masks = old.masks := rfl
  have ek : switchKeptS (singleSh old) = switchKept old := rfl
  unfold Own.swFrame swFrameS
  simp only [← switchParts_sh, Ground.Sh.tableBitsS_eq, ← rowBits_sh, ← shapeAt_sh, e1, e2, e3, e4,
    ek]
  cases S.codes.base[old.code]? with
  | none => rfl
  | some code =>
    cases S.codes.mask[old.maskCode]? with
    | none => rfl
    | some zk =>
      cases S.codes.base[T.shape.code]? with
      | none => rfl
      | some newCode =>
        by_cases hc : (anew.size == (switchKept old).size) = true
        · simp only [Option.bind_some, Option.bind_eq_bind, guard, hc, if_true, Option.pure_def]
          rfl
        · simp only [Option.bind_some, Option.bind_eq_bind, guard, hc, Bool.false_eq_true,
            if_false]
          rfl

/-! ## 5 The carried claim -/

def emptyMk : RowMk := ⟨.plain, [], [], [], []⟩

theorem rowMk_empty : rowMk ({} : OnBytes.Row) = emptyMk := rfl

def addKeptW (W : SwitchFrame) (r : RowMk) (k : KeptPlace) (c : FormSh) : RowMk :=
  addKeptS r k.pad k.anew W.g W.restPart W.places k.oldPadAt c

theorem addKeptW_mk (W : SwitchFrame) (r : OnBytes.Row) (k : KeptPlace) (c : Form) :
    rowMk (W.addKept r k c) = addKeptW W (rowMk r) k (formSh c) :=
  addKept_mk r k.pad k.anew W.g W.restPart W.places k.oldPadAt c

theorem d_size (old : SingleRows) (j : Nat) :
    (old.d.getD j #[]).size = (singleSh old).d.getD j 0 := by
  show _ = (old.d.toList.map (·.size)).getD j 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases old.d[j]? <;> rfl

/-- Own.swCarried on makes. -/
def swCarriedS (W : SwitchFrame) (old : SingleSh) : Option RowMk :=
  (old.kept.foldlM (fun r f => (W.kept.find? (·.old == f.1)).map fun k => addKeptW W r k f.2)
    { emptyMk with forms :=
        [⟨W.g, switchLiftS old.c W.code.logEll W.mainCut W.rowBits W.tableBits⟩] }).map fun b =>
    (List.range old.masks).foldl (fun r j =>
      addRestES r W.g W.restPart
        (switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j 0)) (old.d.getD j 0)) b

theorem swCarried_mk (W : SwitchFrame) (old : SingleRows) :
    (Own.swCarried W old).map rowMk = swCarriedS W (singleSh old) := by
  have e : Own.swCarried W old =
      (old.kept.toList.foldlM (fun (r : OnBytes.Row) f =>
          (W.kept.find? (·.old == f.oracle)).bind fun k => some (W.addKept r k f.c))
        (({} : OnBytes.Row).addForm W.g
          (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits))).bind fun b =>
        some { (List.range old.masks).foldl (fun (r : OnBytes.Row) j =>
            switchAddRestE r W.g W.restPart
              (switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j #[]).size)
              (old.d.getD j #[])) b with target := old.target } := by
    unfold Own.swCarried
    simp only [← Array.foldlM_toList]
    rfl
  have h0 : rowMk (({} : OnBytes.Row).addForm W.g
      (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits)) =
      { emptyMk with forms :=
        [⟨W.g, switchLiftS (singleSh old).c W.code.logEll W.mainCut W.rowBits W.tableBits⟩] } := by
    rw [rowMk_addForm, switchLift_mk]
    rfl
  have h1 := foldlM_mk rowMk (fun k : KeptForm => (k.oracle, formSh k.c))
    (fun (r : OnBytes.Row) f =>
      (W.kept.find? (·.old == f.oracle)).bind fun k => some (W.addKept r k f.c))
    (fun r f => (W.kept.find? (·.old == f.1)).map fun k => addKeptW W r k f.2)
    (fun r f => by
      show ((W.kept.find? (·.old == f.oracle)).bind fun k => some (W.addKept r k f.c)).map rowMk =
        (W.kept.find? (·.old == f.oracle)).map fun k => addKeptW W (rowMk r) k (formSh f.c)
      cases W.kept.find? (·.old == f.oracle) with
      | none => rfl
      | some k => exact congrArg some (addKeptW_mk W r k f.c))
    old.kept.toList (({} : OnBytes.Row).addForm W.g
      (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits))
  rw [h0] at h1
  rw [e]
  unfold swCarriedS
  rw [show (singleSh old).kept = old.kept.toList.map fun k => (k.oracle, formSh k.c) from rfl,
    ← h1]
  cases old.kept.toList.foldlM (fun (r : OnBytes.Row) f =>
      (W.kept.find? (·.old == f.oracle)).bind fun k => some (W.addKept r k f.c))
    (({} : OnBytes.Row).addForm W.g
      (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits)) with
  | none => rfl
  | some b =>
    show some (rowMk _) = some _
    congr 1
    rw [rowMk_target, foldl_mk rowMk id
      (fun (r : OnBytes.Row) j => switchAddRestE r W.g W.restPart
        (switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j #[]).size)
        (old.d.getD j #[]))
      (fun r j => addRestES r W.g W.restPart
        (switchPieces W.places (W.parts.maskAt.getD j 0) ((singleSh old).d.getD j 0))
        ((singleSh old).d.getD j 0))
      (fun r j => by rw [addRestE_mk, d_size]; rfl), List.map_id]
    rfl

/-! ## 6 The kept members' old sample rows -/

theorem mapM_mk {α β κ δ : Type} (sh : β → δ) (mk : α → κ) (f : α → Option β)
    (fS : κ → Option δ) (h : ∀ x, (f x).map sh = fS (mk x)) : ∀ (l : List α),
      (l.mapM f).map (·.map sh) = (l.map mk).mapM fS
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, List.map_cons, List.mapM_cons, ← h, ← mapM_mk sh mk f fS h l]
    cases f x with
    | none => rfl
    | some y =>
      cases l.mapM f with
      | none => rfl
      | some ys => rfl

/-- Own.swOldSamples on makes. -/
def swOldSamplesS (F : FormsSh) (W : SwitchFrame) : Option (List RowMk) :=
  (W.kept.mapM fun k => ((F.oracles[k.old]?).getD []).mapM fun sample =>
    (swFormOnS k.old sample).map fun c => addKeptW W emptyMk k c).map List.flatten

theorem samples_at (S : Statement) (o : Nat) :
    (S.oracles.getD o default).sampleRows.toList.map rowMk =
      ((formsOf S).oracles[o]?).getD [] := by
  unfold formsOf
  dsimp only
  rw [List.getElem?_map, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  cases S.oracles[o]? <;> rfl

theorem swOldSamples_mk (S : Statement) (W : SwitchFrame) :
    (Own.swOldSamples S W).map (·.map rowMk) = swOldSamplesS (formsOf S) W := by
  unfold Own.swOldSamples swOldSamplesS
  rw [Option.map_map]
  have h := mapM_mk (List.map rowMk) id
    (fun (k : KeptPlace) => (S.oracles.getD k.old default).sampleRows.toList.mapM
      fun (sample : OnBytes.Row) => (Own.swFormOn k.old sample).bind fun c =>
        some ({ W.addKept {} k c with target := sample.target } : OnBytes.Row))
    (fun k => (((formsOf S).oracles[k.old]?).getD []).mapM fun sample =>
      (swFormOnS k.old sample).map fun c => addKeptW W emptyMk k c)
    (fun k => by
      dsimp only [id]
      rw [← samples_at]
      exact mapM_mk rowMk rowMk _ _ (fun sample => by
        rw [← swFormOn_mk]
        cases Own.swFormOn k.old sample with
        | none => rfl
        | some c =>
          show some (rowMk { W.addKept {} k c with target := sample.target }) = _
          rw [rowMk_target, addKeptW_mk]
          rfl) _) W.kept
  rw [List.map_id] at h
  rw [← h, Option.map_map]
  congr 1
  funext l
  simp [List.map_flatten]

/-! ## 7 The generator rows of one draw -/

theorem tensorSh_product (f : List F) (s : E) :
    tensorSh (Tensor.product f s) = ⟨f.length, [], 0, 0⟩ := by
  unfold Tensor.product tensorSh
  simp

def finishS (r : RowMk) : RowMk := { r with kind := .generator }

theorem rowMk_finish (r : OnBytes.Row) (t : E) :
    rowMk { r with kind := .generator, target := t } = finishS (rowMk r) := by
  cases r
  rfl

def onBoxS (b : SwitchBox) (v : TensorSh) (vars tableBits : Nat) : TensorSh :=
  (v.insertChoice 0 b.shift).insertChoice (b.shift + vars) (tableBits - b.shift - vars)

theorem onBox_mk (b : SwitchBox) (v : Tensor) (vars tableBits : Nat) :
    tensorSh (switchOnBox b v vars tableBits) = onBoxS b (tensorSh v) vars tableBits := by
  unfold switchOnBox onBoxS
  rw [tensorSh_insertChoice, tensorSh_insertChoice]

/-- The make of the generator row's form on a message of the main code. -/
def onMessageS (c : Code) : FormSh := ⟨[⟨min c.logEll c.logDim, [], 0, 0⟩], []⟩

theorem onMessage_mk (c : Code) (x : Nat) :
    formSh (Form.ofTensor (Tensor.product ((generatorAt c x).f.take c.logEll)
      (ofF (generatorAt c x).messageScale))) = onMessageS c := by
  show (⟨[tensorSh _], []⟩ : FormSh) = _
  rw [tensorSh_product, List.length_take]
  show (⟨[⟨min c.logEll (squaresOf c.logDim _).length, [], 0, 0⟩], []⟩ : FormSh) = _
  rw [OnBytes.Slice.length_squaresOf]
  rfl

/-- switchGenerators on makes: it does not hang on the position. -/
def gensS (W : SwitchFrame) (masks : Nat) : List RowMk :=
  finishS (addRestFS
      { emptyMk with forms :=
        [⟨W.g, switchLiftS (onMessageS W.code) W.code.logEll W.mainCut W.rowBits W.tableBits⟩] }
      W.g W.restPart W.mainTail) ::
    (W.kept.foldl (fun (s : List RowMk × Nat) k =>
      (List.range k.rows).foldl (fun (s : List RowMk × Nat) b =>
        (finishS (addRestFS (addKeptW W emptyMk k ((onMessageS W.code).insertChoice 0 k.rowBits b))
          W.g W.restPart (W.keptTail.getD s.2 [])) :: s.1, s.2 + 1)) s) ([], 0)).1.reverse ++
    (List.range masks).map fun j =>
      finishS (addRestFS
        (match W.box.getD j none with
          | some b =>
            { emptyMk with terms := [⟨W.g, W.restPart,
                onBoxS b ⟨min (ceilLog2 W.zk.ell) W.zk.logDim, [], 0, 0⟩ (ceilLog2 W.zk.ell)
                  W.restBits⟩] }
          | none => addRestFS emptyMk W.g W.restPart (W.maskMessage.getD j []))
        W.g W.restPart (W.maskTail.getD j []))

theorem gens_mk (W : SwitchFrame) (old : SingleRows) (x : Nat) (symbols : Nat → E) :
    (switchGenerators W old x symbols).map rowMk = gensS W old.masks := by
  unfold switchGenerators gensS
  dsimp only
  rw [List.map_append, List.map_cons, List.map_reverse, List.map_map]
  congr 1
  · congr 1
    · rw [rowMk_finish, addRestF_mk, rowMk_addForm, switchLift_mk, onMessage_mk]
      rfl
    · congr 1
      have h := foldl_mk (fun s : List OnBytes.Row × Nat => (s.1.map rowMk, s.2)) id
        (fun (s : List OnBytes.Row × Nat) (k : KeptPlace) =>
          (List.range k.rows).foldl (fun (s : List OnBytes.Row × Nat) b =>
            (({ switchAddRestF (W.addKept {} k
                ((Form.ofTensor (Tensor.product ((generatorAt W.code x).f.take W.code.logEll)
                  (ofF (generatorAt W.code x).messageScale))).insertChoice 0 k.rowBits b))
                W.g W.restPart (W.keptTail.getD s.2 []) (generatorTail W.code x) with
                kind := .generator, target := symbols (1 + s.2) } : OnBytes.Row) :: s.1,
              s.2 + 1)) s)
        (fun (s : List RowMk × Nat) k =>
          (List.range k.rows).foldl (fun (s : List RowMk × Nat) b =>
            (finishS (addRestFS
              (addKeptW W emptyMk k ((onMessageS W.code).insertChoice 0 k.rowBits b))
              W.g W.restPart (W.keptTail.getD s.2 [])) :: s.1, s.2 + 1)) s)
        (fun s k => by
          refine (foldl_mk (fun s : List OnBytes.Row × Nat => (s.1.map rowMk, s.2)) id _
            (fun (s : List RowMk × Nat) b =>
              (finishS (addRestFS
                (addKeptW W emptyMk k ((onMessageS W.code).insertChoice 0 k.rowBits b))
                W.g W.restPart (W.keptTail.getD s.2 [])) :: s.1, s.2 + 1))
            (fun s b => by
              dsimp only [id]
              rw [List.map_cons, rowMk_finish, addRestF_mk, addKeptW_mk, formSh_insertChoice,
                onMessage_mk]
              rfl) (List.range k.rows) s).trans ?_
          rw [List.map_id]
          rfl)
        W.kept ([], 0)
      rw [List.map_id] at h
      exact congrArg (·.1) h
  · apply List.map_congr_left
    intro j _
    show rowMk _ = _
    rw [rowMk_finish, addRestF_mk]
    congr 2
    cases W.box.getD j none with
    | none => exact addRestF_mk _ _ _ _ _
    | some b =>
      show rowMk (({} : OnBytes.Row).add W.g W.restPart _) = _
      rw [rowMk_add, onBox_mk, tensorSh_product, List.length_take]
      show _ = ({ emptyMk with terms := [⟨W.g, W.restPart,
        onBoxS b ⟨min (ceilLog2 W.zk.ell) W.zk.logDim, [], 0, 0⟩ (ceilLog2 W.zk.ell)
          W.restBits⟩] } : RowMk)
      rw [show (generatorAt W.zk (shortPosition W.zk.logN x)).f.length = W.zk.logDim from
        OnBytes.Slice.length_squaresOf _ _]
      rfl

/-! ## 8 All rows of a code switch -/

theorem mapM_all {α β : Type} (f : α → Option β) : ∀ (l : List α) (ys : List β),
    l.mapM f = some ys → ys.length = l.length ∧ ∀ y ∈ ys, ∃ x ∈ l, f x = some y
  | [], ys, h => by
    cases h
    exact ⟨rfl, fun _ hy => by cases hy⟩
  | x :: l, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    obtain ⟨e1, e2⟩ := mapM_all f l t ht
    refine ⟨by simp [e1], fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨w, hw, hf⟩ := e2 z hz
      exact ⟨w, List.mem_cons_of_mem _ hw, hf⟩

/-- Own.swRows on makes. draws: how many positions were drawn. -/
def swRowsS (a : StSh) (F : FormsSh) (old : SingleSh) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (draws : Nat) : Option (List RowMk) :=
  (swFrameS a old T g anew).bind fun W =>
  (swCarriedS W old).bind fun carried =>
  (swOldSamplesS F W).map fun samples =>
    carried :: samples ++ (List.replicate draws (gensS W old.masks)).flatten

/-- **The makes of a code switch's rows, where the maker returns**: a function of the statement's
shape, its rows' makes, the carried single rows' make, the target, the new messages' numbers and
the NUMBER of drawn positions. -/
theorem swRows_mk {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {pos : Positions} {y : Array E} {rows : List OnBytes.Row}
    (h : Own.swRows S old T g anew pos y = some rows) :
    swRowsS (stSh S) (formsOf S) (singleSh old) T g anew pos.draws.size =
      some (rows.map rowMk) := by
  unfold Own.swRows at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨carried, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨samples, hs, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨gens, hg, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  unfold swRowsS
  rw [← swFrame_sh, hW]
  show ((swCarriedS W (singleSh old)).bind fun carried => _) = _
  rw [← swCarried_mk, hc]
  show ((swOldSamplesS (formsOf S) W).map fun samples => _) = _
  rw [← swOldSamples_mk, hs]
  show some _ = some _
  congr 1
  show (rowMk carried :: samples.map rowMk) ++ _ = _
  rw [List.map_append, List.map_cons, List.map_flatten]
  congr 2
  symm
  rw [List.eq_replicate_iff]
  obtain ⟨hlen, hall⟩ := mapM_all _ _ _ hg
  refine ⟨by rw [List.length_map, hlen, Array.length_toList], fun b hb => ?_⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hb
  obtain ⟨x, -, hx⟩ := hall l hl
  obtain ⟨i, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  cases hx
  exact gens_mk W old x _

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.gens_mk
#print axioms VerifiableInference.Desc.First.Shape.swRows_mk
#print axioms VerifiableInference.Desc.First.Shape.swCarried_mk
#print axioms VerifiableInference.Desc.First.Shape.swOldSamples_mk
#print axioms VerifiableInference.Desc.First.Shape.swFormOn_mk
#print axioms VerifiableInference.Desc.First.Shape.switchParts_sh
#print axioms VerifiableInference.Desc.First.Shape.swFrame_sh
#print axioms VerifiableInference.Desc.First.Shape.switchLift_mk
#print axioms VerifiableInference.Desc.First.Shape.addRestE_mk
#print axioms VerifiableInference.Desc.First.Shape.addRestF_mk
#print axioms VerifiableInference.Desc.First.Shape.addKept_mk
#print axioms VerifiableInference.Desc.First.Shape.rowMk_empty
