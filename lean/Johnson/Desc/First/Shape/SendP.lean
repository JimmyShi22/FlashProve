-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SendP.lean: THE SHARED SENDING (Desc.Plain.sendP at the description's
ground functions, Johnson/Desc/Ground/Calls.lean:104), FROM ITS OWN YES, SEEN THROUGH THE ONE CORE
AND THROUGH THE ROWS' MAKES. General laws; nothing is evaluated.

What it is for. A code switch sends by this text, not by the kind K1's own decision; so its step on
shapes needs this sending on shapes. From a yes alone: no premise on the plan, the rounds or a
value.

  1 `formMadeS`, **`formMade_mk`**: the make of a sample row as Own.formMade makes it: a function
    of the codes, the message's shape and number, and the NUMBER of the seed's coordinates.
  2 `rowsMkS`, `rowsFor_mk`: one message's sample rows: as many as asked, all of one make.
  3 `loopS`, `loopF`, `sampleLoop_sh`: message by message: admitS on the core; the makes laid at
    the message's number.
  4 `todoL`, `pairsL`, `bitsL`, **`sendPS`** (the receiving, then the sampled messages are
    admitted), **`sendPF`**, `seedsMade_len`, **`sendP_sh`**: sendP groundG p own d sent r₁ r₂ =
    some (ids, …, d') ⊢ sendPS p.firstTree sent (shD d) = some (ids, shD d') ∧ formsOf d'.st =
    sendPF p.firstTree sent (shD d) (formsOf d.st).

It calls recvS, admitS and their laws "carries" (Johnson/Desc/Ground/Shape/Ground.lean).

Limits. One way: that the sending returns where sendPS does is not here: it takes tests on the
rounds and on values (no seed's factor is 0), AND TESTS ON THE FORM THAT sendPS DOES NOT ASK
(Johnson/Desc/Ground/Calls.lean:116-117): at least one new message is to be sampled; their numbers
rise; none of them is sampled already. That a return of sendPS gives the last two is not shown.
Whether a run's coefficients lie inside its table cannot be read off a make (RunMk holds their
number alone). Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Shape.SendForms
import Johnson.Desc.Ground.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open _root_.Desc.Plain (DState GPar groundG sendP sampleLoop rowsFor)
open VerifiableInference.Desc.Ground.Sh (CoreSh shD recvS admitS recv_carries admit_carries modAt)

variable {L : Type}

/-! ## 1 A sample row's make, as the shared sending makes it -/

/-- Own.formMade's make. zlen: the number of the seed's coordinates. -/
def formMadeS (codes : Codes) (s : OracleShape) (o zlen : Nat) : Option RowMk :=
  (Own.padMade codes s).map fun places =>
    { kind := .sample
      terms :=
        (if (Send.cube codes s).hasMain then
          [⟨o, .main, ⟨min (Send.cube codes s).mainBits zlen, [], 0, 0⟩⟩] else []) ++
        (if (Send.cube codes s).hasMask then
          [⟨o, .mask, ⟨min (Send.cube codes s).maskBits zlen, [], 0, 0⟩⟩] else [])
      units := places.map fun p => ⟨o, p.part, p.index⟩
      runs := [], forms := [] }

theorem units_loop2 {ι : Type} (o : Nat) (pt : ι → Part) (ix : ι → Nat) (c : ι → E) :
    ∀ (l : List ι) (r : OnBytes.Row),
      rowMk (l.foldl (fun r x => r.addUnit o (pt x) (ix x) (c x)) r) =
        { rowMk r with units := (rowMk r).units ++ l.map fun x => ⟨o, pt x, ix x⟩ }
  | [], r => by simp
  | x :: l, r => by
    rw [List.foldl_cons, units_loop2 o pt ix c l]
    unfold OnBytes.Row.addUnit rowMk
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]
    rfl

theorem formMade_mk (codes : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed)
    (answer : Nat) :
    (Own.formMade codes s o seed answer).map rowMk = formMadeS codes s o seed.z.length := by
  unfold Own.formMade formMadeS
  cases hp : Own.padMade codes s with
  | none => rfl
  | some places =>
    show some (rowMk _) = some _
    congr 1
    have hu := units_loop2 o (fun p : PadPlace => p.part) (fun p => p.index)
      (fun p => subE (if p.answer == answer then mulE seed.beta p.basis else zeroE)
        ((if p.part == .main then
            Tensor.eq (seed.z.take (Send.cube codes s).mainBits)
              (Send.front seed.z (Send.cube codes s) (Send.cube codes s).mainBits false)
          else Tensor.eq (seed.z.take (Send.cube codes s).maskBits)
              (Send.front seed.z (Send.cube codes s) (Send.cube codes s).maskBits true)).entry
          p.index)) places { kind := .sample }
    revert hu
    generalize List.foldl _ ({ kind := .sample } : OnBytes.Row) places = r₀
    intro hu
    by_cases h1 : (Send.cube codes s).hasMain = true <;>
      by_cases h2 : (Send.cube codes s).hasMask = true
    · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, rowMk_add, rowMk_add, hu, tensorSh_eq,
        tensorSh_eq, List.length_take, List.length_take]
      rfl
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, rowMk_add, hu, tensorSh_eq,
        List.length_take]
      rfl
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, rowMk_add, hu, tensorSh_eq,
        List.length_take]
      rfl
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, hu]
      rfl

/-! ## 2 One message's sample rows -/

/-- The makes of n sample rows of one message. -/
def rowsMkS (codes : Codes) (s : OracleShape) (o v n : Nat) : List RowMk :=
  match formMadeS codes s o v with
  | some mk => List.replicate n mk
  | none => []

theorem rowsMkS_zero (codes : Codes) (s : OracleShape) (o v : Nat) :
    rowsMkS codes s o v 0 = [] := by
  unfold rowsMkS
  split <;> rfl

theorem rowsFor_mk (codes : Codes) (s : OracleShape) (o v : Nat) (seeds : List SampleSeed)
    (hv : ∀ x ∈ seeds, x.z.length = v) :
    ∀ (is : List Nat) (ys : List E) (acc rows : Array OnBytes.Row) (ys' : List E),
      rowsFor codes s o seeds is ys acc = some (rows, ys') →
      rows.size = acc.size + is.length ∧
        rows.toList.map rowMk = acc.toList.map rowMk ++ rowsMkS codes s o v is.length
  | [], ys, acc, rows, ys', h => by
    unfold rowsFor at h
    cases h
    rw [List.length_nil, rowsMkS_zero, List.append_nil]
    exact ⟨rfl, rfl⟩
  | i :: is, [], acc, rows, ys', h => by
    unfold rowsFor at h
    cases h
  | i :: is, y :: ys, acc, rows, ys', h => by
    unfold rowsFor at h
    split at h
    · cases h
    · rename_i seed hs
      split at h
      · cases h
      · rename_i row hr
        obtain ⟨h1, h2⟩ := rowsFor_mk codes s o v seeds hv is ys _ rows ys' h
        have hm : formMadeS codes s o v = some (rowMk row) := by
          rw [← hv seed (List.mem_of_getElem? hs), ← formMade_mk codes s o seed i, hr]
          rfl
        refine ⟨by rw [h1, Array.size_push, List.length_cons]; omega, ?_⟩
        rw [h2, Array.toList_push, List.map_append, List.map_cons, List.map_nil, rowMk_target,
          List.append_assoc]
        congr 1
        unfold rowsMkS
        rw [hm, List.length_cons]
        show [rowMk row] ++ List.replicate is.length (rowMk row) =
          List.replicate (is.length + 1) (rowMk row)
        rw [List.replicate_succ]
        rfl

/-! ## 3 Message by message -/

/-- sampleLoop on the core. -/
def loopS : List (Nat × OracleShape) → CoreSh → Option CoreSh
  | [], a => some a
  | x :: l, a => (admitS a x.1 x.2.answers).bind (loopS l)

/-- sampleLoop on the makes. -/
def loopF (codes : Codes) (v : Nat) (l : List (Nat × OracleShape)) (F : FormsSh) : FormsSh :=
  l.foldl (fun F x => { F with
    oracles := modAt F.oracles x.1 fun _ => rowsMkS codes x.2 x.1 v x.2.answers }) F

theorem sampleLoop_sh (p : GPar) (codes : Codes) (v : Nat) (seeds : List SampleSeed)
    (hv : ∀ x ∈ seeds, x.z.length = v) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      sampleLoop groundG p codes seeds l ys d = some (d', left) →
      loopS l (shD d) = some (shD d') ∧ formsOf d'.st = loopF codes v l (formsOf d.st)
  | [], ys, d, d', left, h => by
    unfold sampleLoop at h
    cases h
    exact ⟨rfl, rfl⟩
  | (o, s) :: l, ys, d, d', left, h => by
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i rows ys' hr
      split at h
      · cases h
      · rename_i d₁ ha
        have ha' : Ground.admitP d o rows = some d₁ := ha
        obtain ⟨h1, h2⟩ := rowsFor_mk codes s o v seeds hv _ _ _ _ _ hr
        obtain ⟨g1, g2⟩ := sampleLoop_sh p codes v seeds hv l ys' d₁ d' left h
        have hsz : rows.size = s.answers := by
          rw [h1]
          simp
        constructor
        · show (admitS (shD d) o s.answers).bind (loopS l) = _
          rw [← hsz, admit_carries d d₁ o rows ha']
          exact g1
        · rw [g2, admit_forms ha', h2]
          unfold loopF
          rw [List.foldl_cons]
          simp

/-! ## 4 The sending -/

/-- The new messages that are sampled. a: the core behind the receiving. -/
def todoL (a : CoreSh) (ids : Array Nat) : List Nat :=
  ids.toList.filter fun o => ((a.st.oracles[o]?).map (·.shape.answers)).getD 0 != 0

def pairsL (a : CoreSh) (todo : List Nat) : List (Nat × OracleShape) :=
  todo.filterMap fun o => (a.st.oracles[o]?).map fun x => (o, x.shape)

/-- The number of a seed's coordinates. -/
def bitsL (codes : Codes) (l : List (Nat × OracleShape)) : Nat :=
  l.foldl (fun b x => max b (Send.cube codes x.2).bits) 0

/-- **The shared sending on the core**: the receiving, then the sampled messages are admitted. -/
def sendPS (ft : Nat) (sent : Array OracleNotice) (a : CoreSh) : Option (Array Nat × CoreSh) :=
  (recvS ft a sent).bind fun x =>
    (loopS (pairsL x.2 (todoL x.2 x.1)) x.2).map fun a2 => (x.1, a2)

/-- **The shared sending on the makes.** a: the core in front. -/
def sendPF (ft : Nat) (sent : Array OracleNotice) (a : CoreSh) (F : FormsSh) : FormsSh :=
  match recvS ft a sent with
  | some x =>
    loopF x.2.st.codes (bitsL x.2.st.codes (pairsL x.2 (todoL x.2 x.1)))
      (pairsL x.2 (todoL x.2 x.1))
      { F with oracles := F.oracles ++ List.replicate sent.size [] }
  | none => F

theorem seedsMade_len (bits : Nat) : ∀ (n : Nat) (l : List E) (seeds : List SampleSeed),
    Own.seedsMade bits n l = some seeds → ∀ x ∈ seeds, x.z.length = bits
  | 0, [], seeds, h, x, hx => by
    unfold Own.seedsMade at h
    cases h
    cases hx
  | 0, _ :: _, seeds, h, x, hx => by
    unfold Own.seedsMade at h
    cases h
  | n + 1, l, seeds, h, x, hx => by
    unfold Own.seedsMade at h
    split at h
    · cases h
    · rename_i beta rest hd
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hx with rfl | hx
      · show (l.take bits).length = bits
        have : (l.drop bits).length = rest.length + 1 := by rw [hd]; rfl
        rw [List.length_drop] at this
        rw [List.length_take]
        omega
      · exact seedsMade_len bits n rest t ht x hx

theorem zip_mapM (S : Statement) : ∀ (todo : List Nat) (shapes : List OracleShape),
    (todo.mapM fun o => (S.oracles[o]?).map (·.shape)) = some shapes →
    todo.zip shapes = todo.filterMap (fun o =>
      ((Ground.Sh.stSh S).oracles[o]?).map fun x => (o, x.shape)) ∧
      todo.length = shapes.length
  | [], shapes, h => by
    cases h
    exact ⟨rfl, rfl⟩
  | o :: todo, shapes, h => by
    rw [List.mapM_cons] at h
    obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hs
    obtain ⟨e1, e2⟩ := zip_mapM S todo l hl
    refine ⟨?_, by simp [e2]⟩
    rw [List.zip_cons_cons, e1, List.filterMap_cons, Ground.Sh.orc_get, hx]
    rfl

theorem foldl_zip {α β γ : Type} (f : γ → β → γ) : ∀ (l : List α) (m : List β) (c : γ),
    l.length = m.length → (l.zip m).foldl (fun b x => f b x.2) c = m.foldl f c
  | [], [], _, _ => rfl
  | _ :: l, y :: m, c, h => by
    rw [List.zip_cons_cons, List.foldl_cons, List.foldl_cons]
    exact foldl_zip f l m _ (by simpa using h)
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- **The shared sending's yes, seen through the core and through the rows' makes.** From the yes
alone. -/
theorem sendP_sh {p : GPar} {own : Bool} {d d' : DState L} {sent : Array OracleNotice}
    {r₁ r₂ : Fmt.RoundView} {ids : Array Nat} {sd an : List E} {took : Nat}
    (h : sendP groundG p own d sent r₁ r₂ = some (ids, sd, an, took, d')) :
    sendPS p.firstTree sent (shD d) = some (ids, shD d') ∧
      formsOf d'.st = sendPF p.firstTree sent (shD d) (formsOf d.st) := by
  unfold sendP at h
  obtain ⟨⟨ids1, d₁⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  obtain ⟨shapes, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨seeds, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨an1, h4, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨⟨d₂, left⟩, h5, h⟩ := Option.bind_eq_some_iff.1 h
    dsimp only at h
    split at h
    · cases h
      have h1' : Ground.recvP p.firstTree d sent = some (ids, d₁) := h1
      have hr := recv_carries p.firstTree d d₁ sent ids h1'
      obtain ⟨e1, e2⟩ := zip_mapM d₁.st _ shapes h2
      have et : (ids.toList.filter fun o =>
          ((d₁.st.oracles[o]?).map (·.shape.answers)).getD 0 != 0) = todoL (shD d₁) ids := by
        unfold todoL
        apply List.filter_congr
        intro o _
        show _ = ((((Ground.Sh.stSh d₁.st).oracles[o]?).map (·.shape.answers)).getD 0 != 0)
        rw [Ground.Sh.orc_get]
        cases d₁.st.oracles[o]? <;> rfl
      rw [et] at e1 e2 h5
      have ep : (todoL (shD d₁) ids).zip shapes = pairsL (shD d₁) (todoL (shD d₁) ids) := e1
      rw [ep] at h5
      have eb : shapes.foldl (fun b s => max b (Send.cube d₁.st.codes s).bits) 0 =
          bitsL d₁.st.codes (pairsL (shD d₁) (todoL (shD d₁) ids)) := by
        rw [← ep]
        exact (foldl_zip (fun b s => max b (Send.cube d₁.st.codes s).bits) _ shapes 0 e2).symm
      obtain ⟨g1, g2⟩ := sampleLoop_sh p d₁.st.codes _ seeds
        (seedsMade_len _ _ _ seeds h3) _ _ d₁ d' left h5
      constructor
      · unfold sendPS
        rw [hr]
        show (loopS _ (shD d₁)).map _ = _
        rw [g1]
        rfl
      · unfold sendPF
        rw [hr, g2, recv_forms h1', eb]
        rfl
    · cases h
  · cases h

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.sendP_sh
#print axioms VerifiableInference.Desc.First.Shape.rowsFor_mk
#print axioms VerifiableInference.Desc.First.Shape.sampleLoop_sh
#print axioms VerifiableInference.Desc.First.Shape.formMade_mk
