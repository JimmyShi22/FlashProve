-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqSizes.lean: THE FOUR TESTS ON SIZES THAT THE SUB-PROTOCOL "THE ONE EQUATION"'s NAMED TEST
`oneV` (Johnson/AtFull/Shape/ValsBool.lean) ASKS OF THE STATE ITSELF, `termsB`, `madeB`, `seatsB`, `maskB`, AS ONE Bool ON THE
SHAPE OF THE FIRST CHAIN's STATE (`chainSh`, Johnson/Desc/First/Shape/Chain.lean), but for one clause. Definitions with
code, and the law that a yes on the shape gives the four at the state. General; nothing is evaluated.

Why. The library's step on shapes at this sub-protocol (`oneG`, Johnson/Desc/First/Batch/Shape/DoorChain.lean) leaves these
four to the state. All that they read is in the shape: the link's layout, table of arrays and list; the frame of the calls
(next call, link, own and kept messages, the groups' targets); of each array of the ledger its numbers of rows and columns
and of each virtual row three sizes; of the statement the messages' shapes, the codes and the groups' members. THE ONE
CLAUSE THAT IS NOT: "a virtual row's product form is well formed" (`rowFormFits`) reads the sizes of three lists that the
shape does not hold. It is kept apart, as the Bool `fitsB` of the state.

  `treeAt`, `rowS`, `termsS`      `termsB` without that clause, on shapes      `fitsB`   that clause, of the state
  `termS`, `madeR`, `madeS`       `madeB` on shapes
  `thereS`, `seatS`, `seatsS`, `maskS`   `seatsB`, `maskB` on shapes
  **`oneSizes`**                  the Bool on the chain's shape
  `terms_of`, `made_of`, `seats_of`, `mask_of`   each test at the state, from its like at the shapes
  **`sizes_of_shape`**            where a link L and a ledger F are open at s: `oneSizes (chainSh s) = true` and `fitsB L F = true` give
                               the four tests in the forms in which `oneV` and `OneRest` ask them (the door shut)

Limits. One way: a yes on the shape gives the tests. That `oneSizes` accepts at any shape, or `fitsB` at any state, is not proved
here. Where no link or no ledger is open `oneSizes` says no. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.First.Batch.Shape.DoorChain
import Johnson.Desc.First.Batch.Shape.DoorMkAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh LinkSh linkSh LedSh ledSh TreeSh treeSh RowSh rowSh frameSh
  rowBitsS rowBits_sh)
open VerifiableInference.Desc.Ground.Sh (StSh GrpSh stSh grpSh tableBitsS tableBitsS_eq orc_get grp_get)
open VerifiableInference.Desc.K9 (arrayLaid rowFormFits messageNow)
open VerifiableInference.Desc.K9.Shape (termsB rowB madeB termB seatsB seatB maskB msgOf maskAt blockB WSh treeD_sh)

/-! ## 1 The tests on shapes -/

/-- Array number ti of the ledger's shape; outside the list: the shape of the empty array. -/
def treeAt (F : LedSh) (ti : ℕ) : TreeSh := F.trees.getD ti (treeSh {})

/-- A virtual row's three sizes, in an array of R rows and K columns. -/
def rowS (R K : ℕ) (r : RowSh) : Bool := r.coef == R && r.entries == K && r.col0 == 0

/-- The listed arrays: each is laid with its numbers of rows and columns; each virtual row has its sizes. -/
def termsS (L : LinkSh) (F : LedSh) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    arrayLaid L.check.rows.layout (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2 (treeAt F ti).R
      (treeAt F ti).K && (treeAt F ti).rows.all (rowS (treeAt F ti).R (treeAt F ti).K)

/-- The clause that the shape does not hold: each product form of a listed array's virtual row is well formed. -/
def fitsB (L : LinkCtx) (F : Fork) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    (F.trees.getD ti {}).rows.all fun r => !r.rowForm || rowFormFits (F.trees.getD ti {}) r

/-- A term's test on sizes. rb, pb: the numbers of row bits and of place bits of a message's main table. -/
def termS (layout : ReqLayout) (f : ReqFrame) (rb pb : ℕ → ℕ) (born : ℕ) (array : String) (onI onC : WSh) : Bool :=
  match (layout.link[born]?).bind fun arrays => arrays.find? fun a => a.name == array with
  | none => false
  | some a =>
    match messageNow f born a.message with
    | none => false
    | some o => a.blocks.all fun b => blockB b (rb o) (pb o) onI onC

/-- The same over the listed arrays and their virtual rows. -/
def madeR (L : LinkSh) (F : LedSh) (rb pb : ℕ → ℕ) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    (treeAt F ti).rows.all fun r =>
      termS L.check.rows.layout L.check.frame.blank rb pb (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
        ⟨clog2 (treeAt F ti).R, clog2 (treeAt F ti).R, none⟩ ⟨0, 0, some r.entries⟩

def madeS (L : LinkSh) (F : LedSh) (st : StSh) : Bool :=
  madeR L F (fun o => rowBitsS st o .main) (fun o => tableBitsS st o .main - rowBitsS st o .main)

/-- The table is there. -/
def thereS (st : StSh) (o : ℕ) (part : Part) : Bool := (st.oracles[o]?).any fun x => decide (0 < x.shape.rows part)

/-- A term's message is a member of the group and has a main table. -/
def seatS (layout : ReqLayout) (f : ReqFrame) (st : StSh) (G : GrpSh) (born : ℕ) (array : String) : Bool :=
  match msgOf layout f born array with
  | none => false
  | some o => G.members.contains o && thereS st o .main

def seatsS (L : LinkSh) (F : LedSh) (st : StSh) (G : GrpSh) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    (treeAt F ti).rows.isEmpty ||
      seatS L.check.rows.layout L.check.frame.blank st G (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2

/-- The mask message's seat. n: the number of coefficients on masks. -/
def maskS (f : ReqFrame) (st : StSh) (G : GrpSh) (n : ℕ) : Bool :=
  n == 0 ||
    match maskAt f with
    | none => false
    | some o => G.members.contains o && thereS st o .mask && decide (n - 1 < 2 ^ tableBitsS st o .mask)

/-- **The four tests on sizes, but for the clause `fitsB`, on the chain's shape.** -/
def oneSizes (a : ChainSh) : Bool :=
  match a.link, a.led with
  | some L, some F =>
    termsS L F && madeS L F a.core.st &&
      match a.core.st.groups[L.check.frame.group]? with
      | some G => seatsS L F a.core.st G && maskS L.check.frame.blank a.core.st G F.ns
      | none => false
  | _, _ => false

/-! ## 2 A yes on the shapes gives the tests -/

theorem treeAt_sh (F : Fork) (ti : ℕ) : treeAt (ledSh F) ti = treeSh (F.trees.getD ti {}) := treeD_sh F.trees ti

theorem there_sh (S₀ : Statement) (o : ℕ) (part : Part) : thereS (stSh S₀) o part = Own.tableThere S₀ o part := by
  unfold thereS Own.tableThere
  rw [orc_get]
  cases S₀.oracles[o]? <;> rfl

theorem members_sh (G : Group) (o : ℕ) : (grpSh G).members.contains o = G.members.contains o := by
  show G.members.toList.contains o = _
  rw [Array.contains_toList]

theorem terms_of (L : LinkCtx) (F : Fork) (h : termsS (linkSh L) (ledSh F) = true) (hf : fitsB L F = true) :
    termsB L F = true := by
  unfold termsB
  refine List.all_eq_true.2 fun ti hti => ?_
  show (arrayLaid L.check.rows.layout (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
    (F.trees.getD ti {}).R (F.trees.getD ti {}).K && (F.trees.getD ti {}).rows.all (rowB (F.trees.getD ti {}))) = true
  unfold termsS at h
  have h1 := List.all_eq_true.1 h ti hti
  beta_reduce at h1
  rw [treeAt_sh, Bool.and_eq_true] at h1
  unfold fitsB at hf
  have f1 := List.all_eq_true.1 hf ti hti
  beta_reduce at f1
  rw [Bool.and_eq_true]
  refine ⟨h1.1, Array.all_eq_true'.2 fun r hr => ?_⟩
  have r1 : rowS (F.trees.getD ti {}).R (F.trees.getD ti {}).K (rowSh r) = true :=
    List.all_eq_true.1 h1.2 (rowSh r) (List.mem_map.2 ⟨r, Array.mem_toList_iff.2 hr, rfl⟩)
  have r2 := Array.all_eq_true'.1 f1 r hr
  unfold rowB
  rw [Bool.and_eq_true]
  exact ⟨r1, r2⟩

theorem made_of (L : LinkCtx) (F : Fork) (S₀ : Statement) (h : madeS (linkSh L) (ledSh F) (stSh S₀) = true) :
    madeB L F S₀ = true := by
  have e1 : (fun o => rowBitsS (stSh S₀) o .main) = fun o => S₀.rowBits o .main :=
    funext fun o => (rowBits_sh S₀ o .main).symm
  have e2 : (fun o => tableBitsS (stSh S₀) o .main - rowBitsS (stSh S₀) o .main) = fun o => S₀.placeBits o .main := by
    funext o
    rw [tableBitsS_eq, ← rowBits_sh]
    show S₀.rowBits o .main + S₀.placeBits o .main - S₀.rowBits o .main = _
    exact Nat.add_sub_cancel_left _ _
  unfold madeS at h
  rw [e1, e2] at h
  unfold madeB
  refine List.all_eq_true.2 fun ti hti => ?_
  unfold madeR at h
  have h1 := List.all_eq_true.1 h ti hti
  beta_reduce at h1
  rw [treeAt_sh] at h1
  refine Array.all_eq_true'.2 fun r hr => ?_
  exact List.all_eq_true.1 h1 (rowSh r) (List.mem_map.2 ⟨r, Array.mem_toList_iff.2 hr, rfl⟩)

theorem seat_of (layout : ReqLayout) (f : ReqFrame) (S₀ : Statement) (G : Group) (born : ℕ) (array : String) :
    seatS layout (frameSh f).blank (stSh S₀) (grpSh G) born array = seatB layout f S₀ G born array := by
  have e : msgOf layout (frameSh f).blank born array = msgOf layout f born array := rfl
  unfold seatS seatB
  rw [e]
  cases msgOf layout f born array with
  | none => rfl
  | some o =>
    show ((grpSh G).members.contains o && thereS (stSh S₀) o .main) = _
    rw [members_sh, there_sh]

theorem seats_of (L : LinkCtx) (F : Fork) (S₀ : Statement) (G : Group)
    (h : seatsS (linkSh L) (ledSh F) (stSh S₀) (grpSh G) = true) : seatsB L F S₀ G = true := by
  unfold seatsB
  refine List.all_eq_true.2 fun ti hti => ?_
  unfold seatsS at h
  have h1 := List.all_eq_true.1 h ti hti
  beta_reduce at h1
  rw [treeAt_sh, Bool.or_eq_true] at h1
  beta_reduce
  rw [Bool.or_eq_true]
  rcases h1 with h1 | h1
  · left
    have h2 : ((F.trees.getD ti {}).rows.toList.map rowSh).isEmpty = true := h1
    rw [List.isEmpty_map] at h2
    rw [← Array.isEmpty_toList]
    exact h2
  · right
    have h2 := seat_of L.check.rows.layout L.check.frame S₀ G (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
    rw [← h2]
    exact h1

theorem mask_of (f : ReqFrame) (S₀ : Statement) (G : Group) (n : ℕ)
    (h : maskS (frameSh f).blank (stSh S₀) (grpSh G) n = true) : maskB f S₀ G n = true := by
  have e : maskAt (frameSh f).blank = maskAt f := rfl
  unfold maskS at h
  unfold maskB
  rw [e] at h
  cases hm : maskAt f with
  | none => rw [hm] at h; exact h
  | some o =>
    rw [hm] at h
    have h' : (n == 0 || ((grpSh G).members.contains o && thereS (stSh S₀) o .mask &&
      decide (n - 1 < 2 ^ tableBitsS (stSh S₀) o .mask))) = true := h
    rw [members_sh, there_sh, tableBitsS_eq] at h'
    exact h'

/-- The Bool, where the shape has a link and a ledger. -/
theorem oneSizes_at (a : ChainSh) (L : LinkSh) (F : LedSh) (h1 : a.link = some L) (h2 : a.led = some F) :
    oneSizes a = (termsS L F && madeS L F a.core.st &&
      match a.core.st.groups[L.check.frame.group]? with
      | some G => seatsS L F a.core.st G && maskS L.check.frame.blank a.core.st G F.ns
      | none => false) := by
  unfold oneSizes
  rw [h1, h2]

/-- The three tests that read the ledger read its arrays alone. -/
theorem termsB_shut (L : LinkCtx) (F : Fork) : termsB L { F with doorShutF := true } = termsB L F := by
  unfold termsB
  rfl

theorem madeB_shut (L : LinkCtx) (F : Fork) (S₀ : Statement) :
    madeB L { F with doorShutF := true } S₀ = madeB L F S₀ := by
  unfold madeB
  rfl

theorem seatsB_shut (L : LinkCtx) (F : Fork) (S₀ : Statement) (G : Group) :
    seatsB L { F with doorShutF := true } S₀ G = seatsB L F S₀ G := by
  unfold seatsB
  rfl

/-- **The four tests at the state, from the Bool on its shape and the clause that is kept apart.** -/
theorem sizes_of_shape {s : S} {L : LinkCtx} {F : Fork} (hL : s.link? = some L) (hF : s.fork? = some F)
    (h : oneSizes (chainSh s) = true) (hf : fitsB L F = true) :
    termsB L { F with doorShutF := true } = true ∧ madeB L { F with doorShutF := true } s.st = true ∧
      ∃ G, s.st.groups[L.check.group]? = some G ∧ seatsB L { F with doorShutF := true } s.st G = true ∧
        maskB L.check.frame s.st G F.ns = true := by
  have l1 : (chainSh s).link = some (linkSh L) := by
    show s.link?.map linkSh = _
    rw [hL]
    rfl
  have l2 : (chainSh s).led = some (ledSh F) := by
    show s.fork?.map ledSh = _
    rw [hF]
    rfl
  have ec : (chainSh s).core.st = stSh s.st := rfl
  have eg : (linkSh L).check.frame.group = L.check.group := rfl
  have en : (ledSh F).ns = F.ns := rfl
  have ef : (linkSh L).check.frame.blank = (frameSh L.check.frame).blank := rfl
  rw [oneSizes_at _ _ _ l1 l2, ec, eg, en, ef, grp_get, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨t1, t2⟩, t3⟩ := h
  rw [termsB_shut, madeB_shut]
  cases hG : s.st.groups[L.check.group]? with
  | none =>
    rw [hG] at t3
    exact nomatch t3
  | some G =>
    rw [hG] at t3
    simp only [Option.map_some, Bool.and_eq_true] at t3
    refine ⟨terms_of L F t1 hf, made_of L F s.st t2, G, rfl, ?_, mask_of L.check.frame s.st G F.ns t3.2⟩
    rw [seatsB_shut]
    exact seats_of L F s.st G t3.1

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.terms_of
#print axioms ProofFile.Honest.K9.made_of
#print axioms ProofFile.Honest.K9.seat_of
#print axioms ProofFile.Honest.K9.seats_of
#print axioms ProofFile.Honest.K9.mask_of
#print axioms ProofFile.Honest.K9.oneSizes_at
#print axioms ProofFile.Honest.K9.termsB_shut
#print axioms ProofFile.Honest.K9.madeB_shut
#print axioms ProofFile.Honest.K9.seatsB_shut
#print axioms ProofFile.Honest.K9.sizes_of_shape
