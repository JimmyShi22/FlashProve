-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/GenRows.lean: THE GENERATOR ROWS OF A CODE SWITCH SAY TRUE OF THE
HONEST NEW MESSAGES, where their targets are the code words' symbols. Statements and proofs.

  `FrameIs`, `frameIs`   the fields of the program's frame of a switch, in the terms of the
                    statement, the single rows and the target
  `sym_split`       a code word's symbol, as the weights on the message and on the tail
  `liftPiece`, `stretchPiece`, `worth_liftPiece`, `worth_stretchPiece`   two sorts of pieces as
                    functions of coefficients, with their worth (Inner/RowWorth.lean's)
  `tensor_vars`     the generator's message tensor has the main code's variables
  `mainTail_fits`, `mask_fits`   the main row's tail, a mask row's message and tail lie inside the
                    rest
  `main_pieces`, `main_holds`   the main row's generator row: its pieces; it says true
  `mask_off`, `mask_holds`   a mask row's: no coefficient on a message other than g; it says true

By: `genMain_at`, `genMask_at` (Johnson/Top/H0/H2K/GenRowsAt.lean); the frame's facts behind the
program's test (`frame_fields`, `frame_bits`, `frame_g`, `frame_more`, `places_inc`,
`maskAt_of_check`); Inner/RowWorth.lean; Inner/RestIsPartsProof.lean.

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.KeptWorth
import Johnson.Top.H0.K2Hands.AtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE readE coefAt formAt stretchAt codeOf wM wT genMain genMask
  messageTensor)
open OnBytes.Means (Says value)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG)
open Finset (range)

/-- The fields of the program's frame of a switch. -/
structure FrameIs (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (Fr : SwitchFrame) : Prop where
  gIs : Fr.g = g
  code : Fr.code = S.codes.base.getD old.code default
  zk : Fr.zk = S.codes.mask.getD old.maskCode default
  restPart : Fr.restPart = T.rest.part
  mainCut : Fr.mainCut = T.main
  rowBits : Fr.rowBits = switchRowBits T .main
  tableBits : Fr.tableBits =
    switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll
  places : Fr.places = SwitchPlaces.make S.codes T
  parts : Fr.parts = switchParts S old
  restBits : Fr.restBits = S.tableBits g T.rest.part

theorem frameIs {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {Fr : SwitchFrame} (h : switchFrame S old T g anew = some Fr) :
    FrameIs S old T g Fr := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, _⟩ := Johnson.Top.H.frame_fields S old T g anew Fr h
  obtain ⟨nc, hn, b1, b2⟩ := Johnson.Top.H.frame_bits S old T g anew Fr h
  refine ⟨VerifiableInference.Desc.First.K2.frame_g S old T g anew Fr h, ?_, ?_, f3, f4, f5,
    ?_, f6, f7, b2⟩
  · rw [Array.getD_eq_getD_getElem?, f1]; rfl
  · rw [Array.getD_eq_getD_getElem?, f2]; rfl
  · rw [b1, f5, Array.getD_eq_getD_getElem?, hn]; rfl

/-- A code word's symbol, as the weights on the message and on the tail. -/
theorem sym_split (c : OnBytes.Code) (x : Nat) (m r : Nat → GE) :
    ∑ j ∈ range c.ell, wM (codeOf c) x j * m j + ∑ q ∈ range c.r, wT (codeOf c) x q * r q =
      symG (codeOf c) x m r := by
  unfold symG
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    have h : q < (codeOf c).r := Finset.mem_range.1 hq
    unfold wT
    rw [if_pos h]
  · apply Finset.sum_congr rfl
    intro j hj
    have h : j < (codeOf c).l := Finset.mem_range.1 hj
    unfold wM
    rw [if_pos h]

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- A form on the old main row's message, carried to g: as a function of coefficients. -/
def liftPiece (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (c : Form) :
    Nat → Part → Nat → GE := fun o q J =>
  if g == o && q == .main then
    formAt (switchLift c (S.codes.base.getD old.code default).logEll T.main (switchRowBits T .main)
      (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll)) J else 0

/-- Coefficients on a stretch of the rest: as a function of coefficients. -/
def stretchPiece (S : Statement) (T : SwitchTarget) (g a n : Nat) (c : Nat → GE) :
    Nat → Part → Nat → GE := fun o q J =>
  if g == o && T.rest.part == q then stretchAt (SwitchPlaces.make S.codes T) a n c J else 0

theorem worth_liftPiece (A : AtSwitch S old T g anew W V) (c : Form)
    (hc : ∀ v ∈ c.tensors, v.vars = (S.codes.base.getD old.code default).logEll) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew (liftPiece S old T g c) =
      ∑ j ∈ range (S.codes.base.getD old.code default).ell, formAt c j * W.main j :=
  worth_lift A c hc

theorem worth_stretchPiece (A : AtSwitch S old T g anew W V) (a n : Nat) (c : Nat → GE)
    (hfit : a + n ≤ (rest (sizesAt S old T) W).length) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew (stretchPiece S T g a n c) =
      ∑ i ∈ range n, c i * (rest (sizesAt S old T) W).getD (a + i) zeroG :=
  worth_stretch A a n c hfit

/-- The generator's message tensor has the main code's variables. -/
theorem tensor_vars (c : OnBytes.Code) (x : Nat) (hpow : c.ell = 2 ^ c.logEll) :
    ∀ v ∈ (Form.ofTensor (messageTensor c x)).tensors, v.vars = c.logEll := by
  intro v hv
  have e : v = messageTensor c x := List.mem_singleton.1 hv
  rw [e]
  exact OnBytes.Slice.vars_messageTensor c x hpow

/-- The main row's tail lies inside the rest. -/
theorem mainTail_fits (A : AtSwitch S old T g anew W V) :
    (switchParts S old).mainTailAt + (S.codes.base.getD old.code default).r ≤
      (rest (sizesAt S old T) W).length := by
  rw [(restIsParts S old T W A.target.masks A.fits).1]
  have h := (Johnson.Top.H.parts_laws S old).1
  unfold Johnson.Top.H.restHead at h
  have e : (switchParts S old).mainTailAt =
      old.masks * (S.codes.mask.getD old.maskCode default).ell := rfl
  rw [e]
  omega

/-- The main row's generator row, as two pieces. -/
theorem main_pieces (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.base.getD old.code default).logN ≤ 32) (x : Nat)
    (hx : x < 2 ^ (S.codes.base.getD old.code default).logN) (t : E) :
    coefAt (genMain Fr x t) = fun o p J =>
      liftPiece S old T g
        (Form.ofTensor (messageTensor (S.codes.base.getD old.code default) x)) o p J +
      stretchPiece S T g (switchParts S old).mainTailAt (S.codes.base.getD old.code default).r
        (wT (codeOf (S.codes.base.getD old.code default)) x) o p J := by
  have I := frameIs hFr
  funext o p J
  have h := H2K.Lift.genMain_at Fr Fr.parts.mainTailAt
    (VerifiableInference.Desc.First.K2Hands.frame_more S old T g anew Fr hFr).1
    (VerifiableInference.Desc.First.K2Hands.places_inc S old T g anew Fr hFr A.check _ _)
    (by rw [I.code]; exact hlog) x (by rw [I.code]; exact hx) t o p J
  rw [I.gIs, I.code, I.mainCut, I.rowBits, I.tableBits, I.restPart, I.places, I.parts] at h
  exact h

/-- **The main row's generator row.** -/
theorem main_holds (A : AtSwitch S old T g anew W V) (hn : ∀ o ∈ anew.toList, o < S.oracles.size)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.base.getD old.code default).logN ≤ 32) (x : Nat)
    (hx : x < 2 ^ (S.codes.base.getD old.code default).logN) (t : E)
    (ht : readE t = symG (codeOf (S.codes.base.getD old.code default)) x W.main W.mainTail) :
    Says rdE S (genMain Fr x t) (newWords (sizesAt S old T) g anew V) := by
  have hpow : (S.codes.base.getD old.code default).ell =
      2 ^ (S.codes.base.getD old.code default).logEll := A.target.power.2.symm
  have R := (restIsParts S old T W A.target.masks A.fits).2.2.1
  have h1 := value_worth A hn (genMain Fr x t)
  rw [main_pieces A hFr hlog x hx t, worthOf_add, worth_liftPiece A _ (tensor_vars _ x hpow),
    worth_stretchPiece A _ _ _ (mainTail_fits A)] at h1
  have htg : rdE.val (genMain Fr x t).target = readE t := rfl
  have ha : ∑ j ∈ range (S.codes.base.getD old.code default).ell,
      formAt (Form.ofTensor (messageTensor (S.codes.base.getD old.code default) x)) j * W.main j =
      ∑ j ∈ range (S.codes.base.getD old.code default).ell,
        wM (codeOf (S.codes.base.getD old.code default)) x j * W.main j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have e := congrFun (OnBytes.Slice.cut_messageTensor _ x hlog hx hpow) j
    rw [OnBytes.Slice.cut_of_lt (by rw [← hpow]; exact hj')] at e
    rw [OnBytes.Slice.formAt_ofTensor, e]
  have hb : ∑ q ∈ range (S.codes.base.getD old.code default).r,
      wT (codeOf (S.codes.base.getD old.code default)) x q *
        (rest (sizesAt S old T) W).getD ((switchParts S old).mainTailAt + q) zeroG =
      ∑ q ∈ range (S.codes.base.getD old.code default).r,
        wT (codeOf (S.codes.base.getD old.code default)) x q * W.mainTail q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [← R q (Finset.mem_range.1 hq)]
  unfold Says
  rw [h1, htg, ht, ← sym_split, ha, hb]

/-- A mask row's generator row has no coefficient on a message other than g. -/
theorem mask_off (Fr : SwitchFrame) (j aM aT : Nat) (h : H2K.Lift.MaskAt Fr j aM aT) (x : Nat)
    (t : E) (o : Nat) (p : Part) (J : Nat) (ho : (Fr.g == o) = false) :
    coefAt (genMask Fr x j t) o p J = 0 := by
  have key : ∀ r : OnBytes.Row, coefAt ({ switchAddRestF r Fr.g Fr.restPart (Fr.maskTail.getD j [])
        (generatorTail Fr.zk (shortPosition Fr.zk.logN x)) with
        kind := .generator, target := t } : OnBytes.Row) o p J = coefAt r o p J := by
    intro r
    show coefAt (switchAddRestF r Fr.g Fr.restPart (Fr.maskTail.getD j [])
      (generatorTail Fr.zk (shortPosition Fr.zk.logN x))) o p J = _
    rw [h.tail, OnBytes.Slice.coefAt_restF_at _ _ _ _ _ _ h.incT, ho]
    simp
  unfold genMask
  rw [key]
  split
  · rw [OnBytes.Slice.coefAt_add, OnBytes.Slice.coefAt_empty, ho]
    simp
  · rename_i hb
    rw [h.msg hb, OnBytes.Slice.coefAt_restF_at _ _ _ _ _ _ h.incM, OnBytes.Slice.coefAt_empty, ho]
    simp

/-- A mask row's message and tail lie inside the rest. -/
theorem mask_fits (A : AtSwitch S old T g anew W V) (j : Nat) (hj : j < 2) :
    (switchParts S old).maskAt.getD j 0 + (S.codes.mask.getD old.maskCode default).ell ≤
        (rest (sizesAt S old T) W).length ∧
      (switchParts S old).maskTailAt.getD j 0 + (S.codes.mask.getD old.maskCode default).r ≤
        (rest (sizesAt S old T) W).length := by
  rw [(restIsParts S old T W A.target.masks A.fits).1]
  have h := (Johnson.Top.H.parts_laws S old).1
  unfold Johnson.Top.H.restHead at h
  have hm := A.target.masks
  have e1 : (switchParts S old).maskAt.getD j 0 =
      0 + (S.codes.mask.getD old.maskCode default).ell * j :=
    startsFrom_getD _ _ old.masks j (by omega)
  have e2 : (switchParts S old).maskTailAt.getD j 0 =
      old.masks * (S.codes.mask.getD old.maskCode default).ell +
        (S.codes.base.getD old.code default).r +
        old.keptRows * (S.codes.base.getD old.code default).r +
        (S.codes.mask.getD old.maskCode default).r * j :=
    startsFrom_getD _ _ old.masks j (by omega)
  rw [e1, e2]
  rw [hm] at h ⊢
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero]
    omega
  · simp only [Nat.mul_one]
    omega

/-- **A mask row's generator row.** -/
theorem mask_holds (A : AtSwitch S old T g anew W V) (hn : ∀ o ∈ anew.toList, o < S.oracles.size)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.mask.getD old.maskCode default).logN ≤ 32) (j : Nat) (hj : j < 2) (x : Nat)
    (t : E)
    (ht : readE t = symG (codeOf (S.codes.mask.getD old.maskCode default))
      (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN) (W.mask j) (W.maskTail j)) :
    Says rdE S (genMask Fr x j t) (newWords (sizesAt S old T) g anew V) := by
  have I := frameIs hFr
  obtain ⟨xo, hxo, hxs⟩ := Option.map_eq_some_iff.1 A.seated.carrying
  have M := VerifiableInference.Desc.First.K2Hands.maskAt_of_check S old T g anew Fr hFr A.check
    xo hxo hxs (by rw [I.zk]; exact hlog) j hj
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons] at hap
  have R := restIsParts S old T W A.target.masks A.fits
  have hsplit : worthOf S (newWords (sizesAt S old T) g anew V) g anew
      (coefAt (genMask Fr x j t)) =
      worthOf S (newWords (sizesAt S old T) g anew V) g anew (fun o p J =>
        stretchPiece S T g ((switchParts S old).maskAt.getD j 0)
          (S.codes.mask.getD old.maskCode default).ell
          (wM (codeOf (S.codes.mask.getD old.maskCode default))
            (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN)) o p J +
        stretchPiece S T g ((switchParts S old).maskTailAt.getD j 0)
          (S.codes.mask.getD old.maskCode default).r
          (wT (codeOf (S.codes.mask.getD old.maskCode default))
            (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN)) o p J) := by
    apply worthOf_congr
    · intro J hJ
      have hJ' : J < 2 ^ Fr.restBits := by
        rw [I.restBits, A.restMain]
        unfold OnBytes.Means.tableSize at hJ
        split at hJ
        · exact hJ
        · omega
      have h := H2K.Lift.genMask_at Fr j _ _ M x t g .main J hJ'
      rw [I.gIs, I.restPart, I.places, I.parts, I.zk] at h
      rw [h]
      unfold stretchPiece
      rw [A.restMain]
      simp [shortPosition]
    · intro o ho J _
      have hg' : (g == o) = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun e => hap.1 (List.mem_append_left _ (e ▸ ho))
      rw [mask_off Fr j _ _ M x t o .main J (by rw [I.gIs]; exact hg')]
      unfold stretchPiece
      simp [hg']
  have h1 := value_worth A hn (genMask Fr x j t)
  rw [hsplit, worthOf_add, worth_stretchPiece A _ _ _ (mask_fits A j hj).1,
    worth_stretchPiece A _ _ _ (mask_fits A j hj).2] at h1
  have htg : rdE.val (genMask Fr x j t).target = readE t := rfl
  have ha : ∑ i ∈ range (S.codes.mask.getD old.maskCode default).ell,
      wM (codeOf (S.codes.mask.getD old.maskCode default))
          (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN) i *
        (rest (sizesAt S old T) W).getD ((switchParts S old).maskAt.getD j 0 + i) zeroG =
      ∑ i ∈ range (S.codes.mask.getD old.maskCode default).ell,
        wM (codeOf (S.codes.mask.getD old.maskCode default))
          (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN) i * W.mask j i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← R.2.1 j i hj (Finset.mem_range.1 hi)]
  have hb : ∑ q ∈ range (S.codes.mask.getD old.maskCode default).r,
      wT (codeOf (S.codes.mask.getD old.maskCode default))
          (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN) q *
        (rest (sizesAt S old T) W).getD ((switchParts S old).maskTailAt.getD j 0 + q) zeroG =
      ∑ q ∈ range (S.codes.mask.getD old.maskCode default).r,
        wT (codeOf (S.codes.mask.getD old.maskCode default))
          (x % 2 ^ (S.codes.mask.getD old.maskCode default).logN) q * W.maskTail j q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [← R.2.2.2.2.1 j q hj (Finset.mem_range.1 hq)]
  unfold Says
  rw [h1, htg, ht, ← sym_split, ha, hb]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.main_holds
#print axioms VerifiableInference.Desc.K2.Honest.mask_holds
