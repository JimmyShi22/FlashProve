-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/GenJoin.lean: the code switch: the generator rows of one draw, as the
program lays them, ARE the typed library's generator rows of the folded complex with kept slots,
entry by entry: here for the main row and the two mask rows, with the places of all rows of a draw.

Two sides are joined. THE TEXT's SIDE. The program's switchGenerators (OnBytes/Iop/Cs.lean), read in
the field by coefAt. Johnson/Top/H0/H2K/GenRowsAt.lean has each row in closed form (genMain_at,
genMask_at) and the list of a draw (switchGenerators_all). THE TYPED SIDE. The vector of a generator
row in LdLocD.rowsOf (Cb/Req1/LdSegAfterRows.lean) at the complex Sg.cKept: the weights keptRow
(OnBytes/Slice/CsRowKept.lean), carried along two maps of names iJ and iQ into the entries of the
new sending (pushTo). THE DICTIONARY between an entry of the sending and the program's three numbers
(which message, which table, which index) is entAt (Johnson/Top/H/SwitchNames.lean), with pushTo_at.
Main names:
  pushTo_rowOf, pushTo_left, pushTo_right  carried coefficients that are 0 outside one part of the
                names
  genVec        the typed vector of the generator row at a position x and a coordinate α
  genVec_row, genVec_mask0, genVec_mask1  that vector, written out: the weights wM on one row's
                message and wT on its tail
  ReadsAs       a row of the text has, at the three numbers of every entry of the sending, the
                coefficient that a typed vector has at that entry
  FrameOK       what is asked of the switch's frame: GenRowsAt.lean's premises, gathered
  Names         what is asked of iJ and iQ: at which three numbers the entries of the main row and
                of the two mask rows lie
  cutIndex_inj, lift_sum, genMask_off, mask_sum, tab_main, tab_rest, cons_at  small steps
  mask_reads    a mask row, at any two maps of names that lie on its two stretches: the lemma behind
                both mask joins
  main_reads, mask0_reads, mask1_reads  THE JOIN for these three rows
  rowsBefore, keptRows  the kept rows in front of member number a; all kept rows (two definitions
                that the later files spend)
  keptFrom_length, keptFrom_at, gens_length, gens_main, gens_kept, gens_mask  the rows of a draw,
                each at its place in the list
LIMITS. FrameOK and Names are PREMISES: nothing here says that a switch of the programs meets them,
and iJ, iQ, ids are letters. (Brought further, not paid: Paid.lean's paid_frame and paid_names make
them from the record AtSwitch, a premise.) ReadsAs speaks of the entries of the new sending alone:
what a row's coefficient is at an index of a table that is no entry (a row number from the shape's
rows on), or on a message outside the sending, is not said here (in part: Support.lean's and
SupportClaim.lean's OnlyAt, joined in HandsOn.lean). The kept rows' vectors are not joined here
(KeptJoin.lean's kept_reads). Nothing is said here on the carried claim (ClaimJoin.lean) or on the
old sample rows (RowsJoin.lean). No soundness is claimed.
-/
import Johnson.Top.H.SwitchNames
import OnBytes.Slice.CsRowKept
import Johnson.Top.H0.H2K.GenRowsAt
import Johnson.Top.H0.K2Hands.RowsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

/-! ## Carried coefficients that are 0 outside one part of the names -/

section Push
variable {R A B Ent : Type}

theorem pushTo_rowOf [Fintype R] [DecidableEq R] [Fintype A] [Fintype B]
    (p : (R × A) ⊕ B → Ent) (c : (R × A) ⊕ B → GE) (k : R) (f : A → GE)
    (h1 : ∀ r a, c (.inl (r, a)) = if r = k then f a else 0) (h2 : ∀ b, c (.inr b) = 0) (n : Ent) :
    pushTo p c n = pushTo (fun a => p (.inl (k, a))) f n := by
  unfold pushTo
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp [h1, h2]
  · intro r _ hr
    simp [h1, hr]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pushTo_right [Fintype A] [Fintype B] (p : A ⊕ B → Ent) (c : A ⊕ B → GE)
    (h : ∀ a, c (.inl a) = 0) (n : Ent) :
    pushTo p c n = pushTo (fun b => p (.inr b)) (fun b => c (.inr b)) n := by
  unfold pushTo
  rw [Fintype.sum_sum_type]
  simp [h]

theorem pushTo_left [Fintype A] [Fintype B] (p : A ⊕ B → Ent) (c : A ⊕ B → GE)
    (h : ∀ b, c (.inr b) = 0) (n : Ent) :
    pushTo p c n = pushTo (fun a => p (.inl a)) (fun a => c (.inl a)) n := by
  unfold pushTo
  rw [Fintype.sum_sum_type]
  simp [h]

end Push

/-! ## The typed vector of a generator row -/

section Typed
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K] {Ent : Type}
  (iJ : (s.cKept K).J → Ent) (iQ : (s.cKept K).Q → Ent)

/-- The typed vector of the generator row at the position x and the coordinate α. -/
noncomputable def genVec (x : ℕ) (α : (s.cKept K).Aa) (n : Ent) : GE :=
  pushTo iJ (fun j => keptRow s K x α (.inl j)) n + pushTo iQ (fun q => keptRow s K x α (.inr q)) n

/-- A main row: the folded one (none) or a kept one. -/
theorem genVec_row (x : ℕ) (k : Option K) (n : Ent) :
    genVec s K iJ iQ x (.inl (k, ())) n =
      pushTo (fun j : Fin s.C.l => iJ (.inl (k, j))) (fun j => wM s.C x j.val) n +
        pushTo (fun q : Fin s.C.r => iQ (.inl (k, q))) (fun q => wT s.C x q.val) n := by
  unfold genVec
  exact congrArg₂ (· + ·)
    (pushTo_rowOf (R := Option K) (A := Fin s.C.l) (B := Fin s.Z.l ⊕ Fin s.Z.l) iJ
      (fun j => keptRow s K x (.inl (k, ())) (.inl j)) k (fun j => wM s.C x j.val)
      (fun r a => keptRow_msg s K x k r a) (fun b => by rcases b with _ | _ <;> rfl) n)
    (pushTo_rowOf (R := Option K) (A := Fin s.C.r) (B := Fin s.Z.r ⊕ Fin s.Z.r) iQ
      (fun q => keptRow s K x (.inl (k, ())) (.inr q)) k (fun q => wT s.C x q.val)
      (fun r a => keptRow_tail s K x k r a) (fun b => by rcases b with _ | _ <;> rfl) n)

/-- The carried mask row. -/
theorem genVec_mask0 (x : ℕ) (n : Ent) :
    genVec s K iJ iQ x (.inr (.inl ())) n =
      pushTo (fun j : Fin s.Z.l => iJ (.inr (.inl j)))
          (fun j => wM s.Z (Fmt.M1.cp s.Z x) j.val) n +
        pushTo (fun q : Fin s.Z.r => iQ (.inr (.inl q)))
          (fun q => wT s.Z (Fmt.M1.cp s.Z x) q.val) n := by
  unfold genVec
  exact congrArg₂ (· + ·)
    ((pushTo_right (A := Option K × Fin s.C.l) (B := Fin s.Z.l ⊕ Fin s.Z.l) iJ
      (fun j => keptRow s K x (.inr (.inl ())) (.inl j)) (fun a => by rcases a with ⟨_, _⟩; rfl)
      n).trans
      (pushTo_left (A := Fin s.Z.l) (B := Fin s.Z.l) (fun b => iJ (.inr b))
        (fun b => keptRow s K x (.inr (.inl ())) (.inl (.inr b))) (fun _ => rfl) n))
    ((pushTo_right (A := Option K × Fin s.C.r) (B := Fin s.Z.r ⊕ Fin s.Z.r) iQ
      (fun q => keptRow s K x (.inr (.inl ())) (.inr q)) (fun a => by rcases a with ⟨_, _⟩; rfl)
      n).trans
      (pushTo_left (A := Fin s.Z.r) (B := Fin s.Z.r) (fun b => iQ (.inr b))
        (fun b => keptRow s K x (.inr (.inl ())) (.inr (.inr b))) (fun _ => rfl) n))

/-- The fresh mask row. -/
theorem genVec_mask1 (x : ℕ) (n : Ent) :
    genVec s K iJ iQ x (.inr (.inr ())) n =
      pushTo (fun j : Fin s.Z.l => iJ (.inr (.inr j)))
          (fun j => wM s.Z (Fmt.M1.cp s.Z x) j.val) n +
        pushTo (fun q : Fin s.Z.r => iQ (.inr (.inr q)))
          (fun q => wT s.Z (Fmt.M1.cp s.Z x) q.val) n := by
  unfold genVec
  exact congrArg₂ (· + ·)
    ((pushTo_right (A := Option K × Fin s.C.l) (B := Fin s.Z.l ⊕ Fin s.Z.l) iJ
      (fun j => keptRow s K x (.inr (.inr ())) (.inl j)) (fun a => by rcases a with ⟨_, _⟩; rfl)
      n).trans
      (pushTo_right (A := Fin s.Z.l) (B := Fin s.Z.l) (fun b => iJ (.inr b))
        (fun b => keptRow s K x (.inr (.inr ())) (.inl (.inr b))) (fun _ => rfl) n))
    ((pushTo_right (A := Option K × Fin s.C.r) (B := Fin s.Z.r ⊕ Fin s.Z.r) iQ
      (fun q => keptRow s K x (.inr (.inr ())) (.inr q)) (fun a => by rcases a with ⟨_, _⟩; rfl)
      n).trans
      (pushTo_right (A := Fin s.Z.r) (B := Fin s.Z.r) (fun b => iQ (.inr b))
        (fun b => keptRow s K x (.inr (.inr ())) (.inr (.inr b))) (fun _ => rfl) n))

end Typed

/-! ## What is asked of the frame and of the names -/

/-- What is asked of the switch's frame. aMain: where the main row's tail begins in the rest; aM0,
aT0,
aM1, aT1: where the two mask rows' messages and tails begin. -/
structure FrameOK (W : SwitchFrame) (aMain aM0 aT0 aM1 aT1 : ℕ) : Prop where
  mainPieces : W.mainTail = switchPieces W.places aMain W.code.r
  mainInc : ∀ i j, i < j → j < W.code.r → W.places.get (aMain + i) < W.places.get (aMain + j)
  logC : W.code.logN ≤ 32
  pow : W.code.ell = 2 ^ W.code.logEll
  cutBits : W.mainCut.bits ≤ W.code.logEll
  cutRow : W.mainCut.bits ≤ W.rowBits
  cutTab : W.code.logEll + (W.rowBits - W.mainCut.bits) ≤ W.tableBits
  cutAl : 2 ^ W.mainCut.bits ∣ W.mainCut.firstRow
  cutFirst : W.mainCut.firstRow / 2 ^ W.mainCut.bits < 2 ^ (W.rowBits - W.mainCut.bits)
  mask0 : MaskAt W 0 aM0 aT0
  mask1 : MaskAt W 1 aM1 aT1

section Join
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K] (cs : Codes) (l : List (OracleShape × ℕ))
  (iJ : (s.cKept K).J → (sigOf cs l).Ent) (iQ : (s.cKept K).Q → (sigOf cs l).Ent)

/-- A row of the text has, at the three numbers of every entry of the sending, the coefficient that
the typed vector v has at that entry. ids: the statement's number of each message of the sending. -/
def ReadsAs (ids : ℕ → ℕ) (r : OnBytes.Row) (v : (sigOf cs l).Ent → GE) : Prop :=
  ∀ n, coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 = v n

/-- What is asked of the names: g is the sending's first message; where the entries of the main row
and
of the two mask rows lie. -/
structure Names (W : SwitchFrame) (ids : ℕ → ℕ) (aMain aM0 aT0 aM1 aT1 : ℕ) : Prop where
  codeC : s.C = codeOf W.code
  codeZ : s.Z = codeOf W.zk
  gIs : ∀ n : (sigOf cs l).Ent, ids (entAt cs l n).1 = W.g ↔ (entAt cs l n).1 = 0
  mainIn : ∀ n : (sigOf cs l).Ent, (entAt cs l n).1 = 0 → (entAt cs l n).2.1 = Part.main →
    (entAt cs l n).2.2 < 2 ^ W.tableBits
  restIn : ∀ n : (sigOf cs l).Ent, (entAt cs l n).1 = 0 → (entAt cs l n).2.1 = W.restPart →
    (entAt cs l n).2.2 < 2 ^ W.restBits
  mainMsg : ∀ j : Fin s.C.l, entAt cs l (iJ (.inl (none, j))) =
    (0, Part.main, cutIndex W.mainCut W.rowBits j.val)
  mainTail : ∀ q : Fin s.C.r, entAt cs l (iQ (.inl (none, q))) =
    (0, W.restPart, W.places.get (aMain + q.val))
  mask0Msg : ∀ j : Fin s.Z.l, entAt cs l (iJ (.inr (.inl j))) =
    (0, W.restPart, W.places.get (aM0 + j.val))
  mask0Tail : ∀ q : Fin s.Z.r, entAt cs l (iQ (.inr (.inl q))) =
    (0, W.restPart, W.places.get (aT0 + q.val))
  mask1Msg : ∀ j : Fin s.Z.l, entAt cs l (iJ (.inr (.inr j))) =
    (0, W.restPart, W.places.get (aM1 + j.val))
  mask1Tail : ∀ q : Fin s.Z.r, entAt cs l (iQ (.inr (.inr q))) =
    (0, W.restPart, W.places.get (aT1 + q.val))

end Join

/-! ## Small steps -/

theorem tab_main {g o i i0 : ℕ} {part : Part} (h : o = g ↔ i = i0) :
    ((g == o && part == Part.main) = true) ↔ (i = i0 ∧ part = Part.main) := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ← h]
  exact ⟨fun e => ⟨e.1.symm, e.2⟩, fun e => ⟨e.1.symm, e.2⟩⟩

theorem tab_rest {g o i i0 : ℕ} {part rp : Part} (h : o = g ↔ i = i0) :
    ((g == o && rp == part) = true) ↔ (i = i0 ∧ part = rp) := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ← h]
  exact ⟨fun e => ⟨e.1.symm, e.2.symm⟩, fun e => ⟨e.1.symm, e.2.symm⟩⟩

/-- A cut places two entries at two indices. -/
theorem cutIndex_inj (q : RowCut) (R : ℕ) (hR : q.bits ≤ R) (hal : 2 ^ q.bits ∣ q.firstRow)
    (hf : q.firstRow / 2 ^ q.bits < 2 ^ (R - q.bits)) {i j : ℕ}
    (h : cutIndex q R i = cutIndex q R j) : i = j := by
  obtain ⟨a1, -, a3⟩ := cutIndex_parts q R i hR hal hf
  obtain ⟨b1, -, b3⟩ := cutIndex_parts q R j hR hal hf
  rw [h] at a1 a3
  have e1 : i % 2 ^ q.bits = j % 2 ^ q.bits := a1.symm.trans b1
  have e2 : i / 2 ^ q.bits = j / 2 ^ q.bits := a3.symm.trans b3
  calc i = 2 ^ q.bits * (i / 2 ^ q.bits) + i % 2 ^ q.bits := (Nat.div_add_mod _ _).symm
    _ = 2 ^ q.bits * (j / 2 ^ q.bits) + j % 2 ^ q.bits := by rw [e1, e2]
    _ = j := Nat.div_add_mod _ _

/-- The lifted message of the generator's main row, at an index of g's main table, as a sum over the
message's entries. -/
theorem lift_sum (W : SwitchFrame) {aMain aM0 aT0 aM1 aT1 : ℕ}
    (F : FrameOK W aMain aM0 aT0 aM1 aT1) (x : ℕ) (hx : x < 2 ^ W.code.logN) (C : Fmt.M1.Code)
    (hC : C = codeOf W.code) (J : ℕ) (hJ : J < 2 ^ W.tableBits) :
    formAt (switchLift (Form.ofTensor (messageTensor W.code x)) W.code.logEll W.mainCut W.rowBits
      W.tableBits) J =
      ∑ j : Fin C.l, if cutIndex W.mainCut W.rowBits j.val = J then wM C x j.val else 0 := by
  subst hC
  have hl : (codeOf W.code).l = 2 ^ W.code.logEll := F.pow
  by_cases ex : ∃ j, j < 2 ^ W.code.logEll ∧ cutIndex W.mainCut W.rowBits j = J
  · obtain ⟨j0, hj0, rfl⟩ := ex
    rw [lift_message_cutIndex W F.pow F.logC F.cutBits F.cutRow F.cutTab F.cutAl F.cutFirst x hx j0
      hj0, Finset.sum_eq_single (⟨j0, by rw [hl]; exact hj0⟩ : Fin (codeOf W.code).l)]
    · simp
    · intro j _ hne
      rw [if_neg]
      intro e
      exact hne (Fin.ext (cutIndex_inj _ _ F.cutRow F.cutAl F.cutFirst e))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [lift_message_off W F.pow F.cutBits F.cutRow F.cutTab F.cutAl F.cutFirst x J hJ
      fun j hj e => ex ⟨j, hj, e⟩]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg]
    intro e
    exact ex ⟨j.val, lt_of_lt_of_eq j.isLt hl, e⟩

/-- A mask row has the coefficient 0 on every table but the one of g that takes the rest, at every
index. -/
theorem genMask_off (W : SwitchFrame) (j aM aT : ℕ) (h : MaskAt W j aM aT) (x : ℕ) (t : OnBytes.E)
    (o : ℕ) (part : Part) (J : ℕ) (hc : (W.g == o && W.restPart == part) = false) :
    coefAt (genMask W x j t) o part J = 0 := by
  have key : ∀ r : OnBytes.Row, coefAt ({ switchAddRestF r W.g W.restPart (W.maskTail.getD j [])
        (generatorTail W.zk (shortPosition W.zk.logN x)) with
        kind := .generator, target := t } : OnBytes.Row) o part J = coefAt r o part J := by
    intro r
    show coefAt (switchAddRestF r W.g W.restPart (W.maskTail.getD j [])
      (generatorTail W.zk (shortPosition W.zk.logN x))) o part J = _
    rw [h.tail, coefAt_restF_at _ _ _ _ _ _ h.incT, hc]
    simp
  unfold genMask
  rw [key]
  split
  · rw [coefAt_add, coefAt_empty, hc]
    simp
  · rename_i hb
    rw [h.msg hb, coefAt_restF_at _ _ _ _ _ _ h.incM, coefAt_empty, hc]
    simp

/-- A mask row's two stretches, as sums over the entries of its message and of its tail. -/
theorem mask_sum (W : SwitchFrame) (aM aT : ℕ) (Z : Fmt.M1.Code) (hZ : Z = codeOf W.zk) (x J : ℕ) :
    stretchAt W.places aM W.zk.ell (wM (codeOf W.zk) (shortPosition W.zk.logN x)) J +
        stretchAt W.places aT W.zk.r (wT (codeOf W.zk) (shortPosition W.zk.logN x)) J =
      (∑ j : Fin Z.l, if W.places.get (aM + j.val) = J then wM Z (Fmt.M1.cp Z x) j.val else 0) +
        ∑ q : Fin Z.r, if W.places.get (aT + q.val) = J then wT Z (Fmt.M1.cp Z x) q.val else 0 := by
  subst hZ
  unfold stretchAt
  exact congrArg₂ (· + ·) (Finset.sum_range _) (Finset.sum_range _)

/-! ## The join: the main row and the two mask rows -/

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ}

/-- **The main row.** -/
theorem main_reads (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (x : ℕ) (hx : x < 2 ^ W.code.logN)
    (t : OnBytes.E) :
    ReadsAs cs l ids (genMain W x t) (genVec s K iJ iQ x (.inl (none, ()))) := by
  intro n
  rw [genVec_row, genMain_at W aMain F.mainPieces F.mainInc F.logC x hx t,
    pushTo_at cs l _ _ 0 Part.main _ D.mainMsg n, pushTo_at cs l _ _ 0 W.restPart _ D.mainTail n]
  refine congrArg₂ (· + ·) (if_ctx_congr (tab_main (D.gIs n)) (fun c => ?_) fun _ => rfl)
    (if_ctx_congr (tab_rest (D.gIs n)) (fun _ => ?_) fun _ => rfl)
  · exact lift_sum W F x hx s.C D.codeC _ (D.mainIn n c.1 c.2)
  · have hr : W.code.r = s.C.r := by rw [D.codeC]; rfl
    rw [hr, ← D.codeC]
    unfold stretchAt
    exact Finset.sum_range _

/-- A mask row, at any two maps of names that lie on its two stretches. -/
theorem mask_reads (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (j aM aT : ℕ)
    (hM : MaskAt W j aM aT) (pM : Fin s.Z.l → (sigOf cs l).Ent) (pT : Fin s.Z.r → (sigOf cs l).Ent)
    (hpM : ∀ i, entAt cs l (pM i) = (0, W.restPart, W.places.get (aM + i.val)))
    (hpT : ∀ i, entAt cs l (pT i) = (0, W.restPart, W.places.get (aT + i.val))) (x : ℕ)
    (t : OnBytes.E) :
    ReadsAs cs l ids (genMask W x j t) fun n =>
      pushTo pM (fun i => wM s.Z (Fmt.M1.cp s.Z x) i.val) n +
        pushTo pT (fun i => wT s.Z (Fmt.M1.cp s.Z x) i.val) n := by
  intro n
  show _ = pushTo pM (fun i => wM s.Z (Fmt.M1.cp s.Z x) i.val) n +
    pushTo pT (fun i => wT s.Z (Fmt.M1.cp s.Z x) i.val) n
  rw [pushTo_at cs l _ _ 0 W.restPart _ hpM n, pushTo_at cs l _ _ 0 W.restPart _ hpT n]
  by_cases c : (entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = W.restPart
  · rw [if_pos c, if_pos c, genMask_at W j aM aT hM x t _ _ _ (D.restIn n c.1 c.2),
      if_pos ((tab_rest (D.gIs n)).2 c)]
    exact mask_sum W aM aT s.Z D.codeZ x _
  · rw [if_neg c, if_neg c, add_zero]
    refine genMask_off W j aM aT hM x t _ _ _ ?_
    rw [Bool.eq_false_iff]
    exact fun h => c ((tab_rest (D.gIs n)).1 h)

/-- **The carried mask row.** -/
theorem mask0_reads (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (x : ℕ) (t : OnBytes.E) :
    ReadsAs cs l ids (genMask W x 0 t) (genVec s K iJ iQ x (.inr (.inl ()))) := fun n =>
  (mask_reads D 0 aM0 aT0 F.mask0 _ _ D.mask0Msg D.mask0Tail x t n).trans
    (genVec_mask0 s K iJ iQ x n).symm

/-- **The fresh mask row.** -/
theorem mask1_reads (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (x : ℕ) (t : OnBytes.E) :
    ReadsAs cs l ids (genMask W x 1 t) (genVec s K iJ iQ x (.inr (.inr ()))) := fun n =>
  (mask_reads D 1 aM1 aT1 F.mask1 _ _ D.mask1Msg D.mask1Tail x t n).trans
    (genVec_mask1 s K iJ iQ x n).symm

end Join

/-! ## The rows of one draw, each at its place -/

/-- The kept rows in front of member number a. -/
def rowsBefore (ks : List KeptPlace) (a : ℕ) : ℕ := ((ks.take a).map (·.rows)).sum

/-- All kept rows. -/
def keptRows (W : SwitchFrame) : ℕ := (W.kept.map (·.rows)).sum

theorem keptFrom_length (W : SwitchFrame) (x : ℕ) (sy : ℕ → OnBytes.E) :
    ∀ (ks : List KeptPlace) (n : ℕ), (keptFrom W x sy ks n).length = (ks.map (·.rows)).sum
  | [], _ => rfl
  | k :: ks, n => by
    rw [keptFrom, List.length_append, keptFrom_length W x sy ks, List.length_map, List.length_range,
      List.map_cons, List.sum_cons]

theorem keptFrom_at (W : SwitchFrame) (x : ℕ) (sy : ℕ → OnBytes.E) :
    ∀ (ks : List KeptPlace) (n a b : ℕ) (k : KeptPlace), ks[a]? = some k → b < k.rows →
      (keptFrom W x sy ks n)[rowsBefore ks a + b]? =
        some (genKept W k b (n + (rowsBefore ks a + b)) x (sy (1 + (n + (rowsBefore ks a + b)))))
  | [], _, _, _, _, h, _ => by simp at h
  | k0 :: ks, n, 0, b, k, h, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have e : rowsBefore (k0 :: ks) 0 + b = b := by simp [rowsBefore]
    rw [e, keptFrom,
      List.getElem?_append_left (by rw [List.length_map, List.length_range]; exact hb),
      List.getElem?_map, List.getElem?_range hb]
    rfl
  | k0 :: ks, n, a + 1, b, k, h, hb => by
    simp only [List.getElem?_cons_succ] at h
    have ih := keptFrom_at W x sy ks (n + k0.rows) a b k h hb
    have e : rowsBefore (k0 :: ks) (a + 1) + b = k0.rows + (rowsBefore ks a + b) := by
      simp only [rowsBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
      omega
    have e2 : n + k0.rows + (rowsBefore ks a + b) = n + (k0.rows + (rowsBefore ks a + b)) := by
        omega
    rw [e2] at ih
    rw [e, keptFrom, List.getElem?_append_right
      (by rw [List.length_map, List.length_range]; exact Nat.le_add_right _ _), List.length_map,
      List.length_range, Nat.add_sub_cancel_left]
    exact ih

theorem cons_at {α : Type} (r : α) (L : List α) (m : ℕ) : (r :: L)[1 + m]? = L[m]? := by
  rw [Nat.add_comm, List.getElem?_cons_succ]

section Draw
variable (W : SwitchFrame) (old : SingleRows) (x : ℕ) (sy : ℕ → OnBytes.E)

theorem gens_length : (switchGenerators W old x sy).length = 1 + keptRows W + old.masks := by
  rw [switchGenerators_all, List.length_append, List.length_cons, keptFrom_length, List.length_map,
    List.length_range, keptRows]
  omega

theorem gens_main : (switchGenerators W old x sy)[0]? = some (genMain W x (sy 0)) := by
  rw [switchGenerators_all]
  rfl

theorem gens_kept (a b : ℕ) (k : KeptPlace) (hk : W.kept[a]? = some k) (hb : b < k.rows) :
    (switchGenerators W old x sy)[1 + (rowsBefore W.kept a + b)]? =
      some (genKept W k b (rowsBefore W.kept a + b) x (sy (1 + (rowsBefore W.kept a + b)))) := by
  have h := keptFrom_at W x sy W.kept 0 a b k hk hb
  rw [Nat.zero_add] at h
  rw [switchGenerators_all, List.cons_append, cons_at,
    List.getElem?_append_left ((List.getElem?_eq_some_iff.1 h).1)]
  exact h

theorem gens_mask (j : ℕ) (hj : j < old.masks) :
    (switchGenerators W old x sy)[1 + (keptRows W + j)]? =
      some (genMask W x j (sy (old.maskRow j))) := by
  rw [switchGenerators_all, Nat.add_comm 1, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [keptFrom_length]; exact Nat.le_add_right _ _),
    keptFrom_length, keptRows, Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range hj]
  rfl

end Draw

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.main_reads
#print axioms VerifiableInference.Desc.First.K2Hands.mask0_reads
#print axioms VerifiableInference.Desc.First.K2Hands.mask1_reads
#print axioms VerifiableInference.Desc.First.K2Hands.gens_length
#print axioms VerifiableInference.Desc.First.K2Hands.gens_main
#print axioms VerifiableInference.Desc.First.K2Hands.gens_kept
#print axioms VerifiableInference.Desc.First.K2Hands.gens_mask
