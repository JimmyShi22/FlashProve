-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyPile21.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE NAMED PREMISE PileOfEval OF point_back₂ (Johnson/RunOne/KeyRow21.lean) PAID: «Eval» and «V is
the row weights applied to the matrix in the witness's cells» give the pile: FOR CERTAIN: at the
library's reading of words (Reading.gl), by K13's files' eval_value | evalIn_of_rowIn
(Johnson/Desc/K13/Law/EvalProofs.lean | M4.lean) and rowHolds_iff_says_of_rowIn (Johnson/Desc/Key/).
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY.
OBJECT: PileOfEval at ρ := Reading.gl · USER: point_back₂'s premise hpile · LETTERS: the tables'; S
is p.S.
  formAt_val | eqk_rd | member_row   a mask form, the weight of a column, and a claim read back as a
    row and forth: three small bridges
  firstAt_of     what the last chain's start reads of the first chain's last state, where that holds
    a claim
  PileTies       WHAT IS LEFT, UNDER on₂ … 1: (1) V's number in the first chain's last state is
    the plan's message 2 [payable from last₁At's sizesB; at a plan without a stage it is false: a
    public condition is owed] · (2) every mask entry of the claim lies on a MASK table [a third,
    «V's layout bears the columns», is paid by the
    block's own test: layW_of_linOk]
CLAUSE (2): «Eval» reads a mask entry at its own part, the pile at the mask part: the tables lay
«L.claim.masks.all (·.part == .mask)» into sizesB from border 17 on.
BOTH CLAUSES ARE PAID OUT OF THE PROMISE, at the tables' own letters:
Johnson/RunOne/KeyPileTies.lean.

  pile_of_eval   PROVED FROM: hsame · K₁.lin = p.S · PileTies
WHAT IS SPENT OF THE PROMISE IN FRONT: Free₂ 1's eval (EvalIs) · order₁ · codes.
Nothing on soundness.
-/
import Johnson.RunOne.KeyRow21
import Johnson.Desc.K13.Law.EvalProofs
import Johnson.Desc.K13.Law.M4
import Johnson.Desc.K14.Law.LinOkGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (eqK eqK_ofFn entry_eq)
open _root_.Desc.K14.Law.ZetaWords (val_sumE)
open VerifiableInference.Desc.K13.Law (formVal maskOf lowBits eval_value evalIn_of_rowIn ρg)
open Johnson.L5.Layers (rd)

/-- A mask form in the program's arithmetic reads as the sum of coefficient times entry. -/
theorem formAt_loop {K : Type} [Field K] (ρ : Model.Reading K) (mk : Slot → E) : ∀ (f : MaskForm) (s
    : E),
    ρ.val (f.foldl (fun s x => addE s (mulE x.2 (mk x.1))) s) = ρ.val s + (f.map fun t => ρ.val t.2
        * ρ.val (mk t.1)).sum
  | [], s => by simp
  | t :: f, s => by
    rw [List.foldl_cons, formAt_loop ρ mk f, ρ.add, ρ.mul]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem formAt_val (mk : Slot → E) (f : MaskForm) : ρg.val (formAt mk f) = formVal ρg (fun s =>
    ρg.val (mk s)) f := by
  unfold formAt formVal
  rw [formAt_loop, ρg.zero, zero_add]

/-- The weight of a column at the claim's point, in the two ways of writing it. -/
theorem eqk_rd (k : Nat) (psi : List E) (hk : psi.length = k) (e : Nat) :
    Alg.eqk (rd ρg k psi) (lowBits k e) = eqK (psi.map ρg.val) e := by
  have h : psi.map ρg.val = List.ofFn (rd ρg k psi) := by
    refine List.ext_getElem (by simp [hk]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn, List.getElem_map]
    show _ = ρg.val (psi.getD i zeroE)
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  rw [h, eqK_ofFn]
  rfl

/-- A claim whose mask entries all lie on mask tables is the claim of its own row. -/
theorem member_row (c : LinClaim) (h : ∀ u ∈ c.masks.toList, u.part = .mask) : memberClaim
    (rowOfLinClaim c) = c := by
  obtain ⟨g, psi, masks, target⟩ := c
  have e : ((masks.toList.map fun m => ((⟨m.oracle, m.index⟩ : Slot), m.coeff)).map fun m =>
      (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)) = masks.toList := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id masks.toList]
    refine List.map_congr_left fun u hu => ?_
    have hp := h u hu
    obtain ⟨o, pt, i, cf⟩ := u
    simp only at hp
    subst hp
    rfl
  unfold memberClaim rowOfLinClaim
  simp only [e, Array.toArray_toList]

/-- What the last chain's start reads of the first chain's last state, where that holds a claim. -/
theorem firstAt_of (S : LinShape) (s : FirstState) (L) (hL : s.lin = some L) (f :
    VerifiableInference.Desc.Third.FirstOut)
    (h : firstAt S s = some f) : f.st = s.d.st ∧ f.own = L.own ∧ f.g = L.claim.g := by
  unfold firstAt at h
  simp only [hL, Option.bind_some, firstOf, VerifiableInference.Desc.Third.firstOutFrom] at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, rfl, rfl⟩

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **WHAT IS LEFT.** UNDER THE PROMISE IN FRONT. Paid at the tables' own letters:
Johnson/RunOne/KeyPileTies.lean. -/
def PileTies : Prop :=
  ∀ (x : (P₂ × St₂) × Fr₂.E.Str), on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 1 x → ∀ L,
      x.1.1.2.lin = some L →
    K₁.num L.w = some 2 ∧ ∀ u ∈ L.claim.masks.toList, u.part = .mask

/-- **PileOfEval, paid.** -/
theorem pile_of_eval (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y) (hK : K₁.lin = p.S)
    (hT : PileTies F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂) :
    PileOfEval F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρg := by
  intro x w hx hlin hE hV
  have hf : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 x.1 (strsOf Fr₂ x.2) := by
    rcases hx with hn | ⟨_, _, h3, _⟩
    · exact absurd trivial hn
    · exact h3
  obtain ⟨L, r, hL, hr, hrow⟩ := hf.eval
  obtain ⟨hnum, hmask⟩ := hT x hx L hL
  have hbits : p.S.kCol ≤ (linLayW x.1.1.2.d.st.codes p.S).bits := by
    rw [← hf.codes]
    exact _root_.Desc.K14.Law.layW_of_linOk _ _ hlin
  obtain ⟨r', hr', hH⟩ := (eval₄_is F G₂ at_ p.S K₁ R enc rad x.1 (strsOf Fr₂ x.2) w).1 hE
  -- the row that «Eval» names is the claim's
  have hr'' : (firstAt p.S x.1.1.2).bind (fun f => (f.st.groups[f.own]?).bind (·.rows[0]?)) = some
      r' := hr'
  obtain ⟨f, hfa, hf2⟩ := Option.bind_eq_some_iff.1 hr''
  obtain ⟨e1, e2, e3⟩ := firstAt_of p.S x.1.1.2 L hL f hfa
  rw [e1, e2, hrow] at hf2
  obtain rfl := Option.some.inj hf2
  -- it lies in order
  obtain ⟨G, hG, hG0⟩ := Option.bind_eq_some_iff.1 hrow
  have hmem : r ∈ G.rows.toList := by
    have := Array.mem_of_getElem? hG0
    exact Array.mem_toList_iff.2 this
  have hin : Means.RowIn x.1.1.2.d.st G r := hf.order₁.rows _ G hG r hmem
  have hH' : RowHolds (fun a b => ρg.val a = ρg.val b) x.1.1.2.d.st (valOf K₁ R w) r := by
    have t : RowHolds R.same x.1.1.2.d.st (valOf K₁ R w) r := hH
    unfold RowHolds at t ⊢
    exact (hsame _ _).1 t
  have hS := (rowHolds_iff_says_of_rowIn ρg x.1.1.2.d.st G _ r hin).1 hH'
  -- what it is worth
  have hmc := member_row L.claim hmask
  have hr2 : linEvalRow p.S (memberClaim (rowOfLinClaim L.claim)) L.w (linLayW x.1.1.2.d.st.codes
      p.S) = some r := by rw [hmc]; exact hr
  obtain ⟨hlen, hreq⟩ := OnBytes.Slice.linEvalRow_inv p.S L.claim L.w _ r hr
  have hEI := evalIn_of_rowIn (St := x.1.1.2.d.st) (G := G) (row := rowOfLinClaim L.claim) (w :=
      L.w) (lay := linLayW x.1.1.2.d.st.codes p.S)
    (by show L.claim.psi.length ≤ _; rw [hlen]; exact hbits) (by rw [hmc, ← hreq]; exact hin)
  have hval := eval_value p.S (rowOfLinClaim L.claim) L.w _ r x.1.1.2.d.st (fun o pt i => ρg.val
      (valOf K₁ R w o pt i)) hbits hr2 hEI
  have htar : r.target = L.claim.target := by rw [hreq]; rfl
  unfold Means.Says at hS
  rw [hval, htar] at hS
  -- the pile
  refine ⟨rowOfLinClaim L.claim, by rw [hL]; rfl, ?_⟩
  unfold TensorRowHolds
  rw [hsame, ρg.add, formAt_val, val_sumE]
  have hm : K₁.m = ⟨p.S.kCol, p.S.matrixRows⟩ := by
    unfold KPlan.m
    rw [hK]
    rfl
  rw [hm]
  show (∑ q ∈ Finset.range p.S.matrixRows, ρg.val (sumE (2 ^ p.S.kCol) fun c =>
      mulE (mulE (weightAt L.claim.g q) ((Tensor.eq L.claim.psi).entry c)) (ofF (matOf K₁ R w q
          c)))) +
    formVal ρg (fun s => ρg.val (mkOf K₁ R w s)) (rowOfLinClaim L.claim).masks = ρg.val
        L.claim.target
  rw [← hS]
  congr 1
  have hgs : (firstAt p.S x.1.1.2).map (·.g) = some L.claim.g := by rw [hfa]; exact congrArg some e3
  have e4 : ∀ e ∈ Finset.range (2 ^ p.S.kCol), Alg.eqk (rd ρg p.S.kCol (rowOfLinClaim L.claim).psi)
      (lowBits p.S.kCol e) *
      ρg.val (valOf K₁ R w L.w .main ((linLayW x.1.1.2.d.st.codes p.S).index e)) =
      ∑ q ∈ Finset.range p.S.matrixRows, ρg.val (weightAt L.claim.g q) * eqK (L.claim.psi.map
          ρg.val) e * ρg.val (ofF (matOf K₁ R w q e)) := fun e he => by
    have hv := hV e (Finset.mem_range.1 he)
    have ev : vK R ρg p.S x.1.2.st.codes w e = ρg.val (valOf K₁ R w L.w .main ((linLayW
        x.1.1.2.d.st.codes p.S).index e)) := by
      unfold vK vOf' valOf
      rw [hnum, hf.codes]
      rfl
    have hk' : Alg.eqk (rd ρg p.S.kCol (rowOfLinClaim L.claim).psi) (lowBits p.S.kCol e) = eqK
        (L.claim.psi.map ρg.val) e :=
      eqk_rd p.S.kCol L.claim.psi hlen e
    rw [← ev, hv, hk', Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have eg : gK ρg p.S x.1.1 q = ρg.val (weightAt L.claim.g q) := by
      unfold gK
      rw [hgs]
    have em : _root_.Desc.K14.Law.matOf p.S.kLo (tabK R ρg (some w.cells)) q e = ρg.val (ofF (matOf
        K₁ R w q e)) := by
      unfold matOf
      rw [hK]
      rfl
    rw [eg, em]
    ring
  rw [Finset.sum_congr rfl e4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [val_sumE]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ρg.mul, ρg.mul, entry_eq ρg, ρg.one, one_mul]

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.member_row
#print axioms Johnson.RunOne.KeyRows23.pile_of_eval
